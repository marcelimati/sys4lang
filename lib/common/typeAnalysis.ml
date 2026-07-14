(* Copyright (C) 2021 Nunuhara Cabbage <nunuhara@haniwa.technology>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://gnu.org/licenses/>.
 *)

open Base
open Jaf
open CompileError

(* When true, FuncType None and Delegate None will match any function types.
   This is necessary for the LSP contexts where functype/delegate information
   read from ain file is incomplete. *)
let loose_functype_check = ref false
let sprintf = Printf.sprintf

(* v11+ interface subtyping: a Struct value satisfies a parameter / return
   type of a different Struct iff the actual struct implements the
   expected struct as an interface (per Ain.Struct.interfaces). Set at
   the start of [check_types_exn] / [resolve_overload]'s containing
   visitor; nil-out at exit to avoid leaking across files. *)
let current_ain : Ain.t option ref = ref None

let struct_implements_interface ~actual_idx ~expected_idx =
  match !current_ain with
  | None -> false
  | Some ain ->
      if actual_idx < 0 || expected_idx < 0 then false
      else
        let s = Ain.get_struct_by_index ain actual_idx in
        List.exists s.interfaces ~f:(fun (i : Ain.Struct.interface) ->
            i.struct_type = expected_idx)

let is_interface_compatible expected actual =
  match (expected, actual) with
  | Struct (_, exp_idx), Struct (_, act_idx) ->
      struct_implements_interface ~actual_idx:act_idx ~expected_idx:exp_idx
  | Ref (Struct (_, exp_idx)), Ref (Struct (_, act_idx))
  | Ref (Struct (_, exp_idx)), Struct (_, act_idx)
  | Struct (_, exp_idx), Ref (Struct (_, act_idx)) ->
      struct_implements_interface ~actual_idx:act_idx ~expected_idx:exp_idx
  | _ -> false

(* An lvalue is an expression which denotes a location that can be assigned to. *)
let rec is_lvalue = function
  | { ty = TyFunction _; _ } -> false
  | { node = Ident _ | Member _ | Subscript _ | New _ | OptionalMember _; _ } ->
      true
  (* v12 interface downcast (`(IFoo)expr`) preserves the underlying
     storage — if the inner is an lvalue, the cast is too. *)
  | { node = Cast (_, inner); _ } -> is_lvalue inner
  (* v11 [hll_param] is the polymorphic wildcard — HLL-side parameter
     storage that the language doesn't introspect — so any expression
     typed [HLLParam] is treated as an addressable slot. *)
  | { ty = HLLParam; _ } -> true
  (* A call returning a reference (e.g. HLL [Array.EmplaceBack] /
     [Array.Last]) yields an lvalue: the returned reference denotes
     the underlying storage. *)
  | {
      node =
        Call (_, _, (HLLCall _ | BuiltinCall _ | MethodCall _ | FunctionCall _));
      ty = Ref _;
      _;
    } ->
      true
  | _ -> false

(* A value from which a reference can be made. NULL, reference, this, and
   lvalue are referenceable. *)
let rec is_referenceable = function
  | { ty = NullType | Ref _; _ } -> true
  | { node = This; _ } -> true
  | {
      node =
        Call (_, _, (MethodCall _ | BuiltinCall _ | HLLCall _ | FunctionCall _));
      _;
    } ->
      true
  | { node = RvalueRef _; _ } -> true
  (* v12 [a ?? b] / [a ? b : c]: referenceable if the primary branch
     is — v12 source uses int sentinels like `-1` on the fallback
     side for ref-typed returns, where -1 is the null encoding. *)
  | { node = NullCoalesce (a, _); _ } -> is_referenceable a
  | { node = Ternary (_, b, _); _ } -> is_referenceable b
  (* v12 cast preserves referenceability of its inner expression. *)
  | { node = Cast (_, inner); _ } -> is_referenceable inner
  (* v12 array/new expressions are addressable temporaries. *)
  | { node = ArrayLiteral _ | New _ | NewCall _; _ } -> true
  | e -> is_lvalue e

(* Implicit dereference of variables and members. The value of a comma
   expression follows its right operand. *)
let rec maybe_deref (e : expression) =
  match e with
  | {
      ty = Ref t;
      node =
        Ident _ | Member _
        | Call (_, _, (HLLCall _ | MethodCall _ | FunctionCall _ | BuiltinCall _))
        | Subscript _;
      _;
    } ->
      e.ty <- t
  | { node = Seq (_, e2); _ } ->
      maybe_deref e2;
      e.ty <- e2.ty
  (* v11 [Wrap T] is a fat-ref representation used for ref-returning
     HLL calls and foreach-desugared containers; surface code observes
     the inner type. *)
  | { ty = Wrap t; _ } -> e.ty <- t
  | _ -> ()

let insert_rvalue_ref e =
  let needs_wrap =
    (not (is_referenceable e))
    ||
    match e.node with
    (* A call whose ain-level return is a ref still needs a dummy slot
       when the language-level type isn't [Ref _], so the rvalue has a
       stable address for downstream consumers (e.g. method receivers).
       [FunctionCall] belongs here too: [f(...).String()] must spill
       the result into a [<dummy : 右辺値参照化用>] local because the
       Int/Float HLL receiver is a (page, index) pair — passing the
       bare value makes the VM pop the value as the index and whatever
       lies beneath as the page. *)
    | Call
        (_, _, (BuiltinCall _ | HLLCall _ | MethodCall _ | FunctionCall _)) -> (
        match e.ty with Ref _ -> false | _ -> true)
    | _ -> false
  in
  if needs_wrap then (
    e.node <- RvalueRef (clone_expr e);
    e.ty <- Ref e.ty)

let rec type_equal (expected : jaf_type) (actual : jaf_type) =
  match (expected, actual) with
  | TypeUnion (a, b), t -> type_equal a t || type_equal b t
  | Ref a, Ref b -> type_equal a b
  (* v11: a bare [T] satisfies a [Ref T] expectation when their inner
     types match — the RvalueRef wrapping is inserted later in
     [insert_rvalue_ref]. *)
  | Ref a, b when type_equal a b -> true
  (* v12 allows the inverse — a [Ref T] expression in a [T] context
     is implicitly dereffed. Lets e.g. a ternary returning [Ref T]
     flow into a struct-typed assignment target. *)
  | a, Ref b when type_equal a b -> true
  | Void, Void -> true
  | Int, (Int | Bool | LongInt) -> true
  | Bool, (Int | Bool | LongInt) -> true
  | LongInt, (Int | Bool | LongInt) -> true
  | (Int | Bool | LongInt), Enum _ -> true
  | Enum _, (Int | Bool | LongInt) -> true
  | Enum (_, a), Enum (_, b) -> a = b
  | Float, Float -> true
  | String, String -> true
  | Struct (_, a), Struct (_, b) -> a = -1 (* any struct *) || a = b
  | IMainSystem, (IMainSystem | Int) -> true
  | FuncType (Some (_, a)), FuncType (Some (_, b)) -> a = b
  | FuncType None, FuncType _ | FuncType _, FuncType None -> true
  | Delegate (Some (_, a)), Delegate (Some (_, b)) -> a = b
  (* v12 decompiler sometimes loses delegate-specialization info and
     emits [unknown_delegate]; treat as compatible with any concrete
     delegate. Same idea as the [loose_functype_check] LSP flag, but
     unconditional for the compiler — we'd rather under-check than
     refuse to compile decompiled v12 source. *)
  | Delegate None, Delegate _ | Delegate _, Delegate None -> true
  | MemberPtr (s1, t1), MemberPtr (s2, t2) ->
      String.equal s1 s2 && type_equal t1 t2
  | NullType, (FuncType _ | Delegate _ | IMainSystem | NullType) -> true
  (* v11 [hll_param] is the polymorphic wildcard — HLL-side storage
     the language doesn't introspect. Compatible with any type from
     either direction, also through a [Ref _] wrapper. *)
  | HLLParam, _ -> true
  | _, HLLParam -> true
  | Ref HLLParam, _ -> true
  | _, Ref HLLParam -> true
  (* v11 [hll_func2] is the polymorphic-callable wildcard used by HLL
     bridges; same wildcard semantics as [hll_param]. *)
  | HLLFunc2, _ -> true
  | _, HLLFunc2 -> true
  (* v11 [Wrap T] is a fat-ref representation; strip it on either
     side, including the [Wrap T] vs [Ref T] case where the wrap is
     just an alternate encoding of the same reference. *)
  | Wrap a, Ref b | Ref a, Wrap b -> type_equal a b
  | Wrap a, b | b, Wrap a -> type_equal a b
  | Array _, Array Void | Array Void, Array _ -> true
  | Array a, Array b -> type_equal a b
  | HLLFunc, _ -> true
  | _, HLLFunc -> true
  | Void, _
  | Ref _, _
  | Int, _
  | Bool, _
  | LongInt, _
  | Enum _, _
  | Float, _
  | String, _
  | Struct _, _
  | IMainSystem, _
  | FuncType _, _
  | Delegate _, _
  | Array _, _
  | TyFunction _, _
  | TyMethod _, _
  | NullType, _
  | MemberPtr _, _ ->
      false
  | Untyped, _ -> compiler_bug "expected type is untyped" None
  | Unresolved _, _ -> compiler_bug "expected type is unresolved" None

let type_castable (dst : jaf_type) (src : jaf_type) =
  match (dst, src) with
  (* FIXME: cast to void should be allowed *)
  | Void, _ -> compiler_bug "type checker cast to void type" None
  | (Int | LongInt | Bool | Float | String | Enum _),
    (Int | LongInt | Bool | Float | Enum _) ->
      true
  (* v12 user-type casts (`IParts(rect)`, `ISpriteParts(p.Get(state))`) —
     allow any struct-to-struct cast; runtime handles interface checks. *)
  | Struct _, Struct _ -> true
  | Struct _, Ref (Struct _) -> true
  | Struct _, NullType -> true
  (* HLL-generic source flows into any cast target. *)
  | _, HLLParam -> true
  | _ -> false

let type_check parent expected (actual : expression) =
  (match expected with Ref _ -> () | _ -> maybe_deref actual);
  match actual.ty with
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | NullType -> (
      match expected with
      | Ref _ | FuncType _ | Delegate _ | IMainSystem
      (* v11+ allow NULL for Struct/Array/String parameters/returns —
         these are heap-allocated and have a NULL representation at
         runtime. *)
      | Struct _ | Array _ | String
      (* v12 also lets NULL flow into method/function-typed parameters
         (e.g. `b ? handler : NULL` to clear a callback). *)
      | TyMethod _ | TyFunction _ -> actual.ty <- expected
      | _ -> type_error expected (Some actual) parent)
  | Void ->
      (* v12 sometimes flows Void into positions expecting another
         type (e.g. property-set in null-coalesce that feeds a
         ternary). Accept — the value is unused at the type-check
         level. *)
      ()
  (* HLL generic flows into any expected type *)
  | HLLParam -> ()
  | a_t ->
      (* v12 sometimes assigns a Struct value into a Delegate-typed
         slot (decompiler quirk where the actual type info was lost).
         Permit at compile time; runtime handles. *)
      let struct_to_delegate =
        match (expected, a_t) with
        | (Delegate _ | FuncType _), Struct _ -> true
        | _ -> false
      in
      if (not (type_equal expected a_t))
         && (not (is_interface_compatible expected a_t))
         && not struct_to_delegate
      then type_error expected (Some actual) parent

let ref_type_check parent expected (actual : expression) =
  match actual.ty with
  | NullType -> actual.ty <- Ref expected
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | Ref t ->
      if (not (type_equal expected t))
         && not (is_interface_compatible expected t)
      then type_error (Ref expected) (Some actual) parent
  | _ ->
      if (not (type_equal expected actual.ty))
         && not (is_interface_compatible expected actual.ty)
      then type_error (Ref expected) (Some actual) parent

let type_check_numeric parent (actual : expression) =
  maybe_deref actual;
  match actual.ty with
  | Int | Bool | LongInt | Float | Enum _ -> ()
  (* HLL-generic values flow as if numeric — the wildcard means we
     can't say more at compile time. *)
  | HLLParam -> ()
  (* v12 sometimes a property-set expression (which is typed Void)
     feeds into a ternary/null-coalesce that expects numeric. Accept
     Void with a no-op rather than erroring; the runtime semantics
     are governed by the surrounding NullCoalesce. *)
  | Void -> ()
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | _ -> type_error Int (Some actual) parent

let type_check_member_lhs ?(v11 = false) parent (actual : expression) =
  match actual.ty with
  | Ref (Struct (name, _)) -> name
  (* v11 [Wrap (Struct _)] / [Wrap (Ref Struct _)] are fat-ref encodings
     that surface in HLL-returned struct expressions; member access on
     them is legal. *)
  | Wrap (Struct (name, _)) | Wrap (Ref (Struct (name, _))) when v11 -> name
  | Struct (name, _) -> (
      let allowed_v11 = function
        | Call _ | New _ | OptionalMember _ | NullCoalesce _ -> true
        (* v12 user-type cast result is also a transient struct value
           that can serve as the receiver for further member access. *)
        | Cast _ -> true
        | _ -> false
      in
      match actual.node with
      | Ident _ | Member _ | Subscript _ | This -> name
      (* v11 permits chained member access on transient struct values
         returned by calls / [new T()] / [obj?.X] / [a ?? b]. *)
      | n when v11 && allowed_v11 n -> name
      | _ ->
          compile_error "Member access not allowed for temporary object" parent)
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | _ -> type_error (Struct ("struct", 0)) (Some actual) parent

let check_not_array (e : expression) =
  match e.ty with
  | Array _ | Ref (Array _) -> (
      (* v11: an array-typed expression is allowed at statement
         position when it carries an intentional side effect — a call
         (chainable HLL methods like [arr.AscSort()]) or an assignment
         (array copy-assign). Pre-v11 didn't have these patterns. *)
      match e.node with
      | Call _ | Assign _ -> ()
      (* v12 sometimes leaves a bare ArrayLiteral as an expression
         statement (decompiler quirk where the array's use was lost).
         Permit — the runtime effect is just allocate-and-drop. *)
      | ArrayLiteral _ -> ()
      | _ ->
          compile_error "array expression not allowed here" (ASTExpression e))
  | _ -> ()

(** True if the expression already produces a 0/1 bool at bytecode
    level (comparisons, logical ops, [LogNot], explicit Bool cast).
    v11 codegen uses this to decide whether to insert an [ITOB]
    normalisation before [IFZ]. *)
let is_bool_producing_expr (e : expression) =
  match e.node with
  | Binary (op, _, _) -> (
      match op with
      | Equal | NEqual | LT | GT | LTE | GTE | RefEqual | RefNEqual | LogOr
      | LogAnd ->
          true
      | _ -> false)
  | Unary (LogNot, _) -> true
  | Cast (Bool, _) -> true
  | _ -> false

(* Substitute the polymorphic [HLLParam] wildcard with the concrete
   element type of the receiver. v11 HLL Array methods like
   [EmplaceBack] declare their result as [ref hll_param]; on a typed
   [array<T>] receiver this should be [ref T] so further member access
   on the returned value (e.g. calling a method on a returned struct)
   typechecks. *)
let specialize_hll_param elem_ty t =
  match elem_ty with
  | None -> t
  | Some et ->
      let rec sub = function
        | HLLParam -> et
        | Array Void -> Array et
        | Ref (Array Void) -> Ref (Array et)
        | Wrap (Array Void) -> Wrap (Array et)
        | Wrap (Ref (Array Void)) -> Wrap (Ref (Array et))
        (* [Ref HLLParam] specialised with an element type that's
           itself [Ref T] would yield [Ref (Ref T)] — an ill-formed
           double ref. Collapse into a single [Ref T]. *)
        | Ref HLLParam -> ( match et with Ref _ -> et | _ -> Ref et)
        | Array t -> Array (sub t)
        | Ref t -> Ref (sub t)
        | Wrap t -> Wrap (sub t)
        | t -> t
      in
      sub t

let rec array_elem_type_of_expr (e : expression) =
  let concrete_elem = function
    | Array HLLParam | Ref (Array HLLParam) | Wrap (Array HLLParam)
    | Wrap (Ref (Array HLLParam)) ->
        None
    | Array t | Ref (Array t) | Wrap (Array t) | Wrap (Ref (Array t)) ->
        Some t
    | _ -> None
  in
  match concrete_elem e.ty with
  | Some _ as elem -> elem
  | None -> (
      match e.node with
      | Cast (_, inner) | RvalueRef inner | DummyRef (_, inner) ->
          array_elem_type_of_expr inner
      | Call (_, Some receiver :: _, HLLCall _) ->
          array_elem_type_of_expr receiver
      | _ -> None)

let is_builtin = function
  | Int | Float | String | Array _ | Delegate _ -> true
  | Ref (Int | Float | String | Array _ | Delegate _) -> true
  (* v11 fat-ref encoding for HLL returns wraps the payload in a Wrap
     node — member access should still dispatch to the underlying
     primitive's builtins. *)
  | Wrap (Int | Float | String | Array _ | Delegate _) -> true
  | Wrap (Ref (Int | Float | String | Array _ | Delegate _)) -> true
  | _ -> false

let resolve_builtin ctx e name =
  let lib_name, builtin_getter =
    match e.ty with
    | Int | Ref Int | Wrap Int | Wrap (Ref Int) ->
        ("Int", Bytecode.int_builtin_of_string)
    | Float | Ref Float | Wrap Float | Wrap (Ref Float) ->
        ("Float", Bytecode.float_builtin_of_string)
    | String | Ref String | Wrap String | Wrap (Ref String) ->
        ("String", Bytecode.string_builtin_of_string)
    | Array _ | Ref (Array _) | Wrap (Array _) | Wrap (Ref (Array _)) ->
        ("Array", Bytecode.array_builtin_of_string)
    | Delegate _ | Ref (Delegate _) | Wrap (Delegate _) | Wrap (Ref (Delegate _)) ->
        ("Delegate", Bytecode.delegate_builtin_of_string)
    | _ -> failwith "cannot happen"
  in
  match Hashtbl.find ctx.libraries lib_name with
  | Some l when ctx.version >= 800 -> (
      match Hashtbl.find l.functions name with
      | Some _ -> Some (BuiltinHLL lib_name)
      | None -> None)
  | _ -> (
      maybe_deref e;
      match builtin_getter name with
      | Some b -> Some (BuiltinMethod b)
      | None -> None)

let insert_cast t (e : expression) =
  e.node <- Cast (t, clone_expr e);
  e.ty <- t

let type_coerce_numerics parent op a b =
  type_check_numeric parent a;
  type_check_numeric parent b;
  let coerce t e =
    insert_cast t e;
    t
  in
  let is_compare_op = function
    | Equal | NEqual | LT | GT | LTE | GTE -> true
    | _ -> false
  in
  match (a.ty, b.ty) with
  | Float, Float -> Float
  | Float, _ -> coerce Float b
  | _, Float -> coerce Float a
  | LongInt, LongInt -> LongInt
  | LongInt, Int when is_compare_op op -> LongInt
  | Int, LongInt when is_compare_op op -> LongInt
  | LongInt, _ -> coerce LongInt b
  | _, LongInt -> coerce LongInt a
  | Enum _, Enum _ -> Int
  | Enum _, _ -> coerce Int a
  | _, Enum _ -> coerce Int b
  | Int, Int -> Int
  | Int, _ -> coerce Int b
  | _, Int -> coerce Int a
  | Bool, Bool -> (
      match op with
      | Equal | NEqual | LogOr | LogAnd | BitOr | BitAnd | BitXor -> Bool
      | _ -> compile_error "invalid operation on boolean type" parent)
  | _ -> compiler_bug "coerce_numerics: non-numeric type" (Some parent)

class type_analyze_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val mutable errors : compile_error list = []
    method errors = List.rev errors

    method catch_errors f =
      try f () with Compile_error e -> errors <- e :: errors

    method ensure_array_callback_delegate ?(readonly = false) kind elem_ty =
      if Ain.version_gte ctx.ain (12, 0) then
        let callback_ty =
          match elem_ty with
          | Struct _ -> Ref elem_ty
          | _ -> elem_ty
        in
        let callback_name_ty =
          match elem_ty with
          | Struct (name, _) -> "ref " ^ name
          | _ -> jaf_type_to_string elem_ty
        in
        let callback_name_ty =
          if readonly then "readonly " ^ callback_name_ty
          else callback_name_ty
        in
        let name = sprintf "<Array%sFunc@%s>" kind callback_name_ty in
        let allowed_by_reference =
          match ctx.v12_reference_array_delegates with
          | None -> true
          | Some delegates -> Hashtbl.mem delegates name
        in
        if allowed_by_reference && not (Hashtbl.mem ctx.delegates name) then begin
          let param pname ty =
            {
              name = pname;
              location = dummy_location;
              array_dim = [];
              is_const = false;
              is_private = false;
              kind = Parameter;
              type_spec = { ty; location = dummy_location };
              initval = None;
              index = None;
            }
          in
          let return_ty, params =
            match kind with
            | "Find" -> (Bool, [ param "obj" callback_ty ])
            | "Sort" ->
                ( Bool,
                  [ param "lhs" callback_ty; param "rhs" callback_ty ] )
            | "Equal" ->
                ( Bool,
                  [ param "lhs" callback_ty; param "rhs" callback_ty ] )
            | "Compare" -> (Int, [ param "obj" callback_ty ])
            | _ -> (Void, [])
          in
          let f =
            {
              name;
              loc = dummy_location;
              return = { ty = return_ty; location = dummy_location };
              params;
              body = None;
              is_label = false;
              is_lambda = false;
              is_private = false;
              index = Some (Ain.add_delegate ctx.ain name).index;
              class_name = None;
              class_index = None;
            }
          in
          Hashtbl.set ctx.delegates ~key:name ~data:f;
          jaf_to_ain_functype ~ctx f |> Ain.write_delegate ctx.ain
        end

    method ensure_array_hll_callback_delegates fun_name elem_ty raw_params args =
      if Ain.version_gte ctx.ain (12, 0) then begin
        let has_hll_func_arg =
          List.exists2_exn raw_params args ~f:(fun p arg ->
              match (p.type_spec.ty, arg) with
              | (HLLFunc | HLLFunc2), Some _ -> true
              | _ -> false)
        in
        let has_hll_param_arg =
          List.exists2_exn raw_params args ~f:(fun p arg ->
              match (p.type_spec.ty, arg) with
              | HLLParam, Some _ -> true
              | _ -> false)
        in
        match fun_name with
        | "Find" | "FindLast" | "IsExist" | "Any" | "All" | "Erase"
        | "EraseAll" | "Remain" | "Numof" | "Where" | "First" | "Last"
          when has_hll_func_arg ->
            (* v12 may materialize both mutable and readonly callback
               delegate names for the same Array HLL predicate type. *)
            self#ensure_array_callback_delegate "Find" elem_ty;
            self#ensure_array_callback_delegate ~readonly:true "Find" elem_ty
        | "Sort" | "QuickSort" | "Min" | "Max" when has_hll_func_arg ->
            self#ensure_array_callback_delegate "Sort" elem_ty
        | "Unique" when has_hll_func_arg ->
            self#ensure_array_callback_delegate "Equal" elem_ty
        | "Find" | "FindLast" | "IsExist" | "Unique" when has_hll_param_arg -> (
            match elem_ty with
            | Int | String -> self#ensure_array_callback_delegate "Equal" elem_ty
            | Bool -> ()
            | _ -> self#ensure_array_callback_delegate "Find" elem_ty)
        | "LowerBound" | "UpperBound" | "BinarySearch"
          when has_hll_func_arg ->
            (* Same dual-name behavior as predicate callbacks. *)
            self#ensure_array_callback_delegate "Compare" elem_ty;
            self#ensure_array_callback_delegate ~readonly:true "Compare" elem_ty
        | "LowerBound" | "UpperBound" | "BinarySearch"
          when has_hll_param_arg ->
            self#ensure_array_callback_delegate "Compare" elem_ty
        | _ -> ()
      end

    method check_lvalue e parent =
      if not (is_lvalue e) then not_an_lvalue_error e parent

    method check_referenceable e parent =
      if not (is_referenceable e) then not_an_lvalue_error e parent

    (* v11 overload resolution: a name registered in [ctx.functions]
       may have alternates in [ctx.overloads]. Pick the candidate
       whose parameter types match the actual argument types; fall
       back to the primary so [check_call] can produce its own
       diagnostics on mismatch. Empty alternate list (the pre-v11 /
       non-overloaded common case) returns the primary unchanged. *)
    method resolve_overload (name : string) (args : expression option list) =
      let primary =
        match Hashtbl.find ctx.functions name with
        | Some f -> f
        | None ->
            (* Tolerate missing-by-name: a name might be a virtual /
               interface method handled at runtime. Construct a stub
               so check_call can still progress. *)
            { name; loc = dummy_location;
              return = { ty = HLLParam; location = dummy_location };
              params = []; body = None;
              is_label = false; is_lambda = false; is_private = false;
              index = Some 0; class_name = None; class_index = None }
      in
      match Hashtbl.find ctx.overloads name with
      | None | Some [] -> primary
      | Some alternates ->
          let arg_types =
            List.map args ~f:(function Some a -> Some a.ty | None -> None)
          in
          let arg_compat_with_param (param : variable) (arg_ty : jaf_type) =
            match (param.type_spec.ty, arg_ty) with
            | Delegate _, (TyMethod _ | TyFunction _) -> true
            | FuncType _, (TyMethod _ | TyFunction _) -> true
            (* A [ref T] argument satisfies a plain [T] parameter; the
               reference is dereffed at call time. *)
            | pt, Ref at when type_equal pt at -> true
            (* NULL is a valid argument for any nullable parameter type
               (delegates, function types, structs, arrays, strings —
               the things that have a NULL value at runtime). Without
               this, `f(x, NULL, NULL)` overload resolution falls back
               to the primary by mistake. *)
            | (Delegate _ | FuncType _ | Struct _ | Array _ | Ref _ | String), NullType
              -> true
            (* Implicit numeric conversions for overload arity-matching:
               int param accepts float arg (truncate), and vice versa. *)
            | (Int | LongInt | Bool), (Int | LongInt | Bool | Float) -> true
            | Float, (Int | LongInt | Bool | Float) -> true
            | _ -> type_equal param.type_spec.ty arg_ty
          in
          let param_matches (fd : fundecl) =
            List.length fd.params = List.length arg_types
            && List.for_all2_exn fd.params arg_types ~f:(fun p at ->
                   match at with
                   | None -> true (* default argument; accept *)
                   | Some t -> arg_compat_with_param p t)
          in
          (match
             List.filter (primary :: alternates) ~f:param_matches
           with
          | [ fd ] -> fd
          | fd :: _ as matches -> (
              match self#env#current_function with
              | Some current -> (
                  let current_idx = current.index in
                  match current_idx with
                  | Some _ -> (
                      match
                        List.find matches ~f:(fun f ->
                            not (Option.equal Int.equal f.index current_idx))
                      with
                      | Some non_current -> non_current
                      | None -> fd)
                  | None -> fd)
              | None -> fd)
          | [] -> primary)

    (* v11 HLL overload resolution: pick the library function matching
       the actual call's arity. Among same-arity candidates, prefer one
       whose param types specifically accept a function/lambda argument
       when one is being passed (e.g. [Array.Find(int, int, hll_func2)]
       over [Array.Find(int, int, hll_param)] when the user passes a
       lambda; the reverse when passing values). [skip_self] is true for
       built-in HLL methods, where [params.[0]] is the implicit receiver
       and only [params.[1..]] participate in matching against the
       user-visible call args. *)
    method resolve_hll_overload (lib : library) (fun_name : string)
        ~(skip_self : bool) (args : expression option list) =
      let primary = Hashtbl.find_exn lib.functions fun_name in
      let alternates =
        Option.value ~default:[] (Hashtbl.find lib.overloads fun_name)
      in
      match alternates with
      | [] -> primary
      | _ ->
          let nr_user_args = List.length args in
          let user_params (fd : fundecl) =
            if skip_self then List.tl_exn fd.params else fd.params
          in
          let arity_matches (fd : fundecl) =
            List.length (user_params fd) = nr_user_args
          in
          let candidates = primary :: alternates in
          let by_arity = List.filter candidates ~f:arity_matches in
          let call_has_func_arg =
            List.exists args ~f:(function
              | Some { ty = TyMethod _ | TyFunction _ | HLLFunc | HLLFunc2; _ }
                ->
                  true
              | Some { node = Lambda _; _ } -> true
              | _ -> false)
          in
          let prefers_func_param (fd : fundecl) =
            List.exists (user_params fd) ~f:(fun p ->
                match p.type_spec.ty with
                | HLLFunc | HLLFunc2 -> true
                | _ -> false)
          in
          let fn_overloads, non_fn_overloads =
            List.partition_tf by_arity ~f:prefers_func_param
          in
          let ordered =
            if call_has_func_arg then fn_overloads @ non_fn_overloads
            else non_fn_overloads @ fn_overloads
          in
          (* Prefer overloads whose parameter types match the actual
             arg types element-wise (compatible with type_equal). This
             distinguishes e.g. `Erase(int)` from `Erase(ref array)`
             when both are arity-1. Falls through to the arity-only
             ordering when no exact type match exists. *)
          let arg_types_match (fd : fundecl) =
            List.for_all2_exn (user_params fd) args ~f:(fun p a ->
                match a with
                | None -> true
                | Some a -> type_equal p.type_spec.ty a.ty)
          in
          let typed_match =
            List.filter ordered ~f:arg_types_match
          in
          (match typed_match with
          | fd :: _ -> fd
          | [] -> (
              match ordered with
              | fd :: _ -> fd
              | [] -> primary))

    (* Map a chosen HLL fundecl back to its ain library-function index.
       [Ain.get_library_function_index] looks up by name and returns
       the first matching entry, which is wrong when the library has
       multiple ain entries sharing a name. Walk the library's
       functions array looking for an entry whose argument types
       match the chosen fundecl's parameter types; fall back to the
       first same-arity entry, then to the name-keyed lookup. *)
    method resolve_hll_ain_index (lib_no : int) (f : fundecl) =
      let lib = Ain.get_library_by_index ctx.ain lib_no in
      let expected_arity = List.length f.params in
      let param_types_match (lf : Ain.Library.Function.t) =
        List.length lf.arguments = expected_arity
        && List.for_all2_exn lf.arguments f.params ~f:(fun la p ->
               Poly.equal la.value_type (jaf_to_ain_type p.type_spec.ty))
      in
      let arity_matches (lf : Ain.Library.Function.t) =
        List.length lf.arguments = expected_arity
      in
      let by_full_match =
        Array.find lib.functions ~f:(fun lf ->
            String.equal lf.name f.name && param_types_match lf)
      in
      match by_full_match with
      | Some lf ->
          fst
            (Option.value_exn
               (Array.findi lib.functions ~f:(fun _ x -> phys_equal x lf)))
      | None -> (
          let by_arity =
            Array.findi lib.functions ~f:(fun _ lf ->
                String.equal lf.name f.name && arity_matches lf)
          in
          match by_arity with
          | Some (i, _) -> i
          | None ->
              Option.value_exn
                (Ain.get_library_function_index ctx.ain lib_no f.name))

    (*
     * Assigning to a functype or delegate variable is special.
     * The RHS should be an expression like &foo, which has type
     * 'ref function'. This is then converted into the declared
     * functype of the variable (if the prototypes match).
     *)
    method check_functype_compatible parent functype (expr : expression) =
      match (functype, expr.ty) with
      | Some (ft_name, _), TyFunction ft ->
          let fd = Hashtbl.find_exn ctx.functypes ft_name in
          if not (ft_compatible (ft_of_fundecl fd) ft) then
            type_error (FuncType functype) (Some expr) parent
      | Some (ft_name, _), FuncType (Some (ft2_name, _)) ->
          let ft = Hashtbl.find_exn ctx.functypes ft_name in
          let ft2 = Hashtbl.find_exn ctx.functypes ft2_name in
          if not (ft_compatible (ft_of_fundecl ft) (ft_of_fundecl ft2)) then
            type_error (FuncType functype) (Some expr) parent
      | Some _, String -> ()
      | Some _, NullType -> expr.ty <- FuncType functype
      | None, (TyFunction _ | FuncType _ | String | NullType)
        when !loose_functype_check ->
          ()
      | _ -> type_check parent (FuncType functype) expr

    method check_delegate_compatible parent delegate (expr : expression) =
      if Ain.version ctx.ain >= 12 then (
        match (delegate, expr.ty) with
        | Some _, String ->
            insert_cast (Delegate delegate) expr
        | Some (dg_name, _), TyFunction ft ->
            let dt = ft_of_fundecl (Hashtbl.find_exn ctx.delegates dg_name) in
            if ft_compatible dt ft then insert_cast (TyMethod dt) expr
        | Some _, NullType | None, NullType ->
            expr.ty <- Delegate delegate
        | _ ->
            ())
      else
      match delegate with
      | Some (dg_name, dg_i) -> (
          let dt = ft_of_fundecl (Hashtbl.find_exn ctx.delegates dg_name) in
          let check ft =
            if not (ft_compatible dt ft) then
              type_error (Delegate delegate) (Some expr) parent
          in
          match expr.ty with
          | TyMethod ft -> check ft
          | TyFunction ft ->
              check ft;
              insert_cast (TyMethod dt) expr
          | Delegate (Some (name, idx)) ->
              if not (String.equal name dg_name && dg_i = idx) then
                type_error (Delegate delegate) (Some expr) parent
          | NullType -> expr.ty <- Delegate delegate
          | String ->
              (* String -> Method conversion, but needs a delegate index
                 for DG_STR_TO_METHOD. Pre-v11 the cast leaves a method-
                 pointer on the stack so the surrounding [Delegate] arg
                 path needs to know to wrap with DG_NEW_FROM_METHOD —
                 mark [expr.ty] as [TyMethod] for that. v11's cast
                 handler emits DG_NEW_FROM_METHOD inline, so leave the
                 type as the natural [Delegate]; otherwise
                 [compile_argument] would add a *second* wrap and the
                 call would push a doubly-wrapped delegate. *)
              insert_cast (Delegate delegate) expr;
              if not (Ain.version_gte ctx.ain (11, 0)) then
                expr.ty <- TyMethod dt
          | _ -> type_check parent (Delegate delegate) expr)
      | None -> (
          match expr.ty with
          | Delegate None -> ()
          | (TyMethod _ | TyFunction _ | Delegate _ | String | NullType)
            when !loose_functype_check ->
              ()
          | _ -> type_check parent (Delegate delegate) expr)

    method check_assign parent t (rhs : expression) =
      (* v12 [target = NULL]: a bare [NULL] literal has [ty = NullType]
         until we coerce it. Push the lhs type onto the Null so the
         codegen [Null] case picks the right opcode (DG_NEW for
         delegate, PUSH -1 for struct/array, S_PUSH 0 for string,
         etc.). Without this, codegen treats it as an [Int] [PUSH 0]
         and downstream ASSIGN/POP get misaligned. *)
      (match rhs with
       | { node = Null; ty = NullType; _ } -> rhs.ty <- t
       | _ -> ());
      match t with
      | FuncType ft -> self#check_functype_compatible parent ft rhs
      | Delegate dg -> self#check_delegate_compatible parent dg rhs
      | TyFunction cb -> (
          match rhs.ty with
          | TyFunction f ->
              if not (ft_compatible cb f) then type_error t (Some rhs) parent
          | _ -> type_error t (Some rhs) parent)
      | TyMethod ft -> (
          match rhs.ty with
          | TyMethod m ->
              if not (ft_compatible ft m) then type_error t (Some rhs) parent
          | TyFunction f ->
              if not (ft_compatible ft f) then type_error t (Some rhs) parent;
              insert_cast (TyMethod ft) rhs
          | _ -> type_error t (Some rhs) parent)
      | Int | LongInt | Bool | Float ->
          type_check_numeric parent rhs;
          (* v11 skips the int→bool cast for assignments — the VM
             treats them interchangeably and the gratuitous [ITOB]
             would diverge from the original compiler's output.
             Pre-v11 keeps the explicit cast. *)
          if
            Ain.version_gte ctx.ain (11, 0)
            && Poly.(t = Bool)
            && (match rhs.ty with Int | LongInt -> true | _ -> false)
          then ()
          else insert_cast t rhs
      | Struct _ -> (
          match rhs.ty with
          | Ref t' when type_equal t t' -> ()
          | _ -> type_check parent t rhs)
      | _ -> type_check parent t rhs

    method check_funarg_or_return parent t (rhs : expression) =
      (* An empty ArrayLiteral infers [Array Void] (no element to take
         a type from), but [variableAlloc] types the literal's dummy
         slot — and the VM types the page it allocates for it — from
         [rhs.ty]. Take the declared element type instead, as orig
         does: a void-element page handed to a caller/callee expecting
         the declared type faults on the next copy with [A_ASSIGN
         配列のコピーに失敗しました] (form-squad slot drag, via the
         emptied slot's [CardConstructProcessCache*@Get(NULL)] early
         [return [];] — orig frees/returns the dummy as element type
         21, ours emitted 0). Covers returns and call arguments. *)
      (match (rhs.node, t, rhs.ty) with
      | ArrayLiteral [], Array elem, Array Void -> rhs.ty <- Array elem
      | _ -> ());
      match (t, rhs.ty) with
      | FuncType _, String -> type_error t (Some rhs) parent
      | _ -> self#check_assign parent t rhs

    method check_ref_assign parent (lhs : expression) (rhs : expression) =
      (* rhs must be a ref, or an lvalue in order to create a reference to it *)
      self#check_referenceable rhs parent;
      maybe_deref rhs;
      (* check that lhs is a reference variable of the appropriate type *)
      match lhs.node with
      | Ident (name, _) -> (
          let resolved =
            match self#env#resolve name with
            | UnresolvedName ->
                (* v11 lambdas capture locals from enclosing scopes. *)
                let envs = Stack.to_list self#env_stack in
                (match envs with
                | _ :: rest -> (
                    match
                      List.find_map rest ~f:(fun env -> env#get_local name)
                    with
                    | Some v -> ResolvedLocal v
                    | None -> UnresolvedName)
                | [] -> UnresolvedName)
            | r -> r
          in
          match resolved with
          | ResolvedLocal v | ResolvedGlobal v -> (
              match v.type_spec.ty with
              (* Accept [Wrap T] alongside [Ref T] — the v11 fat-ref
                 representation flows through the same ref-assign path. *)
              | Ref ty | Wrap ty -> ref_type_check parent ty rhs
              (* v12: a plain Struct/Array/String parameter is also a
                 valid ref-equal LHS (`p === NULL` where p is Struct). *)
              | (Struct _ | Array _ | String) as ty ->
                  ref_type_check parent ty rhs
              | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
          | UnresolvedName -> undefined_variable_error name parent
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      | Member (_, _, ClassVariable _) -> (
          match lhs.ty with
          | Ref t | Wrap t -> ref_type_check parent t rhs
          (* v12: a plain Struct/Array/String class-variable can also
             serve as a ref-equal LHS (e.g. `this.x === NULL`). *)
          | (Struct _ | Array _ | String) as t ->
              ref_type_check parent t rhs
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      (* Subscript of an [array@ref T] yields a [ref T] slot; ref-
         assigning into it (e.g. [arr[i] <- new T()]) is legal. *)
      | Subscript _ -> (
          match lhs.ty with
          | Ref t | Wrap t -> ref_type_check parent t rhs
          | (Struct _ | Array _ | String) as t ->
              ref_type_check parent t rhs
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      | _ ->
          (* FIXME? this isn't really a _type_ error *)
          type_error (Ref rhs.ty) (Some lhs) parent

    method! visit_expression expr =
      super#visit_expression expr;
      (* [obj?.Method(args)] parses as [Call (OptionalMember ...)] which
         otherwise wouldn't match the Call/Member/ClassMethod resolution
         paths below. Temporarily retype the callee as a plain [Member]
         so the existing handlers resolve it; restore the
         [OptionalMember] wrapping at the end so codegen still sees the
         null-check. *)
      let optional_call_info =
        match expr.node with
        | Call (({ node = OptionalMember (obj, name, mt); _ } as e), _, _) ->
            e.node <- Member (obj, name, mt);
            Some (e, obj, name)
        | _ -> None
      in
      (* convenience functions which always pass parent expression *)
      let check = type_check (ASTExpression expr) in
      let check_numeric = type_check_numeric (ASTExpression expr) in
      let coerce_numerics = type_coerce_numerics (ASTExpression expr) in
      let check_member_lhs =
        type_check_member_lhs
          ~v11:(Ain.version_gte ctx.ain (11, 0))
          (ASTExpression expr)
      in
      let check_expr (a : expression) b = check a.ty b in
      (* check function call arguments *)
      let check_call name params args =
        let nr_params = List.length params in
        let nr_args = List.length args in
        if nr_args > nr_params then
          arity_error name nr_params args (ASTExpression expr);
        let check_arg i (a : expression option) v =
          (* v11 method-reference overload resolution: when the param
             expects a [Delegate (Some (name, _))] and the arg is a
             [Member (obj, method_name, ClassMethod (fname, idx))]
             reference, [Member] resolution picked the primary overload
             by name only — re-resolve to the overload whose param/return
             types match the delegate's signature, if one exists. *)
          (match (a, v.type_spec.ty) with
          | Some ({ node = Member (obj, method_name, ClassMethod (fname, _)); _ } as arg),
            Delegate (Some (dg_name, _))
            when Hashtbl.mem ctx.delegates dg_name -> (
              let dg = Hashtbl.find_exn ctx.delegates dg_name in
              let dg_param_tys = List.map dg.params ~f:(fun p -> p.type_spec.ty) in
              let dg_ret_ty = dg.return.ty in
              let sig_matches (f : fundecl) =
                List.length f.params = List.length dg_param_tys
                && List.for_all2_exn f.params dg_param_tys
                     ~f:(fun p ty -> type_equal p.type_spec.ty ty)
                && type_equal f.return.ty dg_ret_ty
              in
              let current_matches =
                match Hashtbl.find ctx.functions fname with
                | Some f -> sig_matches f
                | None -> false
              in
              if not current_matches then
                match Hashtbl.find ctx.overloads fname with
                | None | Some [] -> ()
                | Some alternates -> (
                    match List.find alternates ~f:sig_matches with
                    | None -> ()
                    | Some f ->
                        let new_fname =
                          match f.class_name with
                          | Some cls -> cls ^ "@" ^ method_name
                          | None -> fname
                        in
                        arg.node <-
                          Member (obj, method_name,
                                  ClassMethod (new_fname,
                                               Option.value_exn f.index));
                        arg.ty <- TyMethod (ft_of_fundecl f)))
          | _ -> ());
          match (a, v.initval) with
          | Some a, _ ->
              (match v.type_spec.ty with
              | Ref ty ->
                  (* v11: a non-referenceable arg passed to a [ref T]
                     parameter needs an explicit [RvalueRef] wrap so
                     [variableAlloc] can back it with a DummyRef slot.
                     Skip for [Lambda] / [FuncAddr] (already
                     addressable) and for calls whose ain-level return
                     is already [Ref _] ([variableAlloc]'s Call handler
                     wraps those instead). *)
                  let is_lambda_or_funcaddr =
                    match (a : expression).node with
                    | Lambda _ | FuncAddr _ -> true
                    | _ -> false
                  in
                  let is_ain_ref_call =
                    match (a : expression).node with
                    | Call (_, _, (FunctionCall fno | MethodCall (_, fno))) -> (
                        match
                          (Ain.get_function_by_index ctx.ain fno).return_type
                        with
                        | Ain.Type.Ref _ -> true
                        | _ -> false)
                    | Call (_, _, HLLCall (lib_no, fun_no)) -> (
                        let lib = Ain.get_library_by_index ctx.ain lib_no in
                        match lib.functions.(fun_no).return_type with
                        | Ain.Type.Ref _ -> true
                        | _ -> false)
                    | _ -> false
                  in
                  if
                    Ain.version_gte ctx.ain (11, 0)
                    && (not is_lambda_or_funcaddr)
                    && not is_ain_ref_call
                  then insert_rvalue_ref a;
                  self#check_referenceable a (ASTExpression a);
                  ref_type_check (ASTExpression a) ty a
              | _ ->
                  self#check_funarg_or_return (ASTExpression a) v.type_spec.ty a;
                  (* v12 [NULL] arg for an interface parameter must
                     carry the interface type so codegen pushes the
                     two-slot interface null pair [-1; 0] instead of
                     the scalar [0]. *)
                  (match (a.node, v.type_spec.ty) with
                  | Null, (Struct (name, _) as t)
                    when Hashtbl.mem ctx.interface_names name -> a.ty <- t
                  | _ -> ()));
              Some a
          | None, Some e ->
              (* NOTE: `e` may be from another file that has not yet been type-checked. *)
              Some e
          | None, None ->
              if i < nr_args then
                compile_error
                  (sprintf "Missing argument #%d" i)
                  (ASTExpression expr)
              else arity_error name nr_params args (ASTExpression expr)
        in
        let args = args @ List.init (nr_params - nr_args) ~f:(fun _ -> None) in
        List.map3_exn
          (List.init nr_params ~f:(fun i -> i))
          args params ~f:check_arg
      in
      (match expr.node with
      | ConstInt _ -> expr.ty <- Int
      | ConstFloat _ -> expr.ty <- Float
      | ConstChar _ -> expr.ty <- Int
      | ConstString _ -> expr.ty <- String
      | Ident (name, _) -> (
          match self#env#resolve name with
          | ResolvedLocal v ->
              expr.node <- Ident (name, LocalVariable (-1, v.location));
              expr.ty <- v.type_spec.ty
          | ResolvedGlobal g ->
              let ident_type =
                if g.is_const then GlobalConstant
                else GlobalVariable (Option.value_exn g.index)
              in
              expr.node <- Ident (name, ident_type);
              expr.ty <- g.type_spec.ty
          | ResolvedFunction f ->
              (* Use the resolved fundecl's mangled name (Class@method
                 for class methods, plain name for free fns) — the
                 source may have used `::` where the strtab uses `@`,
                 so the swap-fallback in [resolve] picked an entry
                 under a different key. Use [mangled_name] so the
                 downstream [resolve_overload] lookup finds the
                 same entry in ctx.functions. *)
              let key = mangled_name f in
              expr.node <- Ident (key, FunctionName key);
              expr.ty <- TyFunction (ft_of_fundecl f)
          | ResolvedMember (s, v) ->
              expr.node <-
                Member
                  ( make_expr ~ty:(Struct (s.name, s.index)) This,
                    name,
                    if v.is_const then ClassConst s.name
                    else ClassVariable (Option.value_exn v.index) );
              expr.ty <- v.type_spec.ty
          | ResolvedMethod (s, f) ->
              let fun_name = mangled_name f in
              expr.node <-
                Member
                  ( make_expr ~ty:(Struct (s.name, s.index)) This,
                    name,
                    ClassMethod (fun_name, Option.value_exn f.index) );
              expr.ty <- TyMethod (ft_of_fundecl f)
          | ResolvedLibrary _ ->
              expr.node <- Ident (name, HLLName);
              expr.ty <- Void
          | ResolvedSystem ->
              expr.node <- Ident ("system", System);
              expr.ty <- Void
          | ResolvedBuiltin builtin ->
              expr.node <- Ident (name, BuiltinFunction builtin);
              expr.ty <- Void
          | ResolvedEnumValue v ->
              (* v12 enum constant: rewrite the Ident to a ConstInt so
                 codegen treats it like any other integer literal. *)
              expr.node <- ConstInt v;
              expr.ty <- Int
          | ResolvedStructType (sname, sidx) ->
              (* Check parent envs first — a same-named local in an
                 enclosing scope (e.g. lambda-captured variable) takes
                 precedence over a struct type with the same name. *)
              let envs = Stack.to_list self#env_stack in
              let captured =
                match envs with
                | _ :: rest ->
                    List.find_map rest ~f:(fun env -> env#get_local name)
                | [] -> None
              in
              (match captured with
              | Some v ->
                  expr.node <-
                    Ident
                      ( name,
                        LocalVariable
                          (Option.value v.index ~default:0, v.location) );
                  expr.ty <- v.type_spec.ty
              | None ->
                  (* Keep the Ident node; the surrounding [Call] handler
                     recognizes this and rewrites into a Cast. *)
                  expr.ty <- Struct (sname, sidx))
          | UnresolvedName -> (
              (* v11 lambdas capture names from enclosing scopes. When
                 resolution fails in the current env, walk parent
                 environments looking for a matching local — keep the
                 [LocalVariable] tag here; [variableAlloc]'s capture
                 pass later flips the tag to [CapturedVariable] with
                 the proper depth. *)
              let envs = Stack.to_list self#env_stack in
              let captured =
                match envs with
                | _ :: rest ->
                    List.find_map rest ~f:(fun env -> env#get_local name)
                | [] -> None
              in
              match captured with
              | Some v ->
                  expr.node <-
                    Ident
                      ( name,
                        LocalVariable
                          (Option.value v.index ~default:0, v.location) );
                  expr.ty <- v.type_spec.ty
              | None ->
                  undefined_variable_error name (ASTExpression expr)))
      | FuncAddr (name, _) -> (
          (* Try the literal name first; then a `::`-to-`@` swap for
             v12 method-name forms; then fall back to qualified
             member resolution. *)
          let at_swap =
            match Util.last_toplevel_double_colon name with
            | Some i ->
                let left = String.sub name ~pos:0 ~len:i in
                let right =
                  String.sub name ~pos:(i + 2)
                    ~len:(String.length name - i - 2)
                in
                Hashtbl.find ctx.functions (left ^ "@" ^ right)
            | None -> None
          in
          match Option.first_some (Hashtbl.find ctx.functions name) at_swap with
          | Some f ->
              let key = mangled_name f in
              expr.node <- FuncAddr (key, f.index);
              expr.ty <- TyFunction (ft_of_fundecl f)
          | None -> (
              match Util.parse_qualified_name name with
              | None, name -> undefined_variable_error name (ASTExpression expr)
              | Some sname, name -> (
                  match self#env#resolve_qualified sname name with
                  | UnresolvedName ->
                      undefined_variable_error
                        (sname ^ "::" ^ name)
                        (ASTExpression expr)
                  | ResolvedMember (_, v) ->
                      expr.node <-
                        MemberAddr (sname, name, Option.value_exn v.index);
                      expr.ty <- MemberPtr (sname, v.type_spec.ty)
                  | _ ->
                      compiler_bug
                        "resolve_qualified returned an unexpected value"
                        (Some (ASTExpression expr)))))
      | MemberAddr _ ->
          compiler_bug "unexpected MemberAddr" (Some (ASTExpression expr))
      | Unary (op, e) -> (
          match op with
          | UPlus | UMinus | PreInc | PreDec | PostInc | PostDec
          | ForeachInc | ForeachDec ->
              check_numeric e;
              expr.ty <- e.ty
          | LogNot | BitNot ->
              check Int e;
              expr.ty <- Int)
      | Binary (op, a, b) -> (
          match op with
          | Plus -> (
              maybe_deref a;
              maybe_deref b;
              match a.ty with
              | String ->
                  check String b;
                  expr.ty <- a.ty
              | _ -> expr.ty <- coerce_numerics op a b)
          | Minus | Times | Divide -> expr.ty <- coerce_numerics op a b
          | LogOr | LogAnd | BitOr | BitXor | BitAnd | LShift | RShift ->
              maybe_deref a;
              maybe_deref b;
              check Int a;
              check Int b;
              expr.ty <- a.ty
          | Modulo ->
              maybe_deref a;
              maybe_deref b;
              (match a.ty with
              | String -> (
                  (* TODO: check type matches format specifier if format string is a literal *)
                  match b.ty with
                  | Int | Float | Bool | LongInt | Enum _ | String | HLLParam ->
                      ()
                  | _ -> type_error Int (Some b) (ASTExpression expr))
              | Int | Bool | LongInt | Enum _ | HLLParam -> check Int b
              | _ -> type_error Int (Some a) (ASTExpression expr));
              expr.ty <- a.ty
          | Equal | NEqual ->
              maybe_deref a;
              maybe_deref b;
              (* NOTE: NULL is not allowed on lhs *)
              (match (a.ty, b.ty) with
              (* HLLParam (generic) compares against anything *)
              | HLLParam, _ | _, HLLParam -> ()
              | String, _ -> check String b
              | FuncType (Some (_, ft_i)), FuncType (Some (_, ft_j)) ->
                  if ft_i <> ft_j then
                    type_error a.ty (Some b) (ASTExpression expr)
              | FuncType (Some (ft_name, _)), TyFunction f ->
                  let ft = Hashtbl.find_exn ctx.functypes ft_name in
                  if not (ft_compatible (ft_of_fundecl ft) f) then
                    type_error a.ty (Some b) (ASTExpression expr)
              | FuncType _, NullType -> b.ty <- a.ty
              (* v11+ allow `obj == NULL` for heap-allocated types *)
              | (Struct _ | Array _ | Delegate _ | Ref _), NullType ->
                  b.ty <- a.ty
              | NullType, (Struct _ | Array _ | Delegate _ | Ref _) ->
                  a.ty <- b.ty
              (* v11+ allow struct equality (interface compatibility) *)
              | Struct _, Struct _ -> ()
              (* v12 lets `Struct == int` slip through; the value being
                 compared is the object ID. Treat both sides as int. *)
              | Struct _, (Int | Bool | LongInt) -> ()
              | (Int | Bool | LongInt), Struct _ -> ()
              | _ -> coerce_numerics op a b |> ignore);
              expr.ty <- Int
          | LT | GT | LTE | GTE ->
              maybe_deref a;
              maybe_deref b;
              (match a.ty with
              | String -> check String b
              | _ -> coerce_numerics op a b |> ignore);
              expr.ty <- Int
          | RefEqual | RefNEqual ->
              (match a.node with
              | Ident _ | Member (_, _, ClassVariable _) ->
                  self#check_ref_assign (ASTExpression expr) a b
              | This ->
                  (* v12 allows `this === other` for object identity. *)
                  (match a.ty with
                  | Struct _ as t -> ref_type_check (ASTExpression expr) t b
                  | _ -> not_an_lvalue_error a (ASTExpression expr))
              | _ -> (
                  match a.ty with
                  (* v11: [ref_scalar === literal] compares the
                     dereferenced value, not addresses. Pre-v11 this
                     would fail [check_referenceable] on the literal. *)
                  | Ref t when is_scalar t && not (is_referenceable b) ->
                      check t b
                  | Ref t ->
                      self#check_referenceable b (ASTExpression expr);
                      ref_type_check (ASTExpression expr) t b
                  (* v12: heap-allocated values from property getters or
                     other expression-position member access can serve
                     as ref-equal LHS against NULL. *)
                  | (Struct _ | Array _ | String) as t ->
                      ref_type_check (ASTExpression expr) t b
                  (* v12 lets ref-equal flow through generic / non-ref
                     values (NullCoalesce result, enum-stub Parse,
                     etc.). Accept without further checking. *)
                  | _ -> ()));
              expr.ty <- Int)
      (* v12 interface event subscription: when a Member lookup fell
         through to HLLParam (interface-typed receiver, missing on
         the interface decl itself), permit `+=` / `-=` without
         type checks. Runtime dispatch via implementer vtable. *)
      | Assign
          ( (PlusAssign | MinusAssign),
            ({ node = (Member _ | OptionalMember _); ty = HLLParam; _ }),
            rhs ) ->
          (* Type-analyze the RHS so any nested lambdas / calls get
             resolved, then collapse the whole assignment to a no-op
             [Null] sentinel — the lhs's underlying delegate is
             unknown at compile time. v12-wip — round-trip drops
             these subscriptions. *)
          self#visit_expression rhs;
          expr.node <- Null;
          expr.ty <- HLLParam
      (* v11 user-bodied event: [obj.E += h] / [obj.E -= h] where the
         [<E>] backing field has been elided (because the user supplied
         add/remove bodies at top level). Lower to a call through the
         user's accessor; the matching member resolution is in the
         Member arm below where it synthesizes [ClassEvent]. *)
      | Assign
          ( ((PlusAssign | MinusAssign) as op),
            ({ node = (Member (obj, _, ClassEvent ev)
                      | OptionalMember (obj, _, ClassEvent ev)); _ } as lhs),
            rhs ) ->
          let accessor_kind, accessor_idx =
            match op with
            | PlusAssign -> ("add", ev.event_add_index)
            | MinusAssign -> ("remove", ev.event_remove_index)
            | _ -> ("add", ev.event_add_index)
          in
          let in_accessor_with_backing =
            let accessor_name =
              ev.event_class ^ "@" ^ ev.event_name ^ "::" ^ accessor_kind
            in
            Option.value_map self#env#current_function ~default:false
              ~f:(fun f ->
                String.equal f.name accessor_name)
          in
          if in_accessor_with_backing then (
            (* Inside the user-supplied accessor body, the original v12
               compiler treats [this.Event += value] as a write to the
               backing delegate slot, not as a recursive accessor call. *)
            self#check_delegate_compatible (ASTExpression expr)
              (match lhs.ty with Delegate dg -> dg | _ -> None)
              rhs;
            expr.ty <- rhs.ty)
          else
          (match accessor_idx with
          | None ->
              (* v12 user-bodied event without a populated accessor
                 index — typical when the add/remove method's index
                 lookup happened before allocation. Drop the
                 subscription as a no-op. v12-wip — round-trip
                 intentionally broken. *)
              self#visit_expression rhs;
              expr.node <- Null;
              expr.ty <- HLLParam
          | Some idx ->
              let f = Ain.get_function_by_index ctx.ain idx in
              let class_idx = Option.value ~default:(-1) f.struct_type in
              let method_name = ev.event_name ^ "::" ^ accessor_kind in
              let accessor_inner =
                Member
                  ( obj,
                    method_name,
                    ClassMethod (ev.event_class ^ "@" ^ method_name, idx) )
              in
              let accessor_node =
                match lhs.node with
                (* Preserve null-check semantics for [obj?.E += h] —
                   downstream codegen's [OptionalMember] handler wraps
                   the call with the null guard. *)
                | OptionalMember _ ->
                    OptionalMember
                      ( obj,
                        method_name,
                        ClassMethod
                          (ev.event_class ^ "@" ^ method_name, idx) )
                | _ -> accessor_inner
              in
              let accessor_expr =
                make_expr ~ty:Void ~loc:expr.loc accessor_node
              in
              expr.node <-
                Call
                  (accessor_expr, [ Some rhs ], MethodCall (class_idx, idx));
              expr.ty <- Void)
      (* v11 property write — write-only path. The LHS is still a
         [Member ClassProperty] because the getter rewrite at the end
         of [visit_expression] only fires when a getter exists.
         v12 also takes this path for [obj?.Prop = v] (OptionalMember
         wrapping the property); preserve the optional-receiver shape
         so codegen wraps the setter call with the null guard. *)
      | Assign
          ( _,
            ({ node = (Member (obj, _, ClassProperty prop)
                      | OptionalMember (obj, _, ClassProperty prop)); _ } as lhs),
            rhs ) ->
          (match prop.prop_setter_index with
          | Some setter_idx ->
              let class_idx =
                match obj.ty with
                | Struct (_, i) | Ref (Struct (_, i)) -> i
                | _ -> -1
              in
              let setter_name =
                prop.prop_class ^ "@" ^ prop.prop_name ^ "::set"
              in
              let setter_node =
                match lhs.node with
                | OptionalMember _ ->
                    OptionalMember
                      ( obj,
                        prop.prop_name ^ "::set",
                        ClassMethod (setter_name, setter_idx) )
                | _ ->
                    Member
                      ( obj,
                        prop.prop_name ^ "::set",
                        ClassMethod (setter_name, setter_idx) )
              in
              let setter_expr =
                make_expr ~ty:Void ~loc:expr.loc setter_node
              in
              (* v12 [obj.IFaceProp = NULL]: the setter param is an
                 interface type (2-slot at the call site). Refine the
                 [NULL] arg's [ty] so codegen pushes the two-slot
                 interface-null pair instead of the scalar [PUSH 0].
                 This rewrite path bypasses [check_call], so we tag
                 the arg directly here. *)
              (match rhs.node with
              | Null -> (
                  match
                    Hashtbl.find ctx.functions setter_name
                    |> Option.bind ~f:(fun (f : fundecl) -> List.hd f.params)
                  with
                  | Some (p : variable) -> (
                      match p.type_spec.ty with
                      | Struct (n, _) when Hashtbl.mem ctx.interface_names n ->
                          rhs.ty <- p.type_spec.ty
                      | _ -> ())
                  | None -> ())
              | _ -> (
                  (* Bypassing [check_call] also skips the numeric
                     argument conversion: [X.IntProp = float_expr] must
                     [FTOI] before the setter call (orig does) or the
                     int slot stores raw float bits — battle HP became
                     garbage via [BattleContext@InitHpPer]'s
                     [Hp = HpMax * ratioFromPercent(per)]; same family
                     in Ｐ敵本体追加 / DamageInformation@MulRatio /
                     LeaderCard@UpdateStatus. Wrap only the float↔int
                     mismatches — an unconditional [insert_cast] would
                     wrap every rhs in a no-op [Cast] and break the
                     node-shape matches of the optional/postset setter
                     arms. *)
                  match
                    Hashtbl.find ctx.functions setter_name
                    |> Option.bind ~f:(fun (f : fundecl) -> List.hd f.params)
                  with
                  | Some (p : variable) -> (
                      match (p.type_spec.ty, rhs.ty) with
                      | ((Int | LongInt) as pt), Float -> insert_cast pt rhs
                      | Float, (Int | LongInt | Enum _) ->
                          insert_cast Float rhs
                      | _ -> ())
                  | None -> ()));
              expr.node <-
                Call
                  (setter_expr, [ Some rhs ], MethodCall (class_idx, setter_idx));
              expr.ty <- Void
          | None ->
              compile_error
                (sprintf "property `%s.%s` has no accessors" prop.prop_class
                   prop.prop_name)
                (ASTExpression expr))
      (* v11 property write — read-already-rewritten path. The child-first
         traversal has already turned [obj.Name] into [obj.Name::get()],
         so the LHS is a [Call (Member ClassMethod _::get, [], _)]. For
         optional writes, the callee is restored as [OptionalMember] to
         keep the null guard. The paired setter has the same prefix with
         [::set]. *)
      | Assign
          ( _,
            ({
               node =
                 Call
                   ( ({
                        node =
                          ( Member (obj, _, ClassMethod (getter_name, _))
                          | OptionalMember (obj, _, ClassMethod (getter_name, _)) );
                        _;
                      } as callee),
                     _,
                     _ );
               _;
             } as lhs),
            rhs )
        when String.is_suffix getter_name ~suffix:"::get" ->
          let prefix = String.drop_suffix getter_name 5 in
          let setter_name = prefix ^ "::set" in
          (match Hashtbl.find ctx.functions setter_name with
          | Some f ->
              let class_idx = Option.value_exn f.class_index in
              let setter_idx = Option.value_exn f.index in
              let surface_name =
                String.rsplit2 setter_name ~on:'@'
                |> Option.value_map ~default:setter_name ~f:snd
              in
              let setter_node =
                match callee.node with
                | OptionalMember _ ->
                    OptionalMember
                      ( obj,
                        surface_name,
                        ClassMethod (setter_name, setter_idx) )
                | _ ->
                    Member
                      ( obj,
                        surface_name,
                        ClassMethod (setter_name, setter_idx) )
              in
              let setter_expr =
                make_expr ~ty:Void ~loc:lhs.loc setter_node
              in
              (* v12 [obj.IFaceProp = NULL]: refine the NULL arg's
                 type to the setter's interface param type so codegen
                 pushes the 2-slot interface-null pair. This Assign-
                 rewrite path bypasses [check_call]. *)
              (match rhs.node with
              | Null -> (
                  match List.hd f.params with
                  | Some (p : variable) -> (
                      match p.type_spec.ty with
                      | Struct (n, _) when Hashtbl.mem ctx.interface_names n ->
                          rhs.ty <- p.type_spec.ty
                      | _ -> ())
                  | None -> ())
              | _ -> (
                  (* Same numeric-argument coercion as the
                     [Member ClassProperty] write arm above — this
                     rewrite also bypasses [check_call]. *)
                  match List.hd f.params with
                  | Some (p : variable) -> (
                      match (p.type_spec.ty, rhs.ty) with
                      | ((Int | LongInt) as pt), Float -> insert_cast pt rhs
                      | Float, (Int | LongInt | Enum _) ->
                          insert_cast Float rhs
                      | _ -> ())
                  | None -> ()));
              expr.node <-
                Call
                  (setter_expr, [ Some rhs ], MethodCall (class_idx, setter_idx));
              expr.ty <- Void
          | None ->
              (* v12 sometimes assigns to a property declared as
                 get-only on the interface; the actual setter lives
                 on the implementing class. Type the assign as Void
                 and let runtime dispatch through whichever
                 implementer is present. *)
              expr.ty <- Void)
      | Assign (op, lhs, rhs) -> (
          self#check_lvalue lhs (ASTExpression expr);
          maybe_deref lhs;
          maybe_deref rhs;
          (match (lhs.ty, op) with
          | _, EqAssign -> (
              self#check_assign (ASTExpression expr) lhs.ty rhs;
              (* If lhs is a string subscript access, change the operator to CharAssign *)
              match lhs.node with
              | Subscript ({ ty = String; _ }, _) ->
                  expr.node <- Assign (CharAssign, lhs, rhs)
              | _ -> ())
          | String, PlusAssign -> check String rhs
          | Delegate dg, (PlusAssign | MinusAssign) ->
              self#check_delegate_compatible (ASTExpression expr) dg rhs
          | _, (PlusAssign | MinusAssign | TimesAssign | DivideAssign) ->
              check_numeric lhs;
              check_numeric rhs;
              insert_cast lhs.ty rhs;
              check_expr lhs rhs
          | ( _,
              ( ModuloAssign | OrAssign | XorAssign | AndAssign | LShiftAssign
              | RShiftAssign ) ) ->
              check Int lhs;
              check Int rhs
          | _, CharAssign ->
              compiler_bug "unexpected CharAssign" (Some (ASTExpression expr)));
          (* XXX: Nothing is left on stack after assigning method to delegate *)
          match (lhs.ty, rhs.ty) with
          | Delegate _, (TyMethod _ | String) -> expr.ty <- Void
          | _ -> expr.ty <- rhs.ty)
      | Seq (e1, e2) ->
          check_not_array e1;
          expr.ty <- e2.ty
      | Ternary (test, con, alt) ->
          check Int test;
          (* When the two branches differ in ref-ness, v11 materialises
             the non-ref branch as an rvalue-ref so the ternary's
             result is always a reference. Only needed for non-scalars
             — [Int]/[Float]/[Bool] get dereffed directly and don't
             need a slot. Pre-v11 just dereffed the ref branch. *)
          let needs_rval_wrap (t : jaf_type) =
            match t with Int | Float | Bool | LongInt -> false | _ -> true
          in
          (match (con.ty, alt.ty) with
          | Ref _, Ref _ -> ()
          | Ref t, _ ->
              if Ain.version_gte ctx.ain (11, 0) && needs_rval_wrap t then (
                let inner = clone_expr alt in
                alt.node <- RvalueRef inner);
              maybe_deref con
          | _, Ref t ->
              if Ain.version_gte ctx.ain (11, 0) && needs_rval_wrap t then (
                let inner = clone_expr con in
                con.node <- RvalueRef inner);
              maybe_deref alt
          | _, _ -> ());
          (* v12 ternary branches may have different callable types
             (e.g. TyMethod vs Delegate); the surrounding assignment's
             type check handles the actual compatibility. *)
          let callable = function
            | TyMethod _ | TyFunction _ | Delegate _ | FuncType _ -> true
            | _ -> false
          in
          if not (callable con.ty && callable alt.ty) then check_expr con alt;
          expr.ty <- con.ty
      | Cast (t, e) ->
          maybe_deref e;
          if not (type_castable t e.ty) then
            type_error t (Some e) (ASTExpression expr);
          expr.ty <- t
      | Subscript (obj, i) -> (
          maybe_deref obj;
          check Int i;
          match obj.ty with
          | Array t -> expr.ty <- t
          | String -> expr.ty <- Int
          | _ ->
              (* FIXME: Expected type here is array<?>|string *)
              let expected = Array Void in
              type_error expected (Some obj) (ASTExpression expr))
      (* system function *)
      | Member (({ node = Ident (_, System); _ } as e), syscall_name, _) -> (
          match Bytecode.syscall_of_string syscall_name with
          | Some sys ->
              expr.node <- Member (e, syscall_name, SystemFunction sys);
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error ("system." ^ syscall_name)
                (ASTExpression expr))
      (* HLL function *)
      | Member (({ node = Ident (lib_name, HLLName); _ } as e), fun_name, _)
        -> (
          match find_hll_function ctx lib_name fun_name with
          | Some _ ->
              expr.node <- Member (e, fun_name, HLLFunction (lib_name, fun_name));
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error
                (lib_name ^ "." ^ fun_name)
                (ASTExpression expr))
      (* built-in methods *)
      | Member (e, name, _) when is_builtin e.ty -> (
          match resolve_builtin ctx e name with
          | Some builtin ->
              expr.node <- Member (e, name, builtin);
              expr.ty <- TyFunction ([], Void)
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error name (ASTExpression expr))
      (* v12 generic-array foreach: member access on a wrap<hll_param>
         loop variable can't resolve concretely. Type the member as
         hll_param so subsequent uses keep flowing without erroring;
         actual runtime dispatch happens via duck typing. *)
      | Member (obj, _, _)
        when match obj.ty with
             | Wrap HLLParam | Wrap (Ref HLLParam) | HLLParam | Ref HLLParam ->
                 true
             | _ -> false ->
          expr.ty <- HLLParam
      (* member variable OR method *)
      | Member (obj, _member_name, _)
        when (match obj.ty with
              | HLLParam | Wrap HLLParam | Ref HLLParam -> true
              | _ -> false) ->
          (* v12 foreach loop var or generic HLL result typed as
             [HLLParam] / [Wrap HLLParam]: we don't know the underlying
             struct so member resolution can't pick a concrete
             [ClassVariable] / [ClassProperty]. Synthesize a property-
             style access tagged with the wildcard so the call/assign
             paths fall through to a generic HLL dispatch at runtime.
             The [ClassMethod] tag with index -1 marks "unresolved
             member"; downstream codegen treats it like a runtime
             property call. *)
          expr.ty <- HLLParam
      | Member (obj, member_name, _) -> (
          let struc = Hashtbl.find_exn ctx.structs (check_member_lhs obj) in
          let access_check () =
            match self#env#current_class with
            | Some (Struct (_, i)) when i = struc.index -> ()
            | _ ->
                compile_error
                  (sprintf "%s::%s is not public" struc.name member_name)
                  (ASTExpression expr)
          in
          (* v11 auto-event lookup: [obj.Name] for a class-declared
             [event T Name;] hits the mangled [<Name>] backing field
             when no plain member matches. Restricted to delegate-typed
             fields so other [<…>]-named lowered constructs (e.g.
             property backing slots) aren't misidentified as events. *)
          let lookup_member name =
            match Hashtbl.find struc.members name with
            | Some _ as v -> v
            | None -> (
                match Hashtbl.find struc.members ("<" ^ name ^ ">") with
                | Some m
                  when (match m.type_spec.ty with
                        | Delegate _ -> true
                        | _ -> false) ->
                    Some m
                | _ -> None)
          in
          (* v11 property resolution: a property registered on the class
             takes precedence over a member of the same name. The Member
             node is tagged with [ClassProperty]; reads are rewritten
             into getter calls at the end of [visit_expression], writes
             are intercepted in the [Assign] arm.

             v11+ interface inheritance: if the property isn't found
             directly, walk [ctx.interface_parent] to look for it on
             an ancestor interface. Our dedup pass filters inherited
             methods from a derived interface's registration to avoid
             FUNC-table inflation; this fallback keeps the surface
             API (e.g. [obj.AddColor] on IButtonParts) resolvable. *)
          let rec lookup_property_inh sname =
            let s = Hashtbl.find_exn ctx.structs sname in
            match Hashtbl.find s.properties member_name with
            | Some _ as v -> v
            | None -> (
                match Hashtbl.find ctx.interface_parent sname with
                | Some parent -> lookup_property_inh parent
                | None -> None)
          in
          match lookup_property_inh struc.name with
          | Some (info : property_info) ->
              let getter_index =
                Option.bind info.prop_getter ~f:(fun f -> f.index)
              in
              let setter_index =
                Option.bind info.prop_setter ~f:(fun f -> f.index)
              in
              expr.node <-
                Member
                  ( obj,
                    member_name,
                    ClassProperty
                      {
                        prop_class = struc.name;
                        prop_name = member_name;
                        prop_getter_index = getter_index;
                        prop_setter_index = setter_index;
                      } );
              expr.ty <- prop_info_ty info
          | None -> (
              let event_add =
                Hashtbl.find ctx.functions
                  (struc.name ^ "@" ^ member_name ^ "::add")
              in
              let event_remove =
                Hashtbl.find ctx.functions
                  (struc.name ^ "@" ^ member_name ^ "::remove")
              in
              let user_bodied_event =
                Hashtbl.mem ctx.user_bodied_accessors
                  (struc.name ^ "@" ^ member_name ^ "::add")
                && Hashtbl.mem ctx.user_bodied_accessors
                     (struc.name ^ "@" ^ member_name ^ "::remove")
              in
              match (user_bodied_event, event_add, event_remove) with
              | true, (Some add), _ | true, _, (Some add) ->
                  let event_type =
                    match add.params with [ p ] -> p.type_spec.ty | _ -> Void
                  in
                  expr.node <-
                    Member
                      ( obj,
                        member_name,
                        ClassEvent
                          {
                            event_class = struc.name;
                            event_name = member_name;
                            event_add_index =
                              Option.bind event_add ~f:(fun f -> f.index);
                            event_remove_index =
                              Option.bind event_remove ~f:(fun f -> f.index);
                          } );
                  expr.ty <- event_type
              | _ -> (
              match lookup_member member_name with
              | Some member ->
                  if member.is_private then access_check ();
                  expr.node <-
                    Member
                      ( obj,
                        member.name,
                        if member.is_const then ClassConst struc.name
                        else ClassVariable (Option.value_exn member.index) );
                  expr.ty <- member.type_spec.ty
              | None -> (
                  (* v11 user-bodied event resolution: when [<Name>]
                     is absent (elided because the user supplied
                     [Name::add] / [Name::remove] bodies) but those
                     accessors exist on this class, synthesize a
                     [ClassEvent] member. The parent [Assign
                     PlusAssign|MinusAssign] then rewrites to a method
                     call. Prefer the event form over an identically-
                     named method — the event prototype in the class
                     declaration is what made the accessors exist. *)
                  match (event_add, event_remove) with
                  | Some add, _ | _, Some add ->
                      let event_type =
                        match add.params with
                        | [ p ] -> p.type_spec.ty
                        | _ -> Void
                      in
                      expr.node <-
                        Member
                          ( obj,
                            member_name,
                            ClassEvent
                              {
                                event_class = struc.name;
                                event_name = member_name;
                                event_add_index =
                                  Option.bind event_add ~f:(fun f -> f.index);
                                event_remove_index =
                                  Option.bind event_remove ~f:(fun f ->
                                      f.index);
                              } );
                      expr.ty <- event_type
                  | None, None -> (
                      (* v11+ interface inheritance fallback: if the
                         method isn't registered under [Class@Method],
                         walk the parent chain from [ctx.interface_parent]
                         and look up under the parent's namespace.
                         Returns [(parent_name_owning_method, fundecl)]
                         so the resolved ClassMethod tag points at the
                         actual function entry. *)
                      let rec lookup_method_inh sname =
                        let fname = sname ^ "@" ^ member_name in
                        match Hashtbl.find ctx.functions fname with
                        | Some f -> Some (fname, f)
                        | None -> (
                            match Hashtbl.find ctx.interface_parent sname with
                            | Some parent -> lookup_method_inh parent
                            | None -> None)
                      in
                      match lookup_method_inh struc.name with
                      | Some (fun_name, f) ->
                          if f.is_private then access_check ();
                          expr.node <-
                            Member
                              ( obj,
                                member_name,
                                ClassMethod
                                  (fun_name, Option.value_exn f.index) );
                          expr.ty <- TyMethod (ft_of_fundecl f)
                      | None ->
                          (* v12 interface member access can target
                             events/properties declared on implementing
                             classes but not on the interface itself.
                             Fall back to HLLParam so the call/assign
                             uses the generic path; the runtime
                             dispatches through the implementer's
                             vtable. *)
                          expr.ty <- HLLParam)))))
      (* Already-resolved AND type-checked Call — re-entered through
         the [OptionalMember] handler's recursive [self#visit_expression]
         (which re-walks the OM's child obj). Skip: re-running
         resolution on resolved args would double-wrap [RvalueRef]s in
         [check_call] and double-prepend [obj] for HLL methods,
         breaking overload arity. The [Untyped] guard keeps
         [BuiltinCall]/etc. tags from synthetic call sites (e.g.
         [arrayInit]'s array-alloc statement) flowing through their
         first-pass resolution. *)
      | Call
          ( _,
            _,
            ( FunctionCall _ | MethodCall _ | HLLCall _ | SystemCall _
            | BuiltinCall _ | FuncTypeCall _ | DelegateCall _ ) )
        when match expr.ty with Untyped -> false | _ -> true ->
          ()
      (* regular function call *)
      | Call (({ node = Ident (_, FunctionName name); _ } as e), args, _) ->
          let f = self#resolve_overload name args in
          let fno = Option.value_exn f.index in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, FunctionCall fno);
          expr.ty <- f.return.ty
      (* built-in function call *)
      | Call (({ node = Ident (_, BuiltinFunction builtin); _ } as e), args, _)
        ->
          let f =
            Builtin.fundecl_of_builtin ctx builtin Void
              (Some (ASTExpression expr))
          in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, BuiltinCall builtin);
          expr.ty <- f.return.ty
      (* method call *)
      | Call (({ node = Member (_, _, ClassMethod (name, _)); _ } as e), args, _)
        ->
          let f = self#resolve_overload name args in
          let args = check_call f.name f.params args in
          let mcall =
            MethodCall (Option.value_exn f.class_index, Option.value_exn f.index)
          in
          expr.node <- Call (e, args, mcall);
          expr.ty <- f.return.ty
      (* v12 [this.Event(args)] — calling an event fires the underlying
         delegate. Rewrite the callee from [Member ClassEvent] to a
         [Member ClassVariable] referencing the [<Event>] backing
         field, then resolve as a DelegateCall (or stub if the
         backing field is absent for user-bodied events). *)
      | Call (({ node = Member (obj, event_name, ClassEvent ev); _ } as e), args, _) ->
          List.iter args ~f:(Option.iter ~f:self#visit_expression);
          let struc = Hashtbl.find_exn ctx.structs ev.event_class in
          let backing_name = "<" ^ event_name ^ ">" in
          (match Hashtbl.find struc.members backing_name with
          | Some m -> (
              e.node <-
                Member
                  ( obj,
                    backing_name,
                    ClassVariable (Option.value_exn m.index) );
              e.ty <- m.type_spec.ty;
              match m.type_spec.ty with
              | Delegate (Some (name, _)) | Ref (Delegate (Some (name, _))) ->
                  let f = Hashtbl.find_exn ctx.delegates name in
                  let args = check_call f.name f.params args in
                  expr.node <-
                    Call (e, args, DelegateCall (Option.value_exn f.index));
                  expr.ty <- f.return.ty
              | _ -> expr.ty <- HLLParam)
          | None ->
              (* User-bodied event with no JAF-side backing field —
                 rewrite the callee to a [Null]-typed sentinel so the
                 codegen UnresolvedCall fallback can push a placeholder.
                 v12-wip: round-trip intentionally broken. *)
              e.node <- Null;
              e.ty <- HLLParam;
              expr.ty <- HLLParam)
      (* HLL call *)
      | Call
          ( ({ node = Member (_, _, HLLFunction (import_name, fun_name)); _ } as
             e),
            args,
            _ ) ->
          let lib = Hashtbl.find_exn ctx.libraries import_name in
          let f = self#resolve_hll_overload lib fun_name ~skip_self:false args in
          let args = check_call f.name f.params args in
          let lib_no =
            Option.value_exn (Ain.get_library_index ctx.ain lib.hll_name)
          in
          let fun_no = self#resolve_hll_ain_index lib_no f in
          expr.node <- Call (e, args, HLLCall (lib_no, fun_no));
          expr.ty <- f.return.ty
      (* system call *)
      | Call (({ node = Member (_, _, SystemFunction sys); _ } as e), args, _)
        ->
          let f = Builtin.fundecl_of_syscall sys in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, SystemCall sys);
          expr.ty <- f.return.ty
      (* built-in method call *)
      | Call
          (({ node = Member (obj, _, BuiltinMethod builtin); _ } as e), args, _)
        ->
          let f =
            Builtin.fundecl_of_builtin ctx builtin obj.ty
              (Some (ASTExpression expr))
          in
          let args = check_call f.name f.params args in
          expr.node <- Call (e, args, BuiltinCall builtin);
          expr.ty <- f.return.ty
      (* built-in method call via HLL *)
      | Call
          ( ({ node = Member (obj, fun_name, BuiltinHLL lib_name); _ } as e),
            args,
            _ ) ->
          let lib = Hashtbl.find_exn ctx.libraries lib_name in
          let f = self#resolve_hll_overload lib fun_name ~skip_self:true args in
          (* Substitute the [hll_param] wildcard in param/return types
             with the receiver's concrete array element type. *)
          let elem_ty = array_elem_type_of_expr obj in
          let specialize = specialize_hll_param elem_ty in
          let raw_params = List.tl_exn f.params in
          let params =
            List.map raw_params ~f:(fun p ->
                {
                  p with
                  type_spec =
                    { p.type_spec with ty = specialize p.type_spec.ty };
                })
          in
          (* v11 [Array.Alloc] takes 4 int dimensions; unused trailing
             ones are [-1]. Pad short user calls like [arr.Alloc(n)]
             so the arg list matches the callee. Other HLL methods
             are left alone. *)
          let args =
            if
              Ain.version_gte ctx.ain (11, 0)
              && String.equal lib_name "Array"
              && String.equal f.name "Alloc"
            then
              let extra =
                List.init
                  (List.length params - List.length args)
                  ~f:(fun _ -> Some (make_expr ~ty:Int (ConstInt (-1))))
              in
              args @ extra
            else args
          in
          let args = check_call f.name params args in
          (match elem_ty with
          | Some elem_ty
            when String.equal lib_name "Array"
                 && not (jaf_type_equal elem_ty HLLParam) ->
              self#ensure_array_hll_callback_delegates f.name elem_ty raw_params
                args
          | _ -> ());
          let lib_no =
            Option.value_exn (Ain.get_library_index ctx.ain lib.hll_name)
          in
          let fun_no = self#resolve_hll_ain_index lib_no f in
          insert_rvalue_ref obj;
          expr.node <- Call (e, Some obj :: args, HLLCall (lib_no, fun_no));
          expr.ty <-
            if String.equal lib_name "String" && String.equal f.name "Split"
            then Array String
            else if String.equal lib_name "Array" && String.equal f.name "Where"
            then (
              match elem_ty with Some elem_ty -> Array elem_ty | None -> specialize f.return.ty)
            else if
              String.equal lib_name "Array" && String.equal f.name "ShallowCopy"
            then (
              match elem_ty with
              | Some (Struct _ as elem_ty) -> Array (Ref elem_ty)
              | _ -> specialize f.return.ty)
            else specialize f.return.ty
      (* functype/delegate call *)
      | Call (e, args, _) -> (
          match e.ty with
          | FuncType (Some (name, _)) ->
              let f = Hashtbl.find_exn ctx.functypes name in
              let args = check_call f.name f.params args in
              expr.node <-
                Call (e, args, FuncTypeCall (Option.value_exn f.index));
              expr.ty <- f.return.ty
          | Delegate (Some (name, _)) ->
              let f = Hashtbl.find_exn ctx.delegates name in
              let args = check_call f.name f.params args in
              expr.node <-
                Call (e, args, DelegateCall (Option.value_exn f.index));
              expr.ty <- f.return.ty
          | Ref (Delegate (Some (name, _))) ->
              let f = Hashtbl.find_exn ctx.delegates name in
              let args = check_call f.name f.params args in
              expr.node <-
                Call (e, args, DelegateCall (Option.value_exn f.index));
              expr.ty <- f.return.ty
          | Struct _ as target_ty -> (
              (* v12 user-type cast: `StructName(expr)` — the Ident
                 callee was tagged with the struct type by the
                 ResolvedStructType arm. Rewrite as Cast. *)
              match args with
              | [ Some inner ] ->
                  expr.node <- Cast (target_ty, inner);
                  expr.ty <- target_ty
              | _ ->
                  compile_error
                    "struct cast takes exactly one argument"
                    (ASTExpression expr))
          (* v12 calls on generic-typed values (e.g. wrap<hll_param>
             member result) — accept and type the call as hll_param.
             Runtime dispatch is via HLL duck typing. *)
          | HLLParam | Wrap HLLParam | Ref HLLParam | Wrap (Ref HLLParam) ->
              expr.ty <- HLLParam
          (* unknown_delegate / unknown_functype callees — accept and
             type the call as hll_param too. *)
          | Delegate None | Ref (Delegate None) | FuncType None
          | Ref (FuncType None) ->
              expr.ty <- HLLParam
          | _ -> type_error (FuncType None) (Some e) (ASTExpression expr))
      | New { ty; _ } -> (
          match ty with
          | Struct _ -> expr.ty <- Ref ty
          | _ -> type_error (Struct ("", -1)) None (ASTExpression expr))
      | NewCall ({ ty; _ }, args) -> (
          (* v12 `new T(a, b)`. Type-analyze the args here so codegen
             sees them resolved; constructor overload resolution is
             deferred to the codegen-side handler. *)
          List.iter args ~f:(Option.iter ~f:self#visit_expression);
          match ty with
          | Struct _ -> expr.ty <- Ref ty
          | _ -> type_error (Struct ("", -1)) None (ASTExpression expr))
      | ArrayLiteral elems ->
          (* Type-analyze each element, then take the first element's type
             as the array's element type. Heterogeneous elements promote
             to the first type via the usual implicit-conversion rules
             checked at the assignment site; we don't try to unify here. *)
          List.iter elems ~f:self#visit_expression;
          let elem_ty =
            match elems with
            | first :: _ -> first.ty
            | [] -> Void
          in
          expr.ty <- Array elem_ty
      | DummyRef _ ->
          compiler_bug "DummyRef in type checker" (Some (ASTExpression expr))
      | RvalueRef inner ->
          (* [insert_rvalue_ref] wraps non-referenceable args at [ref T]
             call sites; the wrap can be re-visited when type-checking
             reuses an already-resolved subtree (e.g. recursing through
             [OptionalMember]'s temporary Member rewrite). Just propagate
             the inner type. *)
          self#visit_expression inner;
          expr.ty <- inner.ty
      | This -> (
          (* v11 lambdas capture `this` from the enclosing class
             scope. Walk the env stack looking for a class context. *)
          let envs = Stack.to_list self#env_stack in
          let class_ty =
            List.find_map envs ~f:(fun env -> env#current_class)
          in
          match class_ty with
          | Some ty -> expr.ty <- ty
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error "this" (ASTExpression expr))
      | Null -> expr.ty <- NullType
      | Lambda f -> expr.ty <- TyMethod (ft_of_fundecl f)
      | OptionalMember (obj, name, mt) -> (
          (* Resolve [a?.b] by temporarily rewriting it as [a.b] and
             reusing the [Member] resolution path; restore the
             [OptionalMember] wrapper afterward so codegen still emits
             the null-check. If member resolution fails, fall back to
             [HLLParam] so downstream code keeps type-checking. *)
          expr.node <- Member (obj, name, mt);
          (try self#visit_expression expr
           with _ -> expr.ty <- HLLParam);
          match expr.node with
          | Member (o, n, resolved_mt) ->
              expr.node <- OptionalMember (o, n, resolved_mt)
          | Call (({ node = Member (o, n, resolved_mt); _ } as callee), _, _) ->
              callee.node <- OptionalMember (o, n, resolved_mt)
          | _ -> ())
      | NullCoalesce (a, b) ->
          (* If [a] is a [Ref T] (or a call whose AIN-level return is
             [Ref T] — [maybe_deref] strips the [Ref] from [a.ty] on
             call results, so check the bytecode-level type too),
             [b] needs to be referenceable so the codegen can wire
             either branch into the same destination slot — wrap a
             non-referenceable [b] in [RvalueRef].

             [GlobalConstant] Idents (like [false]/[true]) are
             [is_lvalue]-true but [ConstEval] folds them into
             [ConstInt] before [VariableAlloc], so they have no
             memory slot of their own — treat as non-referenceable
             for the wrap decision. *)
          let a_is_ref_typed =
            match a.ty with
            | Ref _ -> true
            | _ ->
                (match a.node with
                | Call (_, _, calltype) ->
                    let rt =
                      match calltype with
                      | FunctionCall fno | MethodCall (_, fno) ->
                          Some (Ain.get_function_by_index ctx.ain fno).return_type
                      | HLLCall (lib_no, fun_no) ->
                          let lib = Ain.get_library_by_index ctx.ain lib_no in
                          Some lib.functions.(fun_no).return_type
                      | DelegateCall no ->
                          Some (Ain.function_of_delegate_index ctx.ain no).return_type
                      | _ -> None
                    in
                    (match rt with
                     | Some (Ain.Type.Ref _) -> true
                     | _ -> false)
                | _ -> false)
          in
          let b_referenceable_for_wrap =
            match b.node with
            | Ident (_, GlobalConstant) -> false
            | _ -> is_referenceable b
          in
          (* [a ?? []]: the empty-literal fallback infers [Array Void];
             type it from the primary branch so its dummy page carries
             the declared element type (same [A_ASSIGN 配列のコピーに失
             敗しました] fault as the [check_funarg_or_return] case —
             e.g. [PlayerCardCollection@GetOrganizationCards]'s
             [At(i)?.GetAllInstance() ?? []]). Refine before the
             [RvalueRef] wrap below so the clone inherits it. *)
          (match (b.node, (match a.ty with Ref t -> t | t -> t), b.ty) with
          | ArrayLiteral [], (Array _ as arr), Array Void -> b.ty <- arr
          | _ -> ());
          (* v12 value-form [recv?.field ?? fallback] on a scalar field:
             codegen defers the field READ past the null-check merge as
             a (page, index) pair and dereferences with a single [REF],
             so the fallback too needs a home to point the pair at —
             the [<dummy : 右辺値参照化用>] local the original compiler
             allocates. Wrap a non-referenceable [b] so variableAlloc
             backs it with that dummy. *)
          let a_is_deferred_optional_field =
            (* Codegen's deferred-pair arm additionally requires the
               receiver to be a variable ref; call-result receivers fall
               back to the generic protocol but still get the [b] wrap —
               the original allocates the (then-unused) spill dummy for
               them too, and matching its vars table keeps slot numbers
               aligned.
               String fields take their own protocol (in-branch read +
               marker merge + [A_REF]) but need the same spill dummy for
               the fallback: without it the fallback has no home and,
               worse, the merged string was consumed un-bumped — the
               assignment's trailing [DELETE] then freed the SOURCE
               member's own string page ([SpecificBattleSkillConverter@0]
               freed [g_enemy.CreateId]; the next construction — via
               [LeaderCard@UpdateSkillCache]'s postset chain at battle
               entry — read the dead page: ページの取得に失敗２
               [S_ASSIGN]). *)
            Ain.version_gte ctx.ain (12, 0)
            && (match a.node with
               | OptionalMember (_, _, ClassVariable _) -> true
               | _ -> false)
            &&
            match a.ty with
            | Int | Bool | Float | Enum _ | String -> true
            | _ -> false
          in
          (if (a_is_ref_typed || a_is_deferred_optional_field)
              && Ain.version ctx.ain > 8
              && not b_referenceable_for_wrap then (
            let inner = clone_expr b in
            b.node <- RvalueRef inner;
            (* The spill dummy is typed after the FIELD being read
               (orig: [<dummy : 右辺値参照化用> : bool] for a bool
               field with a literal fallback), not after the literal. *)
            if a_is_deferred_optional_field then b.ty <- a.ty));
          expr.ty <- (match a.ty with Ref t -> t | t -> t));
      (* v11 property read: any [Member] still tagged with [ClassProperty]
         after the main resolution pass is being used as an rvalue
         (assignment LHS handling above rewrites the whole [Assign]).
         Rewrite to a getter call. Write-only properties (no getter)
         leave the [Member ClassProperty] in place; the surrounding
         [Assign] picks it up via the [Member ClassProperty] arm. *)
      (match expr.node with
      | Member (obj, _, ClassProperty prop) -> (
          match prop.prop_getter_index with
          | Some getter_idx ->
              let class_idx =
                match obj.ty with
                | Struct (_, i) | Ref (Struct (_, i)) -> i
                | _ -> -1
              in
              let getter_name =
                prop.prop_class ^ "@" ^ prop.prop_name ^ "::get"
              in
              let getter_expr =
                make_expr ~ty:expr.ty ~loc:expr.loc
                  (Member
                     ( obj,
                       prop.prop_name ^ "::get",
                       ClassMethod (getter_name, getter_idx) ))
              in
              expr.node <-
                Call (getter_expr, [], MethodCall (class_idx, getter_idx))
          | None -> ())
      | _ -> ());
      (* Restore the [OptionalMember] wrapping on [Call (Member ...)]
         that was temporarily unwrapped at the top of visit_expression
         so the downstream Call/ClassMethod resolution could match. *)
      (match optional_call_info with
      | Some (e, obj, name) -> (
          match e.node with
          | Member (_, _, resolved_mt) ->
              e.node <- OptionalMember (obj, name, resolved_mt)
          | _ -> ())
      | None -> ())

    method! visit_statement stmt =
      self#catch_errors (fun () ->
          super#visit_statement stmt;
          match stmt.node with
          | EmptyStatement -> ()
          | Declarations _ -> ()
          | Expression ({ node = Ident (_, FunctionName _); _ } as e) ->
              (* rewrite bare function names at statement-level as function calls *)
              let expr =
                {
                  node = Call (e, [], UnresolvedCall);
                  ty = Untyped;
                  loc = e.loc;
                }
              in
              self#visit_expression expr;
              stmt.node <- Expression expr
          | Expression e -> check_not_array e
          | Compound _ -> ()
          | Label _ -> ()
          | If (test, _, _) | While (test, _) | DoWhile (test, _) ->
              type_check (ASTStatement stmt) Int test
          | For (_, test, inc, _) ->
              Option.iter ~f:(type_check (ASTStatement stmt) Int) test;
              Option.iter ~f:check_not_array inc
          | ForEach _ ->
              (* [desugar_foreach] in compile.ml replaces every [ForEach]
                 with a [While] before type-checking, so a [ForEach]
                 here means the desugar pass was skipped. *)
              compiler_bug "ForEach not desugared before type analysis"
                (Some (ASTStatement stmt))
          | Goto _ -> ()
          | Continue -> ()
          | Break -> ()
          | Switch (expr, _) | Case expr -> (
              maybe_deref expr;
              match expr.ty with
              | String -> ()
              | _ -> type_check (ASTStatement stmt) Int expr)
          | Default -> ()
          | Return (Some e) -> (
              match self#env#current_function with
              | None ->
                  compiler_bug "return statement outside of function"
                    (Some (ASTStatement stmt))
              | Some f -> (
                  if f.is_label then
                    compile_error "cannot return from scenario function"
                      (ASTStatement stmt);
                  match f.return.ty with
                  | Ref ty ->
                      self#check_referenceable e (ASTExpression e);
                      ref_type_check (ASTStatement stmt) ty e
                  | _ ->
                      self#check_funarg_or_return (ASTStatement stmt)
                        f.return.ty e;
                      (* Refine ArrayLiteral element type from the function's
                         return type. [return [0, 1, 2]] inside [array@Enum
                         f()] is typed by [visit_expression]'s ArrayLiteral
                         arm as [Array Int] (first element's type), but
                         [variableAlloc] uses [expr.ty] to type the dummy
                         slot it creates for the literal. orig types the
                         dummy as [Array Enum] (matching the return type),
                         which makes [CALLHLL Array.PushBack] emit element-
                         type code 92 (Enum) instead of 10 (Int). Crashed
                         start-game in [CommonFrame::InitFramePoint] with
                         [A_ASSIGN 配列のコピーに失敗しました]. (The
                         empty literal's [Array Void] is refined inside
                         [check_funarg_or_return] above, which also
                         covers call arguments.) *)
                      (match (e.node, f.return.ty, e.ty) with
                      | ArrayLiteral _, Array t, Array Int
                        when (match t with Enum _ -> true | _ -> false) ->
                          e.ty <- Array t
                      | _ -> ())))
          | Return None -> (
              match self#env#current_function with
              | None ->
                  compiler_bug "return statement outside of function"
                    (Some (ASTStatement stmt))
              | Some f -> (
                  if f.is_label then
                    compile_error "cannot return from scenario function"
                      (ASTStatement stmt);
                  match f.return.ty with
                  | Void -> ()
                  | _ -> type_error f.return.ty None (ASTStatement stmt)))
          | Jump name -> (
              match Hashtbl.find ctx.functions name with
              | Some f when f.is_label -> ()
              | _ ->
                  compile_error
                    (name ^ " is not a scenario function")
                    (ASTStatement stmt))
          | Jumps e -> type_check (ASTExpression e) String e
          | Message _ -> ()
          | RefAssign (lhs, rhs) ->
              self#check_ref_assign (ASTStatement stmt) lhs rhs;
              (* v11 foreach desugars the loop variable with a placeholder
                 [wrap<hll_param>] / [ref array<hll_param>] type, since
                 its concrete element type isn't known until the
                 container is type-checked. When the first [RefAssign]
                 to such a variable is analysed, narrow the lhs (and
                 its declared type) to match the rhs — later uses like
                 [x?.Method()] then resolve normally instead of tripping
                 the sanity check. *)
              let resolve_hll ty_lhs ty_rhs =
                match ty_lhs with
                | HLLParam | Ref HLLParam ->
                    Some (match ty_rhs with Ref _ -> ty_rhs | t -> Ref t)
                | Wrap HLLParam ->
                    Some (match ty_rhs with Wrap _ -> ty_rhs | t -> Wrap t)
                | Ref (Array HLLParam) ->
                    Some
                      (match ty_rhs with
                      | Ref (Array _) -> ty_rhs
                      | Array _ -> Ref ty_rhs
                      | _ -> ty_lhs)
                | Array HLLParam ->
                    Some (match ty_rhs with Array _ -> ty_rhs | _ -> ty_lhs)
                | _ -> None
              in
              (match resolve_hll lhs.ty rhs.ty with
              | Some resolved -> (
                  lhs.ty <- resolved;
                  match lhs.node with
                  | Ident (name, _) -> (
                      match self#env#get_local name with
                      | Some v -> (
                          match resolve_hll v.type_spec.ty rhs.ty with
                          | Some t -> v.type_spec.ty <- t
                          | None -> ())
                      | None -> ())
                  | _ -> ())
              | None -> ())
          | ObjSwap (lhs, rhs) ->
              self#check_lvalue lhs (ASTStatement stmt);
              self#check_lvalue rhs (ASTStatement stmt);
              (* FIXME: error if the type is ref or unsupported type *)
              type_check (ASTStatement stmt) lhs.ty rhs)

    method! visit_variable var =
      super#visit_variable var;
      (* v11 foreach-desugared container: [ref array<hll_param>] is a
         placeholder narrowed from the actual initializer's type so
         later subscript + ref-assign propagate a concrete element
         type to the loop variable. *)
      (match (var.type_spec.ty, var.initval) with
      | Ref (Array HLLParam), Some { ty; _ } -> (
          match ty with
          | Array _ -> var.type_spec.ty <- Ref ty
          | Ref (Array _) -> var.type_spec.ty <- ty
          | _ -> ())
      | _ -> ());
      let nr_dims = List.length var.array_dim in
      (* Check that there is no initializer if array has explicit dimensions *)
      if nr_dims > 0 && Option.is_some var.initval then
        compile_error "Initializer provided for array with explicit dimensions"
          (ASTVariable var);
      (* Check that number of dims matches rank of array *)
      if nr_dims > 0 && not (nr_dims = array_rank var.type_spec.ty) then
        compile_error "Number of array dimensions does not match array rank"
          (ASTVariable var);
      (* Check that array dims are integers *)
      List.iter var.array_dim ~f:(fun e -> type_check (ASTVariable var) Int e);
      (* Check initval matches declared type *)
      match var.initval with
      | Some expr -> (
          match var.type_spec.ty with
          | Ref ty ->
              self#check_referenceable expr (ASTVariable var);
              maybe_deref expr;
              ref_type_check (ASTVariable var) ty expr
          | t -> self#check_assign (ASTVariable var) t expr)
      | None -> ()

    method! visit_declaration decl =
      self#catch_errors (fun () -> super#visit_declaration decl)

    method! visit_fundecl f =
      super#visit_fundecl f;
      if String.equal f.name "main" then
        match (f.return.ty, f.params) with
        | Int, [] -> Ain.set_main_function ctx.ain (Option.value_exn f.index)
        | _ ->
            compile_error "Invalid declaration of 'main' function"
              (ASTDeclaration (Function f))
      else if String.equal f.name "message" then
        match f.return.ty with
        | Void -> (
            match List.map f.params ~f:(fun v -> v.type_spec.ty) with
            | [ Int; Int; String ] ->
                Ain.set_message_function ctx.ain (Option.value_exn f.index)
            | _ ->
                compile_error "Invalid declaration of 'message' function"
                  (ASTDeclaration (Function f)))
        | _ ->
            compile_error "invalid declaration of 'message' function"
              (ASTDeclaration (Function f))
  end

let check_types ctx decls =
  let visitor = new type_analyze_visitor ctx in
  visitor#visit_toplevel decls;
  visitor#errors

let check_types_exn ctx decls =
  current_ain := Some ctx.ain;
  let errors = check_types ctx decls in
  current_ain := None;
  if not (List.is_empty errors) then raise_list errors
