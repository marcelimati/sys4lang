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

(* An lvalue is an expression which denotes a location that can be assigned to. *)
let is_lvalue = function
  | { ty = TyFunction _; _ } -> false
  | { node = Ident _ | Member _ | Subscript _ | New _; _ } -> true
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
let is_referenceable = function
  | { ty = NullType | Ref _; _ } -> true
  | { node = This; _ } -> true
  | {
      node =
        Call (_, _, (MethodCall _ | BuiltinCall _ | HLLCall _ | FunctionCall _));
      _;
    } ->
      true
  | { node = RvalueRef _; _ } -> true
  | e -> is_lvalue e

(* Implicit dereference of variables and members. The value of a comma
   expression follows its right operand. *)
let rec maybe_deref (e : expression) =
  match e with
  | {
      ty = Ref t;
      node = Ident _ | Member _ | Call (_, _, HLLCall _) | Subscript _;
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
       stable address for downstream consumers (e.g. method receivers). *)
    | Call (_, _, (BuiltinCall _ | HLLCall _ | MethodCall _)) -> (
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
  | Void, Void -> true
  | Int, (Int | Bool | LongInt) -> true
  | Bool, (Int | Bool | LongInt) -> true
  | LongInt, (Int | Bool | LongInt) -> true
  | Float, Float -> true
  | String, String -> true
  | Struct (_, a), Struct (_, b) -> a = -1 (* any struct *) || a = b
  | IMainSystem, (IMainSystem | Int) -> true
  | FuncType (Some (_, a)), FuncType (Some (_, b)) -> a = b
  | FuncType None, FuncType None -> true
  | Delegate (Some (_, a)), Delegate (Some (_, b)) -> a = b
  | Delegate None, Delegate None -> true
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
  | Array a, Array b -> type_equal a b
  | HLLFunc, _ -> true
  | _, HLLFunc -> true
  | Void, _
  | Ref _, _
  | Int, _
  | Bool, _
  | LongInt, _
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
  | (Int | LongInt | Bool | Float | String), (Int | LongInt | Bool | Float) ->
      true
  | _ -> false

let type_check parent expected (actual : expression) =
  (match expected with Ref _ -> () | _ -> maybe_deref actual);
  match actual.ty with
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | NullType -> (
      match expected with
      | Ref _ | FuncType _ | Delegate _ | IMainSystem -> actual.ty <- expected
      | _ -> type_error expected (Some actual) parent)
  | a_t ->
      if not (type_equal expected a_t) then
        type_error expected (Some actual) parent

let ref_type_check parent expected (actual : expression) =
  match actual.ty with
  | NullType -> actual.ty <- Ref expected
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | Ref t ->
      if not (type_equal expected t) then
        type_error (Ref expected) (Some actual) parent
  | _ ->
      if not (type_equal expected actual.ty) then
        type_error (Ref expected) (Some actual) parent

let type_check_numeric parent (actual : expression) =
  maybe_deref actual;
  match actual.ty with
  | Int | Bool | LongInt | Float -> ()
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
        (* [Ref HLLParam] specialised with an element type that's
           itself [Ref T] would yield [Ref (Ref T)] — an ill-formed
           double ref. Collapse into a single [Ref T]. *)
        | Ref HLLParam -> ( match et with Ref _ -> et | _ -> Ref et)
        | Ref t -> Ref (sub t)
        | t -> t
      in
      sub t

let is_builtin = function
  | Int | Float | String | Array _ | Delegate _ -> true
  | Ref (Int | Float | String | Array _ | Delegate _) -> true
  | _ -> false

let resolve_builtin ctx e name =
  let lib_name, builtin_getter =
    match e.ty with
    | Int | Ref Int -> ("Int", Bytecode.int_builtin_of_string)
    | Float | Ref Float -> ("Float", Bytecode.float_builtin_of_string)
    | String | Ref String -> ("String", Bytecode.string_builtin_of_string)
    | Array _ | Ref (Array _) -> ("Array", Bytecode.array_builtin_of_string)
    | Delegate _ | Ref (Delegate _) ->
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
      let primary = Hashtbl.find_exn ctx.functions name in
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
          | fd :: _ -> fd
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
          (match ordered with
          | fd :: _ -> fd
          | [] -> primary)

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
              | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
          | UnresolvedName -> undefined_variable_error name parent
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      | Member (_, _, ClassVariable _) -> (
          match lhs.ty with
          | Ref t | Wrap t -> ref_type_check parent t rhs
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      (* Subscript of an [array@ref T] yields a [ref T] slot; ref-
         assigning into it (e.g. [arr[i] <- new T()]) is legal. *)
      | Subscript _ -> (
          match lhs.ty with
          | Ref t | Wrap t -> ref_type_check parent t rhs
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
        let check_arg i a v =
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
                  self#check_funarg_or_return (ASTExpression a) v.type_spec.ty a);
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
              expr.node <- Ident (name, FunctionName name);
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
          match Hashtbl.find ctx.functions name with
          | Some f ->
              expr.node <- FuncAddr (name, f.index);
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
                  | Int | Float | Bool | LongInt | String -> ()
                  | _ -> type_error Int (Some b) (ASTExpression expr))
              | Int | Bool | LongInt -> check Int b
              | _ -> type_error Int (Some a) (ASTExpression expr));
              expr.ty <- a.ty
          | Equal | NEqual ->
              maybe_deref a;
              maybe_deref b;
              (* NOTE: NULL is not allowed on lhs *)
              (match (a.ty, b.ty) with
              | String, _ -> check String b
              | FuncType (Some (_, ft_i)), FuncType (Some (_, ft_j)) ->
                  if ft_i <> ft_j then
                    type_error a.ty (Some b) (ASTExpression expr)
              | FuncType (Some (ft_name, _)), TyFunction f ->
                  let ft = Hashtbl.find_exn ctx.functypes ft_name in
                  if not (ft_compatible (ft_of_fundecl ft) f) then
                    type_error a.ty (Some b) (ASTExpression expr)
              | FuncType _, NullType -> b.ty <- a.ty
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
              | This -> not_an_lvalue_error a (ASTExpression expr)
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
                  | _ ->
                      self#check_referenceable b (ASTExpression expr);
                      not_an_lvalue_error a (ASTExpression expr)));
              expr.ty <- Int)
      (* v11 user-bodied event: [obj.E += h] / [obj.E -= h] where the
         [<E>] backing field has been elided (because the user supplied
         add/remove bodies at top level). Lower to a call through the
         user's accessor; the matching member resolution is in the
         Member arm below where it synthesizes [ClassEvent]. *)
      | Assign
          ( ((PlusAssign | MinusAssign) as op),
            ({ node = Member (obj, _, ClassEvent ev); _ }),
            rhs ) ->
          let accessor_kind, accessor_idx =
            match op with
            | PlusAssign -> ("add", ev.event_add_index)
            | MinusAssign -> ("remove", ev.event_remove_index)
            | _ -> ("add", ev.event_add_index)
          in
          (match accessor_idx with
          | None ->
              compile_error
                (sprintf "event `%s.%s` has no %s accessor" ev.event_class
                   ev.event_name accessor_kind)
                (ASTExpression expr)
          | Some idx ->
              let f = Ain.get_function_by_index ctx.ain idx in
              let class_idx = Option.value ~default:(-1) f.struct_type in
              let method_name = ev.event_name ^ "::" ^ accessor_kind in
              let accessor_expr =
                make_expr ~ty:Void ~loc:expr.loc
                  (Member
                     ( obj,
                       method_name,
                       ClassMethod
                         (ev.event_class ^ "@" ^ method_name, idx) ))
              in
              expr.node <-
                Call
                  (accessor_expr, [ Some rhs ], MethodCall (class_idx, idx));
              expr.ty <- Void)
      (* v11 property write — write-only path. The LHS is still a
         [Member ClassProperty] because the getter rewrite at the end
         of [visit_expression] only fires when a getter exists. *)
      | Assign (_, ({ node = Member (obj, _, ClassProperty prop); _ }), rhs) ->
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
              let setter_expr =
                make_expr ~ty:Void ~loc:expr.loc
                  (Member
                     ( obj,
                       prop.prop_name ^ "::set",
                       ClassMethod (setter_name, setter_idx) ))
              in
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
         so the LHS is a [Call (Member ClassMethod _::get, [], _)]. The
         paired setter has the same prefix with [::set]. *)
      | Assign
          ( _,
            ({
               node =
                 Call
                   ( { node = Member (obj, _, ClassMethod (getter_name, _)); _ },
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
              let setter_expr =
                make_expr ~ty:Void ~loc:lhs.loc
                  (Member (obj, surface_name, ClassMethod (setter_name, setter_idx)))
              in
              expr.node <-
                Call
                  (setter_expr, [ Some rhs ], MethodCall (class_idx, setter_idx));
              expr.ty <- Void
          | None ->
              let prop_name =
                String.rsplit2 prefix ~on:'@'
                |> Option.value_map ~default:prefix ~f:snd
              in
              compile_error
                (sprintf "property `%s` is read-only" prop_name)
                (ASTExpression expr))
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
          check_expr con alt;
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
      (* member variable OR method *)
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
             are intercepted in the [Assign] arm. *)
          match Hashtbl.find struc.properties member_name with
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
                      let fun_name = struc.name ^ "@" ^ member_name in
                      match Hashtbl.find ctx.functions fun_name with
                      | Some f ->
                          if f.is_private then access_check ();
                          expr.node <-
                            Member
                              ( obj,
                                member_name,
                                ClassMethod
                                  (fun_name, Option.value_exn f.index) );
                          expr.ty <- TyMethod (ft_of_fundecl f)
                      | None ->
                          (* TODO: separate error type for this? *)
                          undefined_variable_error
                            (struc.name ^ "." ^ member_name)
                            (ASTExpression expr))))))
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
          let elem_ty =
            match obj.ty with
            | Array t | Ref (Array t) -> Some t
            | _ -> None
          in
          let specialize = specialize_hll_param elem_ty in
          let params =
            List.map (List.tl_exn f.params) ~f:(fun p ->
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
          let lib_no =
            Option.value_exn (Ain.get_library_index ctx.ain lib.hll_name)
          in
          let fun_no = self#resolve_hll_ain_index lib_no f in
          insert_rvalue_ref obj;
          expr.node <- Call (e, Some obj :: args, HLLCall (lib_no, fun_no));
          expr.ty <- specialize f.return.ty
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
          | _ -> type_error (FuncType None) (Some e) (ASTExpression expr))
      | New { ty; _ } -> (
          match ty with
          | Struct _ -> expr.ty <- Ref ty
          | _ -> type_error (Struct ("", -1)) None (ASTExpression expr))
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
          match self#env#current_class with
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
          | _ -> ())
      | NullCoalesce (a, b) ->
          (* If [a] is a [Ref T], [b] needs to be referenceable so the
             codegen can wire either branch into the same destination
             slot — wrap a non-referenceable [b] in [RvalueRef]. *)
          (match a.ty with
          | Ref _ when Ain.version ctx.ain > 8 && not (is_referenceable b) ->
              let inner = clone_expr b in
              b.node <- RvalueRef inner
          | _ -> ());
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
                        f.return.ty e))
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
  let errors = check_types ctx decls in
  if not (List.is_empty errors) then raise_list errors
