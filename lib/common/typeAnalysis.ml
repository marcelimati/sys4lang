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
  | { ty = HLLParam; _ } -> true (* hll_param is a wildcard; allow as lvalue *)
  | { node = Call (_, _, HLLCall _); _ } -> true (* HLL call returning ref *)
  | _ -> false

(* A value from which a reference can be made. NULL, reference, this, and
   lvalue are referenceable. *)
let is_referenceable = function
  | { ty = NullType | Ref _; _ } -> true
  | { node = This; _ } -> true
  | { node = Call (_, _, (MethodCall _ | BuiltinCall _ | HLLCall _ | FunctionCall _)); _ } -> true
  | { node = RvalueRef _; _ } -> true
  | e -> is_lvalue e

(* Implicit dereference of variables and members. *)
let maybe_deref (e : expression) =
  match e with
  | { ty = Ref t; node = Ident _ | Member _ | Call (_, _, HLLCall _) | Subscript _; _ } ->
      e.ty <- t
  (* Wrap is always dereffed - the Wrap type only matters for the variable declaration *)
  | { ty = Wrap t; _ } -> e.ty <- t
  | _ -> ()

let insert_rvalue_ref e =
  let needs_wrap =
    (not (is_referenceable e))
    || (match e.node with
        | Call (_, _, (BuiltinCall _ | HLLCall _ | MethodCall _)) ->
            (* Non-ref return values need rvalue ref wrapping for DummyRef *)
            (match e.ty with Ref _ -> false | _ -> true)
        | _ -> false)
  in
  if needs_wrap then (
    e.node <- RvalueRef (clone_expr e);
    e.ty <- Ref e.ty)

let rec type_equal (expected : jaf_type) (actual : jaf_type) =
  match (expected, actual) with
  | TypeUnion (a, b), t -> type_equal a t || type_equal b t
  | Ref a, Ref b -> type_equal a b
  | Ref a, b when type_equal a b -> true (* collapse double-ref *)
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
  | HLLParam, _ -> true
  | _, HLLParam -> true
  | _, Ref HLLParam -> true
  | Ref HLLParam, _ -> true
  | Wrap a, Ref b | Ref a, Wrap b -> type_equal a b
  | Wrap a, b | b, Wrap a -> type_equal a b
  | HLLFunc, _ -> true
  | _, HLLFunc -> true
  | HLLFunc2, _ -> true
  | _, HLLFunc2 -> true
  | Array a, Array b -> type_equal a b
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
      | Ref _ | FuncType _ | Delegate _ | IMainSystem | HLLParam | HLLFunc | HLLFunc2 ->
          actual.ty <- expected
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
      if not (type_equal expected t || type_equal expected actual.ty) then
        type_error (Ref expected) (Some actual) parent
  | _ ->
      if not (type_equal expected actual.ty) then
        (* Try with Ref wrapping for double-ref cases *)
        if not (type_equal (Ref expected) actual.ty) then
          type_error (Ref expected) (Some actual) parent

let type_check_numeric parent (actual : expression) =
  maybe_deref actual;
  match actual.ty with
  | Int | Bool | LongInt | Float | HLLParam -> ()
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | _ -> type_error Int (Some actual) parent

let type_check_member_lhs parent (actual : expression) =
  match actual.ty with
  | Ref (Struct (name, _)) | Wrap (Struct (name, _)) -> name
  | Struct (name, _) -> (
      match actual.node with
      | Ident _ | Member _ | Subscript _ | This | Call _ | New _
      | OptionalMember _ | NullCoalesce _ ->
          name
      | _ ->
          compile_error "Member access not allowed for temporary object" parent)
  | Untyped ->
      compiler_bug "tried to type check untyped expression" (Some parent)
  | _ -> type_error (Struct ("struct", 0)) (Some actual) parent

let check_not_array e =
  match e.ty with
  | Array _ | Ref (Array _) ->
      compile_error "array expression not allowed here" (ASTExpression e)
  | _ -> ()

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

(** Check if an expression already produces a boolean (0/1) result,
    so ITOB is unnecessary. *)
let is_bool_producing_expr (e : expression) =
  match e.node with
  | Binary (op, _, _) -> (
      match op with
      | Equal | NEqual | LT | GT | LTE | GTE
      | RefEqual | RefNEqual
      | LogOr | LogAnd -> true
      | _ -> false)
  | Unary (LogNot, _) -> true
  | Cast (Bool, _) -> true
  | _ -> false

(** Check if an expression is a comparison operator that produces 0/1.
    Unlike is_bool_producing_expr, this does NOT include LogNot —
    the original v11 compiler adds ITOB after NOT but not after
    comparison operators (EQUALE, NOTE, LT, etc.). *)
let is_v11_comparison_expr (e : expression) =
  match e.node with
  | Binary (op, _, _) -> (
      match op with
      | Equal | NEqual | LT | GT | LTE | GTE
      | RefEqual | RefNEqual
      | LogOr | LogAnd -> true
      | _ -> false)
  | Cast (Bool, _) -> true
  | _ -> false

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
  | HLLParam, _ -> b.ty
  | _, HLLParam -> a.ty
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

    (* Try resolving a name in parent environments (for lambda captures) *)
    method resolve_capture name =
      let envs = Stack.to_list env_stack in
      if List.length envs > 1 then
        List.find_map (List.tl_exn envs) ~f:(fun env ->
            env#get_local name)
      else None
    method errors = List.rev errors

    method catch_errors f =
      try f () with Compile_error e -> errors <- e :: errors

    method check_lvalue e parent =
      if not (is_lvalue e) then not_an_lvalue_error e parent

    method check_referenceable e parent =
      if not (is_referenceable e) then not_an_lvalue_error e parent

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
              (* XXX: String -> Method conversion, but needs a delegate index
                 for DG_STR_TO_METHOD instruction *)
              insert_cast (Delegate delegate) expr;
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
          (* Skip int→bool cast for assignments - the VM treats them interchangeably. *)
          if Poly.(t = Bool) && Poly.(rhs.ty = Int || rhs.ty = LongInt) then ()
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
          match self#env#resolve name with
          | ResolvedLocal v | ResolvedGlobal v -> (
              match v.type_spec.ty with
              | Ref ty | Wrap ty -> ref_type_check parent ty rhs
              | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
          | UnresolvedName -> (
              match self#resolve_capture name with
              | Some v -> (
                  match v.type_spec.ty with
                  | Ref ty | Wrap ty -> ref_type_check parent ty rhs
                  | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
              | None -> undefined_variable_error name parent)
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      | Member (_, _, ClassVariable _) | Subscript _ -> (
          match lhs.ty with
          | Ref t | Wrap t -> ref_type_check parent t rhs
          | _ -> type_error (Ref rhs.ty) (Some lhs) parent)
      | _ ->
          (* FIXME? this isn't really a _type_ error *)
          type_error (Ref rhs.ty) (Some lhs) parent

    method! visit_expression expr =
      super#visit_expression expr;
      (* Temporarily normalize OptionalMember to Member for type resolution,
         then restore OptionalMember so codegen sees the null-check semantics. *)
      let optional_call_info = match expr.node with
        | Call ({ node = OptionalMember (obj, name, mt); _ } as e, _args, _ct) ->
            e.node <- Member (obj, name, mt);
            Some (e, obj, name)
        | _ -> None
      in
      (* convenience functions which always pass parent expression *)
      let check = type_check (ASTExpression expr) in
      let check_numeric = type_check_numeric (ASTExpression expr) in
      let coerce_numerics = type_coerce_numerics (ASTExpression expr) in
      let check_member_lhs = type_check_member_lhs (ASTExpression expr) in
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
                  let is_lambda_or_funcaddr =
                    match (a : expression).node with Lambda _ | FuncAddr _ -> true | _ -> false
                  in
                  (* Skip insert_rvalue_ref for calls that already return ref
                     at the ain level - variableAlloc's Call handler creates
                     DummyRef for those. Only wrap non-ref-returning calls. *)
                  let is_ain_ref_call =
                    match (a : expression).node with
                    | Call (_, _, (FunctionCall fno | MethodCall (_, fno))) ->
                        (match (Ain.get_function_by_index ctx.ain fno).return_type with
                        | Ain.Type.Ref _ -> true | _ -> false)
                    | Call (_, _, HLLCall (lib_no, fun_no)) ->
                        let lib = Ain.get_library_by_index ctx.ain lib_no in
                        (match (List.nth_exn lib.functions fun_no).return_type with
                        | Ain.Type.Ref _ -> true | _ -> false)
                    | _ -> false
                  in
                  if Ain.version ctx.ain > 8
                     && not is_lambda_or_funcaddr
                     && not is_ain_ref_call then
                    insert_rvalue_ref a;
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
              (* Try resolving as a captured variable from outer scope *)
              match self#resolve_capture name with
              | Some v ->
                  expr.node <- Ident (name, LocalVariable (Option.value ~default:0 v.index, v.location));
                  expr.ty <- v.type_spec.ty
              | None ->
                  undefined_variable_error name (ASTExpression expr))
          )
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
                  | Int | Float | Bool | LongInt | String | HLLParam -> ()
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
              | HLLParam, _ | _, HLLParam -> ()
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
              let a_ty =
                match a.ty with Ref t | Wrap t -> t | t -> t
              in
              if Poly.(a_ty = HLLParam) then
                (* hll_param: defer type checking to runtime *)
                ()
              else (
                match a.node with
                | Ident _ | Member (_, _, ClassVariable _) ->
                    self#check_ref_assign (ASTExpression expr) a b
                | This -> not_an_lvalue_error a (ASTExpression expr)
                | _ -> (
                    match a.ty with
                    | Ref t ->
                        if is_referenceable b then
                          ref_type_check (ASTExpression expr) t b
                        else if is_scalar t then
                          () (* scalar ref === literal: treat like == *)
                        else (
                          self#check_referenceable b (ASTExpression expr);
                          ref_type_check (ASTExpression expr) t b)
                    | _ ->
                        self#check_referenceable b (ASTExpression expr);
                        not_an_lvalue_error a (ASTExpression expr)));
              expr.ty <- Int)
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
          (* When the two branches differ in ref-ness, materialize the
             non-ref branch as an rvalue ref so the ternary returns a
             reference. Only needed for non-scalar types where the value
             must live in a slot - Int/Float/Bool are dereffed directly. *)
          let needs_rval_wrap (t : jaf_type) =
            match t with Int | Float | Bool | LongInt -> false | _ -> true
          in
          (match (con.ty, alt.ty) with
          | Ref _, Ref _ -> ()
          | Ref t, _ ->
              if Ain.version ctx.ain > 8 && needs_rval_wrap t then (
                let inner = clone_expr alt in
                alt.node <- RvalueRef inner);
              maybe_deref con
          | _, Ref t ->
              if Ain.version ctx.ain > 8 && needs_rval_wrap t then (
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
          | HLLParam -> expr.ty <- HLLParam
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
      | Member (obj, _member_name, _) when Poly.(obj.ty = HLLParam || obj.ty = Ref HLLParam) ->
          (* hll_param member access - type unknown, resolve at runtime *)
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
          match Hashtbl.find struc.members member_name with
          | Some member ->
              if member.is_private then access_check ();
              expr.node <-
                Member
                  ( obj,
                    member_name,
                    if member.is_const then ClassConst struc.name
                    else ClassVariable (Option.value_exn member.index) );
              expr.ty <- member.type_spec.ty
          | None -> (
              let fun_name = struc.name ^ "@" ^ member_name in
              match Hashtbl.find ctx.functions fun_name with
              | Some f ->
                  if f.is_private then access_check ();
                  expr.node <-
                    Member
                      ( obj,
                        member_name,
                        ClassMethod (fun_name, Option.value f.index ~default:(-1)) );
                  expr.ty <- TyMethod (ft_of_fundecl f)
              | None -> (
                  (* Try property getter/setter (Name::get / Name::set) *)
                  let getter_name = struc.name ^ "@" ^ member_name ^ "::get" in
                  let setter_name = struc.name ^ "@" ^ member_name ^ "::set" in
                  match Hashtbl.find ctx.functions getter_name with
                  | Some f ->
                      if f.is_private then access_check ();
                      let idx = Option.value f.index ~default:(-1) in
                      expr.node <-
                        Member
                          ( obj,
                            member_name,
                            ClassMethod (getter_name, idx) );
                      expr.ty <- f.return.ty
                  | None -> (
                      match Hashtbl.find ctx.functions setter_name with
                      | Some f ->
                          if f.is_private then access_check ();
                          let idx = Option.value f.index ~default:(-1) in
                          expr.node <-
                            Member
                              ( obj,
                                member_name,
                                ClassMethod (setter_name, idx) );
                          (* Setter param type is the property type *)
                          expr.ty <-
                            (match f.params with
                            | [ p ] -> p.type_spec.ty
                            | _ -> Void)
                      | None ->
                          undefined_variable_error
                            (struc.name ^ "." ^ member_name)
                            (ASTExpression expr)))))
      (* regular function call *)
      | Call (({ node = Ident (_, FunctionName name); _ } as e), args, _) ->
          let nr_call_args = List.length args in
          let candidates =
            let base = Hashtbl.find_exn ctx.functions name in
            let others =
              let rec collect suffix acc =
                let k =
                  if suffix = 0 then Printf.sprintf "%s#%d" name nr_call_args
                  else Printf.sprintf "%s#%d_%d" name nr_call_args suffix
                in
                match Hashtbl.find ctx.functions k with
                | Some (fd : fundecl) when List.length fd.params = nr_call_args ->
                    collect (suffix + 1) (fd :: acc)
                | Some _ -> collect (suffix + 1) acc
                | None -> List.rev acc
              in
              collect 0 []
            in
            if List.length base.params = nr_call_args then base :: others
            else others @ [ base ]
          in
          let rec try_candidates (cands : fundecl list) =
            match cands with
            | [ fd ] ->
                let resolved_args = check_call fd.name fd.params args in
                (fd, resolved_args)
            | fd :: rest -> (
                try
                  let resolved_args = check_call fd.name fd.params args in
                  (fd, resolved_args)
                with CompileError.Compile_error _ -> try_candidates rest)
            | [] -> failwith "no overload candidates"
          in
          let f, args = try_candidates candidates in
          let fno = Option.value f.index ~default:(-1) in
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
          let nr_call_args = List.length args in
          (* Collect all overloads with matching arity *)
          let candidates =
            let base = Hashtbl.find_exn ctx.functions name in
            let others =
              let rec collect suffix acc =
                let k =
                  if suffix = 0 then Printf.sprintf "%s#%d" name nr_call_args
                  else Printf.sprintf "%s#%d_%d" name nr_call_args suffix
                in
                match Hashtbl.find ctx.functions k with
                | Some fd when List.length fd.params = nr_call_args ->
                    collect (suffix + 1) (fd :: acc)
                | Some _ -> collect (suffix + 1) acc
                | None -> List.rev acc
              in
              collect 0 []
            in
            if List.length base.params = nr_call_args then base :: others
            else others @ [ base ]
          in
          (* Try each candidate; use the first that type-checks *)
          let rec try_candidates (cands : fundecl list) =
            match cands with
            | [ fd ] ->
                let resolved_args = check_call fd.name fd.params args in
                (fd, resolved_args)
            | fd :: rest -> (
                try
                  let resolved_args = check_call fd.name fd.params args in
                  (fd, resolved_args)
                with CompileError.Compile_error _ -> try_candidates rest)
            | [] -> failwith "no overload candidates"
          in
          let f, args = try_candidates candidates in
          let mcall =
            MethodCall (Option.value f.class_index ~default:(-1), Option.value f.index ~default:(-1))
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
          let nr_call_args = List.length args in
          let f =
            let base = Hashtbl.find_exn lib.functions fun_name in
            if List.length base.params = nr_call_args then base
            else
              let arity_key =
                Printf.sprintf "%s#%d" fun_name nr_call_args
              in
              match Hashtbl.find lib.functions arity_key with
              | Some f -> f
              | None -> base
          in
          let args = check_call f.name f.params args in
          let lib_no =
            Option.value_exn (Ain.get_library_index ctx.ain lib.hll_name)
          in
          let nr_params = List.length f.params in
          let fun_no =
            let lib_funcs = (Ain.get_library_by_index ctx.ain lib_no).functions in
            match
              List.findi lib_funcs ~f:(fun _ (lf : Ain.Library.Function.t) ->
                  String.equal lf.name fun_name
                  && List.length lf.arguments = nr_params)
            with
            | Some (i, _) -> i
            | None ->
                Option.value_exn
                  (Ain.get_library_function_index ctx.ain lib_no fun_name)
          in
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
          insert_rvalue_ref obj;
          expr.node <- Call (e, args, BuiltinCall builtin);
          expr.ty <- f.return.ty
      (* already-resolved builtin call (e.g., array Alloc from arrayInit) *)
      | Call (_, _, BuiltinCall builtin) ->
          let f =
            Builtin.fundecl_of_builtin ctx builtin Void
              (Some (ASTExpression expr))
          in
          expr.ty <- f.return.ty
      (* built-in method call via HLL *)
      | Call
          ( ({ node = Member (obj, fun_name, BuiltinHLL lib_name); _ } as e),
            args,
            _ ) ->
          let lib = Hashtbl.find_exn ctx.libraries lib_name in
          let nr_call_args = List.length args + 1 in (* +1 for implicit self *)
          let candidates =
            let base = Hashtbl.find_exn lib.functions fun_name in
            let others =
              let rec collect suffix acc =
                let k =
                  if suffix = 0 then
                    Printf.sprintf "%s#%d" fun_name nr_call_args
                  else
                    Printf.sprintf "%s#%d_%d" fun_name nr_call_args suffix
                in
                match Hashtbl.find lib.functions k with
                | Some (fd : fundecl) when List.length fd.params = nr_call_args ->
                    collect (suffix + 1) (fd :: acc)
                | Some _ -> collect (suffix + 1) acc
                | None -> if suffix > 5 then List.rev acc else collect (suffix + 1) acc
              in
              collect 0 []
            in
            let all =
              if List.length base.params = nr_call_args then base :: others
              else others @ [ base ]
            in
            (* When call has a lambda/method arg, prefer hll_func2 overloads *)
            let call_has_func_arg =
              List.exists args ~f:(function
                | Some { ty = TyMethod _ | TyFunction _ | HLLFunc2 | HLLFunc; _ } -> true
                | Some { node = Lambda _; _ } -> true
                | _ -> false)
            in
            if call_has_func_arg then
              let has_func_param (fd : fundecl) =
                List.exists fd.params ~f:(fun p ->
                    Poly.(p.type_spec.ty = HLLFunc2 || p.type_spec.ty = HLLFunc))
              in
              let specific, generic = List.partition_tf all ~f:has_func_param in
              specific @ generic
            else all
          in
          let rec try_hll_candidates (cands : fundecl list) =
            match cands with
            | [ fd ] ->
                let resolved_args = check_call fd.name (List.tl_exn fd.params) args in
                (fd, resolved_args)
            | fd :: rest -> (
                try
                  let resolved_args = check_call fd.name (List.tl_exn fd.params) args in
                  (fd, resolved_args)
                with CompileError.Compile_error _ -> try_hll_candidates rest)
            | [] -> failwith "no HLL overload candidates"
          in
          let f, args = try_hll_candidates candidates in
          let lib_no =
            Option.value_exn (Ain.get_library_index ctx.ain lib.hll_name)
          in
          let nr_params = List.length f.params in
          let fun_no =
            (* Find the HLL function index matching the resolved overload's arity and types *)
            let lib_funcs = (Ain.get_library_by_index ctx.ain lib_no).functions in
            let has_func_arg =
              List.exists (List.tl_exn f.params) ~f:(fun p ->
                  Poly.(p.type_spec.ty = HLLFunc2 || p.type_spec.ty = HLLFunc))
            in
            match
              List.findi lib_funcs ~f:(fun _ (lf : Ain.Library.Function.t) ->
                  String.equal lf.name fun_name
                  && List.length lf.arguments = nr_params
                  && (if has_func_arg then
                        List.exists lf.arguments ~f:(fun (a : Ain.Library.Argument.t) ->
                            Poly.(a.value_type = Ain.Type.HLLFunc2
                                  || a.value_type = Ain.Type.HLLFunc))
                      else
                        not (List.exists lf.arguments ~f:(fun (a : Ain.Library.Argument.t) ->
                            Poly.(a.value_type = Ain.Type.HLLFunc2
                                  || a.value_type = Ain.Type.HLLFunc)))))
            with
            | Some (i, _) -> i
            | None ->
                Option.value_exn
                  (Ain.get_library_function_index ctx.ain lib_no fun_name)
          in
          insert_rvalue_ref obj;
          expr.node <- Call (e, Some obj :: args, HLLCall (lib_no, fun_no));
          (* For HLL methods returning hll_param, resolve to array element type *)
          let return_ty =
            match (f.return.ty, obj.ty) with
            | HLLParam, Array t | HLLParam, Ref (Array t) -> t
            | Ref HLLParam, Array (Ref t) | Ref HLLParam, Ref (Array (Ref t)) -> Ref t
            | Ref HLLParam, Array t | Ref HLLParam, Ref (Array t) -> Ref t
            | ty, _ -> ty
          in
          expr.ty <- return_ty
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
          | HLLParam ->
              (* hll_param as call target - type unknown at compile time *)
              expr.ty <- HLLParam
          | _ -> type_error (FuncType None) (Some e) (ASTExpression expr))
      | New { ty; _ } -> (
          match ty with
          | Struct _ -> expr.ty <- Ref ty
          | _ -> type_error (Struct ("", -1)) None (ASTExpression expr))
      | DummyRef _ ->
          compiler_bug "DummyRef in type checker" (Some (ASTExpression expr))
      | RvalueRef inner ->
          (* RvalueRef is processed by variableAlloc - just type-check inner *)
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
      | NullCoalesce (a, b) ->
          (* Only materialize the fallback as a reference when the primary
             side is itself Ref-typed; otherwise both sides are plain values
             and no rvalue-ref wrapping is needed. *)
          (match a.ty with
          | Ref _ when Ain.version ctx.ain > 8 && not (is_referenceable b) ->
              let inner = clone_expr b in
              b.node <- RvalueRef inner
          | _ -> ());
          expr.ty <- (match a.ty with Ref t -> t | t -> t)
      | OptionalMember (obj, name, mt) -> (
          (* Resolve like normal Member, then wrap back as OptionalMember *)
          expr.node <- Member (obj, name, mt);
          (try
             self#visit_expression expr
           with _ ->
             (* If resolution fails, treat as HLLParam *)
             expr.ty <- HLLParam);
          (* Restore optional semantics *)
          match expr.node with
          | Member (o, n, resolved_mt) ->
              expr.node <- OptionalMember (o, n, resolved_mt)
          | _ -> ())
      | OptionalCall (f, _, _) -> expr.ty <- f.ty (* approximate *));
      (* Restore OptionalMember inside Call after type resolution *)
      (match optional_call_info with
      | Some (e, obj, name) ->
          (match e.node with
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
          | Expression e ->
              if Ain.version ctx.ain < 11 then check_not_array e
          | Compound _ -> ()
          | Label _ -> ()
          | If (test, _, _) | While (test, _) | DoWhile (test, _) ->
              type_check (ASTStatement stmt) Int test
          | For (_, test, inc, _) ->
              Option.iter ~f:(type_check (ASTStatement stmt) Int) test;
              Option.iter ~f:check_not_array inc
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
              match self#env#resolve name with
              | ResolvedFunction f when f.is_label -> ()
              | _ ->
                  compile_error
                    (name ^ " is not a scenario function")
                    (ASTStatement stmt))
          | Jumps e -> type_check (ASTExpression e) String e
          | Message _ -> ()
          | RefAssign (lhs, rhs) ->
              self#check_ref_assign (ASTStatement stmt) lhs rhs;
              (* For HLLParam lhs, resolve type from rhs *)
              let resolve_hll ty_lhs ty_rhs =
                match ty_lhs with
                | HLLParam | Ref HLLParam ->
                    Some (match ty_rhs with Ref t -> Ref t | t -> Ref t)
                | Wrap HLLParam ->
                    Some (match ty_rhs with Wrap t -> Wrap t | t -> Wrap t)
                | Ref (Array HLLParam) ->
                    Some (match ty_rhs with
                          | Ref (Array _) -> ty_rhs
                          | Array _ -> Ref ty_rhs
                          | _ -> ty_lhs)
                | Array HLLParam ->
                    Some (match ty_rhs with
                          | Array _ -> ty_rhs
                          | _ -> ty_lhs)
                | _ -> None
              in
              (match resolve_hll lhs.ty rhs.ty with
              | Some resolved ->
                  lhs.ty <- resolved;
                  (* Also update variable declaration type *)
                  (match lhs.node with
                  | Ident (name, _) ->
                      (match self#env#get_local name with
                      | Some v ->
                          let vt = v.type_spec.ty in
                          (match resolve_hll vt rhs.ty with
                          | Some t -> v.type_spec.ty <- t
                          | None -> ())
                      | None -> ())
                  | _ -> ())
              | None -> ())
          | ObjSwap (lhs, rhs) ->
              self#check_lvalue lhs (ASTStatement stmt);
              self#check_lvalue rhs (ASTStatement stmt);
              (* FIXME: error if the type is ref or unsupported type *)
              type_check (ASTStatement stmt) lhs.ty rhs
          | ForEach _ ->
              () (* foreach type checking deferred to codegen *))

    method! visit_variable var =
      super#visit_variable var;
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
              ref_type_check (ASTVariable var) ty expr;
              (* For HLLParam variables, infer concrete type from initializer *)
              if Poly.(ty = HLLParam) then (
                match expr.ty with
                | Ref t | t -> var.type_spec.ty <- Ref t)
              else if Poly.(ty = Array HLLParam) then (
                match expr.ty with
                | Ref (Array _) | Array _ -> var.type_spec.ty <- Ref expr.ty
                | _ -> ())
          | t ->
              self#check_assign (ASTVariable var) t expr;
              (* For HLLParam variables, infer concrete type from initializer *)
              if Poly.(t = HLLParam || t = Array HLLParam) then
                var.type_spec.ty <- expr.ty)
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
