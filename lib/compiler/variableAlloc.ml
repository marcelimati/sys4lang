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

open Common
open Base
open Jaf
open CompileError

type scope_kind = ScopeAnon | ScopeLoop | ScopeSwitch
type var_set = (int, Int.comparator_witness) Set.t

type scope = {
  (* variables allocated before entering the scope *)
  initial_vars : var_set;
  (* list of unresolved break statements *)
  mutable breaks : (statement * var_set) list;
  (* list of unresolved continue statements *)
  mutable continues : (statement * var_set) list;
}

type label_data = {
  (* list of variables allocated at the label *)
  mutable live_vars : var_set option;
  (* list of goto statements to the label *)
  mutable gotos : (statement * var_set) list;
}

let dummy_var_seqno = ref 0

class variable_alloc_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val func_vars : variable list Stack.t = Stack.create ()
    val scopes = Stack.create ()
    val mutable labels = Hashtbl.create (module String)
    val mutable suppress_direct_new_dummy = 0
    val mutable suppress_foreach_container_rvalue_call_dummy = 0
    val mutable suppress_array_literal_dummy = 0
    val mutable prop_setter_call_dummy_cache :
        (string, int) Hashtbl.t option =
      None
    val mutable null_coalesce_call_dummy_cache :
        (string, int) Hashtbl.t option =
      None
    val mutable current_function_name = None
    val mutable current_function_return_ty : jaf_type option = None
    method is_v12_iface_storage_ty ty =
      let is_true_iface n = Hashtbl.mem ctx.interface_names n in
      let is_iface_compat_class n =
        Hashtbl.mem ctx.iface_compatible_classes n
      in
      let rec walk_outer = function
        | Unresolved name -> is_true_iface name || is_iface_compat_class name
        | Struct (name, _) -> is_true_iface name || is_iface_compat_class name
        | Ref (Unresolved name) -> is_true_iface name
        | Ref (Struct (name, _)) -> is_true_iface name
        | Ref t -> walk_outer t
        | _ -> false
      in
      Ain.version_gte ctx.ain (12, 0) && walk_outer ty

    method defer_v12_uninit_iface_local (v : variable) =
      self#is_v12_iface_storage_ty v.type_spec.ty
      && Poly.equal v.kind LocalVar
      && (not v.is_private)
      && Option.is_none v.index
      && Option.is_none v.initval

    method private assignment_to_deferred_iface_local (lhs : expression) =
      match lhs.node with
      | Ident (name, LocalVariable _) -> (
          match self#env#get_local name with
          | Some v -> self#defer_v12_uninit_iface_local v
          | None -> false)
      | _ -> false

    method start_scope =
      Stack.push scopes
        { initial_vars = self#current_var_set; breaks = []; continues = [] }

    method end_scope kind =
      let scope = Stack.pop_exn scopes in
      let update_break_continue (stmt, vars) =
        stmt.delete_vars <- Set.elements (Set.diff vars scope.initial_vars)
      in
      (* function to transfer breaks to parent scope *)
      let carry_breaks () =
        match Stack.top scopes with
        | None -> (
            match scope.breaks with
            | [] -> ()
            | (stmt, _) :: _ ->
                compile_error "Unresolved break statement" (ASTStatement stmt))
        | Some parent -> parent.breaks <- List.append parent.breaks scope.breaks
      in
      (* function to transfer continues to parent scope *)
      let carry_continues () =
        match Stack.top scopes with
        | None -> (
            match scope.continues with
            | [] -> ()
            | (stmt, _) :: _ ->
                compile_error "Unresolved continue statement"
                  (ASTStatement stmt))
        | Some parent ->
            parent.continues <- List.append parent.continues scope.continues
      in
      match kind with
      | ScopeLoop ->
          List.iter scope.breaks ~f:update_break_continue;
          List.iter scope.continues ~f:update_break_continue
      | ScopeSwitch ->
          List.iter scope.breaks ~f:update_break_continue;
          carry_continues ()
      | ScopeAnon ->
          carry_breaks ();
          carry_continues ()

    method resolve_gotos =
      Hashtbl.iter labels ~f:(fun { live_vars; gotos } ->
          match live_vars with
          | Some label_vars ->
              List.iter gotos ~f:(fun (stmt, goto_vars) ->
                  (* variables which aren't in-scope at the target label should be deleted *)
                  stmt.delete_vars <-
                    Set.elements (Set.diff goto_vars label_vars))
          | None ->
              compile_error "Unresolved label"
                (ASTStatement (fst (List.last_exn gotos))));
      Hashtbl.clear labels

    method current_var_set =
      Set.of_list
        (module Int)
        (List.filter_map self#env#var_list ~f:(fun v -> v.index))

    method add_continue stmt =
      let scope = Stack.top_exn scopes in
      scope.continues <- (stmt, self#current_var_set) :: scope.continues

    method add_break stmt =
      let scope = Stack.top_exn scopes in
      scope.breaks <- (stmt, self#current_var_set) :: scope.breaks

    method add_label name stmt =
      Hashtbl.update labels name ~f:(function
        | None -> { live_vars = Some self#current_var_set; gotos = [] }
        | Some { live_vars = None; gotos } ->
            { live_vars = Some self#current_var_set; gotos }
        | Some _ -> compile_error "Duplicate label" (ASTStatement stmt))

    method add_goto name stmt =
      let d =
        Hashtbl.find_or_add labels name ~default:(fun _ ->
            { live_vars = None; gotos = [] })
      in
      d.gotos <- (stmt, self#current_var_set) :: d.gotos

    method get_var_no name =
      let in_current () = self#env#get_local name in
      let in_parent () =
        (* v11 lambdas capture locals from enclosing scopes. If [name]
           isn't in the current function's env, walk outwards through
           the env_stack. *)
        match Stack.to_list self#env_stack with
        | _ :: rest ->
            List.find_map rest ~f:(fun env -> env#get_local name)
        | [] -> None
      in
      match Option.first_some (in_current ()) (in_parent ()) with
      | Some v -> (
          (* v12 forward-reference: jaf.ml's pre-walk pushes
             declarations into the env BEFORE their textual location,
             so the env knows the name exists. The matching slot is
             still unallocated until the variable is actually used.
             Allocate now (lazily, on first reference) so the slot
             ordering matches the original v12 compiler, which
             allocates in source-encounter order — both for named
             vars and for the [<dummy : ...>] slots [variableAlloc]
             creates during expression compilation.
             Without lazy allocation, my earlier pre-allocate hoist
             put all named locals before any dummies and shifted
             every slot index — breaking [Ident -> LocalVariable]
             references and producing wrong bytecode. *)
          match v.index with
          | Some i -> i
          | None when Ain.version_gte ctx.ain (12, 0) ->
              self#add_var v;
              Option.value_exn v.index
          | None -> compiler_bug ("Undefined variable: " ^ name) None)
      | None -> compiler_bug ("Undefined variable: " ^ name) None

    (* v11 lambda capture: how many enclosing frames to walk to find
       [name] — 0 if local to the current function, 1 for the direct
       parent, 2 for the grandparent, etc. Used to flip a [LocalVariable]
       ident into a [CapturedVariable] so codegen can emit the right
       [X_GETENV] chain. *)
    method get_capture_level name =
      match self#env#get_local name with
      | Some _ -> 0
      | None -> (
          match Stack.to_list self#env_stack with
          | _ :: rest ->
              let rec find level = function
                | [] -> 0
                | env :: tl -> (
                    match env#get_local name with
                    | Some _ -> level
                    | None -> find (level + 1) tl)
              in
              find 1 rest
          | [] -> 0)

    method add_var (v : variable) =
      let vars = Stack.pop_exn func_vars in
      let i = List.length vars in
      v.index <- Some i;
      (* v11 [Wrap T] locals also occupy a [Void] companion slot —
         the VM tracks the fat-ref's referent through the second
         entry, mirroring the existing scalar-ref behaviour.
         v12 interface params/locals also need the void companion
         (original Rance10 [void ReleaseComponent(IUserComponent c)]
         has nargs=2 vars=2: IFace + <void>). *)
      (* IFace void padding applies when the JAF type is:
         - bare interface name (Struct(I, _) where I in interface_names)
         - bare class-implementing-interface (Struct(C, _) where C in
           iface_compatible_classes)
         - Ref to a bare interface (also encodes as IFace)
         NOT for Ref to a class-implementing-interface (encodes as
         Ref Struct, no padding). Matches original Rance10 distinction
         between method params [IFace x] (IFace+<void>) and dummies
         like [Ref ClassImpl] (Ref Struct, no padding). *)
      let is_v12_property_event_ref_param =
        Ain.version_gte ctx.ain (12, 0)
        && Poly.equal v.kind Parameter
        &&
        (match current_function_name with
        | Some name ->
            String.is_suffix name ~suffix:"::postset"
            || String.is_suffix name ~suffix:"::preset"
        | None -> false)
        &&
        match v.type_spec.ty with
        | Ref _ -> true
        | _ -> false
      in
      let needs_void_slot =
        is_ref_scalar v.type_spec.ty
        || is_v12_property_event_ref_param
        || Ain.version ctx.ain > 8
           && match v.type_spec.ty with Wrap _ -> true | _ -> false
        || self#is_v12_iface_storage_ty v.type_spec.ty
      in
      Stack.push func_vars
        (if needs_void_slot then
           let void =
             {
               name = "<void>";
               location = v.location;
               array_dim = [];
               is_const = false;
               is_private = false;
               kind = v.kind;
               type_spec = { ty = Void; location = v.type_spec.location };
               initval = None;
               index = Some (i + 1);
             }
           in
           void :: v :: vars
         else v :: vars)

    method create_dummy_var name ty =
      (* create dummy ref variable to store object for extent of statement.
         v12: original Rance10 names these [<dummy : <descr>>] without
         a sequence-number suffix. Pre-v12 keeps the seqno for
         byte-stability of the existing v11 Ixseal target. *)
      let v_name =
        if Ain.version_gte ctx.ain (12, 0) then
          Printf.sprintf "<dummy : %s>" name
        else
          Printf.sprintf "<dummy : %s : %d>" name !dummy_var_seqno
      in
      let v =
        {
          name = v_name;
          location = dummy_location;
          array_dim = [];
          is_const = false;
          is_private = false;
          kind = LocalVar;
          type_spec = { ty; location = dummy_location };
          initval = None;
          index = None;
        }
      in
      self#add_var v;
      self#env#push_var v;
      dummy_var_seqno := !dummy_var_seqno + 1;
      Option.value_exn v.index

    (* v11: when a [Call] returning [Struct] or [String] is used as a
       member-access receiver, the result needs a dummy slot so the
       subsequent method call or field access can take its address.
       The original compiler names these dummies [【 . 】の左辺] (the
       "LHS of the dot operator") for struct returns and
       [右辺値参照化用] (the "rvalue-refification") for strings. *)
    method maybe_wrap_dot_lhs (e : expression) =
      if Ain.version ctx.ain > 8 then
        match e.node with
        | Call (_, _, (FunctionCall fno | MethodCall (_, fno))) -> (
            let f = Ain.get_function_by_index ctx.ain fno in
            match f.return_type with
            | Ain.Type.Struct _ ->
                let dummy_ty = Ref e.ty in
                let v = self#create_dummy_var "【 . 】の左辺" dummy_ty in
                e.node <- DummyRef (v, clone_expr e)
            | Ain.Type.String ->
                let v = self#create_dummy_var "右辺値参照化用" (Ref e.ty) in
                e.node <- DummyRef (v, clone_expr e)
            | _ -> ())
        | Call (_, _, HLLCall (lib_no, fun_no)) -> (
            let lib = Ain.get_library_by_index ctx.ain lib_no in
            let f = lib.functions.(fun_no) in
            match f.return_type with
            | Ain.Type.Struct _ ->
                let dummy_ty = Ref e.ty in
                let v = self#create_dummy_var "【 . 】の左辺" dummy_ty in
                e.node <- DummyRef (v, clone_expr e)
            | _ -> ())
        | _ -> ()

    method option_return_inner (e : expression) =
      match e.node with
      | Call (_, _, (FunctionCall fno | MethodCall (_, fno))) -> (
          match (Ain.get_function_by_index ctx.ain fno).return_type with
          | Ain.Type.Option inner -> Some inner
          | _ -> None)
      | Call (_, _, HLLCall (lib_no, fun_no)) -> (
          let lib = Ain.get_library_by_index ctx.ain lib_no in
          match lib.functions.(fun_no).return_type with
          | Ain.Type.Option inner -> Some inner
          | _ -> None)
      | _ -> None

    method private null_coalesce_optional_setter (lhs : expression) =
      let rec unwrap (e : expression) =
        match e.node with
        | DummyRef (_, inner) | Cast (_, inner) | RvalueRef inner -> unwrap inner
        | _ -> e
      in
      match (unwrap lhs).node with
      | Call
          ( { node =
                OptionalMember
                  ( _,
                    name,
                    ClassMethod (_, _) );
              _ },
            [ Some _ ],
            MethodCall _ )
        when String.is_suffix name ~suffix:"::set" ->
          true
      | _ -> false

    method! visit_expression expr =
      (* Don't recurse into an already-wrapped [DummyRef]: its inner has
         been walked once during the original wrap, and re-walking would
         fire the Call case again on the clone, producing a nested
         [DummyRef (_, DummyRef (_, Call ...))] with two dummy slots
         for the same call. *)
      (* NOTE: statement-level [struct_var = new T] used to suppress the
         New dummy here (paired with a codegen arm that REBOUND the
         variable's page slot: NEW; ASSIGN; POP). orig instead allocates
         [<dummy : new T>] and DEEP-COPIES via [A_REF; SR_ASSIGN],
         preserving the destination page's identity. Rebinding
         [g_battleResult = new BattleResult] (BattleInitializer::Init,
         the only such statement in Rance10) left every alias of the
         global's original page stale — first string write through one
         faulted as [ページの取得に失敗２：S_ASSIGN] at battle entry.
         Decl-init [Struct x = new T;] (visit_variable below) is the
         only remaining suppression: orig genuinely rebinds there. *)
      let prop_setter_cache =
        if Ain.version_gte ctx.ain (12, 0) then
          match expr.node with
          | Call
              ( { node = Member (_, mname, _); _ },
                [ Some _ ],
                MethodCall _ )
            when String.is_suffix mname ~suffix:"::set" ->
              Some (Hashtbl.create (module String))
          | _ -> None
        else None
      in
      let prev_prop_setter_call_dummy_cache = prop_setter_call_dummy_cache in
      if Option.is_some prop_setter_cache then
        prop_setter_call_dummy_cache <- prop_setter_cache;
      let preallocated_newcall_dummy =
        match expr.node with
        | NewCall (ts, _)
          when Ain.version_gte ctx.ain (12, 0)
               && suppress_direct_new_dummy = 0
               && not (Stack.is_empty func_vars) ->
            let varname =
              match ts.ty with
              | Struct (name, _) -> "new " ^ name
              | _ -> "new <unknown>"
            in
            Some (self#create_dummy_var varname (Ref ts.ty))
        | _ -> None
      in
      (match expr.node with
      | DummyRef _ -> ()
      | Assign (EqAssign, lhs, rhs)
        when self#assignment_to_deferred_iface_local lhs ->
          (* v12 deferred iface local: allocate LHS slot FIRST so the
             named local matches its source-declaration position. If we
             visit RHS first, a call dummy gets the lhs's intended slot
             and the named local lands one slot later — the case-end
             cleanup pass then emits ASSIGN -1 on the named-local slot
             (because cleanup walks slots in numeric order), wiping the
             value we just stored. Matches original Rance10's
             CEnqueteItemManager@Add layout: Item=slot 1, call dummies
             at slots 3/5/7/9/11. *)
          self#visit_expression lhs;
          self#visit_expression rhs
      | NullCoalesce (lhs, rhs) when Ain.version_gte ctx.ain (12, 0) ->
          let prev = null_coalesce_call_dummy_cache in
          null_coalesce_call_dummy_cache <- Some (Hashtbl.create (module String));
          Exn.protect
            ~f:(fun () ->
              self#visit_expression lhs;
              self#visit_expression rhs)
            ~finally:(fun () -> null_coalesce_call_dummy_cache <- prev)
      | _ -> super#visit_expression expr);
      if Option.is_some prop_setter_cache then
        prop_setter_call_dummy_cache <- prev_prop_setter_call_dummy_cache;
      (* After subexpressions are visited, look for a [Call] or
         [Member.ClassMethod] whose receiver is itself a call result —
         wrap the inner call in a [DummyRef] so its returned struct /
         string has a stable home for the member access. *)
      (match expr.node with
      | Call ({ node = Member (obj, _, _); _ }, _, _)
      | Member (obj, _, ClassMethod _) ->
          self#maybe_wrap_dot_lhs obj
      | _ -> ());
      match expr.node with
      | Ident (name, t) -> (
          (* save local variable number at identifier nodes *)
          match t with
          | LocalVariable (_, loc) ->
              let idx = self#get_var_no name in
              let level = self#get_capture_level name in
              if level > 0 then
                expr.node <- Ident (name, CapturedVariable (idx, level))
              else expr.node <- Ident (name, LocalVariable (idx, loc))
          | _ -> ())
      | Call (_, args, calltype) ->
          let v11 = Ain.version_gte ctx.ain (11, 0) in
          (* v11: check the AIN-level return type too — typeAnalysis's
             [maybe_deref] collapses [Ref T] to [T] on call results, so
             [expr.ty] alone misses calls like [CF_CASColor] that return
             [ref CASColor] at bytecode level. Either form needs a
             dummy slot to back the returned reference. *)
          let v12 = Ain.version_gte ctx.ain (12, 0) in
          let is_ref_or_iface = function
            | Ain.Type.Ref _ -> true
            | Ain.Type.IFace _ when v12 -> true
            | _ -> false
          in
          let ain_return_type =
            if not v11 then None
            else
              match calltype with
              | FunctionCall fno | MethodCall (_, fno) ->
                  Some (Ain.get_function_by_index ctx.ain fno).return_type
              | DelegateCall no ->
                  Some (Ain.function_of_delegate_index ctx.ain no).return_type
              | HLLCall (lib_no, fun_no) ->
                  let lib = Ain.get_library_by_index ctx.ain lib_no in
                  Some lib.functions.(fun_no).return_type
              | _ -> None
          in
          let ain_returns_ref =
            match ain_return_type with
            | Some ty -> is_ref_or_iface ty
            | None -> false
          in
          let expr_ty_ref =
            match expr.ty with Ref _ -> true | _ -> false
          in
          if expr_ty_ref || ain_returns_ref then (
            let call_key = expr_to_string expr in
            let varname =
              match calltype with
              | FunctionCall fno | MethodCall (_, fno) ->
                  (Ain.get_function_by_index ctx.ain fno).name
              | HLLCall (lib_no, fun_no) ->
                  let lib = Ain.get_library_by_index ctx.ain lib_no in
                  lib.functions.(fun_no).name
              | DelegateCall _ -> "<delegate>"
              | FuncTypeCall _ -> "<functype>"
              | _ ->
                  compiler_bug "variable_alloc_visitor: unexpected call type"
                    (Some (ASTExpression expr))
            in
            let dummy_ty =
              let ain_return_type_for_dummy =
                match calltype with HLLCall _ -> None | _ -> ain_return_type
              in
              match (calltype, ain_return_type, expr.ty) with
              | HLLCall _, Some (Ain.Type.Ref _), Struct _ -> Ref expr.ty
              | _ -> (
              match ain_return_type_for_dummy with
              | Some (Ain.Type.Ref _ as ty) -> ain_to_jaf_type ctx.ain ty
              | Some (Ain.Type.IFace _ as ty) when v12 ->
                  ain_to_jaf_type ctx.ain ty
              | _ -> (
                  match jaf_to_ain_type ~ctx expr.ty with
                  | Ain.Type.IFace _ when v12 -> expr.ty
                  | _ -> if expr_ty_ref then expr.ty else Ref expr.ty))
            in
            let cache =
              match null_coalesce_call_dummy_cache with
              | Some _ as cache -> cache
              | None -> prop_setter_call_dummy_cache
            in
            match cache with
            | Some cache
              when Ain.version_gte ctx.ain (12, 0)
                   && (Option.is_some null_coalesce_call_dummy_cache
                      || not (self#is_v12_iface_storage_ty dummy_ty)) -> (
                match Hashtbl.find cache call_key with
                | Some v ->
                    expr.node <-
                      if Option.is_some null_coalesce_call_dummy_cache then
                        DummyRef (v, clone_expr expr)
                      else Ident (call_key, LocalVariable (v, expr.loc))
                | None ->
                    let v = self#create_dummy_var varname dummy_ty in
                    Hashtbl.set cache ~key:call_key ~data:v;
                    expr.node <- DummyRef (v, clone_expr expr))
            | _ ->
                let v = self#create_dummy_var varname dummy_ty in
                expr.node <- DummyRef (v, clone_expr expr));
          (* v11 needs a stable home for any [RvalueRef] argument so the
             callee can take its address. Wrap each such arg in a
             [DummyRef] pointing at a fresh local. For reference-shaped
             types (string / struct / array / wrap / functype /
             delegate) the dummy itself must be a [Ref T] so the VM's
             cleanup decrements rather than frees. Pre-v11 codegen
             handles [RvalueRef] args directly without a dummy slot. *)
          if v11 then
            List.iter args ~f:(function
              | Some ({ node = RvalueRef inner; ty; _ } as arg) ->
                  let dummy_ty =
                    match ty with
                    | Ref (Int | Float | Bool | LongInt | Enum _ | FuncType _
                          | HLLParam) ->
                        (match ty with Ref t -> t | _ -> ty)
                    | String | Struct _ | Array _ | Wrap _ | FuncType _
                    | Delegate _ ->
                        Ref ty
                    | _ -> ty
                  in
                  let v = self#create_dummy_var "右辺値参照化用" dummy_ty in
                  arg.node <- DummyRef (v, inner)
              | _ -> ())
      | New ts when suppress_direct_new_dummy = 0 ->
          let varname =
            match ts.ty with
            | Struct (name, _) -> "new " ^ name
            | _ ->
                compiler_bug "Non-struct type in new expression"
                  (Some (ASTExpression expr))
          in
          let v = self#create_dummy_var varname (Ref ts.ty) in
          expr.node <- DummyRef (v, clone_expr expr)
      | NewCall (ts, _)
        when Ain.version_gte ctx.ain (12, 0)
             && suppress_direct_new_dummy = 0
             && not (Stack.is_empty func_vars) ->
          (* v12 [new T(args)]: wrap in a DummyRef so the result has
             a stable local slot. Original Rance10's function "0"
             has 23 dummy slots for [new CASColor]/[new CASVector3D]
             expressions in global init code. Skip if not inside a
             function (e.g. member initializers outside func body). *)
          let v =
            match preallocated_newcall_dummy with
            | Some v -> v
            | None ->
                let varname =
                  match ts.ty with
                  | Struct (name, _) -> "new " ^ name
                  | _ -> "new <unknown>"
                in
                self#create_dummy_var varname (Ref ts.ty)
          in
          expr.node <- DummyRef (v, clone_expr expr)
      | ArrayLiteral _
        when Ain.version_gte ctx.ain (12, 0)
             && suppress_array_literal_dummy = 0
             && not (Stack.is_empty func_vars) ->
          (* orig names the literal's dummy with its full element type in
             the original compiler's angle syntax: [new array<ref T>],
             [new array<string>] — not the jaf [array@T] form. *)
          let rec angle_ty (t : jaf_type) =
            match t with
            | Array e -> "array<" ^ angle_ty e ^ ">"
            | Ref e -> "ref " ^ angle_ty e
            | t -> jaf_type_to_string t
          in
          let v =
            self#create_dummy_var ("new " ^ angle_ty expr.ty) expr.ty
          in
          expr.node <- DummyRef (v, clone_expr expr)
      | Binary
          ( (RefEqual | RefNEqual),
            ({ node = NullCoalesce (a, { node = Null; _ }); _ } as lhs),
            { node = Null; _ } )
        when Ain.version_gte ctx.ain (12, 0)
             && not (Stack.is_empty func_vars) -> (
          match self#option_return_inner a with
          | Some inner ->
              let v =
                self#create_dummy_var "右辺値参照化用"
                  (ain_to_jaf_type ctx.ain inner)
              in
              lhs.node <- DummyRef (v, clone_expr lhs)
          | None -> ())
      | RvalueRef inner when Ain.version_gte ctx.ain (11, 0) ->
          (* v11: wrap any standalone [RvalueRef] (e.g. a non-
             referenceable method receiver) in a [DummyRef] backed by a
             fresh local. The dummy stores the rvalue so the callee can
             take its address. Reference-shaped types use a [Ref T]
             dummy so the VM's cleanup decrements rather than frees.
             Pre-v11 codegen handles [RvalueRef] directly. *)
          let emit_dummy () =
            let dummy_ty =
              match expr.ty with
              | Ref (Int | Float | Bool | LongInt | Enum _ | FuncType _
                    | HLLParam) ->
                  (match expr.ty with Ref t -> t | _ -> expr.ty)
              | String | Struct _ | Array _ | Wrap _ | FuncType _ | Delegate _
                ->
                  Ref expr.ty
              | _ -> expr.ty
            in
            let v = self#create_dummy_var "右辺値参照化用" dummy_ty in
            expr.node <- DummyRef (v, inner)
          in
          if suppress_foreach_container_rvalue_call_dummy > 0 then
            match (inner.node, inner.ty) with
            | Call _, Array _ -> ()
            | ArrayLiteral _, Array _ -> ()
            | DummyRef (_, { node = ArrayLiteral _; _ }), Array _ -> ()
            | _ -> emit_dummy ()
          else emit_dummy ()
      | _ -> ()

    method private foreach_container_preinit_expr stmt =
      match stmt.node with
      | Declarations { vars = [ v ]; _ }
        when Ain.version_gte ctx.ain (12, 0)
             && Poly.equal v.kind LocalVar
             && String.is_prefix v.name ~prefix:"<foreach_container_" -> (
          match v.initval with
          | Some ({ node = Call _; _ } as call)
            when String.is_suffix (expr_to_string call) ~suffix:"::get()" ->
              Some call
          | Some
              {
                node =
                  RvalueRef ({ node = Call _; _ } as call);
                _;
              }
            when String.is_suffix (expr_to_string call) ~suffix:"::get()" ->
              let dummy_ty =
                if match call.ty with Ref _ -> true | _ -> false then call.ty
                else Ref call.ty
              in
              let name =
                String.drop_suffix (expr_to_string call) (String.length "()")
              in
              let dv = self#create_dummy_var name dummy_ty in
              call.node <- DummyRef (dv, clone_expr call);
              None
          | Some
              {
                node =
                  RvalueRef
                    { node = Call ({ node = Member (obj, _, _); _ }, _, _); _ };
                _;
              } -> (
              match obj.node with This | Ident _ -> None | _ -> Some obj)
          | Some { node = RvalueRef ({ node = ArrayLiteral _; _ } as arr); _ }
            ->
              Some arr
          | _ -> None)
      | _ -> None

    method private visit_foreach_compound_with_preinit stmts =
      match stmts with
      | counter_alloc :: loop_var :: container_init :: rest -> (
          match self#foreach_container_preinit_expr container_init with
          | Some expr ->
              self#visit_statement counter_alloc;
              self#visit_expression expr;
              self#visit_statement loop_var;
              self#visit_statement container_init;
              List.iter rest ~f:self#visit_statement;
              true
          | None -> false)
      | _ -> false

    method! visit_statement stmt =
      (* v12 [return this.GetX();] where [GetX] returns a [T] (value
         type) but the enclosing function returns [ref T]: the [Return]
         codegen needs a local-slot anchor for [SP_INC] to claim the
         page before the caller's frame tears down the returned value.
         Wrap the call expression in [RvalueRef] so the existing
         [RvalueRef -> DummyRef] handler allocates that slot. Mirrors
         orig's per-call temp dummy for ref-property forwarders like
         [CCGParts@SurfaceArea::get -> GetSurfaceArea()]. *)
      (match (stmt.node, current_function_return_ty) with
      | Return (Some ({ node = Call _; _ } as ret_e)),
        Some (Ref (Struct _ | Array _ | String | Delegate _) as ret_ty)
        when Ain.version_gte ctx.ain (12, 0)
             && (match ret_e.ty with
                 | Struct _ | Array _ | String | Delegate _ -> true
                 | _ -> false)
             && (match ret_ty with
                 | Ref inner -> Poly.equal ret_e.ty inner
                 | _ -> false) ->
          let inner = clone_expr ret_e in
          ret_e.node <- RvalueRef inner
      | _ -> ());
      let started_scope =
        match stmt.node with
        | Compound _ ->
            self#start_scope;
            true
        | While (_, _) | DoWhile (_, _) | For (_, _, _, _) ->
            self#start_scope;
            true
        | Switch (_, _) ->
            self#start_scope;
            true
        | _ -> false
      in
      (match stmt.node with
      | Label name -> self#add_label name stmt
      | Goto name -> self#add_goto name stmt
      | Continue -> self#add_continue stmt
      | Break -> self#add_break stmt
      | _ -> ());
      let handled =
        match stmt.node with
        | Compound stmts -> self#visit_foreach_compound_with_preinit stmts
        | _ -> false
      in
      if not handled then super#visit_statement stmt;
      match stmt.node with
      | Compound _ when started_scope -> self#end_scope ScopeAnon
      | (While (_, _) | DoWhile (_, _) | For (_, _, _, _)) when started_scope ->
          self#end_scope ScopeLoop
      | Switch (_, _) when started_scope -> self#end_scope ScopeSwitch
      | _ -> ()

    method! visit_variable v =
      (match v.kind with
      | (Parameter | LocalVar) when (not v.is_const) || v.is_private ->
          (* v12 only: pre-hoist pass may have already allocated the
             slot (params + body LocalVars), so don't double-add. On
             v11 the param-add must always run — Ixseal has a
             user-bodied event whose [value_param] is shared between
             [Name::add] and [Name::remove] via [merge_with_prev]'s
             [decl.params <- prev_decl.params]. Skipping by [v.index]
             would leave the second method's [func_vars] empty. *)
          let v12 = Ain.version_gte ctx.ain (12, 0) in
          (* v12: allocate iface locals at their declaration site (no
             defer). If we wait for first-reference, the local isn't in
             [scope.initial_vars] of any enclosing block scope (switch,
             loop) entered between decl and use, so [break]/[continue]
             cleanup treats it as scope-local and emits
             [PUSH -1; ASSIGN] on its slot — wiping a value the
             post-break code expected to survive (e.g., [Item] in
             CEnqueteItemManager@Add storing the case's call result
             before [break]). Matches original Rance10 layout where
             outer-scope iface locals appear in [initial_vars] at
             every nested scope. *)
          if (not v12) || Option.is_none v.index then (
            (* v11 private locals can re-declare a same-named slot;
               reuse the existing slot rather than allocating a new
               one. *)
            let existing =
              if v.is_private then
                List.find self#env#var_list ~f:(fun (ev : variable) ->
                    String.equal ev.name v.name && Option.is_some ev.index)
              else None
            in
            match existing with
            | Some ev -> v.index <- ev.index
            | None -> self#add_var v)
      | _ -> ());
      let suppress =
        Ain.version_gte ctx.ain (12, 0)
        && Poly.equal v.kind LocalVar
        && (match v.type_spec.ty with Struct _ -> true | _ -> false)
        &&
        match v.initval with
        | Some { node = New _ | NewCall _; _ } -> true
        | _ -> false
      in
      if suppress then suppress_direct_new_dummy <- suppress_direct_new_dummy + 1;
      let suppress_foreach_container_rvalue_call_dummy_for_var =
        Ain.version_gte ctx.ain (12, 0)
        && v.is_private
        && String.is_prefix v.name ~prefix:"<foreach_container_"
        &&
        match v.initval with
        | Some { node = RvalueRef { node = Call _; _ }; _ } -> true
        | Some { node = RvalueRef { node = ArrayLiteral _; _ }; _ } -> true
        | Some
            {
              node =
                RvalueRef
                  { node = DummyRef (_, { node = ArrayLiteral _; _ }); _ };
              _;
            } ->
            true
        | _ -> false
      in
      if suppress_foreach_container_rvalue_call_dummy_for_var then
        suppress_foreach_container_rvalue_call_dummy <-
          suppress_foreach_container_rvalue_call_dummy + 1;
      (match (v.type_spec.ty, v.initval) with
      | (Array elem_ty | Ref (Array elem_ty)),
        Some ({ node = ArrayLiteral _; _ } as init) ->
          init.ty <- Array elem_ty
      | _ -> ());
      let suppress_array_literal_dummy_for_var =
        Ain.version_gte ctx.ain (12, 0)
        && Poly.equal v.kind LocalVar
        &&
        match (v.type_spec.ty, v.initval) with
        | Array _, Some { node = ArrayLiteral _; _ } -> true
        | _ -> false
      in
      if suppress_array_literal_dummy_for_var then
        suppress_array_literal_dummy <- suppress_array_literal_dummy + 1;
      super#visit_variable v;
      if suppress_array_literal_dummy_for_var then
        suppress_array_literal_dummy <- suppress_array_literal_dummy - 1;
      if suppress_foreach_container_rvalue_call_dummy_for_var then
        suppress_foreach_container_rvalue_call_dummy <-
          suppress_foreach_container_rvalue_call_dummy - 1;
      if suppress then suppress_direct_new_dummy <- suppress_direct_new_dummy - 1

    method! visit_fundecl f =
      if Option.is_some f.body then (
        let prev_function_name = current_function_name in
        let prev_function_return_ty = current_function_return_ty in
        current_function_name <- Some f.name;
        current_function_return_ty <- Some f.return.ty;
        let parent_labels = labels in
        labels <- Hashtbl.create (module String);
        Stack.push func_vars [];
        (* v12 hoists block-local var decls to function scope. Pre-walk
           the body and allocate indices for every LocalVar VarDecl so
           a hoisted Ident reference (encountered before the textual
           VarDecl) can resolve to a valid local slot. Mirrors the env
           pre-pop in [jaf.ml:visit_fundecl].

           Params must occupy the first [nr_args] slots — call
           [add_var] on each param FIRST, then hoist body locals. The
           later [super#visit_fundecl] re-visits params via
           [visit_variable] but [add_var] is gated by [Option.is_none
           v.index], so each slot is allocated once.

           Reset [p.index] before [add_var] because v11 event/property
           auto-stubs share their [value_param] across both
           [Name::add] and [Name::remove] user impls (via
           [merge_with_prev]'s [decl.params <- prev_decl.params]). A
           shared param keeps the index from the first visit, which
           makes the second visit skip allocation and leave [vars=[]]
           on the second method. Always re-allocate per function.

           v11 doesn't hoist block-local vars — they're allocated in
           textual order by [super#visit_fundecl]'s [visit_variable]
           pass. Pre-walking would shift their slot indices and break
           foreach-pattern recognition in the decompiler. Gate the
           pre-hoist on v12. *)
        if Ain.version_gte ctx.ain (12, 0) then (
          (* Params still need eager allocation: their slot order is
             fixed (first nr_args slots) and shared params from
             event/property auto-stub fundecls (via [merge_with_prev]
             [decl.params <- prev_decl.params]) need a per-function
             reset. Body LocalVars are NOT pre-allocated here — see
             [get_var_no] for the lazy-on-first-use path that matches
             original Rance10's slot ordering. *)
          List.iter f.params ~f:(fun p ->
              match p.kind with
              | Parameter ->
                  p.index <- None;
                  self#add_var p
              | _ -> ()));
        (* Narrow [Ref (Array HLLParam)] / [Wrap (Struct s)] placeholder
           slots to concrete types in the ain-side variable list:
           - foreach-desugared containers carry [Ref (Array HLLParam)]
             until the initialiser reveals the element type. Resolve to
             [Ref (Array elem_ty)] from the variable's own initval, or
             from a sibling slot of the same name.
           - a [Wrap (Struct s)] slot is upgraded to [Wrap (Ref Struct)]
             when the function also has a matching [Ref (Array Ref Struct)]
             container — the wrap is the loop-var alias of an entry in
             that container.
           Both narrowings keep the slot's bytecode-level type aligned
           with the v11 VM's expectations on member access. *)
        let conv_var all_vars index (v : variable) =
          let ain_type = jaf_to_ain_type ~ctx v.type_spec.ty in
          let ain_type =
            if Ain.version_gte ctx.ain (12, 0) && Poly.equal v.kind Parameter
               &&
               (String.is_suffix f.name ~suffix:"::postset"
               || String.is_suffix f.name ~suffix:"::preset")
            then
              match v.type_spec.ty with
              | Ref inner ->
                  Ain.Type.Wrap (jaf_to_ain_type ~ctx inner)
              | _ -> ain_type
            else ain_type
          in
          let ain_type =
            match ain_type with
            | Ain.Type.Ref (Ain.Type.Array Ain.Type.HLLParam) -> (
                let resolved =
                  match v.initval with
                  | Some { ty = Jaf.(Array t | Ref (Array t)); _ } ->
                      Some (jaf_to_ain_type t)
                  | _ -> None
                in
                let resolved =
                  match resolved with
                  | Some _ -> resolved
                  | None ->
                      List.find_map all_vars ~f:(fun (sv : variable) ->
                          if String.equal sv.name v.name then
                            match sv.initval with
                            | Some { ty = Jaf.(Array t | Ref (Array t)); _ } ->
                                Some (jaf_to_ain_type t)
                            | _ -> None
                          else None)
                in
                match resolved with
                | Some elem_ty -> Ain.Type.Ref (Ain.Type.Array elem_ty)
                | None -> ain_type)
            | _ -> ain_type
          in
          let ain_type =
            match ain_type with
            | Ain.Type.Wrap (Ain.Type.Struct sno as inner) ->
                let has_matching_ref_container =
                  List.exists all_vars ~f:(fun (sv : variable) ->
                      match sv.type_spec.ty with
                      | Ref (Array (Ref (Struct (_, sno2))))
                      | Array (Ref (Struct (_, sno2))) ->
                          sno = sno2
                      | _ -> false)
                in
                if has_matching_ref_container then
                  Ain.Type.Wrap (Ain.Type.Ref inner)
                else ain_type
            | _ -> ain_type
          in
          Ain.Variable.make ~index v.name ain_type
        in
        let add_vars vars (a_f : Ain.Function.t) =
          { a_f with vars = List.mapi vars ~f:(conv_var vars) }
        in
        self#start_scope;
        super#visit_fundecl f;
        self#end_scope ScopeAnon;
        self#resolve_gotos;

        (* write updated fundecl to ain file. Look up by index, not by
           name: a v11 overload set has multiple ain entries sharing
           the mangled name, so a name-based lookup would always
           return the first overload and clobber it for every body
           in the set. *)
        let vars = List.rev (Stack.pop_exn func_vars) in
        (* v1 scenario labels have no FUNC entry (index = None); skip the
           write-back for them. *)
        (match (f.index, f.is_label && Ain.version ctx.ain = 1) with
        | _, true -> ()
        | Some idx, false ->
            let obj = Ain.get_function_by_index ctx.ain idx in
            let updated = add_vars vars (jaf_to_ain_function ~ctx f obj) in
            Ain.write_function ctx.ain updated
        | None, false ->
            compiler_bug "Undefined function"
              (Some (ASTDeclaration (Function f))));
        current_function_name <- prev_function_name;
        current_function_return_ty <- prev_function_return_ty;
        labels <- parent_labels)
  end

let allocate_variables ctx decls =
  (new variable_alloc_visitor ctx)#visit_toplevel decls
