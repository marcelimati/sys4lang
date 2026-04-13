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
    (* When visiting the LHS of an Assign, we don't want to wrap a property
       getter expression in a DummyRef - codegen replaces the getter with the
       setter at compile time, so the dummy would never be used. This holds the
       physical-identity reference to the LHS expression that should be skipped. *)
    val mutable assign_lhs_skip : expression option = None

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
      match self#env#get_local name with
      | Some v -> Option.value_exn v.index
      | None ->
          (* Try parent environments (lambda captures) *)
          let envs = Stack.to_list env_stack in
          (match
             List.find_map (List.tl_exn envs) ~f:(fun env ->
                 match env#get_local name with
                 | Some v -> Some (Option.value_exn v.index)
                 | None -> None)
           with
          | Some i -> i
          | None -> compiler_bug ("Undefined variable: " ^ name) None)

    method get_capture_level name =
      (* Returns 0 if local, N>0 if captured from Nth parent *)
      match self#env#get_local name with
      | Some _ -> 0
      | None ->
          let envs = Stack.to_list env_stack in
          let rec find level = function
            | [] -> 0
            | env :: rest ->
                match env#get_local name with
                | Some _ -> level
                | None -> find (level + 1) rest
          in
          find 1 (List.tl_exn envs)

    method add_var (v : variable) =
      let vars = Stack.pop_exn func_vars in
      let i = List.length vars in
      v.index <- Some i;
      let needs_void_slot = is_ref_scalar v.type_spec.ty
        || (Ain.version ctx.ain > 8 && match v.type_spec.ty with Wrap _ -> true | _ -> false)
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
      (* create dummy ref variable to store object for extent of statement *)
      let v =
        {
          name = Printf.sprintf "<dummy : %s : %d>" name !dummy_var_seqno;
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

    method maybe_wrap_dot_lhs (e : expression) =
      if Ain.version ctx.ain > 8 then
        match e.node with
        | Call (_, _, (FunctionCall fno | MethodCall (_, fno))) ->
            let f = Ain.get_function_by_index ctx.ain fno in
            (match f.return_type with
            | Ain.Type.Struct _ ->
                let dummy_ty = Ref e.ty in
                let v = self#create_dummy_var "【 . 】の左辺" dummy_ty in
                e.node <- DummyRef (v, clone_expr e)
            | Ain.Type.String ->
                let v = self#create_dummy_var "右辺値参照化用" (Ref e.ty) in
                e.node <- DummyRef (v, clone_expr e)
            | _ -> ())
        | Call (_, _, HLLCall (lib_no, fun_no)) ->
            let lib = Ain.get_library_by_index ctx.ain lib_no in
            let f = List.nth_exn lib.functions fun_no in
            (match f.return_type with
            | Ain.Type.Struct _ ->
                let dummy_ty = Ref e.ty in
                let v = self#create_dummy_var "【 . 】の左辺" dummy_ty in
                e.node <- DummyRef (v, clone_expr e)
            | _ -> ())
        | _ -> ()

    method! visit_expression expr =
      (* Track LHS-of-assign so we can suppress getter dummy wrapping. The
         visitor walks Assign as: visit lhs; visit rhs. We set the marker
         around the lhs walk only. *)
      (match expr.node with
      | Assign (_, lhs, rhs) ->
          let prev = assign_lhs_skip in
          assign_lhs_skip <- Some lhs;
          self#visit_expression lhs;
          assign_lhs_skip <- prev;
          self#visit_expression rhs
      | DummyRef _ ->
          (* DummyRef is only created by this pass - its inner has already been
             walked and any per-node dummy wrapping done. Re-walking the inner
             would duplicate dummies for the wrapped expression (e.g. a Call
             that returns Ref would get a second dummy on the second visit). *)
          ()
      | _ -> super#visit_expression expr);
      (* Check for member access on call results - needs dot-LHS DummyRef *)
      (match expr.node with
      | Call ({ node = Member (obj, _, _); _ }, _, _)
      | Member (obj, _, ClassMethod _) ->
          self#maybe_wrap_dot_lhs obj
      | _ -> ());
      (* Previously we also wrapped the OUTER call when the object was already
         a DummyRef'd struct-returning call. The original compiler doesn't
         emit this extra dummy - it only wraps the inner (leaf) struct call
         via maybe_wrap_dot_lhs and lets codegen handle the outer call's
         lifetime via the existing DummyRef. *)
      match expr.node with
      | Ident (name, t) -> (
          (* save local variable number at identifier nodes *)
          match t with
          | LocalVariable (_, loc) ->
              let idx = self#get_var_no name in
              let level = self#get_capture_level name in
              if level > 0 then
                expr.node <- Ident (name, CapturedVariable (idx, level))
              else
                expr.node <- Ident (name, LocalVariable (idx, loc))
          | _ -> ())
      | Call (_, call_args, calltype) -> (
          let needs_dummy =
            match expr.ty with
            | Ref _ -> true
            | _ ->
                (* Check actual ain return type - type analysis may have
                   dereffed Ref(Struct) to Struct via maybe_deref *)
                let is_ref_return =
                  match calltype with
                  | HLLCall (lib_no, fun_no) ->
                      let lib = Ain.get_library_by_index ctx.ain lib_no in
                      let f = List.nth_exn lib.functions fun_no in
                      (match f.return_type with Ain.Type.Ref _ -> true | _ -> false)
                  | FunctionCall fno | MethodCall (_, fno) ->
                      let f = Ain.get_function_by_index ctx.ain fno in
                      (match f.return_type with Ain.Type.Ref _ -> true | _ -> false)
                  | _ -> false
                in
                is_ref_return
          in
          if needs_dummy then (
            let varname =
              match calltype with
              | FunctionCall fno | MethodCall (_, fno) ->
                  (Ain.get_function_by_index ctx.ain fno).name
              | HLLCall (lib_no, fun_no) ->
                  let lib = Ain.get_library_by_index ctx.ain lib_no in
                  (List.nth_exn lib.functions fun_no).name
              | DelegateCall idx ->
                  (Ain.get_delegate_by_index ctx.ain idx).name
              | FuncTypeCall idx ->
                  (Ain.get_functype_by_index ctx.ain idx).name
              | _ ->
                  compiler_bug "variable_alloc_visitor: unexpected call type"
                    (Some (ASTExpression expr))
            in
            (* Use the actual return type (may have been dereffed by type checker).
               For HLL calls returning Ref HLLParam, use expr.ty wrapped in Ref
               since HLLParam resolves to the actual element type. *)
            let dummy_ty =
              match expr.ty with
              | Ref _ -> expr.ty  (* already a ref type *)
              | _ ->
                  (* Check if original return type was Ref *)
                  let is_ref_return =
                    match calltype with
                    | HLLCall (lib_no, fun_no) ->
                        let lib = Ain.get_library_by_index ctx.ain lib_no in
                        let f = List.nth_exn lib.functions fun_no in
                        (match f.return_type with Ain.Type.Ref _ -> true | _ -> false)
                    | FunctionCall fno | MethodCall (_, fno) ->
                        let f = Ain.get_function_by_index ctx.ain fno in
                        (match f.return_type with Ain.Type.Ref _ -> true | _ -> false)
                    | _ -> false
                  in
                  if is_ref_return then Ref expr.ty else expr.ty
            in
            (* Resolve HLLParam in dummy type using the self argument's
               array element type. HLL calls like Array.Sort() return
               array@HLLParam but the actual type comes from the self arg. *)
            let dummy_ty = match dummy_ty with
              | Jaf.Array Jaf.HLLParam | Jaf.Ref (Jaf.Array Jaf.HLLParam) ->
                  let self_ty = match call_args with
                    | Some { ty = Jaf.(Array t | Ref (Array t)); _ } :: _ -> Some t
                    | _ -> None
                  in
                  (match self_ty with
                   | Some elem_ty ->
                       let arr = Jaf.Array elem_ty in
                       (match dummy_ty with Jaf.Ref _ -> Jaf.Ref arr | _ -> arr)
                   | None -> dummy_ty)
              | _ -> dummy_ty
            in
            let v = self#create_dummy_var varname dummy_ty in
            expr.node <- DummyRef (v, clone_expr expr));
          (* Also check for RvalueRef in call arguments *)
          let check_args =
            match expr.node with
            | Call (_, args, _) | DummyRef (_, { node = Call (_, args, _); _ }) -> args
            | _ -> []
          in
          List.iter check_args ~f:(function
            | Some ({ node = RvalueRef inner; ty; _ } as arg) ->
                let v = self#create_dummy_var "右辺値参照化用" ty in
                arg.node <- DummyRef (v, inner)
            | _ -> ()))
      | Member (_, _, ClassMethod (name, fno))
        when String.is_suffix name ~suffix:"::get" && Ain.version ctx.ain > 8
             (* Skip if this expression is the LHS of an assignment - codegen
                will use the property setter, not the getter, so wrapping the
                getter in a DummyRef just allocates a dead local. *)
             && not (match assign_lhs_skip with
                     | Some lhs -> phys_equal lhs expr
                     | None -> false) ->
          (* Property getter - compiled as method call, may return ref type *)
          let f = Ain.get_function_by_index ctx.ain fno in
          let needs_dummy =
            match expr.ty with
            | Ref _ -> true
            | _ -> (match f.return_type with Ain.Type.Ref _ -> true | _ -> false)
          in
          if needs_dummy then (
            let dummy_ty =
              match expr.ty with
              | Ref _ -> expr.ty
              | _ -> Ref expr.ty
            in
            let v = self#create_dummy_var name dummy_ty in
            expr.node <- DummyRef (v, clone_expr expr))
      | New ts ->
          let varname =
            match ts.ty with
            | Struct (name, _) -> name
            | _ ->
                compiler_bug "Non-struct type in new expression"
                  (Some (ASTExpression expr))
          in
          let v = self#create_dummy_var varname (Ref ts.ty) in
          expr.node <- DummyRef (v, clone_expr expr)
      | RvalueRef inner ->
          (* For reference types (String, Struct, Array), the dummy needs
             Ref T so the VM's cleanup decrements the ref instead of freeing
             the value. This matches the original compiler's behavior. *)
          let dummy_ty = match expr.ty with
            | Jaf.(String | Struct _ | Array _ | Wrap _
                  | FuncType _ | Delegate _) -> Jaf.Ref expr.ty
            | _ -> expr.ty
          in
          let v = self#create_dummy_var "右辺値参照化用" dummy_ty in
          expr.node <- DummyRef (v, inner)
      | _ -> ()

    method! visit_statement stmt =
      (match stmt.node with
      | Compound _ -> self#start_scope
      | While (_, _) | DoWhile (_, _) -> self#start_scope
      | For (_, _, _, _) -> self#start_scope
      | Switch (_, _) -> self#start_scope
      | Case _ when Ain.version ctx.ain > 8 ->
          (* Switch-case expressions are extracted as constants by codegen
             (add_switch_case unwraps DummyRef anyway). No DummyRef wrapping
             needed - it would just allocate a dead local. *)
          ()
      | Label name -> self#add_label name stmt
      | Goto name -> self#add_goto name stmt
      | Continue -> self#add_continue stmt
      | Break -> self#add_break stmt
      | _ -> ());
      super#visit_statement stmt;
      match stmt.node with
      | Compound _ -> self#end_scope ScopeAnon
      | While (_, _) | DoWhile (_, _) -> self#end_scope ScopeLoop
      | For (_, _, _, _) -> self#end_scope ScopeLoop
      | Switch (_, _) -> self#end_scope ScopeSwitch
      | _ -> ()

    method! visit_variable v =
      (match v.kind with
      | (Parameter | LocalVar) when not v.is_const || v.is_private ->
          (* Two-phase foreach: if is_private and a variable with same name
             already exists, copy its index instead of allocating a new one. *)
          let existing =
            if v.is_private then
              let vars = Stack.top_exn func_vars in
              List.find vars ~f:(fun (ev : variable) ->
                  String.equal ev.name v.name && Option.is_some ev.index)
            else None
          in
          (match existing with
           | Some ev ->
               v.index <- ev.index
           | None ->
               self#add_var v)
      | _ -> ());
      super#visit_variable v

    method! visit_fundecl f =
      if Option.is_some f.body then (
        let parent_labels = labels in
        labels <- Hashtbl.create (module String);
        Stack.push func_vars [];
        let conv_var all_vars index (v : variable) =
          let ain_type = jaf_to_ain_type v.type_spec.ty in
          (* Fix foreach container HLLParam: resolve Ref(Array HLLParam) to
             the actual element type from the initval expression or from
             matching container vars in the same function. *)
          let ain_type = match ain_type with
            | Ain.Type.Ref (Ain.Type.Array Ain.Type.HLLParam) ->
                (* no debug *)
                (* Try initval first *)
                let resolved = match v.initval with
                  | Some { ty = Jaf.(Array t | Ref (Array t)); _ } ->
                      Some (jaf_to_ain_type t)
                  | _ -> None
                in
                (* Fall back to scanning other vars for matching container *)
                let resolved = match resolved with
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
                (match resolved with
                 | Some elem_ty -> Ain.Type.Ref (Ain.Type.Array elem_ty)
                 | None -> ain_type)
            | _ -> ain_type
          in
          (* Fix Wrap type for foreach variables over ref arrays:
             jaf type is Wrap(Struct N) but ain type should be Wrap(Ref(Struct N))
             because the array element type is Ref(Struct).
             Check all variables in the same function for a ref array container. *)
          let ain_type = match ain_type with
            | Ain.Type.Wrap (Ain.Type.Struct sno as inner) ->
                let has_matching_ref_container =
                  List.exists all_vars ~f:(fun (sv : variable) ->
                    match sv.type_spec.ty with
                    | Ref (Array (Ref (Struct (_, sno2)))) -> sno = sno2
                    | Array (Ref (Struct (_, sno2))) -> sno = sno2
                    | _ -> false)
                in
                if has_matching_ref_container then Ain.Type.Wrap (Ain.Type.Ref inner)
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

        (* write updated fundecl to ain file *)
        let vars = List.rev (Stack.pop_exn func_vars) in
        (match f.index with
        | Some idx ->
            Ain.get_function_by_index ctx.ain idx
            |> jaf_to_ain_function f |> add_vars vars
            |> Ain.write_function ctx.ain
        | None ->
            match Ain.get_function ctx.ain (mangled_name f) with
            | Some obj ->
                obj |> jaf_to_ain_function f |> add_vars vars
                |> Ain.write_function ctx.ain
            | None ->
                compiler_bug "Undefined function"
                  (Some (ASTDeclaration (Function f))));
        labels <- parent_labels)
  end

let allocate_variables ctx decls =
  (new variable_alloc_visitor ctx)#visit_toplevel decls
