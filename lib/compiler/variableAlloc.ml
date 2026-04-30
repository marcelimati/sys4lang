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
      | Some v -> Option.value_exn v.index
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
         entry, mirroring the existing scalar-ref behaviour. *)
      let needs_void_slot =
        is_ref_scalar v.type_spec.ty
        || Ain.version ctx.ain > 8
           && match v.type_spec.ty with Wrap _ -> true | _ -> false
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
            let f = List.nth_exn lib.functions fun_no in
            match f.return_type with
            | Ain.Type.Struct _ ->
                let dummy_ty = Ref e.ty in
                let v = self#create_dummy_var "【 . 】の左辺" dummy_ty in
                e.node <- DummyRef (v, clone_expr e)
            | _ -> ())
        | _ -> ()

    method! visit_expression expr =
      (* Don't recurse into an already-wrapped [DummyRef]: its inner has
         been walked once during the original wrap, and re-walking would
         fire the Call case again on the clone, producing a nested
         [DummyRef (_, DummyRef (_, Call ...))] with two dummy slots
         for the same call. *)
      (match expr.node with
      | DummyRef _ -> ()
      | _ -> super#visit_expression expr);
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
          let ain_returns_ref =
            if not v11 then false
            else
              match calltype with
              | FunctionCall fno | MethodCall (_, fno) -> (
                  match
                    (Ain.get_function_by_index ctx.ain fno).return_type
                  with
                  | Ain.Type.Ref _ -> true
                  | _ -> false)
              | HLLCall (lib_no, fun_no) -> (
                  let lib = Ain.get_library_by_index ctx.ain lib_no in
                  match
                    (List.nth_exn lib.functions fun_no).return_type
                  with
                  | Ain.Type.Ref _ -> true
                  | _ -> false)
              | _ -> false
          in
          let expr_ty_ref =
            match expr.ty with Ref _ -> true | _ -> false
          in
          if expr_ty_ref || ain_returns_ref then (
            let varname =
              match calltype with
              | FunctionCall fno | MethodCall (_, fno) ->
                  (Ain.get_function_by_index ctx.ain fno).name
              | HLLCall (lib_no, fun_no) ->
                  let lib = Ain.get_library_by_index ctx.ain lib_no in
                  (List.nth_exn lib.functions fun_no).name
              | DelegateCall _ -> "<delegate>"
              | FuncTypeCall _ -> "<functype>"
              | _ ->
                  compiler_bug "variable_alloc_visitor: unexpected call type"
                    (Some (ASTExpression expr))
            in
            let dummy_ty = if expr_ty_ref then expr.ty else Ref expr.ty in
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
                    | String | Struct _ | Array _ | Wrap _ | FuncType _
                    | Delegate _ ->
                        Ref ty
                    | _ -> ty
                  in
                  let v = self#create_dummy_var "右辺値参照化用" dummy_ty in
                  arg.node <- DummyRef (v, inner)
              | _ -> ())
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
      | RvalueRef inner when Ain.version_gte ctx.ain (11, 0) ->
          (* v11: wrap any standalone [RvalueRef] (e.g. a non-
             referenceable method receiver) in a [DummyRef] backed by a
             fresh local. The dummy stores the rvalue so the callee can
             take its address. Reference-shaped types use a [Ref T]
             dummy so the VM's cleanup decrements rather than frees.
             Pre-v11 codegen handles [RvalueRef] directly. *)
          let dummy_ty =
            match expr.ty with
            | String | Struct _ | Array _ | Wrap _ | FuncType _ | Delegate _
              ->
                Ref expr.ty
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
      | (Parameter | LocalVar) when (not v.is_const) || v.is_private ->
          (* v11 private locals can re-declare a same-named slot; reuse
             the existing slot rather than allocating a new one. *)
          let existing =
            if v.is_private then
              List.find self#env#var_list ~f:(fun (ev : variable) ->
                  String.equal ev.name v.name && Option.is_some ev.index)
            else None
          in
          (match existing with
          | Some ev -> v.index <- ev.index
          | None -> self#add_var v)
      | _ -> ());
      super#visit_variable v

    method! visit_fundecl f =
      if Option.is_some f.body then (
        let parent_labels = labels in
        labels <- Hashtbl.create (module String);
        Stack.push func_vars [];
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
          let ain_type = jaf_to_ain_type v.type_spec.ty in
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
        let obj = Ain.get_function_by_index ctx.ain (Option.value_exn f.index) in
        obj |> jaf_to_ain_function f |> add_vars vars
        |> Ain.write_function ctx.ain;
        labels <- parent_labels)
  end

let allocate_variables ctx decls =
  (new variable_alloc_visitor ctx)#visit_toplevel decls
