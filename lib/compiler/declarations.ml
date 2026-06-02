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

let lambda_index = ref 0

(* Expand a v11 property declaration `T Name { get; set; }` into the
   struct_declaration items the later passes expect: a `<Name>` backing
   field plus synthetic `Name::get` / `Name::set` methods with trivial
   bodies that read/write the backing field. Read-only / write-only
   forms omit the missing accessor.

   Backing-field elision: when EVERY declared accessor is also user-
   bodied at top level (i.e. its [Class@Name::get|set] key is present
   in [ctx.user_bodied_accessors]), no [<Name>] backing field is
   emitted and the auto-stub bodies are stripped — only the prototype
   [Method] decls remain, leaving the user's top-level definitions to
   merge into the function-table slot. Without this elision we
   accumulate hundreds of spurious [<PropName>] slots on HLL-heavy
   classes, corrupting downstream member-index resolution. *)
let expand_property_decl ~(ctx : context) ~(class_name : string)
    (p : property_decl) : struct_declaration list =
  let loc = p.pd_loc in
  let ty = p.pd_typespec in
  let mangled_name = "<" ^ p.pd_name ^ ">" in
  let has_get = ref false in
  let has_set = ref false in
  List.iter p.pd_accessors ~f:(fun (name, _aloc) ->
      match name with
      | "get" ->
          if !has_get then compile_error "duplicate `get` accessor" (ASTType ty);
          has_get := true
      | "set" ->
          if !has_set then compile_error "duplicate `set` accessor" (ASTType ty);
          has_set := true
      | other ->
          compile_error
            (Printf.sprintf
               "unknown property accessor `%s` (expected `get` or `set`)" other)
            (ASTType ty));
  let backing_field : variable =
    {
      name = mangled_name;
      location = loc;
      array_dim = [];
      is_const = false;
      is_private = false;
      kind = ClassVar;
      type_spec = ty;
      initval = None;
      index = None;
    }
  in
  let backing_decl : struct_declaration =
    MemberDecl
      {
        decl_loc = loc;
        is_const_decls = false;
        typespec = ty;
        vars = [ backing_field ];
      }
  in
  let void_ts = { ty = Void; location = loc } in
  let mangled_member () =
    make_expr ~loc (Member (make_expr ~loc This, mangled_name, UnresolvedMember))
  in
  let get_body () =
    Some [ { node = Return (Some (mangled_member ())); delete_vars = []; loc } ]
  in
  let set_body () =
    let lhs = mangled_member () in
    let rhs = make_expr ~loc (Ident ("value", UnresolvedIdent)) in
    let assign = make_expr ~loc (Assign (EqAssign, lhs, rhs)) in
    Some [ { node = Expression assign; delete_vars = []; loc } ]
  in
  let value_param : variable =
    {
      name = "value";
      location = loc;
      array_dim = [];
      is_const = false;
      is_private = false;
      kind = Parameter;
      type_spec = ty;
      initval = None;
      index = None;
    }
  in
  let get_decl =
    if !has_get then
      [
        Method
          {
            name = p.pd_name ^ "::get";
            loc;
            return = ty;
            params = [];
            body = get_body ();
            is_label = false;
            is_lambda = false;
            is_private = false;
            index = None;
            class_name = None;
            class_index = None;
          };
      ]
    else []
  in
  let set_decl =
    if !has_set then
      [
        Method
          {
            name = p.pd_name ^ "::set";
            loc;
            return = void_ts;
            params = [ value_param ];
            body = set_body ();
            is_label = false;
            is_lambda = false;
            is_private = false;
            index = None;
            class_name = None;
            class_index = None;
          };
      ]
    else []
  in
  let declared_is_user_bodied kind =
    Hashtbl.mem ctx.user_bodied_accessors
      (class_name ^ "@" ^ p.pd_name ^ "::" ^ kind)
  in
  let any_declared = !has_get || !has_set in
  let all_declared_user_bodied =
    any_declared
    && (not !has_get || declared_is_user_bodied "get")
    && (not !has_set || declared_is_user_bodied "set")
  in
  let strip_body = function
    | [ Method m ] -> [ Method { m with body = None } ]
    | other -> other
  in
  if all_declared_user_bodied then
    (* Emit prototype-only Method decls (no auto-stub body) and drop
       the backing field — the user's top-level body Function decls
       merge into these prototypes via [merge_with_prev]'s normal
       prototype/body match path. *)
    strip_body get_decl @ strip_body set_decl
  else [ backing_decl ] @ get_decl @ set_decl

(* Expand a v11 event declaration `event T Name;` into a delegate-typed
   [<Name>] backing field plus prototype-only [Name::add] / [Name::remove]
   methods. The accessors carry no body — the original v11 compiler
   emits matching function-table slots that are never invoked at runtime
   for auto-events ([+= h] / [-= h] dispatch lowers to direct delegate
   ops on the backing field). The "no body" exception for these stubs
   is enforced in [type_define_visitor]'s [StructDef] check below. *)
let expand_event_decl (e : event_decl) : struct_declaration list =
  let loc = e.ed_loc in
  let ty = e.ed_typespec in
  let mangled_name = "<" ^ e.ed_name ^ ">" in
  let backing_field : variable =
    {
      name = mangled_name;
      location = loc;
      array_dim = [];
      is_const = false;
      is_private = false;
      kind = ClassVar;
      type_spec = ty;
      initval = None;
      index = None;
    }
  in
  let backing_decl : struct_declaration =
    MemberDecl
      {
        decl_loc = loc;
        is_const_decls = false;
        typespec = ty;
        vars = [ backing_field ];
      }
  in
  let void_ts = { ty = Void; location = loc } in
  let value_param : variable =
    {
      name = "value";
      location = loc;
      array_dim = [];
      is_const = false;
      is_private = false;
      kind = Parameter;
      type_spec = ty;
      initval = None;
      index = None;
    }
  in
  let accessor kind =
    Method
      {
        name = e.ed_name ^ "::" ^ kind;
        loc;
        return = void_ts;
        params = [ value_param ];
        body = None;
        is_label = false;
        is_lambda = false;
        is_private = false;
        index = None;
        class_name = None;
        class_index = None;
      }
  in
  [ backing_decl; accessor "add"; accessor "remove" ]

(* Expand v11 [PropertyDecl] / [EventDecl] entries in a struct's
   declaration list, collecting [property_info] entries for the
   containing struct's [properties] table. The expanded list keeps
   the original ordering; [property_info] entries are returned in
   source order so type analysis can preserve roundtrip stability.

   Also drops [<EventName>] delegate backing fields when both
   [Name::add] and [Name::remove] are user-bodied at top level. The
   original v11 compiler doesn't allocate storage in that case;
   [obj.E += h] / [obj.E -= h] dispatches through the user's accessors
   via [ClassEvent] member resolution in type analysis. *)
let expand_struct_decls ~(ctx : context) ~(class_name : string)
    (decls : struct_declaration list) :
    struct_declaration list * (string * property_info) list =
  let infos = ref [] in
  let event_is_user_bodied name =
    Hashtbl.mem ctx.user_bodied_accessors
      (class_name ^ "@" ^ name ^ "::add")
    && Hashtbl.mem ctx.user_bodied_accessors
         (class_name ^ "@" ^ name ^ "::remove")
  in
  let drop_event_backing (v : variable) =
    let n = String.length v.name in
    n >= 3
    && Char.equal v.name.[0] '<'
    && Char.equal v.name.[n - 1] '>'
    && event_is_user_bodied (String.sub v.name ~pos:1 ~len:(n - 2))
  in
  let expanded =
    List.concat_map decls ~f:(function
      | PropertyDecl p ->
          let decls = expand_property_decl ~ctx ~class_name p in
          let find_method suffix =
            List.find_map decls ~f:(function
              | Method f when String.is_suffix f.name ~suffix -> Some f
              | _ -> None)
          in
          let prop_getter = find_method "::get" in
          let prop_setter = find_method "::set" in
          let info =
            { prop_typespec = p.pd_typespec; prop_getter; prop_setter }
          in
          infos := (p.pd_name, info) :: !infos;
          decls
      | EventDecl e ->
          let decls = expand_event_decl e in
          if event_is_user_bodied e.ed_name then
            List.filter decls ~f:(function MemberDecl _ -> false | _ -> true)
          else decls
      | MemberDecl ds when not ds.is_const_decls ->
          let kept =
            List.filter ds.vars ~f:(fun v -> not (drop_event_backing v))
          in
          if List.is_empty kept then []
          else [ MemberDecl { ds with vars = kept } ]
      | other -> [ other ])
  in
  (expanded, List.rev !infos)

(* Detect the auto-synthesized property-accessor body shape that
   [expand_property_decl] emits: a single-statement [return this.<X>]
   getter or [this.<X> = value] setter. Used by [visit_fundecl]'s
   merge logic to allow a user-supplied top-level body to override the
   auto-stub without triggering a "Duplicate function definition"
   error. *)
let is_property_stub (f : fundecl) =
  let is_mangled_member_access (e : expression) =
    match e.node with
    | Member ({ node = This; _ }, name, _) ->
        let n = String.length name in
        n >= 3
        && Char.equal name.[0] '<'
        && Char.equal name.[n - 1] '>'
    | _ -> false
  in
  match f.body with
  | Some [ { node = Return (Some e); _ } ] -> is_mangled_member_access e
  | Some
      [
        {
          node =
            Expression
              { node = Assign (EqAssign, lhs, { node = Ident ("value", _); _ }); _ };
          _;
        };
      ] ->
      is_mangled_member_access lhs
  | _ -> false

(*
 * AST pass over top-level declarations register names in the .ain file.
 *)
class type_declare_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val mutable gg_index = -1

    method! visit_fundecl decl =
      if decl.is_lambda then (
        lambda_index := !lambda_index + 1;
        decl.name <- Printf.sprintf "<lambda : %d>" !lambda_index;
        decl.class_name <-
          (Option.value_exn self#env#current_function).class_name);
      let name = mangled_name decl in
      let decl_param_types = List.map decl.params ~f:(fun p -> p.type_spec.ty) in
      (* Two decls denote the same overload iff their parameter types
         match exactly. Return type is not part of the signature
         (matches the C-family / v11 convention). *)
      let same_overload (other : fundecl) =
        params_compatible decl_param_types
          (List.map other.params ~f:(fun p -> p.type_spec.ty))
      in
      (* If this body overrides a previously-registered property auto-
         stub, reuse the stub's ain slot rather than allocating a new
         one — otherwise every [T Class::Name { get {...} set {...} }]
         implementation would append a duplicate entry to the function
         table. *)
      let stub_override =
        if Option.is_some decl.body then
          match Hashtbl.find ctx.functions name with
          | Some prev when same_overload prev && is_property_stub prev ->
              prev.index
          | _ -> (
              match Hashtbl.find ctx.overloads name with
              | Some xs ->
                  List.find_map xs ~f:(fun prev ->
                      if same_overload prev && is_property_stub prev then
                        prev.index
                      else None)
              | None -> None)
        else None
      in
      (match stub_override with
      | Some idx -> decl.index <- Some idx
      | None ->
          if Option.is_some decl.body then (
            (* v11 ghost lambda: pre-allocate an undefined function
               slot for each lambda BEFORE the real one. The
               subsequent [add_function ~nr_args] reuses that slot via
               stub-matching (matching name + arity + [address = -1])
               rather than appending another entry. The ghost gives
               the slot its final [is_lambda] / [nr_args] /
               [return_type] metadata before any other pass observes
               the function table — which matters for v11 delegate-
               callback pair lookups that key off arity at
               registration time. *)
            (if decl.is_lambda && Ain.version ctx.ain > 8 then
               let ghost =
                 let open Ain.Function in
                 {
                   (create name) with
                   nr_args = List.length decl.params;
                   return_type = jaf_to_ain_type decl.return.ty;
                   is_lambda = true;
                 }
               in
               ignore (Ain.write_new_function ctx.ain ghost));
            (* Pre-register the [Class@2] array-initializer slot
               immediately before allocating the constructor's slot.
               The original v11 compiler interleaves them so
               [Class@2] sits one index below [Class@0] in the
               function table — the array-initializer pass in
               [arrayInit.ml] later emits the [@2] body and reuses
               this pre-allocated index via [Ain.get_function].
               Without the interleave, [@2] lands far away in the
               table after every constructor is allocated, shifting
               downstream indices and producing [REF Page=N Index=M]
               faults at v11 VM boot. *)
            (if is_constructor decl then
               let init_name = Option.value_exn decl.class_name ^ "@2" in
               match Ain.get_function ctx.ain init_name with
               | Some _ -> ()
               | None -> ignore (Ain.add_function ctx.ain init_name));
            decl.index <-
              Some
                (Ain.add_function ~nr_args:(List.length decl.params)
                   ctx.ain name)
                  .index));
      (* Merge a body or prototype into an existing same-overload entry.
         [prev_decl] has identical parameter types to [decl]; only the
         return type or body presence may differ. *)
      let merge_with_prev (prev_decl : fundecl) =
        if
          not (jaf_type_equal decl.return.ty prev_decl.return.ty)
        then
          compile_error "Function signature mismatch"
            (ASTDeclaration (Function decl))
        else if Option.is_some prev_decl.body && Option.is_some decl.body then
          (* Allow a user-supplied top-level body to override the
             auto-stub emitted by [expand_property_decl]; the stub is
             a forward declaration, not a real second definition. *)
          if is_property_stub prev_decl then (
            (match prev_decl.index with
            | Some _ as idx -> decl.index <- idx
            | None -> ());
            decl)
          else
            compile_error "Duplicate function definition"
              (ASTDeclaration (Function decl))
        else if Option.is_none decl.body then (
          (* Duplicate prototype; ignore. [-1] flags the decl as
             unowned so later passes don't try to write a body. *)
          decl.index <- Some (-1);
          prev_decl)
        else (
          (* [decl] supplies the body for an existing prototype. *)
          prev_decl.index <- decl.index;
          decl.params <- prev_decl.params;
          decl.is_private <- prev_decl.is_private;
          decl)
      in
      let overloading_allowed = Ain.version_gte ctx.ain (11, 0) in
      (match Hashtbl.find ctx.functions name with
      | None -> Hashtbl.set ctx.functions ~key:name ~data:decl
      | Some primary when same_overload primary ->
          Hashtbl.set ctx.functions ~key:name ~data:(merge_with_prev primary)
      | Some _ when not overloading_allowed ->
          (* Pre-v11: same-name decls with different parameter types
             are a signature error, not an overload. *)
          compile_error "Function signature mismatch"
            (ASTDeclaration (Function decl))
      | Some _ ->
          (* [decl] shares a mangled name with the primary but has
             different parameter types — a v11 overload. Match against
             entries previously stashed in [ctx.overloads]; append a new
             one if no same-overload prototype exists. *)
          let overs =
            Hashtbl.find ctx.overloads name |> Option.value ~default:[]
          in
          (match List.findi overs ~f:(fun _ o -> same_overload o) with
          | Some (i, prev) ->
              let merged = merge_with_prev prev in
              let updated =
                List.mapi overs ~f:(fun j x -> if j = i then merged else x)
              in
              Hashtbl.set ctx.overloads ~key:name ~data:updated
          | None ->
              Hashtbl.set ctx.overloads ~key:name ~data:(decl :: overs)));
      super#visit_fundecl decl

    method! visit_declaration decl =
      match decl with
      | Global ds ->
          List.iter ds.vars ~f:(fun g ->
              match Hashtbl.add ctx.globals ~key:g.name ~data:g with
              | `Duplicate ->
                  compile_error "duplicate global definition"
                    (ASTDeclaration decl)
              | `Ok ->
                  if not g.is_const then
                    g.index <- Some (Ain.add_global ctx.ain g.name gg_index))
      | GlobalGroup gg ->
          gg_index <- Ain.add_global_group ctx.ain gg.name;
          List.iter gg.vardecls ~f:(fun ds ->
              self#visit_declaration (Global ds));
          gg_index <- -1
      | Function f ->
          (match Util.parse_qualified_name f.name with
          | None, _ -> ()
          | Some qual, name ->
              if Hashtbl.mem ctx.structs qual then (
                f.name <- name;
                f.class_name <- Some qual;
                if not (Hashtbl.mem ctx.functions (mangled_name f)) then
                  compile_error
                    (f.name ^ " is not declared in class " ^ qual)
                    (ASTDeclaration decl))
              else
                (* v11 doubly-qualified [OuterClass::PropName::accessor]
                   form (top-level user-bodied property/event impls).
                   Re-split [qual] to recover the outer class; rewrite
                   [f.name] to [PropName::accessor] and bind to the
                   outer class. *)
                match Util.parse_qualified_name qual with
                | Some outer_qual, member_name
                  when Ain.version ctx.ain > 8
                       && Hashtbl.mem ctx.structs outer_qual ->
                    f.name <- member_name ^ "::" ^ name;
                    f.class_name <- Some outer_qual;
                    if not (Hashtbl.mem ctx.functions (mangled_name f)) then
                      compile_error
                        (f.name ^ " is not declared in class " ^ outer_qual)
                        (ASTDeclaration decl)
                | _ -> ());
          self#visit_fundecl f
      | FuncTypeDef f -> (
          match Hashtbl.add ctx.functypes ~key:f.name ~data:f with
          | `Duplicate ->
              compile_error "duplicate functype definition"
                (ASTDeclaration decl)
          | `Ok -> f.index <- Some (Ain.add_functype ctx.ain f.name).index)
      | DelegateDef f -> (
          match Hashtbl.add ctx.delegates ~key:f.name ~data:f with
          | `Duplicate ->
              compile_error "duplicate delegate definition"
                (ASTDeclaration decl)
          | `Ok -> f.index <- Some (Ain.add_delegate ctx.ain f.name).index)
      | StructDef s -> (
          let unqualified_struct_name =
            snd (Util.parse_qualified_name s.name)
          in
          let ain_s = Ain.add_struct ctx.ain s.name in
          let jaf_s = new_jaf_struct s.name s.loc ain_s.index in
          let next_index = ref 0 in
          let in_private = ref s.is_class in
          let visit_decl = function
            | AccessSpecifier Public -> in_private := false
            | AccessSpecifier Private -> in_private := true
            | Constructor f ->
                if not (String.equal f.name unqualified_struct_name) then
                  compile_error "constructor name doesn't match struct name"
                    (ASTDeclaration (Function f));
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#visit_fundecl f
            | Destructor f ->
                if not (String.equal f.name ("~" ^ unqualified_struct_name))
                then
                  compile_error "destructor name doesn't match struct name"
                    (ASTDeclaration (Function f));
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#visit_fundecl f
            | Method f ->
                f.class_name <- Some s.name;
                f.class_index <- Some ain_s.index;
                f.is_private <- !in_private;
                self#visit_fundecl f
            | MemberDecl ds ->
                List.iter ds.vars ~f:(fun v ->
                    v.is_private <- !in_private;
                    if not v.is_const then (
                      v.index <- Some !next_index;
                      next_index :=
                        !next_index
                        + if is_ref_scalar v.type_spec.ty then 2 else 1);
                    match Hashtbl.add jaf_s.members ~key:v.name ~data:v with
                    | `Duplicate ->
                        compile_error "duplicate member variable declaration"
                          (ASTVariable v)
                    | `Ok -> ())
            | PropertyDecl _ | EventDecl _ ->
                (* [expand_struct_decls] has rewritten these into their
                   [MemberDecl] + [Method] components before we iterate. *)
                ()
          in
          (* Lower v11 properties to their backing field + synthetic
             accessor methods, and record property metadata on [jaf_s]
             so type analysis can rewrite [obj.Name] / [obj.Name = v]
             into accessor calls. *)
          let expanded, prop_infos =
            expand_struct_decls ~ctx ~class_name:s.name s.decls
          in
          s.decls <- expanded;
          List.iter prop_infos ~f:(fun (name, info) ->
              Hashtbl.set jaf_s.properties ~key:name ~data:info);
          List.iter s.decls ~f:visit_decl;
          match Hashtbl.add ctx.structs ~key:s.name ~data:jaf_s with
          | `Duplicate ->
              compile_error "duplicate struct definition" (ASTDeclaration decl)
          | `Ok -> ())
      | Enum _ ->
          compile_error "enum types not yet supported" (ASTDeclaration decl)
  end

let register_type_declarations ctx decls =
  (new type_declare_visitor ctx)#visit_toplevel decls

(* Pre-scan over a parsed jaf file to record every accessor whose body
   is supplied by a top-level [T Class::Name { ... }] or
   [event T Class::Name { ... }] block. The parser lowers each block
   to two/up-to-two top-level [Function] decls named
   [Class::PropName::accessor] (with [class_name] still unset — that
   field is populated only during pass-1 visit). [parse_qualified_name]
   twice on the raw [f.name] recovers the [Class@Name::accessor] key
   that [expand_property_decl] / [expand_struct_decls] check against. *)
let scan_user_bodied_accessors ctx (decls : declaration list) =
  let record name =
    Hashtbl.set ctx.user_bodied_accessors ~key:name ~data:()
  in
  List.iter decls ~f:(function
    | Function f when Option.is_some f.body -> (
        match Util.parse_qualified_name f.name with
        | Some qual, accessor
          when String.equal accessor "get"
               || String.equal accessor "set"
               || String.equal accessor "add"
               || String.equal accessor "remove" -> (
            match Util.parse_qualified_name qual with
            | Some class_name, prop_name ->
                record (class_name ^ "@" ^ prop_name ^ "::" ^ accessor)
            | None, _ -> ())
        | _ -> ())
    | _ -> ())

(*
 * AST pass to resolve HLL-specific type aliases.
 *)
class hll_type_resolve_visitor ctx =
  object
    inherit ivisitor ctx

    method! visit_type_specifier ts =
      match ts.ty with
      | Unresolved "intp" -> ts.ty <- Ref Int
      | Unresolved "floatp" -> ts.ty <- Ref Float
      | Unresolved "stringp" -> ts.ty <- Ref String
      | Unresolved "boolp" -> ts.ty <- Ref Bool
      | _ -> ()
  end

let resolve_hll_types ctx decls =
  (new hll_type_resolve_visitor ctx)#visit_toplevel decls

(*
 * AST pass to resolve user-defined types (struct/enum/function types).
 *)
class type_resolve_visitor ctx =
  object (self)
    inherit ivisitor ctx as super

    method resolve_type name node =
      match Hashtbl.find ctx.structs name with
      | Some s -> Struct (name, s.index)
      | None -> (
          match Hashtbl.find ctx.functypes name with
          | Some ft -> FuncType (Some (name, Option.value_exn ft.index))
          | None -> (
              match Hashtbl.find ctx.delegates name with
              | Some dg -> Delegate (Some (name, Option.value_exn dg.index))
              | None -> (
                  match name with
                  | "IMainSystem" -> IMainSystem
                  | _ -> compile_error ("Undefined type: " ^ name) node)))

    method! visit_type_specifier ts =
      let rec resolve t =
        match t with
        | Unresolved t -> self#resolve_type t (ASTType ts)
        | Ref t -> Ref (resolve t)
        | Array t -> Array (resolve t)
        | Wrap t -> Wrap (resolve t)
        | _ -> t
      in
      ts.ty <- resolve ts.ty

    method! visit_fundecl decl =
      (if decl.is_lambda then
         match self#env#current_class with
         | Some (Struct (name, index)) ->
             decl.class_name <- Some name;
             decl.class_index <- Some index
         | _ -> ());
      super#visit_fundecl decl

    method! visit_declaration decl =
      (match decl with
      | Function f -> (
          match f.class_name with
          | Some name ->
              f.class_index <- Some (Hashtbl.find_exn ctx.structs name).index
          | _ -> ())
      | FuncTypeDef _ | DelegateDef _ | Global _ | GlobalGroup _ | StructDef _
        ->
          ()
      | Enum _ ->
          compile_error "enum types not yet supported" (ASTDeclaration decl));
      super#visit_declaration decl
  end

let resolve_types ctx decls =
  (new type_resolve_visitor ctx)#visit_toplevel decls

(*
 * AST pass over top-level declarations to define function/struct types.
 *)
class type_define_visitor ctx =
  object (self)
    inherit ivisitor ctx as super

    method! visit_fundecl f =
      super#visit_fundecl f;
      if f.is_lambda then
        let obj =
          Ain.get_function_by_index ctx.ain (Option.value_exn f.index)
        in
        obj |> jaf_to_ain_function f |> Ain.write_function ctx.ain

    method! visit_declaration decl =
      super#visit_declaration decl;
      match decl with
      | Global ds ->
          List.iter ds.vars ~f:(fun g ->
              if not g.is_const then
                Ain.set_global_type ctx.ain g.name
                  (jaf_to_ain_type g.type_spec.ty))
      | GlobalGroup gg ->
          List.iter gg.vardecls ~f:(fun ds ->
              self#visit_declaration (Global ds))
      | Function f ->
          let obj =
            Ain.get_function_by_index ctx.ain (Option.value_exn f.index)
          in
          obj |> jaf_to_ain_function f |> Ain.write_function ctx.ain
      | FuncTypeDef f -> jaf_to_ain_functype f |> Ain.write_functype ctx.ain
      | DelegateDef f -> jaf_to_ain_functype f |> Ain.write_delegate ctx.ain
      | StructDef s -> (
          (* check for undefined methods. Auto-event accessors
             ([Name::add] / [Name::remove] synthesized by
             [expand_event_decl]) keep [body = None] and never get a
             top-level implementation — at runtime, [+= h] / [-= h]
             dispatches via delegate-add/remove on the [<Name>] backing
             field rather than calling these methods. Skip the check
             for those accessors. *)
          let is_event_accessor_stub (f : fundecl) =
            Option.is_none f.body
            && (String.is_suffix f.name ~suffix:"::add"
               || String.is_suffix f.name ~suffix:"::remove")
          in
          (* A body-less [Name::get] / [Name::set] in [s.decls] is the
             prototype emitted by [expand_property_decl] when the user
             provides a top-level body that elides the auto-stub. The
             real fundecl with body and index lives in [ctx.functions]
             after [merge_with_prev]; the prototype in [s.decls] keeps
             [index = None]. Skip the definition-presence check for
             those — their top-level body satisfies the contract. *)
          let is_user_bodied_property_stub (f : fundecl) =
            Option.is_none f.body
            && (String.is_suffix f.name ~suffix:"::get"
               || String.is_suffix f.name ~suffix:"::set")
            && Hashtbl.mem ctx.user_bodied_accessors
                 (s.name ^ "@" ^ f.name)
          in
          List.iter s.decls ~f:(function
            | Method f | Constructor f | Destructor f ->
                if Option.is_none f.index
                   && (not (is_event_accessor_stub f))
                   && not (is_user_bodied_property_stub f)
                then
                  compile_error
                    (Printf.sprintf "No definition of %s::%s found" s.name
                       f.name)
                    (ASTDeclaration (Function f))
            | _ -> ());
          match Ain.get_struct ctx.ain s.name with
          | Some obj -> obj |> jaf_to_ain_struct s |> Ain.write_struct ctx.ain
          | None -> compiler_bug "undefined struct" (Some (ASTDeclaration decl))
          )
      | Enum _ ->
          compile_error "Enum types not yet supported" (ASTDeclaration decl)
  end

let define_types ctx decls = (new type_define_visitor ctx)#visit_toplevel decls

let check_builtin_library builtin_type =
  (* All functions in HLL for a built-in type T must have a first argument of
     type ref T. *)
  List.iter ~f:(fun func ->
      match func.params with
      | [] ->
          compile_error "builtin HLL function must have at least one parameter"
            (ASTDeclaration (Function func))
      | param :: _ ->
          if not (Poly.equal param.type_spec.ty (Ref builtin_type)) then
            compile_error
              (Printf.sprintf "first parameter must be of type ref %s"
                 (jaf_type_to_string builtin_type))
              (ASTVariable param))

let define_library ctx decls hll_name import_name =
  let functions =
    List.map decls ~f:(function
      | Function f -> f
      | decl ->
          compiler_bug "unexpected declaration in .hll file"
            (Some (ASTDeclaration decl)))
  in
  (if ctx.version >= 800 then
     match import_name with
     | "Int" -> check_builtin_library Int functions
     | "Float" -> check_builtin_library Float functions
     | "String" -> check_builtin_library String functions
     | "Array" -> check_builtin_library (Array HLLParam) functions
     | "Delegate" -> check_builtin_library (Delegate None) functions
     | _ -> ());
  Ain.write_library ctx.ain
    {
      (Ain.add_library ctx.ain hll_name) with
      functions = Array.of_list_map functions ~f:jaf_to_ain_hll_function;
    };
  (* v11 HLL libraries may declare multiple functions with the same
     name but different parameter signatures. The first-seen entry
     is the [functions] primary; same-name successors land in
     [overloads]. Pre-v11 .hll files don't allow this, but the data
     shape is uniform across versions — [overloads] just stays empty. *)
  let functions_tbl = Hashtbl.create (module String) in
  let overloads_tbl = Hashtbl.create (module String) in
  List.iter functions ~f:(fun (d : fundecl) ->
      match Hashtbl.find functions_tbl d.name with
      | None -> Hashtbl.set functions_tbl ~key:d.name ~data:d
      | Some _ ->
          Hashtbl.update overloads_tbl d.name ~f:(function
            | None -> [ d ]
            | Some xs -> d :: xs));
  Hashtbl.add_exn ctx.libraries ~key:import_name
    ~data:
      { hll_name; functions = functions_tbl; overloads = overloads_tbl }
