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
  let property_has_set =
    List.exists p.pd_accessors ~f:(fun (name, _) -> String.equal name "set")
  in
  let property_has_initval = Option.is_some p.pd_initval in
  let can_value_store_ref_struct = function
    | Struct (name, _) | Unresolved name ->
        (* Use value storage for the [<Name>] backing field when the
           inner struct can be in-place constructed at the parent's
           [@0] initializer:
           - No constructor at all on the inner struct (lifetime is
             parent-managed).
           - Setter present AND default ctor: the setter clears and
             rebuilds the inline value as needed.
           - Read-only with no source initializer AND default ctor:
             the [@0] pass default-constructs the inline value once.
             A source [pd_initval] flips this to ref storage so the
             [@0] pass can evaluate the [new T(...)] expression and
             assign-by-ref to the [ref T] slot. *)
        (not (Hashtbl.mem ctx.structs_with_constructor name))
        || (property_has_set
           && Hashtbl.mem ctx.structs_with_default_constructor name)
        || (not property_has_initval
           && Hashtbl.mem ctx.structs_with_default_constructor name)
    | _ -> false
  in
  let backing_ty =
    match ty.ty with
    | Ref ((Array _ | Delegate _ | String | HLLParam) as inner) ->
        { ty with ty = inner }
    | Ref ((Struct _ | Unresolved _) as inner)
      when Ain.version_gte ctx.ain (12, 0)
           && not
                (Hashtbl.mem ctx.nullable_ref_properties
                   (class_name ^ "@" ^ p.pd_name))
           && can_value_store_ref_struct inner ->
        { ty with ty = inner }
    | _ -> ty
  in
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
      type_spec = backing_ty;
      initval = p.pd_initval;
      index = None;
    }
  in
  let backing_decl : struct_declaration =
    MemberDecl
      {
        decl_loc = loc;
        is_const_decls = false;
        typespec = backing_ty;
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
    (* Emit prototype-only Method decls (no auto-stub body). The
       backing field is kept ONLY if some user-bodied accessor body
       actually references [this.<PropName>] (recorded into
       [ctx.properties_with_backing_ref] by [scan_user_bodied_accessors]).
       Original v12 elides the field on computed properties like
       [int Count { get { return this.m_data.Numof(); } }] — emitting
       it anyway shifts struct member offsets and caused load-time
       VM crashes. *)
    let body_uses_backing =
      Hashtbl.mem ctx.properties_with_backing_ref
        (class_name ^ "@" ^ p.pd_name)
    in
    let stubs = strip_body get_decl @ strip_body set_decl in
    if body_uses_backing then [ backing_decl ] @ stubs else stubs
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
    ~(implements_interfaces : bool)
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
  (* v11+: each member typed as an interface ref (e.g. [IUserComponent
     UserComponent;]) is followed in original Rance10's STRT by a
     [<void>] padding member. Without the pad, struct member-offset
     references for everything after the IFace field land at wrong
     indices, and the VM faults reading struct-table entries.

     Both jaf [Struct (name, _)] and the pre-resolution [Unresolved
     name] shapes need to match against [ctx.interface_names]. *)
  let needs_void_padding (v : variable) =
    if not (Ain.version_gte ctx.ain (11, 0)) then false
    else
      let rec is_iface = function
        | Unresolved name -> Hashtbl.mem ctx.interface_names name
        | Struct (name, _) -> Hashtbl.mem ctx.interface_names name
        | Ref t -> is_iface t
        | _ -> false
      in
      is_iface v.type_spec.ty
  in
  let void_padding_member loc : struct_declaration =
    let v : variable =
      {
        name = "<void>";
        location = loc;
        array_dim = [];
        is_const = false;
        is_private = false;
        kind = ClassVar;
        type_spec = { ty = Void; location = loc };
        initval = None;
        index = None;
      }
    in
    MemberDecl
      {
        decl_loc = loc;
        is_const_decls = false;
        typespec = { ty = Void; location = loc };
        vars = [ v ];
      }
  in
  let inject_iface_padding_into_decl (ds : vardecls) : struct_declaration list =
    (* Walk the vardecl's vars; for each IFace-typed var, emit it as a
       separate MemberDecl followed by a void-padding MemberDecl. Other
       vars pass through unchanged but the resulting list is one
       MemberDecl per var so the padding lands in the right slot. *)
    List.concat_map ds.vars ~f:(fun v ->
        let solo : struct_declaration =
          MemberDecl
            {
              decl_loc = ds.decl_loc;
              is_const_decls = ds.is_const_decls;
              typespec = ds.typespec;
              vars = [ v ];
            }
        in
        if needs_void_padding v then [ solo; void_padding_member ds.decl_loc ]
        else [ solo ])
  in
  (* v12 source (decompiled) sometimes declares the same event TWICE
     in a class body (e.g. CMotionAlphaData: lines 6900-6906 declare 7
     events, lines 6908-6911 duplicate the first 4 in reverse order).
     Original compiler dedupes; we filter here so expansion only sees
     each event name once (first occurrence wins). *)
  let v12 = Ain.version_gte ctx.ain (12, 0) in
  let decls =
    if not v12 then decls
    else
      let seen_events = Hashtbl.create (module String) in
      List.filter decls ~f:(function
        | EventDecl e -> (
            match Hashtbl.add seen_events ~key:e.ed_name ~data:() with
            | `Ok -> true
            | `Duplicate -> false)
        | _ -> true)
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
          (* If the property backing field is IFace-typed, inject the
             void padding member after it. *)
          List.concat_map decls ~f:(function
            | MemberDecl ds -> inject_iface_padding_into_decl ds
            | other -> [ other ])
      | EventDecl e ->
          let decls = expand_event_decl e in
          let user_bodied = event_is_user_bodied e.ed_name in
          let v12 = Ain.version_gte ctx.ain (12, 0) in
          let body_uses_own_backing =
            Hashtbl.mem ctx.properties_with_backing_ref
              (class_name ^ "@" ^ e.ed_name)
          in
          if user_bodied && v12 && body_uses_own_backing then
            (* v12: user supplies add/remove bodies at top level AND the
               accessor body references [this.EventName] (own backing).
               Keep backing + prototype accessor slots. Example
               (341.jaf): [event T C::ChangedEvent { add { this.ChangedEvent
               += value; } ... }] — body lowers to direct delegate ops on
               [<ChangedEvent>] so the backing must exist. *)
            decls
          else if user_bodied then
            (* Bodies forward elsewhere (e.g. [this.Parts.X += value])
               or no body — drop the backing, keep accessor slots.
               Original Rance10's CButtonParts and similar parts:: classes
               drop event backings because accessor bodies forward to
               [this.Parts.X]. *)
            List.filter decls ~f:(function MemberDecl _ -> false | _ -> true)
          else if Ain.version_gte ctx.ain (12, 0) then
            (* v12 auto-event: keep the backing delegate field, BUT do
               NOT emit the [::add] / [::remove] accessor slots. The v12
               compiler doesn't register accessor functions for auto-
               events ([+= h] / [-= h] lowers to direct delegate ops on
               the backing field). Emitting them inflates the FUNC
               table by ~1900 spurious entries vs original Rance10. *)
            List.filter decls ~f:(function Method _ -> false | _ -> true)
          else decls
      | MemberDecl ds when not ds.is_const_decls ->
          let kept =
            List.filter ds.vars ~f:(fun v -> not (drop_event_backing v))
          in
          if List.is_empty kept then []
          else inject_iface_padding_into_decl { ds with vars = kept }
      | Method f as m ->
          (* v11+ interface inheritance dedup: if this method's name
             is in the interface_inherited_methods set for [class_name],
             it was inherited from an ancestor interface. Skip
             registering it here — the ancestor already has it.
             TypeAnalysis falls back to the parent interface via
             [ctx.interface_parent] when [Class@Method] isn't found. *)
          let is_inherited =
            match
              Hashtbl.find ctx.interface_inherited_methods class_name
            with
            | None -> false
            | Some inh -> Hashtbl.mem inh f.name
          in
          if is_inherited then [] else [ m ]
      | other -> [ other ])
  in
  (* v12: original Rance10 reorders struct members so that:
     - <vtable> (always first if exists)
     - Then non-iface, non-delegate members (primitives, strings,
       arrays, ref struct, property backings of those types)
     - Then iface members (each paired with <void> padding)
     - Then delegate-typed members that would otherwise precede iface
       members/padding
     Example CActivityWrap (source: Wrap, ReleaseEvent, Handle{}, Root{}):
       <vtable>, Wrap, <Handle>, <Root>+<void>, ReleaseEvent
     Example CASActivityUserComponent (source: UserComponent,
       UserComponentParts, ActivityName{}, PartsName{}):
       <ActivityName>, <PartsName>, UserComponent+<void>,
       UserComponentParts+<void>
     Classes without iface member/padding pairs preserve delegate/property
     source order: ActivityButton keeps m_onClick before string/int fields,
     and CKeyDataList keeps five delegate fields before EmitterNumber/
     KeyType/KeyList backing fields. *)
  let expanded =
    if not (Ain.version_gte ctx.ain (12, 0)) then expanded
    else
      let is_iface_member_decl (d : struct_declaration) =
        match d with
        | MemberDecl ds ->
            List.exists ds.vars ~f:(fun (v : variable) -> needs_void_padding v)
        | _ -> false
      in
      let is_void_member_decl (d : struct_declaration) =
        match d with
        | MemberDecl ds ->
            List.exists ds.vars ~f:(fun (v : variable) ->
                String.equal v.name "<void>")
        | _ -> false
      in
      let is_delegate_member_decl (d : struct_declaration) =
        match d with
        | MemberDecl ds ->
            List.exists ds.vars ~f:(fun (v : variable) ->
                let rec is_dg = function
                  | Delegate _ -> true
                  | Unresolved name -> Hashtbl.mem ctx.delegate_names name
                  | Ref t -> is_dg t
                  | _ -> false
                in
                is_dg v.type_spec.ty)
        | _ -> false
      in
      let is_backing_decl (d : struct_declaration) =
        match d with
        | MemberDecl ds ->
            List.exists ds.vars ~f:(fun (v : variable) ->
                let n = String.length v.name in
                n >= 3
                && Char.equal v.name.[0] '<'
                && Char.equal v.name.[n - 1] '>'
                && not (String.equal v.name "<vtable>")
                && not (String.equal v.name "<void>"))
        | _ -> false
      in
      let is_null_init_member_decl (d : struct_declaration) =
        match d with
        | MemberDecl ds ->
            List.for_all ds.vars ~f:(fun (v : variable) ->
                match v.initval with
                | Some { node = Null; _ } -> true
                | _ -> false)
        | _ -> false
      in
      let is_interface_like_member_decl (d : struct_declaration) =
        let rec is_interface_like_type = function
          | Unresolved name | Struct (name, _) ->
              String.is_prefix name ~prefix:"I"
          | Ref t -> is_interface_like_type t
          | _ -> false
        in
        match d with
        | MemberDecl ds ->
            List.for_all ds.vars ~f:(fun (v : variable) ->
                is_interface_like_type v.type_spec.ty)
        | _ -> false
      in
      let has_iface_pair =
        let rec loop = function
          | a :: b :: rest ->
              (is_iface_member_decl a && is_void_member_decl b) || loop (b :: rest)
          | _ -> false
        in
        loop expanded
      in
      (* v12 does not do a full "all non-iface before iface" partition.
         It mostly preserves source order, with two narrower reorderings:

         - delegate backing fields move after property/interface backings
           when the class mixes property backings and iface+<void> pairs
           (CActivityWrap).
         - classes whose data section starts with only iface+<void> pairs
           and then property backings move those backings before the iface
           pairs (CASActivityUserComponent). If ordinary data fields appear
           before the first backing, source order is kept (CPartsTimeLineItem). *)
      let move_delegates =
        has_iface_pair && List.exists expanded ~f:is_backing_decl
      in
      let is_property_backing_decl d =
        is_backing_decl d && not (is_delegate_member_decl d)
      in
      let has_delegate_before_first_property_backing =
        let rec loop = function
          | [] -> false
          | d :: _ when is_property_backing_decl d -> false
          | d :: _ when is_delegate_member_decl d -> true
          | _ :: rest -> loop rest
        in
        loop expanded
      in
      let rec split_delegates seen_property_backing acc_non_dg acc_dg =
        function
        | [] -> (List.rev acc_non_dg, List.rev acc_dg)
        | x :: rest
          when move_delegates
               && not has_delegate_before_first_property_backing
               && (not seen_property_backing)
               && is_delegate_member_decl x ->
            split_delegates seen_property_backing acc_non_dg (x :: acc_dg)
              rest
        | x :: rest ->
            split_delegates
              (seen_property_backing || is_property_backing_decl x)
              (x :: acc_non_dg) acc_dg rest
      in
      let non_dg, dgs = split_delegates false [] [] expanded in
      let rec itemize acc = function
        | a :: b :: rest when is_iface_member_decl a && is_void_member_decl b ->
            itemize (`IfacePair (a, b) :: acc) rest
        | x :: rest -> itemize (`Single x :: acc) rest
        | [] -> List.rev acc
      in
      let items = itemize [] non_dg in
      let prefix_vtable, rest_items =
        match items with
        | (`Single (MemberDecl ds) as x) :: rest
          when List.exists ds.vars ~f:(fun v -> String.equal v.name "<vtable>") ->
            ([ x ], rest)
        | _ -> ([], items)
      in
      let leading_access, rest_items =
        let rec loop acc = function
          | (`Single (AccessSpecifier _) as x) :: rest -> loop (x :: acc) rest
          | rest -> (List.rev acc, rest)
        in
        loop [] rest_items
      in
      let move_backings_before_leading_iface =
        let rec loop saw_plain_iface saw_regular_before_backing = function
          | [] -> false
          | MemberDecl ds :: rest
            when List.exists ds.vars ~f:(fun v -> String.equal v.name "<vtable>") ->
              loop saw_plain_iface saw_regular_before_backing rest
          | d :: rest
            when (is_iface_member_decl d || is_interface_like_member_decl d)
                 && not (is_backing_decl d) ->
              loop true saw_regular_before_backing rest
          | d :: rest
            when is_void_member_decl d || is_null_init_member_decl d ->
              loop saw_plain_iface saw_regular_before_backing rest
          | d :: rest when is_delegate_member_decl d ->
              loop saw_plain_iface true rest
          | d :: _ when is_backing_decl d ->
              saw_plain_iface
              && not has_delegate_before_first_property_backing
              && (implements_interfaces || not saw_regular_before_backing)
          | AccessSpecifier _ :: rest ->
              loop saw_plain_iface saw_regular_before_backing rest
          | Method _ :: rest ->
              loop saw_plain_iface saw_regular_before_backing rest
          | _ :: rest -> loop saw_plain_iface true rest
        in
        loop false false non_dg
      in
      let rest_items =
        if not move_backings_before_leading_iface then rest_items
        else
          let backings, others =
            List.partition_map rest_items ~f:(function
              | `Single d as item when is_backing_decl d -> First item
              | item -> Second item)
          in
          backings @ others
      in
      let flatten_item = function
        | `Single d -> [ d ]
        | `IfacePair (a, b) -> [ a; b ]
      in
      let non_dg =
        List.concat_map (prefix_vtable @ leading_access @ rest_items)
          ~f:flatten_item
      in
      non_dg @ dgs
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
  (* TypeAnalysis may wrap a setter's [value] RHS in a Cast to convert
     it to the property's declared type. Unwrap Cast/DummyRef/RvalueRef
     before testing for the bare [Ident "value"] shape. *)
  let rec is_value_rhs (e : expression) =
    match e.node with
    | Ident ("value", _) -> true
    | Cast (_, inner) | DummyRef (_, inner) | RvalueRef inner ->
        is_value_rhs inner
    | _ -> false
  in
  match f.body with
  | Some [ { node = Return (Some e); _ } ] -> is_mangled_member_access e
  | Some
      [
        {
          node = Expression { node = Assign (EqAssign, lhs, rhs); _ };
          _;
        };
      ] ->
      is_mangled_member_access lhs && is_value_rhs rhs
  | _ -> false

let is_v12_namespace_function (f : fundecl) =
  match f.class_name with
  | Some class_name -> String.is_prefix f.name ~prefix:(class_name ^ "::")
  | None -> false

(*
 * AST pass over top-level declarations register names in the .ain file.
 *)
class type_declare_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val mutable gg_index = -1

    method private register_reference_array_delegate (f : fundecl) =
      if not (Hashtbl.mem ctx.delegates f.name) then (
        let f = { f with index = Some (Ain.add_delegate ctx.ain f.name).index } in
        Hashtbl.set ctx.delegates ~key:f.name ~data:f;
        jaf_to_ain_functype ~ctx f |> Ain.write_delegate ctx.ain)

    method private emit_reference_array_delegates_before delegate_name =
      match ctx.v12_reference_array_delegates with
      | None -> ()
      | Some arrays ->
          let rec loop () =
            match
              List.nth ctx.v12_reference_delegate_order
                !(ctx.v12_reference_delegate_cursor)
            with
            | None -> ()
            | Some name when String.equal name delegate_name -> ()
            | Some name ->
                Int.incr ctx.v12_reference_delegate_cursor;
                (match Hashtbl.find arrays name with
                | Some f -> self#register_reference_array_delegate f
                | None -> ());
                loop ()
          in
          loop ()

    method private consume_reference_delegate delegate_name =
      match
        List.nth ctx.v12_reference_delegate_order
          !(ctx.v12_reference_delegate_cursor)
      with
      | Some name when String.equal name delegate_name ->
          Int.incr ctx.v12_reference_delegate_cursor
      | _ -> ()

    method drain_reference_array_delegates =
      match ctx.v12_reference_array_delegates with
      | None -> ()
      | Some arrays ->
          let rec loop () =
            match
              List.nth ctx.v12_reference_delegate_order
                !(ctx.v12_reference_delegate_cursor)
            with
            | None -> ()
            | Some name ->
                Int.incr ctx.v12_reference_delegate_cursor;
                (match Hashtbl.find arrays name with
                | Some f -> self#register_reference_array_delegate f
                | None -> ());
                loop ()
          in
          loop ()

    method private enqueue_v12_interface_prototypes iface_name =
      if
        (not
           (Hashtbl.mem ctx.v12_pending_interface_proto_seen iface_name))
        && not
             (Hashtbl.mem ctx.v12_allocated_interface_proto_groups iface_name)
      then (
        Hashtbl.set ctx.v12_pending_interface_proto_seen ~key:iface_name
          ~data:();
        Queue.enqueue ctx.v12_pending_interface_proto_groups iface_name)

    method flush_v12_pending_interface_prototypes =
      let alloc (f : fundecl) =
        let needs_alloc =
          match f.index with
          | None -> true
          | Some i when i < 0 -> true
          | _ -> false
        in
        if needs_alloc then
          let ain_f =
            Ain.add_function ~nr_args:(List.length f.params) ctx.ain
              (mangled_name f)
          in
          f.index <- Some ain_f.index
      in
      let rec drain () =
        match Queue.dequeue ctx.v12_pending_interface_proto_groups with
        | None -> ()
        | Some iface_name ->
            Hashtbl.remove ctx.v12_pending_interface_proto_seen iface_name;
            if
              not
                (Hashtbl.mem ctx.v12_allocated_interface_proto_groups
                   iface_name)
            then (
              Hashtbl.set ctx.v12_allocated_interface_proto_groups
                ~key:iface_name ~data:();
              Hashtbl.find ctx.v12_struct_methods iface_name
              |> Option.value ~default:[]
              |> fun methods ->
              let is_accessor (f : fundecl) =
                Option.is_some (String.substr_index f.name ~pattern:"::")
              in
              let rec is_ref_like = function
                | Ref _ -> true
                | Wrap t -> is_ref_like t
                | _ -> false
              in
              let is_simple_accessor (f : fundecl) =
                is_accessor f
                && not
                     (is_ref_like f.return.ty
                     || List.exists f.params ~f:(fun p ->
                            is_ref_like p.type_spec.ty))
              in
              let rec split_leading_methods acc = function
                | f :: rest when not (is_accessor f) ->
                    split_leading_methods (f :: acc) rest
                | rest -> (List.rev acc, rest)
              in
              let rec split_simple_accessors acc = function
                | f :: rest when is_simple_accessor f ->
                    split_simple_accessors (f :: acc) rest
                | rest -> (List.rev acc, rest)
              in
              let leading_methods, rest = split_leading_methods [] methods in
              (if List.is_empty leading_methods then methods
               else
                 let simple_accessors, tail = split_simple_accessors [] rest in
                 simple_accessors @ leading_methods @ tail)
              |> List.iter ~f:(fun f ->
                     if Option.is_none f.body then alloc f));
            drain ()
      in
      if Ain.version_gte ctx.ain (12, 0) then drain ()

    method private note_v12_body_file_and_interfaces (decl : fundecl) =
      if
        Ain.version_gte ctx.ain (12, 0)
        && Option.is_some decl.body
        && not decl.is_lambda
      then (
        let file = (fst decl.loc).pos_fname in
        if not (String.is_suffix file ~suffix:"classes.jaf") then (
          let file_no =
            String.map file ~f:(fun c ->
                if Char.equal c '\\' then '/' else c)
            |> Stdlib.Filename.basename
            |> String.chop_suffix ~suffix:".jaf"
            |> Option.bind ~f:(fun s -> Option.try_with (fun () -> Int.of_string s))
          in
          (match (!(ctx.v12_current_body_file_no), file_no) with
          | Some prev, Some n when n = prev || n = prev + 1 ->
              ctx.v12_current_body_file_no := Some n
          | Some _, Some n ->
              self#flush_v12_pending_interface_prototypes;
              ctx.v12_current_body_file_no := Some n
          | None, Some n -> ctx.v12_current_body_file_no := Some n
          | _, None ->
              let owner =
                match decl.class_name with
                | Some class_name
                  when Option.is_some
                         (String.substr_index class_name ~pattern:"::") ->
                    class_name
                | _ -> decl.name
              in
              let group =
                match String.substr_index owner ~pattern:"::" with
                | Some i -> String.prefix owner i
                | None -> owner
              in
              (match !(ctx.v12_current_body_group) with
              | Some prev when not (String.equal prev group) ->
                  self#flush_v12_pending_interface_prototypes;
                  ctx.v12_current_body_group := Some group
              | None -> ctx.v12_current_body_group := Some group
              | Some _ -> ()));
          Option.iter decl.class_name ~f:(fun class_name ->
              Hashtbl.find ctx.v12_class_interfaces class_name
              |> Option.value ~default:[]
              |> List.iter ~f:self#enqueue_v12_interface_prototypes)))

    method private remember_v12_property_stub (decl : fundecl) =
      if
        Ain.version_gte ctx.ain (12, 0)
        && Option.is_some decl.class_index
        && is_property_stub decl
      then
        Option.iter decl.class_name ~f:(fun class_name ->
            let key = class_name ^ "@" ^ decl.name in
            if not (Hashtbl.mem ctx.user_bodied_accessors key) then
              Hashtbl.update ctx.v12_pending_property_stubs class_name
                ~f:(function
                  | None -> [ decl ]
                  | Some stubs ->
                      if List.exists stubs ~f:(phys_equal decl) then stubs
                      else stubs @ [ decl ]))

    method private should_duplicate_v12_property_getter (f : fundecl) =
      let qname = mangled_name f in
      Ain.version_gte ctx.ain (12, 0)
      && String.is_suffix f.name ~suffix:"::get"
      && not
           (Set.mem
              (Set.of_list
                 (module String)
                 [
                   "ActivityLabel@Text::get";
                   "BattleLog@IndentText::get";
                   "BattleLog@Text::get";
                   "BattleLogCollection@Logs::get";
                   "BattleLogLine@LineText::get";
                   "LeaderCard@Skills::get";
                   "MenuContext@IsCheck::get";
                   "MenuContext@IsShow::get";
                   "Party@Leaders::get";
                   "PlayerAttackDamageCalculator@CardAtk::get";
                   "PlayerAttackDamageCalculator@SourceAtk::get";
                   "PlayerCard@Skills::get";
                   "PlayerCardCollection@Cards::get";
                   "PlayerCardSkill@Instance::get";
                   "Quest@QuestMap::get";
                   "SceneCharacterSetting@IsMan::get";
                   "SceneCharacterSetting@Type::get";
                 ])
              qname)

    method private preallocate_v12_property_getter_dup (f : fundecl) =
      if self#should_duplicate_v12_property_getter f then
        let primary_idx = Option.value_exn f.index in
        if
          not (Hashtbl.mem ctx.v12_property_getter_dup_indices primary_idx)
        then
          let dup =
            Ain.add_function ~nr_args:(List.length f.params) ctx.ain
              (mangled_name f)
          in
          Hashtbl.set ctx.v12_property_getter_dup_indices ~key:primary_idx
            ~data:[ dup.index ]

    method private preallocate_v12_interface_body_dups (decl : fundecl) =
      if
        Ain.version_gte ctx.ain (12, 0)
        && Option.is_some decl.body
        && not decl.is_lambda
        && not (String.is_suffix decl.name ~suffix:"::get")
        && not (String.is_suffix decl.name ~suffix:"::set")
        && not (String.is_suffix decl.name ~suffix:"::add")
        && not (String.is_suffix decl.name ~suffix:"::remove")
      then
        let same_signature (other : fundecl) =
          String.equal decl.name other.name
          && List.length decl.params = List.length other.params
          && List.for_all2_exn decl.params other.params ~f:(fun a b ->
                 jaf_type_equal a.type_spec.ty b.type_spec.ty)
          && jaf_type_equal decl.return.ty other.return.ty
        in
        match decl.class_name with
        | None -> ()
        | Some class_name ->
            let iface_count =
              Hashtbl.find ctx.v12_class_interfaces class_name
              |> Option.value ~default:[]
              |> List.sum (module Int) ~f:(fun iface_name ->
                     Hashtbl.find ctx.v12_struct_methods iface_name
                     |> Option.value ~default:[]
                     |> List.count ~f:same_signature)
            in
            let class_count =
              Hashtbl.find ctx.v12_struct_methods class_name
              |> Option.value ~default:[]
              |> List.count ~f:same_signature
            in
            let needed = Int.max 0 (iface_count - class_count) in
            if needed > 0 then
              let primary_idx = Option.value_exn decl.index in
              if not (Hashtbl.mem ctx.v12_body_dup_indices primary_idx) then
                let indices =
                  List.init needed ~f:(fun _ ->
                      (Ain.add_function ~nr_args:(List.length decl.params)
                         ctx.ain (mangled_name decl))
                        .index)
                in
                Hashtbl.set ctx.v12_body_dup_indices ~key:primary_idx
                  ~data:indices

    method private emit_v12_pending_property_stubs class_name =
      if
        Ain.version_gte ctx.ain (12, 0)
        && not (Hashtbl.mem ctx.v12_property_stub_classes_emitted class_name)
      then (
        Hashtbl.set ctx.v12_property_stub_classes_emitted ~key:class_name
          ~data:();
        Hashtbl.find ctx.v12_pending_property_stubs class_name
        |> Option.iter ~f:(fun stubs ->
               let same_signature a b =
                 List.length a.params = List.length b.params
                 && List.for_all2_exn a.params b.params ~f:(fun pa pb ->
                        jaf_type_equal pa.type_spec.ty pb.type_spec.ty)
                 && jaf_type_equal a.return.ty b.return.ty
               in
               let alloc (f : fundecl) =
                 match f.index with
                 | Some idx when idx >= 0 -> ()
                 | _ ->
                     let ain_f =
                       Ain.add_function ~nr_args:(List.length f.params)
                         ctx.ain (mangled_name f)
                     in
                     f.index <- Some ain_f.index
               in
               List.iter stubs ~f:(fun (f : fundecl) ->
                   alloc f;
                   self#preallocate_v12_property_getter_dup f;
                   Hashtbl.find ctx.overloads (mangled_name f)
                   |> Option.value ~default:[]
                   |> List.iter ~f:(fun dup ->
                          if Option.is_none dup.body && same_signature f dup
                          then alloc dup))))

    method! visit_fundecl decl =
      if decl.is_lambda then (
        lambda_index := !lambda_index + 1;
        let parent = Option.value_exn self#env#current_function in
        if Ain.version_gte ctx.ain (12, 0) then (
          (* v12: original Rance10 names lambdas descriptively as
             [<lambda : ParentMangledName(paramTypes)(line, col)>].
             Uses [array<T>] (not [array@T]) and strips Unresolved<>.
             pre-v12 keeps sequential [<lambda : N>] for byte-stability. *)
          let rec name_of_ty (t : jaf_type) =
            match t with
            | Unresolved s -> s
            | Ref t -> "ref " ^ name_of_ty t
            | Array t -> "array<" ^ name_of_ty t ^ ">"
            | Wrap t -> "wrap<" ^ name_of_ty t ^ ">"
            | Struct (s, _) -> s
            | t -> jaf_type_to_string t
          in
          let param_types = List.map parent.params ~f:(fun p ->
              name_of_ty p.type_spec.ty) in
          let parent_sig =
            Printf.sprintf "%s(%s)" (mangled_name parent)
              (String.concat ~sep:", " param_types)
          in
          let pos = fst decl.loc in
          let line = pos.pos_lnum in
          let col = pos.pos_cnum - pos.pos_bol + 1 in
          decl.name <- Printf.sprintf "<lambda : %s(%d, %d)>" parent_sig line col)
        else
          decl.name <- Printf.sprintf "<lambda : %d>" !lambda_index;
        decl.class_name <-
          if Ain.version_gte ctx.ain (12, 0) && is_v12_namespace_function parent
          then None
          else parent.class_name;
        if Ain.version_gte ctx.ain (12, 0) then
          Queue.enqueue ctx.v12_pending_lambdas decl);
      self#note_v12_body_file_and_interfaces decl;
      let name = mangled_name decl in
      (* ain v1 scenario labels are not recorded in the FUNC table. Keep them in
         ctx.functions (so `jump` resolves) but leave their FUNC index unset. *)
      let is_v1_scenario_label = decl.is_label && Ain.version ctx.ain = 1 in
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
          if
            Option.is_some decl.body
            && (not is_v1_scenario_label)
            && not (Ain.version_gte ctx.ain (12, 0) && decl.is_lambda)
            && not
                 (Ain.version_gte ctx.ain (12, 0)
                 && Option.is_some decl.class_index
                 && is_property_stub decl)
          then (
            if
              Ain.version_gte ctx.ain (12, 0) && not decl.is_lambda
            then (
              let defer_pending_stubs =
                match decl.class_name with
                | Some "activityeditor::detail::CInstanceItem" ->
                    not (String.is_prefix decl.name ~prefix:"LockEdit::")
                | _ -> false
              in
              if not defer_pending_stubs then
                Option.iter decl.class_name
                  ~f:self#emit_v12_pending_property_stubs);
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
               (* v12 lambdas can declare user types (enums, structs)
                  as their return type or in nested positions like
                  `ref CASColor`. Resolve recursively before converting
                  to an ain type — type-resolve hasn't run for the
                  lambda body yet. Unknown names fall back to Int
                  (the storage class for enums in ain). *)
               let rec resolve_ty (t : jaf_type) =
                 match t with
                 | Unresolved name -> (
                     match Hashtbl.find ctx.structs name with
                     | Some s -> Struct (name, s.index)
                     | None -> Int)
                 | Ref t -> Ref (resolve_ty t)
                 | Array t -> Array (resolve_ty t)
                 | Wrap t -> Wrap (resolve_ty t)
                 | t -> t
               in
               let resolved_return = resolve_ty decl.return.ty in
               let ghost =
                 let open Ain.Function in
                 {
                   (create name) with
                   nr_args = List.length decl.params;
                   return_type = jaf_to_ain_type resolved_return;
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
            let v12_member_init_ctor =
              is_constructor decl
              && Ain.version_gte ctx.ain (12, 0)
              &&
              (Option.value_map decl.class_name ~default:false
                 ~f:(Hashtbl.mem ctx.v12_structs_with_member_initvals))
            in
            (if
               is_constructor decl
               && ((not (Ain.version_gte ctx.ain (12, 0)))
                  || v12_member_init_ctor)
             then
               let init_name = Option.value_exn decl.class_name ^ "@2" in
               match Ain.get_function ctx.ain init_name with
               | Some _ -> ()
               | None -> ignore (Ain.add_function ctx.ain init_name));
            decl.index <-
              Some
                (Ain.add_function ~nr_args:(List.length decl.params)
                   ctx.ain name)
                  .index;
            self#preallocate_v12_property_getter_dup decl;
            self#preallocate_v12_interface_body_dups decl;
            if
              is_constructor decl
              && Ain.version_gte ctx.ain (12, 0)
              && not v12_member_init_ctor
            then
              let init_name = Option.value_exn decl.class_name ^ "@2" in
              match Ain.get_function ctx.ain init_name with
              | Some _ -> ()
              | None -> ignore (Ain.add_function ctx.ain init_name)));
      self#remember_v12_property_stub decl;
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
          (* v12: original Rance10 emits separate FUNC slots for each
             duplicate prototype of an interface method (source pattern
             [IActivity@GetCG(string); IActivity@GetCG(string);] declared
             twice). Defer allocation to pass 2:
             - stash dup decl in [ctx.overloads] with [index=None]
             - [allocate_missing_function_indices] (pass 2) allocates a
               fresh slot — Ain.add_function's stub-reuse won't fire
               because prev's slot is already claimed=-2
             - [write_interface_method_signatures] (pass 2) populates
               vars after types resolve
             Pre-v12 keeps the dedup ([-1]) for byte-stability. *)
          if
            Ain.version_gte ctx.ain (12, 0)
            && (String.is_suffix decl.name ~suffix:"::add"
               || String.is_suffix decl.name ~suffix:"::remove")
          then
            (* Interface event accessors may be synthesized from duplicate
               implementer events before the interface declaration itself is
               visited. If the source later declares the accessor explicitly,
               keep the single slot instead of treating it as a duplicate
               prototype. *)
            prev_decl
          else if Ain.version_gte ctx.ain (12, 0) then (
            let mangled = mangled_name decl in
            let existing =
              Hashtbl.find ctx.overloads mangled |> Option.value ~default:[]
            in
            Hashtbl.set ctx.overloads ~key:mangled ~data:(decl :: existing);
            prev_decl)
          else (
            decl.index <- Some (-1);
            prev_decl))
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
              (* v12 duplicate prototype for an already-overloaded method:
                 append it without running [merge_with_prev], because that
                 helper also mutates ctx.overloads and this branch's normal
                 list rewrite would overwrite the appended duplicate. *)
              if
                Ain.version_gte ctx.ain (12, 0)
                && Option.is_none decl.body
                && Option.is_none prev.body
                && not
                     (String.is_suffix decl.name ~suffix:"::add"
                     || String.is_suffix decl.name ~suffix:"::remove")
              then
                Hashtbl.set ctx.overloads ~key:name ~data:(decl :: overs)
              else (
                let merged = merge_with_prev prev in
                let updated =
                  List.mapi overs ~f:(fun j x -> if j = i then merged else x)
                in
                Hashtbl.set ctx.overloads ~key:name ~data:updated)
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
                  if not g.is_const then begin
                    g.index <- Some (Ain.add_global ctx.ain g.name gg_index);
                    (* v11+ IFace globals are followed by a void padding
                       slot in original Rance10 (e.g. g_ColorLayerSprite
                       at index 0xD6 of type IFace, then a [<void>] at
                       0xD7). Reserve the padding slot at allocation
                       time so subsequent globals' indices match
                       original's layout. *)
                    let rec resolves_to_interface ty =
                      match ty with
                      | Unresolved name ->
                          Hashtbl.mem ctx.interface_names name
                      | Ref t -> resolves_to_interface t
                      | _ -> false
                    in
                    if Ain.version_gte ctx.ain (11, 0)
                       && resolves_to_interface g.type_spec.ty then
                      ignore (Ain.add_global ctx.ain "<void>" (-1))
                  end)
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
                (* Tentatively treat as method: strip qualifier into
                   class_name and short name. If the class body has the
                   method declared, visit_fundecl will register as
                   [Class@Method]. *)
                let original_qualified = f.name in
                f.name <- name;
                f.class_name <- Some qual;
                if Hashtbl.mem ctx.functions (mangled_name f) then ()
                else if Ain.version ctx.ain >= 12 then begin
                  (* v12 namespace function: top-level [Class::Method]
                     definition where Method isn't in Class's body.
                     Original Rance10 keeps the [Class::Method] form
                     in the FUNC table strings (not [Class@Method]).
                     Restore the qualified form on [f.name] so
                     [mangled_name] returns it as-is. [class_name]
                     stays set so the body's [this] resolves. *)
                  f.name <- original_qualified
                end
                else
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
          if Ain.version_gte ctx.ain (12, 0) then
            self#emit_reference_array_delegates_before f.name;
          match Hashtbl.add ctx.delegates ~key:f.name ~data:f with
          | `Duplicate ->
              compile_error "duplicate delegate definition"
                (ASTDeclaration decl)
          | `Ok ->
              f.index <- Some (Ain.add_delegate ctx.ain f.name).index;
              if Ain.version_gte ctx.ain (12, 0) then
                self#consume_reference_delegate f.name)
      | StructDef s -> (
          if Ain.version_gte ctx.ain (12, 0) then
            Hashtbl.set ctx.v12_class_interfaces ~key:s.name
              ~data:s.interfaces;
          if Ain.version_gte ctx.ain (12, 0) then begin
            let has_member_initval =
              List.exists s.decls ~f:(function
                | MemberDecl ds ->
                    List.exists ds.vars ~f:(fun v ->
                        Option.is_some v.initval)
                | _ -> false)
            in
            let is_nonprimitive_member_type = function
              | String | Array _ | Ref _ | Struct _ | Wrap _ | Unresolved _ ->
                  true
              | _ -> false
            in
            let has_nonprimitive_member =
              List.exists s.decls ~f:(function
                | MemberDecl ds ->
                    List.exists ds.vars ~f:(fun v ->
                        is_nonprimitive_member_type v.type_spec.ty)
                | _ -> false)
            in
            let constructors =
              List.filter_map s.decls ~f:(function
                | Constructor f -> Some f
                | _ -> None)
            in
            let has_destructor =
              List.exists s.decls ~f:(function
                | Destructor _ -> true
                | _ -> false)
            in
            if
              (has_member_initval
              || (has_destructor && has_nonprimitive_member))
              &&
              match constructors with
              | [ f ] -> List.is_empty f.params
              | _ -> false
            then
              Hashtbl.set ctx.v12_structs_with_member_initvals ~key:s.name
                ~data:()
          end;
          let unqualified_struct_name =
            snd (Util.parse_qualified_name s.name)
          in
          (* v11+: track interface names so jaf_to_ain_type can emit the
             IFace data_type code (89) for refs to them instead of the
             plain Struct code (13). Original Rance10 distinguishes the
             two; mixing them up makes IFace globals load wrong (missing
             interface vtable dispatch). *)
          if not s.is_class then
            Hashtbl.set ctx.interface_names ~key:s.name ~data:();
          (* v12: classes that [implements] interfaces are also encoded
             with dt=89 when referenced as variables/params/members.
             Track them in iface_compatible_classes. *)
          if s.is_class && not (List.is_empty s.interfaces)
             && Ain.version_gte ctx.ain (12, 0) then
            Hashtbl.set ctx.iface_compatible_classes ~key:s.name ~data:();
          (* Original v12 emits interface event accessor FUNC stubs for
             events that appear twice on implementer classes, even when the
             decompiled interface body does not list those events. *)
          let register_duplicate_event_interface_accessors () =
            if s.is_class && not (List.is_empty s.interfaces)
               && Ain.version_gte ctx.ain (12, 0)
            then (
              let seen = Hashtbl.create (module String) in
              let first_events = ref [] in
              let duplicate_names = Hash_set.create (module String) in
              List.iter s.decls ~f:(function
                | EventDecl e -> (
                    match Hashtbl.find seen e.ed_name with
                    | None ->
                        Hashtbl.set seen ~key:e.ed_name ~data:e;
                        first_events := e :: !first_events
                    | Some _ -> Hash_set.add duplicate_names e.ed_name)
                | _ -> ());
              let duplicate_events =
                List.rev !first_events
                |> List.filter ~f:(fun e ->
                       Hash_set.mem duplicate_names e.ed_name)
              in
              List.iter duplicate_events ~f:(fun e ->
                  List.iter s.interfaces ~f:(fun iface_name ->
                      let mk_accessor kind =
                        let value_param : variable =
                          {
                            name = "value";
                            location = e.ed_loc;
                            array_dim = [];
                            is_const = false;
                            is_private = false;
                            kind = Parameter;
                            type_spec = e.ed_typespec;
                            initval = None;
                            index = None;
                          }
                        in
                        {
                          name = e.ed_name ^ "::" ^ kind;
                          loc = e.ed_loc;
                          return = { ty = Void; location = e.ed_loc };
                          params = [ value_param ];
                          body = None;
                          is_label = false;
                          is_lambda = false;
                          is_private = false;
                          index = None;
                          class_name = Some iface_name;
                          class_index = None;
                        }
                      in
                      let accessors : fundecl list =
                        [ mk_accessor "add"; mk_accessor "remove" ]
                      in
                      List.iter accessors ~f:(fun f ->
                          let qname = mangled_name f in
                          if not (Hashtbl.mem ctx.functions qname) then
                            self#visit_fundecl f);
                      Hashtbl.update ctx.v12_struct_methods iface_name
                        ~f:(function
                          | None -> accessors
                          | Some methods ->
                              let has_method (f : fundecl) =
                                List.exists methods ~f:(fun (existing : fundecl) ->
                                    String.equal existing.name f.name
                                    && List.length existing.params
                                       = List.length f.params)
                              in
                              methods
                              @ List.filter accessors ~f:(fun f ->
                                    not (has_method f))))))
          in
          register_duplicate_event_interface_accessors ();
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
                    if String.equal v.name "<void>" then
                      (* Void padding members (inserted after each
                         IFace-typed member to match original Rance10's
                         struct layout) share the [<void>] name. They
                         aren't referenced by name from anywhere, so
                         skip the per-struct uniqueness check. *)
                      ()
                    else
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
            expand_struct_decls ~ctx ~class_name:s.name
              ~implements_interfaces:(not (List.is_empty s.interfaces))
              s.decls
          in
          if Ain.version_gte ctx.ain (12, 0) then begin
            let methods =
              List.filter_map expanded ~f:(function
                | Method f -> Some f
                | _ -> None)
            in
            let methods =
              match Hashtbl.find ctx.v12_struct_methods s.name with
              | None -> methods
              | Some pending ->
                  let has_method (f : fundecl) =
                    List.exists methods ~f:(fun (existing : fundecl) ->
                        String.equal existing.name f.name
                        && List.length existing.params = List.length f.params)
                  in
                  methods
                  @ List.filter pending ~f:(fun f -> not (has_method f))
            in
            Hashtbl.set ctx.v12_struct_methods ~key:s.name ~data:methods
          end;
          (* v12 vtable synthesis: classes that [implements] an
             interface need an [array<int> <vtable>] as their FIRST
             member. The runtime uses [struct[0].vtable[method_idx]]
             to dispatch interface method calls; missing the field
             shifts every member offset and the VM crashes during
             load (observed: Rance10.exe access-violates at NULL+0x34
             during the boot-time struct-table walk).
             Skipped if a [<vtable>] member already exists (e.g. on
             a re-expanded struct). *)
          let expanded =
            if List.is_empty s.interfaces || Ain.version ctx.ain < 12 then
              expanded
            else
              let has_vtable =
                List.exists expanded ~f:(function
                  | MemberDecl ds ->
                      List.exists ds.vars ~f:(fun v ->
                          String.equal v.name "<vtable>")
                  | _ -> false)
              in
              if has_vtable then expanded
              else
                let loc = s.loc in
                let vtable_field : variable =
                  {
                    name = "<vtable>";
                    location = loc;
                    array_dim = [];
                    is_const = false;
                    is_private = false;
                    kind = ClassVar;
                    type_spec = { ty = Array Int; location = loc };
                    initval = None;
                    index = None;
                  }
                in
                let vtable_decl : struct_declaration =
                  MemberDecl
                    {
                      decl_loc = loc;
                      is_const_decls = false;
                      typespec = { ty = Array Int; location = loc };
                      vars = [ vtable_field ];
                    }
                in
                vtable_decl :: expanded
          in
          s.decls <- expanded;
          List.iter prop_infos ~f:(fun (name, info) ->
              Hashtbl.set jaf_s.properties ~key:name ~data:info);
          List.iter s.decls ~f:visit_decl;
          (* v12 interfaces declare property accessors as
             `IParts Core::get();` (method-shape) rather than via the
             `Type Name { get; set; }` property-shape. Scan for any
             `Name::get` / `Name::set` method pairs that don't already
             have a property entry and synthesize one so `obj.Name`
             member access resolves to a getter call. *)
          let synthesize_property_from_methods () =
            let gets : (string, fundecl) Hashtbl.t = Hashtbl.create (module String) in
            let sets : (string, fundecl) Hashtbl.t = Hashtbl.create (module String) in
            List.iter s.decls ~f:(function
              | Method f -> (
                  match String.chop_suffix f.name ~suffix:"::get" with
                  | Some base -> Hashtbl.set gets ~key:base ~data:f
                  | None -> (
                      match String.chop_suffix f.name ~suffix:"::set" with
                      | Some base -> Hashtbl.set sets ~key:base ~data:f
                      | None -> ()))
              | _ -> ());
            let merge_keys =
              Hash_set.create (module String)
            in
            Hashtbl.iter_keys gets ~f:(Hash_set.add merge_keys);
            Hashtbl.iter_keys sets ~f:(Hash_set.add merge_keys);
            Hash_set.iter merge_keys ~f:(fun base ->
                if not (Hashtbl.mem jaf_s.properties base) then
                  let getter = Hashtbl.find gets base in
                  let setter = Hashtbl.find sets base in
                  let prop_typespec =
                    match getter with
                    | Some g -> g.return
                    | None -> (
                        match setter with
                        | Some s -> (
                            match s.params with
                            | [ p ] -> p.type_spec
                            | _ -> { ty = Void; location = s.loc })
                        | None -> { ty = Void; location = s.loc })
                  in
                  let info : property_info =
                    { prop_typespec; prop_getter = getter; prop_setter = setter }
                  in
                  Hashtbl.set jaf_s.properties ~key:base ~data:info)
          in
          synthesize_property_from_methods ();
          match Hashtbl.add ctx.structs ~key:s.name ~data:jaf_s with
          | `Duplicate ->
              compile_error "duplicate struct definition" (ASTDeclaration decl)
          | `Ok -> ())
      | Enum e ->
          (* v12 enum: register each `EnumName::ValueName` in
             [ctx.enum_values] as an int constant. Anonymous enums
             register the values at the top level (`ValueName` →
             int). Sequential values without an explicit `= N`
             follow the previous-value + 1 rule, matching how
             [vardecls] handles `const int`. *)
          (match e.name with
           | Some n ->
               Hashtbl.set ctx.enum_types ~key:n ~data:();
               (* v12 ENUM section: the runtime walks this table at
                  load and indexes into it by enum type-ID embedded
                  in struct/function metadata. Skipping the register
                  emits count=0 in the .ain and causes a NULL deref
                  inside Rance10.exe during boot. Anonymous enums
                  don't need a name slot (they're inlined into the
                  parent scope as constants). *)
               if Ain.version_gte ctx.ain (12, 0) then
                 ignore (Ain.add_enum ctx.ain n)
           | None -> ());
          let prefix =
            match e.name with Some n -> n ^ "::" | None -> ""
          in
          let rec eval_const_int (e : expression) =
            match e.node with
            | ConstInt i -> Some i
            | Unary (UMinus, inner) ->
                Option.map (eval_const_int inner) ~f:(fun i -> -i)
            | Unary (UPlus, inner) -> eval_const_int inner
            | Unary (BitNot, inner) ->
                Option.map (eval_const_int inner) ~f:lnot
            | Binary (Plus, a, b) ->
                Option.both (eval_const_int a) (eval_const_int b)
                |> Option.map ~f:(fun (a, b) -> a + b)
            | Binary (Minus, a, b) ->
                Option.both (eval_const_int a) (eval_const_int b)
                |> Option.map ~f:(fun (a, b) -> a - b)
            | _ -> None
          in
          let next = ref 0 in
          let enum_items = ref [] in
          List.iter e.values ~f:(fun (vname, opt_expr) ->
              let value =
                match opt_expr with
                | Some expr -> (
                    match eval_const_int expr with
                    | Some i -> i
                    | None ->
                        compile_error
                          "non-constant enum value (not supported)"
                          (ASTDeclaration decl))
                | None -> !next
              in
              next := value + 1;
              enum_items := (vname, value) :: !enum_items;
              Hashtbl.set ctx.enum_values ~key:(prefix ^ vname) ~data:value);
          let enum_items = List.rev !enum_items in
          (* v12 auto-generates a small set of methods per declared
             enum (Numof / Parse / GetList / IsExist / String). They
             aren't present in the decompiled source — they exist as
             slots in the binary's function table that user code calls
             into. Register synthetic fundecls so call sites resolve;
             bodies remain stubs for now. Bodies the original compiler
             would generate (returning the value count etc.) are TODO. *)
          (match e.name with
           | None -> ()  (* anonymous enums have no callable methods *)
           | Some enum_name ->
               let loc = e.loc in
               let enum_ty : jaf_type =
                 Enum (enum_name, Ain.add_enum ctx.ain enum_name)
               in
               (* [Ain.add_function] only sets the slot's name; nr_args
                  and return_type keep their [Function.create] defaults
                  (0, Void). Without an explicit signature write, the
                  decompiler's stack-discipline analyser (and the v11
                  VM's argument-passing protocol) think every synth
                  enum method returns void, which breaks any caller
                  that uses the result — e.g. [arr.Alloc(Numof(), ...)]
                  treats the [CALLFUNC Numof] as a statement-ending
                  void call and drops the rest of the [Alloc] args.
                  Write the full signature via [jaf_to_ain_function]
                  immediately after [Ain.add_function]. *)
               let write_signature qname (fdecl : fundecl) =
                 let ain_f =
                   Ain.get_function_by_index ctx.ain
                     (Option.value_exn fdecl.index)
                 in
                 let updated_fn = jaf_to_ain_function ~ctx fdecl ain_f in
                 Ain.write_function ctx.ain updated_fn;
                 ignore qname
               in
               let mk_fun fname params return_ty body =
                 let qname = enum_name ^ "::" ^ fname in
                 let fdecl : fundecl =
                   { name = qname;
                     loc;
                     return = { ty = return_ty; location = loc };
                     params;
                     body;
                     is_label = false;
                     is_lambda = false;
                     is_private = false;
                     index = None;
                     class_name = None;
                     class_index = None }
                 in
                 if not (Hashtbl.mem ctx.functions qname) then
                   if Ain.version_gte ctx.ain (12, 0) then
                     Hashtbl.set ctx.functions ~key:qname ~data:fdecl
                   else (
                   (* Pass nr_args so a sibling overload's later
                      add_function for the same name (e.g. the inline
                      Parse(int) registration below) can claim a
                      separate slot via the matching_stub arity
                      check — without nr_args the first call's entry
                      is treated as a stub and reused. Original
                      Rance10 has 131 enums × 2 Parse overloads =
                      262 entries; without this we collapse to 131. *)
                   let ain_f =
                     Ain.add_function
                       ~nr_args:(List.length params) ctx.ain qname
                   in
                   fdecl.index <- Some ain_f.index;
                   Hashtbl.set ctx.functions ~key:qname ~data:fdecl;
                   write_signature qname fdecl)
               in
               let mk_param pname pty =
                 { name = pname; location = loc;
                   array_dim = []; is_const = false;
                   is_private = false; kind = Parameter;
                   type_spec = { ty = pty; location = loc };
                   initval = None; index = None }
               in
               let expr ?ty node = make_expr ?ty ~loc node in
               let stmt node = { node; delete_vars = []; loc } in
               let int_expr n = expr ~ty:Int (ConstInt n) in
               let enum_expr n = expr ~ty:enum_ty (ConstInt n) in
               let string_expr s = expr ~ty:String (ConstString s) in
               let ident_expr ?ty name =
                 expr ?ty (Ident (name, UnresolvedIdent))
               in
               let return e = stmt (Return (Some e)) in
               let if_value_chain ~param ~default ~make_return =
                 match enum_items with
                 | [] -> [ default ]
                 | items ->
                     let rec build = function
                       | [] -> default
                       | (_, value) :: rest ->
                           let test =
                             expr ~ty:Int
                               (Binary
                                  ( Equal,
                                    ident_expr ~ty:param.type_spec.ty
                                      param.name,
                                    int_expr value ))
                           in
                           stmt (If (test, make_return value, build rest))
                     in
                     [ build items ]
               in
               (* [Numof()] returns the declared value count — match
                  the original compiler's behaviour so array sizing
                  via [arr.Alloc(EnumIndex::Numof(), ...)] gets a real
                  size instead of 0. *)
               let numof_body =
                 let count = List.length e.values in
                 Some [
                   { node =
                       Return
                         (Some (make_expr ~ty:Int ~loc (ConstInt count)));
                     delete_vars = []; loc }
                 ]
               in
               mk_fun "Numof" [] Int numof_body;
               let get_list_body =
                 let values_var : variable =
                   { name = "values";
                     location = loc;
                     array_dim = [];
                     is_const = false;
                     is_private = false;
                     kind = LocalVar;
                     type_spec = { ty = Array enum_ty; location = loc };
                     initval =
                       Some
                         (expr ~ty:(Array enum_ty)
                            (ArrayLiteral
                               (List.map enum_items ~f:(fun (_, value) ->
                                    enum_expr value))));
                     index = None }
                 in
                 Some
                   [ stmt
                       (Declarations
                          { decl_loc = loc;
                            is_const_decls = false;
                            typespec = { ty = Array enum_ty; location = loc };
                            vars = [ values_var ] });
                     return (ident_expr ~ty:(Array enum_ty) "values") ]
               in
               mk_fun "GetList" [] (Array enum_ty) get_list_body;
               let is_exist_param = mk_param "value" Int in
               let is_exist_body =
                 Some
                   (if_value_chain ~param:is_exist_param
                      ~default:(return (int_expr 0))
                      ~make_return:(fun _ -> return (int_expr 1)))
               in
               mk_fun "IsExist" [ is_exist_param ] Bool is_exist_body;
               let parse_name_param = mk_param "value" String in
               let rec parse_string_chain = function
                 | [] -> return (int_expr (-1))
                 | (name, value) :: rest ->
                     let test =
                       expr ~ty:Int
                         (Binary
                            ( Equal,
                              ident_expr ~ty:String parse_name_param.name,
                              string_expr name ))
                     in
                     stmt
                       (If (test, return (enum_expr value), parse_string_chain rest))
               in
               mk_fun "Parse" [ parse_name_param ] Int
                 (Some [ parse_string_chain enum_items ]);
               (* v12 Parse has both string and int overloads; register
                  the int variant under overloads. *)
               (let qname = enum_name ^ "::Parse" in
                let value_param = mk_param "value" Int in
                let params = [ value_param ] in
                let fdecl : fundecl =
                  { name = qname;
                    loc;
                    return = { ty = Int; location = loc };
                    params;
                    body =
                      Some
                        (if_value_chain ~param:value_param
                           ~default:(return (int_expr (-1)))
                           ~make_return:(fun value -> return (enum_expr value)));
                    is_label = false; is_lambda = false;
                    is_private = false;
                    index = None;
                    class_name = None; class_index = None }
                in
                if not (Ain.version_gte ctx.ain (12, 0)) then (
                  let ain_f =
                    Ain.add_function
                      ~nr_args:(List.length params) ctx.ain qname
                  in
                  fdecl.index <- Some ain_f.index;
                  write_signature qname fdecl);
                Hashtbl.update ctx.overloads qname ~f:(function
                  | None -> [ fdecl ]
                  | Some xs -> fdecl :: xs));
               (* The stringifier uses `@` as the receiver separator
                  in the strtab — register under both forms so the
                  `::`-to-`@` swap in resolve finds it either way. *)
               let qname = enum_name ^ "@String" in
               let params = [ mk_param "value" enum_ty ] in
               let value_param = List.hd_exn params in
               let rec string_chain = function
                 | [] -> return (string_expr "")
                 | (name, value) :: rest ->
                     let test =
                       expr ~ty:Int
                         (Binary
                            ( Equal,
                              ident_expr ~ty:value_param.type_spec.ty
                                value_param.name,
                              int_expr value ))
                     in
                     stmt
                       (If (test, return (string_expr name), string_chain rest))
               in
               let fdecl : fundecl =
                 { name = qname;
                   loc;
                   return = { ty = String; location = loc };
                   params;
                   body = Some [ string_chain enum_items ];
                   is_label = false;
                   is_lambda = false;
                   is_private = false;
                   index = None;
                   class_name = None;
                   class_index = None }
               in
               if not (Hashtbl.mem ctx.functions qname) then
                 if Ain.version_gte ctx.ain (12, 0) then
                   Hashtbl.set ctx.functions ~key:qname ~data:fdecl
                 else (
                 let ain_f =
                   Ain.add_function
                     ~nr_args:(List.length params) ctx.ain qname
                 in
                 fdecl.index <- Some ain_f.index;
                 Hashtbl.set ctx.functions ~key:qname ~data:fdecl;
                 write_signature qname fdecl))
  end

(* Pre-scan all top-level decls to populate [ctx.interface_names]
   before the main visit, so [expand_struct_decls] can correctly
   identify IFace-typed members regardless of whether the interface
   is declared before or after the class that uses it (Rance10's
   classes.jaf declares [class CASActivityUserComponent] before
   [interface IUserComponent], so a single-pass approach misses
   the connection). *)
let pre_scan_interface_names ctx decls =
  List.iter decls ~f:(function
    | StructDef s when not s.is_class ->
        Hashtbl.set ctx.interface_names ~key:s.name ~data:()
    | StructDef s when s.is_class
                       && not (List.is_empty s.interfaces)
                       && Ain.version_gte ctx.ain (12, 0) ->
        (* Pre-register classes that implement interfaces so
           jaf_to_ain_type can encode their refs as dt=89 (IFace)
           even when the StructDef itself is processed later. *)
        Hashtbl.set ctx.iface_compatible_classes ~key:s.name ~data:()
    | DelegateDef f ->
        (* Pre-register delegate names (just names; real registration
           into ctx.delegates happens later in DelegateDef visitor). *)
        Hashtbl.set ctx.delegate_names ~key:f.name ~data:()
    | _ -> ())

(* Walk a single jaf file's decls and collect, for each interface
   StructDef, the set of method-name suffixes it declares (e.g. for
   `IButtonParts { void Foo(); int Bar::get(); }` -> {"Foo", "Bar::get"}). *)
let collect_interface_methods_in_file (acc : (string, string list) Hashtbl.t)
    (decls : declaration list) =
  List.iter decls ~f:(function
    | StructDef s when not s.is_class ->
        let methods =
          List.filter_map s.decls ~f:(function
            | Method f -> Some f.name
            | _ -> None)
        in
        let existing =
          Hashtbl.find acc s.name |> Option.value ~default:[]
        in
        Hashtbl.set acc ~key:s.name ~data:(existing @ methods)
    | _ -> ())

(* v11+ interface inheritance dedup. Source jaf for v12 lists all
   inherited methods inline (decompiler-expanded), so a derived
   interface like [IButtonParts] declares all 207 IParts methods plus
   its own 31. Original Rance10 only emits the 31 own ones; inherited
   stay registered under the parent interface (IParts) namespace.

   Heuristic: for each interface I, find the largest other interface
   I' (>= 50 methods) such that at least 90% of I''s methods are also
   in I — I' is treated as ancestor. I's "inherited" methods = the
   overlap with I'. Those get registered ONLY for I' (not for I).
   [ctx.interface_parent] records I -> I' so member-lookup fallback
   in TypeAnalysis can walk the chain when [Class@Method] isn't
   directly registered. *)
let compute_interface_inheritance ctx
    (all_iface_methods : (string, string list) Hashtbl.t) =
  let to_set methods =
    let s = Hashtbl.create (module String) in
    List.iter methods ~f:(fun m -> Hashtbl.set s ~key:m ~data:());
    s
  in
  let sets =
    Hashtbl.map all_iface_methods ~f:to_set
  in
  (* Conservative rule: only treat [IParts] as the ancestor of other
     [I*Parts] interfaces. Original Rance10's I*Parts hierarchy
     genuinely descends from IParts (e.g. IButtonParts contains all
     of IParts's methods plus its own button-specific ones in the
     decomp'd source); other inter-interface method overlaps are
     coincidental (different interfaces share property names like
     [Core::get] without being in an inheritance relationship).
     A broader heuristic would over-mark legitimate own-methods as
     inherited and they'd disappear from the FUNC table. *)
  let iparts_methods = Hashtbl.find sets "IParts" in
  Hashtbl.iteri sets ~f:(fun ~key:i_name ~data:i_methods ->
      if not (String.equal i_name "IParts") then
        match iparts_methods with
        | None -> ()
        | Some anc ->
            let i_size = Hashtbl.length i_methods in
            let o_size = Hashtbl.length anc in
            if o_size >= 50 && i_size > o_size / 2 then begin
              let overlap =
                Hashtbl.fold anc ~init:0 ~f:(fun ~key ~data:_ acc ->
                    if Hashtbl.mem i_methods key then acc + 1 else acc)
              in
              if overlap * 10 >= o_size * 8 then begin
                (* >= 80% of IParts is in this interface → it's a descendant. *)
                Hashtbl.set ctx.interface_parent ~key:i_name ~data:"IParts";
                let inherited = Hashtbl.create (module String) in
                Hashtbl.iter_keys anc ~f:(fun m ->
                    if Hashtbl.mem i_methods m then
                      Hashtbl.set inherited ~key:m ~data:());
                Hashtbl.set ctx.interface_inherited_methods
                  ~key:i_name ~data:inherited
              end
            end)

let register_type_declarations ctx decls =
  pre_scan_interface_names ctx decls;
  let visitor = new type_declare_visitor ctx in
  visitor#visit_toplevel decls;
  if Ain.version_gte ctx.ain (12, 0)
     && !(ctx.v12_reference_delegate_cursor) > 0
  then visitor#drain_reference_array_delegates

(* v12 interface methods are prototype-only (no body), so the index-
   allocation branch in [type_declare_visitor#visit_fundecl] (which
   gates on [Option.is_some decl.body]) is skipped. They stay in
   [ctx.functions] with [index = None] — and member-resolution then
   trips on [Option.value_exn f.index]. Walk all registered functions
   after the file's pass and allocate slots for any still-missing
   indices so subsequent calls can resolve. *)
let allocate_missing_function_indices ctx =
  let alloc (f : fundecl) =
    let needs_alloc =
      match f.index with
      | None -> true
      | Some i when i < 0 -> true
      | _ -> false
    in
    if needs_alloc then (
      (* v12 overload allocation: use [mangled_name] which produces
         [Class@method] for class-body methods AND [Class::method] for
         top-level namespace functions (detected by [f.name] already
         starting with [class_name::]). *)
      let qname = mangled_name f in
      let ain_f =
        Ain.add_function ~nr_args:(List.length f.params) ctx.ain qname
      in
      f.index <- Some ain_f.index)
  in
  if Ain.version_gte ctx.ain (12, 0) then
    Ain.struct_iter ctx.ain ~f:(fun (s : Ain.Struct.t) ->
        if Hashtbl.mem ctx.interface_names s.name then
          Hashtbl.find ctx.v12_struct_methods s.name
          |> Option.iter ~f:(List.iter ~f:alloc));
  Hashtbl.iter ctx.functions ~f:(fun f ->
      if not (Ain.version_gte ctx.ain (12, 0) && f.is_lambda) then alloc f);
  Hashtbl.iter ctx.overloads ~f:(fun fs ->
      List.iter fs ~f:(fun f ->
          if not (Ain.version_gte ctx.ain (12, 0) && f.is_lambda) then
            alloc f));
  (* Also allocate for property getter/setter fundecls referenced from
     struct definitions — they may not have entries in ctx.functions
     (e.g. interface property accessors synthesized from method pairs). *)
  Hashtbl.iter ctx.structs ~f:(fun s ->
      let alloc_property_accessor (f : fundecl) =
        let key = s.name ^ "@" ^ f.name in
        if Option.is_none f.body
           && Hashtbl.mem ctx.user_bodied_accessors key
        then
          match Hashtbl.find ctx.functions key with
          | Some impl when Option.is_some impl.index ->
              f.index <- impl.index
          | _ -> alloc f
        else alloc f
      in
      Hashtbl.iter s.properties ~f:(fun (p : property_info) ->
          Option.iter p.prop_getter ~f:alloc_property_accessor;
          Option.iter p.prop_setter ~f:alloc_property_accessor));
  if Ain.version_gte ctx.ain (12, 0) then
    Queue.iter ctx.v12_pending_lambdas ~f:alloc

(* Write the full signature (return type + var types) for every
   registered function whose ain slot has a default Void/0/0 form —
   primarily v12 interface prototype methods (body-less Method
   decls) whose [Ain.add_function] allocated a slot but
   [visit_fundecl] never reached [jaf_to_ain_function] (gated on
   [Option.is_some decl.body]).

   Must run AFTER type resolution so [f.return.ty] / [f.params[].
   type_spec.ty] are concrete [Struct (name, idx)] etc. rather than
   [Unresolved name].

   Without this, interface prototype methods carry [dt=0 Void] in
   the FUNC entry's return type field instead of their declared
   return (e.g. [string IButtonParts@CGName::get] has dt=12). The VM
   may validate these at load. *)
let write_interface_method_signatures ctx =
  let v12_enum_parse_return_type (f : fundecl) =
    if Ain.version_gte ctx.ain (12, 0) then
      match (String.chop_suffix f.name ~suffix:"::Parse", f.params) with
      | Some enum_name, [ { type_spec = { ty = (String | Int); _ }; _ } ] ->
          Option.map (Ain.get_enum ctx.ain enum_name) ~f:(fun enum_idx ->
              Ain.Type.Option (Ain.Type.Enum2 enum_idx))
      | _ -> None
    else None
  in
  let write_sig (f : fundecl) =
    match f.index with
    | None | Some -1 | Some -2 -> ()
    | Some idx ->
        let ain_f = Ain.get_function_by_index ctx.ain idx in
        let is_void_default =
          match ain_f.return_type with
          | Ain.Type.Void when ain_f.nr_args = 0 && List.is_empty ain_f.vars ->
              true
          | _ -> false
        in
        (* [allocate_missing_function_indices] passes [~nr_args:N] to
           [Ain.add_function], which sets [nr_args=N] but leaves [vars=[]].
           The VM then reads [nr_args] variable entries from a NULL pointer
           on load — observed crash signature [0x609F15 NULL+0x34]. Treat
           this shape as also needing a signature write. *)
        let nr_args_without_vars =
          ain_f.nr_args > 0 && List.is_empty ain_f.vars
        in
        (* Only write if the slot currently has default shape AND the source
           decl says something else. Skip functions whose source signature
           is genuinely [void Foo(void)] — those are correct as-is. *)
        let source_is_void =
          (match f.return.ty with Void -> true | _ -> false)
          && List.is_empty f.params
        in
        (match v12_enum_parse_return_type f with
        | Some return_type ->
            let updated = jaf_to_ain_function ~ctx f ain_f in
            Ain.write_function ctx.ain { updated with return_type }
        | None ->
        if (is_void_default || nr_args_without_vars) && not source_is_void then
          try
            let updated = jaf_to_ain_function ~ctx f ain_f in
            Ain.write_function ctx.ain updated
          with _ -> ())
  in
  Hashtbl.iter ctx.functions ~f:write_sig;
  Hashtbl.iter ctx.overloads ~f:(fun fs -> List.iter fs ~f:write_sig);
  Hashtbl.iter ctx.v12_struct_methods ~f:(fun fs -> List.iter fs ~f:write_sig);
  Hashtbl.iter ctx.structs ~f:(fun s ->
      Hashtbl.iter s.properties ~f:(fun (p : property_info) ->
          Option.iter p.prop_getter ~f:write_sig;
          Option.iter p.prop_setter ~f:write_sig))

(* v12 member-initval / array-literal desugar.

   The compiler historically ignored class-member initializers (codegen
   had a `MemberDecl _ -> () (* TODO: member initvals? *)` arm). v12
   source uses them extensively, including array literals like
   `array@float ZoomTable = [0.25, 0.5, 1.0, 2.0, 5.0];`. Rather than
   teach codegen about per-member init, we rewrite each member with an
   initval into:

     - the same member with [initval = None]
     - one or more statements injected at the head of every constructor
       body: `this.field = e;` for scalars, a sequence of
       `this.field.PushBack(elem);` for array literals.

   If the class has no explicit constructor, we don't synthesize one
   here — [ArrayInit.visitor] later generates a [Class@0] / [Class@2]
   init function and routes through [insert_array_initializer_call],
   so the simplest thing is to leave the init stmts hanging off the
   member and let that pass pick them up. We do this by stashing the
   init stmts on a per-struct sidecar: [ctx.member_init_stmts]. The
   ArrayInit pass appends them to whichever initializer it generates.

   Local-variable array literals (`array@int xs = [1, 2];`) are
   desugared the same way: rewrite into a no-init declaration plus a
   sequence of [xs.PushBack(...)] expression statements inserted in the
   containing block. *)

let dummy_loc = dummy_location

let make_member_init_stmts (var : variable) (init : expression) :
    statement list =
  let loc = init.loc in
  let this_e = { node = This; ty = Untyped; loc } in
  let target =
    { node = Member (this_e, var.name, UnresolvedMember); ty = Untyped; loc }
  in
  match init.node with
  | ArrayLiteral elems ->
      let free =
        let free_member =
          { node = Member (target, "Free", UnresolvedMember);
            ty = Untyped; loc }
        in
        let call =
          { node = Call (free_member, [], UnresolvedCall);
            ty = Untyped; loc }
        in
        { node = Expression call; delete_vars = []; loc }
      in
      free
      :: List.map elems ~f:(fun e ->
          let pb =
            { node = Member (target, "PushBack", UnresolvedMember);
              ty = Untyped; loc }
          in
          let call =
            { node = Call (pb, [ Some e ], UnresolvedCall);
              ty = Untyped; loc }
          in
          { node = Expression call; delete_vars = []; loc })
  | _ ->
      let asg =
        { node = Assign (EqAssign, target, init); ty = Untyped; loc }
      in
      [ { node = Expression asg; delete_vars = []; loc } ]

let make_local_init_stmts (var : variable) (init : expression) :
    statement list =
  let loc = init.loc in
  let target =
    { node = Ident (var.name, UnresolvedIdent); ty = Untyped; loc }
  in
  match init.node with
  | ArrayLiteral elems ->
      List.map elems ~f:(fun e ->
          let pb =
            { node = Member (target, "PushBack", UnresolvedMember);
              ty = Untyped; loc }
          in
          let call =
            { node = Call (pb, [ Some e ], UnresolvedCall);
              ty = Untyped; loc }
          in
          { node = Expression call; delete_vars = []; loc })
  | _ -> []  (* non-array local initvals are already handled by codegen *)

(* Walk a block-item list. For any [Declarations] whose vars carry an
   ArrayLiteral initval, strip the initval and inject PushBack statements
   immediately after the declaration. *)
let rec desugar_local_initvals_in_stmts (stmts : statement list) :
    statement list =
  List.concat_map stmts ~f:(fun s ->
      match s.node with
      | Declarations ds ->
          let injected = ref [] in
          let cleaned_vars =
            List.map ds.vars ~f:(fun v ->
                (* Skip compiler-internal vars (foreach desugar
                   containers, etc.) — they carry ArrayLiteral initvals
                   that the foreach lowering relies on; stripping them
                   would break the loop. *)
                if String.is_prefix v.name ~prefix:"<" then v
                else
                  match v.initval with
                  | Some ({ node = ArrayLiteral _; _ } as init)
                    when (match v.type_spec.ty with
                         | Array _ | Ref (Array _) -> false
                         | _ -> true) ->
                      injected := !injected @ make_local_init_stmts v init;
                      { v with initval = None }
                  | _ -> v)
          in
          let new_ds = { ds with vars = cleaned_vars } in
          let new_decl =
            { s with node = Declarations new_ds }
          in
          new_decl :: !injected
      | Compound inner ->
          [ { s with node = Compound (desugar_local_initvals_in_stmts inner) } ]
      | If (test, t, e) ->
          [ { s with node =
                If (test,
                    desugar_local_initvals_in_stmt t,
                    desugar_local_initvals_in_stmt e) } ]
      | While (test, body) ->
          [ { s with node = While (test, desugar_local_initvals_in_stmt body) } ]
      | DoWhile (test, body) ->
          [ { s with node = DoWhile (test, desugar_local_initvals_in_stmt body) } ]
      | For (init, test, inc, body) ->
          [ { s with node =
                For (init, test, inc, desugar_local_initvals_in_stmt body) } ]
      | Switch (e, body) ->
          [ { s with node =
                Switch (e, desugar_local_initvals_in_stmts body) } ]
      | _ -> [ s ])

and desugar_local_initvals_in_stmt (s : statement) : statement =
  match desugar_local_initvals_in_stmts [ s ] with
  | [ one ] -> one
  | many -> { s with node = Compound many }

let desugar_local_initvals_in_fundecl (f : fundecl) =
  f.body <-
    Option.map f.body ~f:desugar_local_initvals_in_stmts

(* Strip member initvals and inject into every constructor body. If
   the struct has NO constructor, leave initvals in place so
   [ArrayInit.visit_struct_decl] picks them up when generating
   [Class@0]. Without that, classes like [class AdvModeInfo { bool
   IsSkipMode = false; }] (no ctor) would lose the [= false] and the
   STRT entry's [constructor = -1] crashes the VM on [new]. *)
let desugar_struct_member_initvals ~v12 (s : structdecl) =
  let has_ctor =
    List.exists s.decls ~f:(function Constructor _ -> true | _ -> false)
  in
  if (not has_ctor) || v12 then ()
    (* leave initvals for ArrayInit to handle *)
  else
    let collected = ref [] in
    let new_decls =
      List.map s.decls ~f:(function
        | MemberDecl ds ->
            let cleaned =
              List.map ds.vars ~f:(fun v ->
                  match v.initval with
                  | None -> v
                  | Some init ->
                      collected := !collected @ make_member_init_stmts v init;
                      { v with initval = None })
            in
            MemberDecl { ds with vars = cleaned }
        | other -> other)
    in
    if not (List.is_empty !collected) then (
      let init_stmts = !collected in
      let injected_ctors =
        List.map new_decls ~f:(function
          | Constructor f ->
              (match f.body with
               | None -> Constructor f
               | Some body ->
                   Constructor { f with body = Some (init_stmts @ body) })
          | other -> other)
      in
      s.decls <- injected_ctors
    ) else s.decls <- new_decls

let desugar_initvals ~v12 decls =
  List.iter decls ~f:(function
    | Function f | FuncTypeDef f | DelegateDef f ->
        desugar_local_initvals_in_fundecl f
    | StructDef s ->
        desugar_struct_member_initvals ~v12 s;
        List.iter s.decls ~f:(function
          | Method f | Constructor f | Destructor f ->
              desugar_local_initvals_in_fundecl f
          | _ -> ())
    | _ -> ())
  [@@warning "-26-27"]

let _ = dummy_loc

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
  let record_ref name =
    Hashtbl.set ctx.properties_with_backing_ref ~key:name ~data:()
  in
  let record_nullable_ref name =
    Hashtbl.set ctx.nullable_ref_properties ~key:name ~data:()
  in
  (* Walk a user-bodied accessor body looking for [this.<X>] references —
     i.e. [Member(This, "<X>", _)] expressions. Each such reference marks
     [class_name@X] as needing the backing field emitted. Original v12
     elides the [<X>] field when no accessor body references it; emitting
     it anyway shifts struct member offsets and crashes the VM at load. *)
  let accessor_is_event = ref false in
  let rec scan_expr class_name (e : expression) =
    let record_nullable_member name =
      record_nullable_ref (class_name ^ "@" ^ name)
    in
    let is_this_member (e : expression) =
      match e with
      | { node = Member ({ node = This; _ }, name, _); _ } -> Some name
      | _ -> None
    in
    match e.node with
    | Member ({ node = This; _ }, name, _)
      when String.length name >= 2
           && Char.equal name.[0] '<'
           && Char.equal name.[String.length name - 1] '>' ->
        let prop = String.sub name ~pos:1 ~len:(String.length name - 2) in
        record_ref (class_name ^ "@" ^ prop)
    | Member ({ node = This; _ }, name, _)
      when !accessor_is_event && Ain.version_gte ctx.ain (12, 0) ->
        (* v12 event accessors only: bare [this.EventName] reference
           (e.g. [this.MyEvent += value]) needs the [<EventName>]
           backing kept. But if [name] is a computed property with a
           user-bodied get (e.g. [this.FuncSet?.X] where FuncSet is a
           getter), accessing [this.name] invokes the getter — no
           backing needed. Skip recording in that case. *)
        let has_user_getter =
          Hashtbl.mem ctx.user_bodied_accessors
            (class_name ^ "@" ^ name ^ "::get")
        in
        if not has_user_getter then
          record_ref (class_name ^ "@" ^ name)
    | ConstInt _ | ConstFloat _ | ConstChar _ | ConstString _ | Ident _
    | FuncAddr _ | MemberAddr _ | This | Null ->
        ()
    | Unary (_, e) | Cast (_, e) | DummyRef (_, e) | RvalueRef e ->
        scan_expr class_name e
    | Assign (EqAssign, ({ node = Member ({ node = This; _ }, name, _); _ } as a),
        ({ node = Null; _ } as b)) ->
        record_nullable_member name;
        scan_expr class_name a;
        scan_expr class_name b
    | Binary ((Equal | NEqual | RefEqual | RefNEqual), a, b) -> (
        (match (is_this_member a, b.node) with
         | Some name, Null -> record_nullable_member name
         | _ -> ());
        (match (a.node, is_this_member b) with
         | Null, Some name -> record_nullable_member name
         | _ -> ());
        scan_expr class_name a;
        scan_expr class_name b)
    | Binary (_, a, b) | Assign (_, a, b) | Seq (a, b) | NullCoalesce (a, b)
    | Subscript (a, b) ->
        scan_expr class_name a;
        scan_expr class_name b
    | Ternary (a, b, c) ->
        scan_expr class_name a;
        scan_expr class_name b;
        scan_expr class_name c
    | OptionalMember ({ node = This; _ } as obj, name, _) ->
        record_nullable_member name;
        scan_expr class_name obj
    | OptionalMember
        (({ node = Member ({ node = This; _ }, name, _); _ } as obj), _, _) ->
        record_nullable_member name;
        scan_expr class_name obj
    | OptionalMember (obj, _, _) | Member (obj, _, _) ->
        scan_expr class_name obj
    | Call (f, args, _) ->
        scan_expr class_name f;
        List.iter args ~f:(Option.iter ~f:(scan_expr class_name))
    | New _ -> ()
    | NewCall (_, args) ->
        List.iter args ~f:(Option.iter ~f:(scan_expr class_name))
    | ArrayLiteral elems -> List.iter elems ~f:(scan_expr class_name)
    | Lambda fd ->
        (* Lambda bodies belong to a different scope but may still
           dispatch through the enclosing [this]. Walk them too. *)
        Option.iter fd.body ~f:(List.iter ~f:(scan_stmt class_name))
  and scan_stmt class_name (s : statement) =
    match s.node with
    | EmptyStatement | Label _ | Goto _ | Continue | Break | Default
    | Jump _ | Message _ ->
        ()
    | Declarations ds ->
        List.iter ds.vars ~f:(fun v ->
            List.iter v.array_dim ~f:(scan_expr class_name);
            Option.iter v.initval ~f:(scan_expr class_name))
    | Expression e | Case e | Jumps e -> scan_expr class_name e
    | Compound stmts | Switch (_, stmts) ->
        List.iter stmts ~f:(scan_stmt class_name)
    | If (test, cons, alt) ->
        scan_expr class_name test;
        scan_stmt class_name cons;
        scan_stmt class_name alt
    | While (test, body) | DoWhile (test, body) ->
        scan_expr class_name test;
        scan_stmt class_name body
    | For (init, test, inc, body) ->
        scan_stmt class_name init;
        Option.iter test ~f:(scan_expr class_name);
        Option.iter inc ~f:(scan_expr class_name);
        scan_stmt class_name body
    | ForEach (_, _, _, arr, body) ->
        scan_expr class_name arr;
        scan_stmt class_name body
    | Return e -> Option.iter e ~f:(scan_expr class_name)
    | RefAssign (a, b) | ObjSwap (a, b) ->
        scan_expr class_name a;
        scan_expr class_name b
  in
  let scan_fundecl_body (f : fundecl) =
    Option.iter f.body ~f:(fun body ->
        let class_name =
          match f.class_name with
          | Some class_name -> Some class_name
          | None -> (
              match Util.parse_qualified_name f.name with
              | Some class_name, _ -> Some class_name
              | None, _ -> None)
        in
        Option.iter class_name ~f:(fun class_name ->
            List.iter body ~f:(scan_stmt class_name)))
  in
  List.iter decls ~f:(function
    | Function f when Option.is_some f.body -> (
        scan_fundecl_body f;
        match Util.parse_qualified_name f.name with
        | Some qual, accessor
          when String.equal accessor "get"
               || String.equal accessor "set"
               || String.equal accessor "add"
               || String.equal accessor "remove" -> (
            match Util.parse_qualified_name qual with
            | Some class_name, prop_name ->
                record (class_name ^ "@" ^ prop_name ^ "::" ^ accessor);
                accessor_is_event :=
                  String.equal accessor "add"
                  || String.equal accessor "remove";
                Option.iter f.body ~f:(List.iter ~f:(scan_stmt class_name));
                accessor_is_event := false
            | None, _ -> ())
        | _ -> ())
    | StructDef s ->
        let has_ctor = ref false in
        let has_default_ctor = ref false in
        List.iter s.decls ~f:(function
          | Constructor f ->
              has_ctor := true;
              if List.is_empty f.params then has_default_ctor := true;
              scan_fundecl_body f
          | Method f | Destructor f -> scan_fundecl_body f
          | _ -> ())
        ;
        if !has_ctor then
          Hashtbl.set ctx.structs_with_constructor ~key:s.name ~data:();
        if !has_default_ctor then
          Hashtbl.set ctx.structs_with_default_constructor ~key:s.name ~data:()
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
                  if Hashtbl.mem ctx.enum_types name then
                    Enum (name, Ain.add_enum ctx.ain name)
                  else
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
         let parent_is_namespace =
           match self#env#current_function with
           | Some parent when Ain.version_gte ctx.ain (12, 0) ->
               is_v12_namespace_function parent
           | _ -> false
         in
         if not parent_is_namespace then
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
          (* v12 enums are registered in [type_declare_visitor]; nothing
             to resolve at this stage (their value bodies are constant
             ints already). *)
          ());
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
        Ain.write_function ctx.ain (jaf_to_ain_function ~ctx f obj)

    method! visit_declaration decl =
      super#visit_declaration decl;
      match decl with
      | Global ds ->
          List.iter ds.vars ~f:(fun g ->
              if not g.is_const then
                Ain.set_global_type ctx.ain g.name
                  (jaf_to_ain_type ~ctx g.type_spec.ty))
      | GlobalGroup gg ->
          List.iter gg.vardecls ~f:(fun ds ->
              self#visit_declaration (Global ds))
      | Function f ->
          (* v1 scenario labels have no FUNC table entry to define. *)
          if not (f.is_label && Ain.version ctx.ain = 1) then
            let obj =
              Ain.get_function_by_index ctx.ain (Option.value_exn f.index)
            in
            Ain.write_function ctx.ain (jaf_to_ain_function ~ctx f obj)
      | FuncTypeDef f -> jaf_to_ain_functype ~ctx f |> Ain.write_functype ctx.ain
      | DelegateDef f -> jaf_to_ain_functype ~ctx f |> Ain.write_delegate ctx.ain
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
          (* v12 interfaces are modeled as classes whose methods are
             all prototype-only (no body). Skip the definition-presence
             check in that case — interface stubs are expected to be
             unimplemented at the declaration site. *)
          let any_method_has_body =
            List.exists s.decls ~f:(function
              | Method f | Constructor f | Destructor f ->
                  Option.is_some f.body
              | _ -> false)
          in
          List.iter s.decls ~f:(function
            | Method f | Constructor f | Destructor f ->
                if any_method_has_body
                   && Option.is_none f.index
                   && (not (is_event_accessor_stub f))
                   && not (is_user_bodied_property_stub f)
                then
                  compile_error
                    (Printf.sprintf "No definition of %s::%s found" s.name
                       f.name)
                    (ASTDeclaration (Function f))
            | _ -> ());
          match Ain.get_struct ctx.ain s.name with
          | Some obj ->
              Ain.write_struct ctx.ain (jaf_to_ain_struct ~ctx s obj)
          | None -> compiler_bug "undefined struct" (Some (ASTDeclaration decl))
          )
      | Enum _ ->
          (* v12 enums: nothing to define in the .ain — values are
             constant ints, registered in [ctx.enum_values] earlier. *)
          ()
  end

(* v12 [class X implements I1, I2 { ... }]: the parser stores the
   interface names in [structdecl.interfaces]; this pass resolves each
   name to a struct index and writes them to the .ain struct so that
   interface subtyping checks (see [TypeAnalysis.is_interface_compatible])
   and runtime virtual dispatch find the right slots. Runs after all
   structs are registered so forward-referenced interface names resolve. *)
let resolve_interface_lists ctx decls =
  List.iter decls ~f:(function
    | StructDef s when not (List.is_empty s.interfaces) -> (
        match Ain.get_struct ctx.ain s.name with
        | None -> ()
        | Some ain_s ->
            let interfaces =
              List.filter_map s.interfaces ~f:(fun iface_name ->
                  match Ain.get_struct ctx.ain iface_name with
                  | Some i ->
                      Some
                        { Ain.Struct.struct_type = i.index;
                          vtable_offset = 0 }
                  | None -> None)
            in
            Ain.write_struct ctx.ain { ain_s with interfaces })
    | _ -> ())

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
