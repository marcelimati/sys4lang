(* Copyright (C) 2024 kichikuou <KichikuouChrome@gmail.com>
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
open Loc

let collect_lambdas lambdas parent body =
  let acc = ref [] in
  Ast.walk body ~expr_cb:(function
    | BoundMethod (_, ({ kind = Lambda; _ } as f)) ->
        let f = Hashtbl.find_exn lambdas f.id in
        f.CodeSection.parent <- Some parent;
        acc := f :: !acc
    | _ -> ());
  List.rev !acc

let rec decompile_function ~lambdas (f : CodeSection.function_t) =
  let struc = match f.owner with Some (Struct s) -> Some s | _ -> None in
  let body =
    BasicBlock.create f
    |> BasicBlock.generate_var_decls f.func
    |> ControlFlow.analyze
    |> BasicBlock.prepend_var_decls f.func
    |> (new TypeAnalysis.analyzer f.func struc)#analyze_statement
    |> Transform.apply_all_transforms
  in
  let lambdas =
    collect_lambdas lambdas f body |> List.map ~f:(decompile_function ~lambdas)
  in
  CodeGen.{ func = f.func; struc; name = f.name; body; lambdas }

let rec inspect_function (f : CodeSection.function_t) ~lambdas ~print_addr =
  let struc = match f.owner with Some (Struct s) -> Some s | _ -> None in
  BasicBlock.create f
  |> (fun bbs ->
  Stdio.printf "BasicBlock representation:\n%s\n\n"
    ([%show: BasicBlock.t list] bbs);
  bbs)
  |> BasicBlock.generate_var_decls f.func
  |> ControlFlow.analyze
  |> BasicBlock.prepend_var_decls f.func
  |> (fun stmt ->
  Stdio.printf "\nAST representation:\n%s\n" ([%show: Ast.statement loc] stmt);
  stmt)
  |> (new TypeAnalysis.analyzer f.func struc)#analyze_statement
  |> Transform.apply_all_transforms
  |> fun body ->
  let printer = new CodeGen.code_printer ~print_addr "" in
  let lambdas =
    collect_lambdas lambdas f body
    |> List.map ~f:(inspect_function ~lambdas ~print_addr)
  in
  let func = CodeGen.{ func = f.func; struc; name = f.name; body; lambdas } in
  printer#print_function func;
  Stdio.printf "\nDecompiled code:\n%s\n" (Buffer.contents printer#get_buffer);
  func

let to_variable_list vars =
  List.map (Array.to_list vars) ~f:CodeGen.from_ain_variable

type analyzed_initializer_function = {
  is_empty : bool;
  vtable : int array option;
  vars : CodeGen.variable list;
}

let analyze_initializer_function stmt vars =
  let stmts =
    match stmt with
    | { txt = Ast.Block stmts; _ } -> List.rev stmts
    | _ -> [ stmt ]
  in
  let h_dims = Stdlib.Hashtbl.create (Array.length vars) in
  let h_initvals = Stdlib.Hashtbl.create (Array.length vars) in
  let vtable = ref [||] in
  List.iter stmts ~f:(function
    | {
        txt =
          Expression (Call (Builtin (Instructions.A_ALLOC, Var (_, v)), dims));
        _;
      } ->
        Stdlib.Hashtbl.add h_dims v dims
    | {
        txt =
          Expression
            (Call
               ( HllFunc ("Array", { name = "Alloc"; _ }),
                 Load (Var (_, v)) :: dims ));
        _;
      } -> (
        let dims =
          List.take_while dims ~f:(function Number -1l -> false | _ -> true)
        in
        match (v.name, dims) with
        | "<vtable>", [ Number len ] ->
            vtable := Array.create ~len:(Int32.to_int_exn len) (-1)
        | _ -> Stdlib.Hashtbl.add h_dims v dims)
    | {
        txt =
          Expression
            (AssignOp
               (ASSIGN, Elem (Load (Var (StructPage, v)), Number i), Number m));
        _;
      }
      when String.equal v.name "<vtable>" ->
        !vtable.(Int32.to_int_exn i) <- Int32.to_int_exn m
    | {
        txt = Expression (AssignOp (_, Var ((StructPage | GlobalPage), v), e));
        _;
      }
      when Ain.ain.vers >= 12 ->
        Stdlib.Hashtbl.add h_initvals v e
    | stmt ->
        Printf.failwithf "unexpected statement in initializer function: %s"
          (Ast.show_statement stmt.txt)
          ());
  {
    is_empty = List.is_empty stmts;
    vars =
      List.map (Array.to_list vars) ~f:(fun v ->
          let var = CodeGen.from_ain_variable v in
          {
            var with
            dims =
              (match Stdlib.Hashtbl.find_opt h_dims v with
              | None -> var.dims
              | Some dims -> dims);
            initval =
              Option.first_some
                (Stdlib.Hashtbl.find_opt h_initvals v)
                var.initval;
          });
    vtable = (if Array.is_empty !vtable then None else Some !vtable);
  }

let extract_enum_values = function
  | Ast.Return (Some e) ->
      let rec extract = function
        | Ast.TernaryOp (BinaryOp (EQUALE, _, EnumValue (_, n)), String s, rest)
          ->
            (s, n) :: extract rest
        | String "" -> []
        | _ -> failwith "unexpected expression in enum stringifier"
      in
      extract e
  | _ -> failwith "unexpected statement in enum stringifier"

type decompiled_ain = {
  structs : CodeGen.struct_t array;
  globals : CodeGen.variable list;
  global_lambdas : CodeGen.function_t list;
  enums : CodeGen.enum_t array;
  srcs : (string * CodeGen.function_t list) list;
  ain_minor_version : int;
}

(* Ain 6 minor versions:
   - 6.0: Alice 2010, Shaman's Sanctuary, Daiteikoku, Rance Quest
   - 6.10 (DELG introduced): Oyako Rankan, Pastel Chime 3, Drapeko, Rance 01
   - 6.20 (MSG1 introduced): Rance 9, Blade Briders
   - 6.30 (SH_LOCALREF and other instructions removed): Evenicle, Rance 03 *)
let determine_ain_minor_version code =
  let has_sh_localref code =
    List.exists code ~f:(function
      | { txt = Instructions.SH_LOCALREF _; _ } -> true
      | _ -> false)
  in
  if Ain.ain.vers <> 6 then 0
  else if Array.is_empty Ain.ain.delg then 0
  else if Option.is_none Ain.ain.msg1_uk then 10
  else if has_sh_localref code then 20
  else 30

let is_rance7_bad_function (f : CodeGen.function_t) =
  match f with
  | {
      struc = Some {name = "tagBusho"; _};
      name = "getSp";
      body = { txt = (Block [{txt = Return (Some (Load (Var (StructPage, {name = "m_sName"; _ })))); _ }]); _ }; _
    } -> true
  | _ -> false
[@@ocamlformat "disable"]

let process_generated_constructors (structs : CodeGen.struct_t array)
    (parsed : CodeSection.t) =
  {
    parsed with
    files =
      List.map parsed.files ~f:(fun (fname, funcs) ->
          let funcs =
            List.filter funcs ~f:(fun func ->
                match func with
                | {
                 CodeSection.owner = Some (Struct struc);
                 name = "0" | "2";
                 _;
                } -> (
                    try
                      let f = decompile_function ~lambdas:parsed.lambdas func in
                      let inits =
                        analyze_initializer_function f.body struc.members
                      in
                      if String.equal f.name "2" || not inits.is_empty then (
                        let s = structs.(struc.id) in
                        s.members <- inits.vars;
                        Option.iter inits.vtable ~f:(fun vt ->
                            Ain.ain.strt.(struc.id).vtable <- vt);
                        s.initval_lambdas <- f.lambdas;
                        false)
                      else true
                    with _ -> true)
                | _ -> true)
          in
          (fname, funcs));
  }

(* Ain v1 scenario labels (SLBL section) are not recorded in the FUNC table.
   Each label points to bare code that is a single `CALLFUNC <func>` (no args),
   and the decompiler drops that bare code as junk. Here we synthesize a
   `#name() { Func(); }` label function directly from the SLBL entry and the one
   instruction it points to, then place it right before the called function in
   the same source file. *)
let synthesize_scenario_labels code srcs =
  if Array.is_empty Ain.ain.slbl then srcs
  else begin
    let addr_to_insn = Hashtbl.create (module Int) in
    List.iter code ~f:(fun (insn : Instructions.instruction loc) ->
        Hashtbl.set addr_to_insn ~key:insn.addr ~data:insn.txt);
    let labels_by_func = Hashtbl.create (module Int) in
    Array.iter Ain.ain.slbl ~f:(fun (sl : Ain.ScenarioLabel.t) ->
        let addr = Int32.to_int_exn sl.address in
        let func_id =
          match Hashtbl.find addr_to_insn addr with
          | Some (Instructions.CALLFUNC n) -> n
          | _ ->
              Printf.failwithf
                "scenario label \"%s\" at 0x%x is not a single CALLFUNC" sl.name
                addr ()
        in
        let called = Ain.ain.func.(func_id) in
        if called.nr_args <> 0 then
          Printf.failwithf
            "scenario label \"%s\" calls %s, which takes arguments" sl.name
            called.name ();
        let label_func : Ain.Function.t =
          {
            id = -1;
            address = addr;
            name = sl.name;
            kind = Label;
            capture = false;
            return_type = Void;
            vars = [||];
            nr_args = 0;
            crc = 0l;
          }
        in
        let call =
          {
            txt = Ast.Expression (Call (Function called, []));
            addr;
            end_addr = addr;
          }
        in
        let body = { txt = Ast.Block [ call ]; addr; end_addr = addr } in
        let f =
          CodeGen.
            {
              func = label_func;
              struc = None;
              name = sl.name;
              body;
              lambdas = [];
            }
        in
        Hashtbl.add_multi labels_by_func ~key:func_id ~data:f);
    let srcs =
      List.map srcs ~f:(fun (fname, funcs) ->
          let funcs =
            List.concat_map funcs ~f:(fun (func : CodeGen.function_t) ->
                match Hashtbl.find labels_by_func func.func.id with
                | Some labels ->
                    Hashtbl.remove labels_by_func func.func.id;
                    labels @ [ func ]
                | None -> [ func ])
          in
          (fname, funcs))
    in
    Hashtbl.iter_keys labels_by_func ~f:(fun func_id ->
        Stdio.eprintf
          "Warning: scenario label target function %s not found in output\n"
          Ain.ain.func.(func_id).name);
    srcs
  end
(* Compare two [ain_type]s structurally. [Delegate] / [FuncType] wrap a
   [TypeVar]: two [Delegate]s may point to the same underlying function
   type through different link chains, so [Poly.equal] on the surface
   refs is unreliable. Resolve to the root value and compare by id when
   possible; fall back to [Poly.equal] for everything else. *)
let ain_type_equal (t1 : Type.ain_type) (t2 : Type.ain_type) =
  let tv_id tv =
    match Type.TypeVar.get_value tv with
    | Type.TypeVar.Id (n, _) -> Some n
    | _ -> None
  in
  match (t1, t2) with
  | Type.Delegate a, Type.Delegate b | Type.FuncType a, Type.FuncType b -> (
      match (tv_id a, tv_id b) with
      | Some n, Some n' -> n = n'
      | _ -> false)
  | _ -> Poly.equal t1 t2

(* Detect v11 event method pairs on a struct: methods named
   [Name::add(T)] and [Name::remove(T)] with matching single-parameter
   signatures. Returns [(event_pairs, remaining_methods)]. *)
let extract_event_pairs (methods : CodeGen.function_t list) :
    CodeGen.event_pair list * CodeGen.function_t list =
  let split_accessor name =
    match String.chop_suffix name ~suffix:"::add" with
    | Some base -> Some (base, `Add)
    | None -> (
        match String.chop_suffix name ~suffix:"::remove" with
        | Some base -> Some (base, `Remove)
        | None -> None)
  in
  let adds = Hashtbl.create (module String) in
  let removes = Hashtbl.create (module String) in
  let others = ref [] in
  let ordered_names = ref [] in
  let seen_names = Hash_set.create (module String) in
  let record_name base =
    if not (Hash_set.mem seen_names base) then (
      Hash_set.add seen_names base;
      ordered_names := base :: !ordered_names)
  in
  List.iter methods ~f:(fun (m : CodeGen.function_t) ->
      match split_accessor m.name with
      | Some (base, `Add) ->
          Hashtbl.set adds ~key:base ~data:m;
          record_name base
      | Some (base, `Remove) ->
          Hashtbl.set removes ~key:base ~data:m;
          record_name base
      | None -> others := m :: !others);
  let events = ref [] in
  let unpaired = ref [] in
  List.iter (List.rev !ordered_names) ~f:(fun base ->
      match (Hashtbl.find adds base, Hashtbl.find removes base) with
      | Some add, Some remove -> (
          match
            (Ain.Function.args add.func, Ain.Function.args remove.func)
          with
          | [ a ], [ r ] when ain_type_equal a.type_ r.type_ ->
              events :=
                CodeGen.
                  {
                    ev_name = base;
                    ev_type = a.type_;
                    ev_add = add;
                    ev_remove = remove;
                  }
                :: !events;
              Hashtbl.remove removes base
          | _ -> unpaired := add :: !unpaired)
      | Some add, None -> unpaired := add :: !unpaired
      | None, Some _ -> ()
      | None, None -> ());
  Hashtbl.iter removes ~f:(fun m -> unpaired := m :: !unpaired);
  (!events, List.rev !others @ !unpaired)

(* Detect v11 property method groups on a struct: methods named
   [Name::get] (returning T) and/or [Name::set(T)]. Either may exist
   alone (read-only / write-only). Classified as "auto-implemented"
   when both accessor bodies are the trivial shape reading/writing a
   [<Name>] backing field — those are emitted as [T Name { get; set; }]
   with no implementation block. Returns
   [(property_defs, remaining_methods)]. *)
let extract_property_defs (methods : CodeGen.function_t list) :
    CodeGen.property_def list * CodeGen.function_t list =
  let split_accessor name =
    match String.chop_suffix name ~suffix:"::get" with
    | Some base -> Some (base, `Get)
    | None -> (
        match String.chop_suffix name ~suffix:"::set" with
        | Some base -> Some (base, `Set)
        | None -> None)
  in
  let gets = Hashtbl.create (module String) in
  let sets = Hashtbl.create (module String) in
  let others = ref [] in
  (* Order-preserving set of property names: methods are scanned in
     function-table order, so the first [Name::get] (or [Name::set]
     when get is absent) seen determines the property's position in
     the output. Hashtbl iteration would scramble ordering and shift
     where backing fields land. *)
  let ordered_names = ref [] in
  let seen_names = Hash_set.create (module String) in
  let record_name base =
    if not (Hash_set.mem seen_names base) then (
      Hash_set.add seen_names base;
      ordered_names := base :: !ordered_names)
  in
  List.iter methods ~f:(fun (m : CodeGen.function_t) ->
      match split_accessor m.name with
      | Some (base, `Get) ->
          Hashtbl.set gets ~key:base ~data:m;
          record_name base
      | Some (base, `Set) ->
          Hashtbl.set sets ~key:base ~data:m;
          record_name base
      | None -> others := m :: !others);
  let properties = ref [] in
  List.iter (List.rev !ordered_names) ~f:(fun base ->
      let get = Hashtbl.find gets base in
      let set = Hashtbl.find sets base in
      let prop_type =
        match get with
        | Some g -> g.func.return_type
        | None -> (
            match set with
            | Some s -> (
                match Ain.Function.args s.func with
                | [ p ] -> p.type_
                | _ -> Type.Void)
            | None -> Type.Void)
      in
      let single_stmt body =
        match body with
        | Ast.Block [ s ] -> Some s.txt
        | s -> Some s
      in
      let mangled_field = "<" ^ base ^ ">" in
      let is_trivial_get (g : CodeGen.function_t) =
        match single_stmt g.body.txt with
        | Some (Ast.Return (Some (Ast.Load (Ast.Var (Ast.StructPage, v))))) ->
            String.equal v.name mangled_field
        | _ -> false
      in
      let is_trivial_set (s : CodeGen.function_t) =
        match single_stmt s.body.txt with
        | Some
            (Ast.Expression (Ast.AssignOp (_, Ast.Var (Ast.StructPage, v), _)))
          ->
            String.equal v.name mangled_field
        | _ -> false
      in
      let prop_is_auto =
        match (get, set) with
        | Some g, Some s -> is_trivial_get g && is_trivial_set s
        | Some g, None -> is_trivial_get g
        | None, Some s -> is_trivial_set s
        | None, None -> false
      in
      properties :=
        CodeGen.
          {
            prop_name = base;
            prop_type;
            prop_get = get;
            prop_set = set;
            prop_is_auto;
          }
        :: !properties);
  (List.rev !properties, List.rev !others)

let decompile ~move_to_original_file ~continue_on_error =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let structs =
    Array.map Ain.ain.strt ~f:(fun struc ->
        CodeGen.
          {
            struc;
            members = to_variable_list struc.members;
            methods = [];
            initval_lambdas = [];
            events = [];
            properties = [];
          })
  in
  let global_lambdas = ref [] in
  let CodeSection.{ files; lambdas } =
    let open CodeSection in
    CodeSection.parse code
    |> remove_overridden_functions ~move_to_original_file
    |> fix_or_remove_known_broken_functions
    (* For vtable analysis, generated constructors need to be processed first. *)
    |> process_generated_constructors structs
  in
  let enums =
    Array.map Ain.ain.enum ~f:(fun name -> CodeGen.{ name; values = [] })
  in
  let globals = ref (to_variable_list Ain.ain.glob) in
  let srcs =
    List.map files ~f:(fun (fname, funcs) ->
        let decompiled_funcs = ref [] in
        let process_func func =
          try
            let f = decompile_function ~lambdas func in
            match func with
            | { owner = Some (Enum id); name = "String"; _ } ->
                enums.(id).values <- extract_enum_values f.body.txt
            | { owner = Some (Enum _); _ } -> () (* ignore *)
            | { owner = Some (Struct struc); _ } ->
                let s = structs.(struc.id) in
                let f =
                  if String.equal f.name "0" then
                    {
                      f with
                      body = Transform.remove_generated_initializer_call f.body;
                    }
                  else f
                in
                if is_rance7_bad_function f then
                  Stdio.eprintf
                    "Warning: Removing ill-typed tagBusho::getSp() function\n"
                else (
                  if not (phys_equal f.func.kind Lambda) then
                    s.methods <- f :: s.methods;
                  decompiled_funcs := f :: !decompiled_funcs)
            | { owner = None; name = "0"; _ } ->
                globals :=
                  (analyze_initializer_function f.body Ain.ain.glob).vars;
                global_lambdas := f.lambdas
            | { owner = None; name = "NULL"; _ } -> ()
            | _ -> decompiled_funcs := f :: !decompiled_funcs
          with e ->
            Stdio.eprintf "Error while decompiling function %s\n" func.func.name;
            if continue_on_error then Stdio.eprintf "%s\n" (Exn.to_string e)
            else raise e
        in
        List.iter funcs ~f:process_func;
        (fname, List.rev !decompiled_funcs))
  in
  let srcs = synthesize_scenario_labels code srcs in
  Array.iter structs ~f:(fun s ->
      let methods_in_order = List.rev s.methods in
      let events, after_events = extract_event_pairs methods_in_order in
      let properties, remaining = extract_property_defs after_events in
      s.methods <- remaining;
      s.events <- events;
      s.properties <- properties);
  (* Manual events and non-auto properties round-trip as a single
     top-level block ([event T Class::Name { add{} remove{} }] /
     [T Class::Name { get{} set{} }]) replacing the per-class .jaf's
     pair of qualified-method definitions. Drop the function we DON'T
     keep as the marker. For events the marker is [add]; for non-auto
     properties the marker is [get] (or [set] when get is absent).
     Auto-implemented properties have no implementation block at all,
     so both accessors are dropped. *)
  let dropped_func_ids = Hash_set.create (module Int) in
  Array.iter structs ~f:(fun s ->
      List.iter s.events ~f:(fun (e : CodeGen.event_pair) ->
          Hash_set.add dropped_func_ids e.ev_remove.func.id);
      List.iter s.properties ~f:(fun (p : CodeGen.property_def) ->
          if p.prop_is_auto then (
            Option.iter p.prop_get ~f:(fun g ->
                Hash_set.add dropped_func_ids g.func.id);
            Option.iter p.prop_set ~f:(fun set ->
                Hash_set.add dropped_func_ids set.func.id))
          else
            match (p.prop_get, p.prop_set) with
            | Some _, Some set -> Hash_set.add dropped_func_ids set.func.id
            | _ -> ()));
  let srcs =
    List.map srcs ~f:(fun (fname, funcs) ->
        ( fname,
          List.filter funcs ~f:(fun (f : CodeGen.function_t) ->
              not (Hash_set.mem dropped_func_ids f.func.id)) ))
  in
  let ain_minor_version = determine_ain_minor_version code in
  {
    srcs;
    structs;
    globals = !globals;
    global_lambdas = !global_lambdas;
    enums;
    ain_minor_version;
  }

let inspect funcname ~print_addr =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let structs =
    Array.map Ain.ain.strt ~f:(fun struc ->
        CodeGen.
          {
            struc;
            members = to_variable_list struc.members;
            methods = [];
            initval_lambdas = [];
            events = [];
            properties = [];
          })
  in
  let CodeSection.{ files; lambdas } =
    CodeSection.parse code
    |> CodeSection.remove_overridden_functions ~move_to_original_file:false
    |> process_generated_constructors structs
  in
  match
    List.find_map files ~f:(fun (_, funcs) ->
        List.find funcs ~f:(fun f ->
            String.equal f.CodeSection.func.name funcname))
  with
  | None -> failwith ("cannot find function " ^ funcname)
  | Some f -> inspect_function f ~lambdas ~print_addr |> ignore

let export ~print_addr decompiled ain_path write_to_file =
  let sources = ref [] in
  let dbginfo = CodeGen.create_debug_info () in
  let generate ?(add_to_inc = true) fname f =
    if add_to_inc then sources := fname :: !sources;
    let fname_components = String.split fname ~on:'\\' in
    let unix_fname = String.concat ~sep:"/" fname_components in
    let pr =
      new CodeGen.code_printer
        ~print_addr ~dbginfo ~enums:decompiled.enums unix_fname
    in
    f pr;
    write_to_file unix_fname pr#get_buffer
  in
  generate "constants.jaf" (fun pr -> pr#print_constants);
  generate "classes.jaf" (fun pr ->
      Array.iter decompiled.structs ~f:(fun struc ->
          pr#print_struct_decl struc;
          pr#print_newline);
      Array.iter decompiled.enums ~f:(fun enum ->
          pr#print_enum_decl enum;
          pr#print_newline);
      Array.iter Ain.ain.fnct ~f:(fun ft ->
          pr#print_functype_decl "functype" ft);
      Array.iter Ain.ain.delg ~f:(fun ft ->
          pr#print_functype_decl "delegate" ft));
  generate "globals.jaf" (fun pr ->
      pr#print_globals decompiled.globals decompiled.global_lambdas);
  Array.iter Ain.ain.hll0 ~f:(fun hll ->
      generate ~add_to_inc:false
        ("HLL/" ^ hll.name ^ ".hll")
        (fun pr -> pr#print_hll hll.functions));
  generate "HLL\\hll.inc" (fun pr -> pr#print_hll_inc);
  (* Marker tables: when a function is the kept "marker" of a
     non-auto property / manual event accessor pair, replace its
     normal [print_function] emit with a [T Class::Name { ... }] /
     [event T Class::Name { ... }] block. *)
  let event_by_add_id : (int, CodeGen.event_pair) Hashtbl.t =
    let tbl = Hashtbl.create (module Int) in
    Array.iter decompiled.structs ~f:(fun (s : CodeGen.struct_t) ->
        List.iter s.events ~f:(fun (e : CodeGen.event_pair) ->
            Hashtbl.set tbl ~key:e.ev_add.func.id ~data:e));
    tbl
  in
  let property_by_marker_id : (int, CodeGen.property_def) Hashtbl.t =
    let tbl = Hashtbl.create (module Int) in
    Array.iter decompiled.structs ~f:(fun (s : CodeGen.struct_t) ->
        List.iter s.properties ~f:(fun (p : CodeGen.property_def) ->
            if not p.prop_is_auto then
              match p.prop_get with
              | Some g -> Hashtbl.set tbl ~key:g.func.id ~data:p
              | None ->
                  Option.iter p.prop_set ~f:(fun set ->
                      Hashtbl.set tbl ~key:set.func.id ~data:p)));
    tbl
  in
  List.iter decompiled.srcs ~f:(fun (fname, funcs) ->
      if not (List.is_empty funcs) then
        generate fname (fun pr ->
            List.iter funcs ~f:(fun (func : CodeGen.function_t) ->
                (match Hashtbl.find event_by_add_id func.func.id with
                | Some pair -> pr#print_event_def pair
                | None -> (
                    match Hashtbl.find property_by_marker_id func.func.id with
                    | Some prop -> pr#print_property_def prop
                    | None -> pr#print_function func));
                pr#print_newline)));
  generate ~add_to_inc:false "main.inc" (fun pr ->
      pr#print_inc (List.rev !sources));
  let project : CodeGen.project_t =
    {
      name = Stdlib.Filename.(remove_extension @@ basename ain_path);
      output_dir = Stdlib.Filename.dirname ain_path;
      ain_minor_version = decompiled.ain_minor_version;
    }
  in
  generate ~add_to_inc:false (project.name ^ ".pje") (fun pr ->
      pr#print_pje project);
  generate ~add_to_inc:false "debug_info.json" (fun pr -> pr#print_debug_info)
