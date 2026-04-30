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
          Expression
            (Call (Builtin (Instructions.A_ALLOC, PageRef (_, v)), dims));
        _;
      } ->
        Stdlib.Hashtbl.add h_dims v dims
    | {
        txt =
          Expression
            (Call
               ( HllFunc ("Array", { name = "Alloc"; _ }),
                 Deref (PageRef (_, v)) :: dims ));
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
               ( ASSIGN,
                 ArrayRef (Deref (PageRef (StructPage, v)), Number i),
                 Number m ));
        _;
      }
      when String.equal v.name "<vtable>" ->
        !vtable.(Int32.to_int_exn i) <- Int32.to_int_exn m
    | {
        txt =
          Expression
            ( AssignOp (_, PageRef ((StructPage | GlobalPage), v), e)
            | Call
                ( Builtin2
                    (X_SET, Deref (PageRef ((StructPage | GlobalPage), v))),
                  [ e ] ) );
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
      body = { txt = (Block [{txt = Return (Some (Deref (PageRef (StructPage, {name = "m_sName"; _ })))); _ }]); _ }; _
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
        | Some (Ast.Return (Some (Ast.Deref (Ast.PageRef (Ast.StructPage, v)))))
          ->
            String.equal v.name mangled_field
        | _ -> false
      in
      let is_trivial_set (s : CodeGen.function_t) =
        match single_stmt s.body.txt with
        | Some (Ast.Expression
                  (Ast.AssignOp (_, Ast.PageRef (Ast.StructPage, v), _))) ->
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
  Array.iter structs ~f:(fun s ->
      let methods_in_order = List.rev s.methods in
      let properties, remaining = extract_property_defs methods_in_order in
      s.methods <- remaining;
      s.properties <- properties);
  (* Auto-implemented properties round-trip purely via the
     [T Name { get; set; }] declaration in classes.jaf. Drop both
     accessor functions from [srcs] so the per-class .jaf doesn't
     also emit their bodies. *)
  let dropped_func_ids = Hash_set.create (module Int) in
  Array.iter structs ~f:(fun s ->
      List.iter s.properties ~f:(fun (p : CodeGen.property_def) ->
          if p.prop_is_auto then (
            Option.iter p.prop_get ~f:(fun g ->
                Hash_set.add dropped_func_ids g.func.id);
            Option.iter p.prop_set ~f:(fun set ->
                Hash_set.add dropped_func_ids set.func.id))));
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
  List.iter decompiled.srcs ~f:(fun (fname, funcs) ->
      if not (List.is_empty funcs) then
        generate fname (fun pr ->
            List.iter funcs ~f:(fun func ->
                pr#print_function func;
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
