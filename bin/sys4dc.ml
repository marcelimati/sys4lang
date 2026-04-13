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
open Cmdliner
open Decompiler

let rec mkdir_p path =
  if not (Stdlib.Sys.file_exists path) then (
    let parent = Stdlib.Filename.dirname path in
    if not (String.equal parent path) then mkdir_p parent;
    Stdlib.Sys.mkdir path 0o755)
  else if not (Stdlib.Sys.is_directory path) then
    failwith (path ^ " exists but is not a directory")

let write_to_file out_dir fname buf =
  if String.(out_dir = "-") then (
    Stdio.printf "FILE %s\n\n" fname;
    Stdlib.Buffer.output_buffer Stdio.stdout buf)
  else
    let output_path = Stdlib.Filename.concat out_dir fname in
    mkdir_p (Stdlib.Filename.dirname output_path);
    let outc = Stdio.Out_channel.create output_path in
    Stdlib.Buffer.output_buffer outc buf;
    Out_channel.close outc

(* Dump raw bytecode for a named function in the currently-loaded ain. *)
let dump_bytecode_one_function funcname =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  let CodeSection.{ files; _ } = CodeSection.parse code in
  let found = List.find_map files ~f:(fun (_, funcs) ->
      List.find funcs ~f:(fun f ->
          String.equal f.CodeSection.func.name funcname
          || String.equal f.CodeSection.name funcname)) in
  match found with
  | None -> None
  | Some f ->
      let buf = Buffer.create 4096 in
      let func = f.CodeSection.func in
      Stdlib.Buffer.add_string buf
        (Printf.sprintf "  [signature] nr_args=%d total_vars=%d\n"
           func.nr_args (Array.length func.vars));
      Array.iteri func.vars ~f:(fun i v ->
          let prefix = if i < func.nr_args then "arg" else "var" in
          Stdlib.Buffer.add_string buf
            (Printf.sprintf "    %s[%d] %s : %s\n" prefix i v.name
               (Type.show_ain_type v.type_)));
      List.iter f.code ~f:(fun loc ->
          Stdlib.Buffer.add_string buf
            (Printf.sprintf "%6d: %s\n" loc.Loc.addr
               (Instructions.show_instruction loc.Loc.txt)));
      Some (Buffer.contents buf)

(* Decompile one named function from the currently-loaded ain and return its
   printed jaf text. Mirrors the minimal version of Decompile.inspect. *)
let decompile_one_function funcname =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let structs =
    Array.map Ain.ain.strt ~f:(fun struc ->
        CodeGen.
          {
            struc;
            members =
              List.map (Array.to_list struc.members) ~f:CodeGen.from_ain_variable;
            methods = [];
            initval_lambdas = [];
          })
  in
  let CodeSection.{ files; lambdas } =
    CodeSection.parse code
    |> CodeSection.remove_overridden_functions ~move_to_original_file:false
    |> Decompile.process_generated_constructors structs
  in
  match
    List.find_map files ~f:(fun (_, funcs) ->
        List.find funcs ~f:(fun f ->
            String.equal f.CodeSection.func.name funcname
            || String.equal f.CodeSection.name funcname))
  with
  | None -> None
  | Some f ->
      let func = Decompile.decompile_function ~lambdas f in
      let printer = new CodeGen.code_printer "" in
      printer#print_function func;
      Some (Buffer.contents printer#get_buffer)

let compare_func ain1 ain2 funcname =
  let safe_decompile fname =
    try decompile_one_function fname with _ -> Some "<decompile failed>\n"
  in
  Ain.load ain1;
  let s1 = safe_decompile funcname in
  let b1 = dump_bytecode_one_function funcname in
  Ain.load ain2;
  let s2 = safe_decompile funcname in
  let b2 = dump_bytecode_one_function funcname in
  (match b1, b2 with
   | Some bc1, Some bc2 ->
       Stdio.printf "=== bytecode %s in %s ===\n" funcname ain1;
       Stdio.print_string bc1;
       Stdio.printf "\n=== bytecode %s in %s ===\n" funcname ain2;
       Stdio.print_string bc2;
       Stdio.print_endline ""
   | _ -> ());
  match (s1, s2) with
  | None, None ->
      Stdio.printf "Function %s not found in either ain.\n" funcname;
      Stdlib.exit 2
  | None, _ ->
      Stdio.printf "Function %s not found in %s.\n" funcname ain1;
      Stdlib.exit 2
  | _, None ->
      Stdio.printf "Function %s not found in %s.\n" funcname ain2;
      Stdlib.exit 2
  | Some t1, Some t2 ->
      if String.equal t1 t2 then (
        Stdio.printf "=== %s ===\n" funcname;
        Stdio.print_string t1;
        Stdio.print_endline "(identical)")
      else (
        Stdio.printf "=== %s in %s ===\n" funcname ain1;
        Stdio.print_string t1;
        Stdio.printf "\n=== %s in %s ===\n" funcname ain2;
        Stdio.print_string t2)

(* Normalize an instruction to a form suitable for structural comparison:
   keep the opcode mnemonic, drop all numeric operand values. Immediate
   integer values, string indices, function indices, struct indices,
   addresses, etc. all become a generic placeholder so differences in
   those don't count as structural diffs. *)
let normalize_instruction (i : Instructions.instruction) =
  let op_name s =
    (* Strip parens and any space-separated args from show_instruction.
       E.g. "(PUSH 42l)" -> "PUSH"; "(CALLMETHOD (12, 34))" -> "CALLMETHOD".  *)
    let s = String.chop_prefix_if_exists s ~prefix:"(" in
    let s = String.chop_suffix_if_exists s ~suffix:")" in
    match String.lsplit2 s ~on:' ' with
    | Some (name, _) -> name
    | None -> s
  in
  op_name (Instructions.show_instruction i)

(* Structurally compare every function defined in both ains, reporting
   names whose normalized opcode sequences differ. Ignores numeric
   arguments (addresses, indices, immediates) so only opcode-level
   structure matters. *)
let deep_compare ain1 ain2 pattern =
  let load_funcs ain_path =
    Ain.load ain_path;
    let code = Instructions.decode Ain.ain.code in
    let code = CodeSection.preprocess_ain_v0 code in
    let CodeSection.{ files; _ } = CodeSection.parse code in
    let tbl = Hashtbl.create (module String) in
    List.iter files ~f:(fun (_, funcs) ->
        List.iter funcs ~f:(fun f ->
            let key =
              Printf.sprintf "%s#%d" f.CodeSection.func.name
                f.CodeSection.func.nr_args
            in
            let ops =
              List.map f.code ~f:(fun loc -> normalize_instruction loc.Loc.txt)
            in
            Hashtbl.set tbl ~key ~data:ops));
    tbl
  in
  let t1 = load_funcs ain1 in
  let t2 = load_funcs ain2 in
  let diffs = ref [] in
  Hashtbl.iteri t1 ~f:(fun ~key ~data:ops1 ->
      let matches_pattern =
        match pattern with
        | None -> true
        | Some p -> String.is_substring key ~substring:p
      in
      if matches_pattern then
        match Hashtbl.find t2 key with
        | Some ops2 when not (List.equal String.equal ops1 ops2) ->
            diffs := (key, List.length ops1, List.length ops2) :: !diffs
        | _ -> ());
  let sorted =
    List.sort !diffs ~compare:(fun (a, _, _) (b, _, _) -> String.compare a b)
  in
  List.iter sorted ~f:(fun (name, n1, n2) ->
      Stdio.printf "%s  ops1=%d ops2=%d\n" name n1 n2);
  Stdio.printf "Total functions with structural diff: %d\n" (List.length !diffs);
  (* Check variable type mismatches using the parsed function metadata *)
  let load_func_vars ain_path =
    Ain.load ain_path;
    let code = Instructions.decode Ain.ain.code in
    let code = CodeSection.preprocess_ain_v0 code in
    let CodeSection.{ files; _ } = CodeSection.parse code in
    let tbl = Hashtbl.create (module String) in
    List.iter files ~f:(fun (_, funcs) ->
        List.iter funcs ~f:(fun f ->
            let func = f.CodeSection.func in
            let key = Printf.sprintf "%s#%d" func.name func.nr_args in
            let vars = Array.to_list func.vars
              |> List.map ~f:(fun (v : Ain.Variable.t) -> Type.show_ain_type v.type_) in
            Hashtbl.set tbl ~key ~data:vars));
    tbl
  in
  let v1 = load_func_vars ain1 in
  let v2 = load_func_vars ain2 in
  let var_diffs = ref [] in
  Hashtbl.iteri v1 ~f:(fun ~key ~data:vt1 ->
      match Hashtbl.find v2 key with
      | Some vt2 when List.length vt1 = List.length vt2
                       && not (List.equal String.equal vt1 vt2) ->
          var_diffs := key :: !var_diffs
      | _ -> ());
  Stdio.printf "Functions with var type mismatch: %d\n" (List.length !var_diffs);
  List.iter (List.sort !var_diffs ~compare:String.compare) ~f:(fun name ->
      let vt1 = Hashtbl.find_exn v1 name in
      let vt2 = Hashtbl.find_exn v2 name in
      Stdio.printf "  %s:\n" name;
      List.iteri (List.zip_exn vt1 vt2) ~f:(fun i (a, b) ->
          if not (String.equal a b) then
            Stdio.printf "    var[%d] ours=%s orig=%s\n" i a b))

let sys4dc output_dir inspect_function compare_with print_addr
    move_to_original_file continue_on_error deep_compare_flag pattern ain_file =
  match compare_with, inspect_function, deep_compare_flag with
  | Some ain2, None, true -> deep_compare ain_file ain2 pattern
  | Some ain2, Some funcname, false -> compare_func ain_file ain2 funcname
  | Some _, None, false ->
      Stdio.print_endline "--compare-with requires --inspect FUNCNAME or --deep-compare";
      Stdlib.exit 2
  | Some _, Some _, true ->
      Stdio.print_endline "--deep-compare and --inspect are mutually exclusive";
      Stdlib.exit 2
  | None, _, _ ->
      let output_dir = Option.value output_dir ~default:"." in
      Ain.load ain_file;
      (match inspect_function with
      | None ->
          let decompiled =
            Decompile.decompile ~move_to_original_file ~continue_on_error
          in
          (* reroot ain_file to output_dir if possible *)
          let ain_path =
            Fpath.(
              let root =
                v @@ if String.(output_dir = "-") then "." else output_dir
              in
              match relativize ~root (v ain_file) with
              | Some p -> to_string @@ normalize p
              | None -> ain_file)
          in
          Decompile.export ~print_addr decompiled ain_path
            (write_to_file output_dir)
      | Some funcname -> Decompile.inspect funcname ~print_addr)

let cmd =
  let version =
    Option.map (Build_info.V1.version ()) ~f:Build_info.V1.Version.to_string
  in
  let doc = "Decompile an .ain file" in
  let info = Cmd.info "sys4dc" ?version ~doc in
  let output_dir =
    let doc = "Output directory. Use '-' to print everything to stdout." in
    let docv = "DIRECTORY" in
    Cmdliner.Arg.(value & opt (some string) None & info [ "o" ] ~docv ~doc)
  in
  let inspect_function =
    let doc = "Inspect the decompilation process of a function" in
    let docv = "FUNCTION" in
    Cmdliner.Arg.(
      value & opt (some string) None & info [ "inspect" ] ~docv ~doc)
  in
  let compare_with =
    let doc =
      "Compare a single function (specified via --inspect) against the same \
       function in another ain. Prints both decompilations side-by-side."
    in
    let docv = "AIN2" in
    Cmdliner.Arg.(
      value & opt (some string) None & info [ "compare-with" ] ~docv ~doc)
  in
  let print_addr =
    let doc = "Print addresses" in
    Cmdliner.Arg.(value & flag & info [ "address" ] ~doc)
  in
  let move_to_original_file =
    let doc =
      "Move the overridden functions to the files where they were originally \
       defined.  Useful for mods made with AinDecompiler."
    in
    Cmdliner.Arg.(value & flag & info [ "move-to-original-file" ] ~doc)
  in
  let continue_on_error =
    let doc = "Continue decompilation even if an error is encountered." in
    Cmdliner.Arg.(value & flag & info [ "continue-on-error" ] ~doc)
  in
  let deep_compare_flag =
    let doc =
      "With --compare-with, structurally compare ALL functions (opcode \
       sequences, ignoring numeric operands) between the two ains and \
       report names that differ."
    in
    Cmdliner.Arg.(value & flag & info [ "deep-compare" ] ~doc)
  in
  let pattern =
    let doc = "Filter --deep-compare results by function name substring." in
    let docv = "PATTERN" in
    Cmdliner.Arg.(
      value & opt (some string) None & info [ "name" ] ~docv ~doc)
  in
  let ain_file =
    let doc = "The .ain file to decompile" in
    let docv = "AIN_FILE" in
    Cmdliner.Arg.(required & pos 0 (some string) None & info [] ~docv ~doc)
  in
  Cmd.v info
    Term.(
      const sys4dc $ output_dir $ inspect_function $ compare_with $ print_addr
      $ move_to_original_file $ continue_on_error $ deep_compare_flag
      $ pattern $ ain_file)

let () = Stdlib.exit (Cmd.eval cmd)
