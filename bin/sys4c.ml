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
open Compiler
open Cmdliner

let read_text_file ?(encoding = Pje.UTF8) file =
  let content =
    match file with
    | "-" -> In_channel.input_all In_channel.stdin
    | _ -> Stdio.In_channel.read_all file
  in
  match encoding with Pje.UTF8 -> content | Pje.SJIS -> Sjis.to_utf8 content

let handle_errors f get_content =
  try f () with
  | CompileError.Compile_error e ->
      CompileError.print_error e get_content;
      Stdlib.exit 1
  | Sys_error msg ->
      Stdio.print_endline msg;
      Stdlib.exit 1

let do_compile sources output major minor import_as input_encoding =
  let import_as =
    List.map import_as ~f:(fun s ->
        match String.split s ~on:'=' with
        | [ hll_name; name ] -> (hll_name, name)
        | _ -> failwith "invalid import-as format")
  in
  let sources =
    List.map sources ~f:(fun f ->
        if String.is_suffix (String.lowercase f) ~suffix:".hll" then
          let import_name =
            let hll_name = Stdlib.Filename.(chop_extension (basename f)) in
            match List.Assoc.find import_as ~equal:String.equal hll_name with
            | Some name -> name
            | None -> hll_name
          in
          Pje.Hll (f, import_name)
        else Pje.Jaf f)
  in
  let ctx = Jaf.context_from_ain (Ain.create major minor) in
  let files = Hashtbl.create (module String) in
  handle_errors
    (fun () ->
      let read_file file =
        let source = read_text_file ~encoding:input_encoding file in
        Hashtbl.add_exn files ~key:file ~data:source;
        source
      in
      let debug_info = DebugInfo.create () in
      Compile.compile ctx sources debug_info read_file;
      Ain.write_file ctx.ain output)
    (fun file -> Hashtbl.find files file)

let do_build pje_file output_dir_override =
  let pje =
    handle_errors
      (fun () -> PjeLoader.load read_text_file pje_file)
      (fun _ -> None)
  in
  let ctx = Jaf.context_from_ain (Pje.create_ain pje) in
  let files = Hashtbl.create (module String) in
  handle_errors
    (fun () ->
      let source_dir =
        Stdlib.Filename.(concat (dirname pje_file) pje.source_dir)
      in
      let read_file file =
        let file = Stdlib.Filename.(concat source_dir file) in
        let source = read_text_file ~encoding:pje.encoding file in
        Hashtbl.add_exn files ~key:file ~data:source;
        source
      in
      let sources = Pje.collect_sources pje in
      let debug_info = DebugInfo.create () in
      Compile.compile ctx sources debug_info read_file;
      Ain.write_file ctx.ain (Pje.ain_path ?output_dir_override pje);
      DebugInfo.write_to_file debug_info (Pje.debug_info_path pje))
    (fun file -> Hashtbl.find files file)

let encoding_conv =
  let parse s =
    try Ok (Pje.encoding_of_string s)
    with Pje.KeyError msg -> Error (`Msg msg)
  in
  let print ppf e =
    Stdlib.Format.pp_print_string ppf (Pje.string_of_encoding e)
  in
  Arg.conv (parse, print)

let cmd_compile_jaf =
  let doc = "Compile .jaf files." in
  let info = Cmd.info "compile" ~doc in
  let sources =
    let doc = "Source files to compile." in
    Arg.(non_empty & pos_all string [] & info [] ~docv:"SOURCES" ~doc)
  in
  let output =
    let doc = "The output .ain file." in
    Arg.(
      value & opt string "out.ain"
      & info [ "o"; "output" ] ~docv:"OUT_FILE" ~doc)
  in
  let major =
    let doc = "The output .ain file version." in
    Arg.(value & opt int 4 & info [ "ain-version" ] ~docv:"MAJOR" ~doc)
  in
  let minor =
    let doc = "The output .ain file minor version." in
    Arg.(value & opt int 0 & info [ "ain-minor-version" ] ~docv:"MINOR" ~doc)
  in
  let import_as =
    let doc = "Import HLL_NAME as NAME." in
    Arg.(
      value & opt_all string []
      & info [ "import-as" ] ~docv:"HLL_NAME=NAME" ~doc)
  in
  let input_encoding =
    let doc = "The input file encoding. Shift_JIS or UTF-8." in
    Arg.(
      value & opt encoding_conv Pje.UTF8
      & info [ "input-encoding" ] ~docv:"ENCODING" ~doc)
  in
  let test =
    let doc = "Testing." in
    Arg.(value & opt (some string) None & info [ "test" ] ~docv:"TEST" ~doc)
  in
  let compile sources output major minor import_as input_encoding test =
    if Option.is_some test then
      let ain = Ain.load (Option.value_exn test) in
      Ain.write_file ain output
    else do_compile sources output major minor import_as input_encoding
  in
  Cmd.v info
    Term.(
      const compile $ sources $ output $ major $ minor $ import_as
      $ input_encoding $ test)

let cmd_build_pje =
  let doc = "Build a System 4 project from a .pje file." in
  let info = Cmd.info "build" ~doc in
  let project =
    let doc = "The project file to build." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:"PROJECT" ~doc)
  in
  let output_dir =
    let doc = "Override the output directory specified in the pje." in
    Arg.(
      value
      & opt (some string) None
      & info [ "output-dir" ] ~docv:"OUTPUT_DIR" ~doc)
  in
  Cmd.v info Term.(const do_build $ project $ output_dir)

let cmd_dump_addrs =
  let doc = "Dump function addresses from an ain file" in
  let ain_file = Arg.(required & pos 0 (some string) None & info [] ~docv:"AIN") in
  let do_dump ain_file =
    let ain = Ain.load ain_file in
    Ain.function_iter ain ~f:(fun (f : Ain.Function.t) ->
      Stdio.printf "%d\t%d\n" f.index f.address)
  in
  let info = Cmd.info "dump-addrs" ~doc in
  Cmd.v info Term.(const do_dump $ ain_file)

let cmd_func_at =
  let doc = "Find function info by index range or name" in
  let ain_file = Arg.(required & pos 0 (some string) None & info [] ~docv:"AIN") in
  let from_idx = Arg.(value & opt int 0 & info [ "from" ] ~docv:"FROM") in
  let to_idx = Arg.(value & opt int 100000 & info [ "to" ] ~docv:"TO") in
  let name_filter = Arg.(value & opt (some string) None & info [ "name" ] ~docv:"NAME") in
  let do_dump ain_file from_idx to_idx name_filter =
    let ain = Ain.load ain_file in
    Ain.function_iter ain ~f:(fun (f : Ain.Function.t) ->
      let name_match = match name_filter with
        | None -> true
        | Some p -> String.is_substring f.name ~substring:p
      in
      if f.index >= from_idx && f.index <= to_idx && name_match then
        Stdio.printf "%d\t%s\taddr=%d\tnr_args=%d\n" f.index f.name f.address f.nr_args)
  in
  let info = Cmd.info "func-at" ~doc in
  Cmd.v info Term.(const do_dump $ ain_file $ from_idx $ to_idx $ name_filter)

let cmd_compare_func_vars =
  let doc = "Compare var counts of functions between two ains" in
  let ain1 = Arg.(required & pos 0 (some string) None & info [] ~docv:"AIN1") in
  let ain2 = Arg.(required & pos 1 (some string) None & info [] ~docv:"AIN2") in
  let do_cmp ain1 ain2 =
    let a1 = Ain.load ain1 in
    let a2 = Ain.load ain2 in
    let by_key1 = Hashtbl.create (module String) in
    Ain.function_iter a1 ~f:(fun (f : Ain.Function.t) ->
      if f.address > 0 then
        let k = Printf.sprintf "%s#%d" f.name f.nr_args in
        Hashtbl.set by_key1 ~key:k ~data:f);
    Ain.function_iter a2 ~f:(fun (f2 : Ain.Function.t) ->
      if f2.address > 0 then
        let k = Printf.sprintf "%s#%d" f2.name f2.nr_args in
        match Hashtbl.find by_key1 k with
        | None -> ()
        | Some f1 ->
            let n1 = List.length f1.vars in
            let n2 = List.length f2.vars in
            if n1 <> n2 then
              Stdio.printf "%s  orig=%d comp=%d diff=%+d\n" f2.name n1 n2 (n2 - n1))
  in
  let info = Cmd.info "compare-func-vars" ~doc in
  Cmd.v info Term.(const do_cmp $ ain1 $ ain2)

let cmd_compare_structs =
  let doc = "Compare struct member counts/types between two ains" in
  let ain1 = Arg.(required & pos 0 (some string) None & info [] ~docv:"AIN1") in
  let ain2 = Arg.(required & pos 1 (some string) None & info [] ~docv:"AIN2") in
  let do_cmp ain1 ain2 =
    let a1 = Ain.load ain1 in
    let a2 = Ain.load ain2 in
    let by_name1 = Hashtbl.create (module String) in
    Ain.struct_iter a1 ~f:(fun (s : Ain.Struct.t) ->
      Hashtbl.set by_name1 ~key:s.name ~data:s);
    Ain.struct_iter a2 ~f:(fun (s2 : Ain.Struct.t) ->
      match Hashtbl.find by_name1 s2.name with
      | None -> Stdio.printf "MISSING in ain1: %s\n" s2.name
      | Some s1 ->
          let n1 = List.length s1.members in
          let n2 = List.length s2.members in
          if n1 <> n2 then
            Stdio.printf "%s: orig=%d members  comp=%d members\n" s2.name n1 n2);
    Hashtbl.iter_keys by_name1 ~f:(fun k ->
      if not (Option.is_some (Ain.get_struct a2 k)) then
        Stdio.printf "MISSING in ain2: %s\n" k)
  in
  let info = Cmd.info "compare-structs" ~doc in
  Cmd.v info Term.(const do_cmp $ ain1 $ ain2)

let cmd_dump_func =
  let doc = "Dump full function metadata (vars, types) by exact name" in
  let ain_file = Arg.(required & pos 0 (some string) None & info [] ~docv:"AIN") in
  let func_name =
    Arg.(required & pos 1 (some string) None & info [] ~docv:"NAME")
  in
  let do_dump ain_file func_name =
    let ain = Ain.load ain_file in
    Ain.function_iter ain ~f:(fun (f : Ain.Function.t) ->
      if String.equal f.name func_name then (
        Stdio.printf "%d\t%s\taddr=%d\tnr_args=%d\treturn=%s\n"
          f.index f.name f.address f.nr_args
          (Ain.Type.to_string f.return_type);
        List.iteri f.vars ~f:(fun i (v : Ain.Variable.t) ->
          Stdio.printf "  var[%d] %s : %s\n" i v.name
            (Ain.Type.to_string v.value_type))))
  in
  let info = Cmd.info "dump-func" ~doc in
  Cmd.v info Term.(const do_dump $ ain_file $ func_name)

let cmd_compare_funcs =
  let doc = "Find functions with different bytecode size between two ains" in
  let ain1 = Arg.(required & pos 0 (some string) None & info [] ~docv:"AIN1") in
  let ain2 = Arg.(required & pos 1 (some string) None & info [] ~docv:"AIN2") in
  let pattern_arg =
    Arg.(value & opt (some string) None & info [ "name" ] ~docv:"PATTERN")
  in
  let do_compare ain1_path ain2_path pattern =
    let a1 = Ain.load ain1_path in
    let a2 = Ain.load ain2_path in
    let code1_size = Bytes.length (Ain.get_code a1) in
    let code2_size = Bytes.length (Ain.get_code a2) in
    let by_name1 = Hashtbl.create (module String) in
    let by_name2 = Hashtbl.create (module String) in
    Ain.function_iter a1 ~f:(fun (f : Ain.Function.t) ->
      if f.address > 0 then
        Hashtbl.update by_name1 (Printf.sprintf "%s#%d" f.name f.nr_args)
          ~f:(function None -> [f] | Some l -> f :: l));
    Ain.function_iter a2 ~f:(fun (f : Ain.Function.t) ->
      if f.address > 0 then
        Hashtbl.update by_name2 (Printf.sprintf "%s#%d" f.name f.nr_args)
          ~f:(function None -> [f] | Some l -> f :: l));
    (* Compute sizes from sorted addresses *)
    let mk_sizes ain code_size =
      let funcs = ref [] in
      Ain.function_iter ain ~f:(fun (f : Ain.Function.t) ->
        if f.address > 0 then funcs := (f.index, f.address) :: !funcs);
      let sorted = List.sort !funcs ~compare:(fun (_,a) (_,b) -> compare a b) in
      let sizes = Hashtbl.create (module Int) in
      let arr = Array.of_list sorted in
      Array.iteri arr ~f:(fun i (idx, addr) ->
        let next = if i+1 < Array.length arr then snd arr.(i+1) - 6 else code_size in
        Hashtbl.set sizes ~key:idx ~data:(next - (addr - 6)));
      sizes
    in
    let s1 = mk_sizes a1 code1_size in
    let s2 = mk_sizes a2 code2_size in
    let diffs = ref [] in
    Hashtbl.iteri by_name1 ~f:(fun ~key ~data:funcs1 ->
      match Hashtbl.find by_name2 key with
      | Some funcs2 when List.length funcs1 = 1 && List.length funcs2 = 1 ->
          let f1 = List.hd_exn funcs1 in
          let f2 = List.hd_exn funcs2 in
          let sz1 = Option.value (Hashtbl.find s1 f1.index) ~default:0 in
          let sz2 = Option.value (Hashtbl.find s2 f2.index) ~default:0 in
          let pattern_match = match pattern with
            | None -> true
            | Some p -> String.is_substring f1.name ~substring:p
          in
          if sz1 <> sz2 && pattern_match then
            diffs := (f1.name, f1.nr_args, sz1, sz2, sz2 - sz1) :: !diffs
      | _ -> ());
    let sorted = List.sort !diffs ~compare:(fun (_,_,_,_,d1) (_,_,_,_,d2) ->
      compare (abs d2) (abs d1)) in
    List.iter sorted ~f:(fun (name, nargs, sz1, sz2, d) ->
      Stdio.printf "%s#%d  orig=%d comp=%d diff=%+d\n" name nargs sz1 sz2 d);
    Stdio.printf "Total functions with size diff: %d\n" (List.length !diffs)
  in
  let info = Cmd.info "compare-funcs" ~doc in
  Cmd.v info Term.(const do_compare $ ain1 $ ain2 $ pattern_arg)

let cmd =
  let doc = "System 4 Compiler" in
  let version =
    Option.map (Build_info.V1.version ()) ~f:Build_info.V1.Version.to_string
  in
  let info = Cmd.info "sys4c" ?version ~doc in
  Cmd.group info [ cmd_compile_jaf; cmd_build_pje; cmd_dump_addrs; cmd_compare_funcs; cmd_func_at; cmd_dump_func; cmd_compare_structs; cmd_compare_func_vars ]

let () = Stdlib.exit (Cmd.eval cmd)
