(* Census of v12 duplicate-copy targeting ("readonly" variants).

   Rance10's original compiler emits some functions twice with the same
   name and signature (property getters, plus a family of ref-returning
   helpers).  Inside the second copy, accessor calls target the second
   copies of their callees.  This tool answers, for one ain:

   - which functions have exact-signature duplicate copies (by kind)
   - for every function with a body, whether the duplicate-copy callees
     it targets (via PUSH n; CALLMETHOD / DG_NEW_FROM_METHOD, or
     CALLFUNC n) are all rank 0, all rank >= 1, or mixed
   - the single-copy functions that target rank >= 1 exclusively
     (candidates for a [readonly] qualifier), and contradictions

   Usage: scan_readonly ORIG.ain [--list] *)
open Base
open Common

let arg_count_table : int array = Array.create ~len:0x10000 (-1)

let () =
  for op_i = 0 to 0xFFFF do
    match try Some (Bytecode.opcode_of_int op_i) with _ -> None with
    | Some op ->
        arg_count_table.(op_i) <-
          List.length (Bytecode.args_of_opcode ~version:12 op)
    | None -> ()
  done

let op_push = Bytecode.int_of_opcode PUSH
let op_callmethod = Bytecode.int_of_opcode CALLMETHOD
let op_dg_new = Bytecode.int_of_opcode DG_NEW_FROM_METHOD
let op_callfunc = Bytecode.int_of_opcode CALLFUNC

(* callee function indices targeted in [s, e) *)
let callees code s e =
  let len = Bytes.length code in
  let acc = ref [] in
  let p = ref s in
  let last_push = ref None in
  let fail = ref false in
  while (not !fail) && !p < e && !p + 1 < len do
    let op = Stdlib.Bytes.get_int16_le code !p in
    let n = if op >= 0 && op < 0x10000 then arg_count_table.(op) else -1 in
    if n < 0 || !p + 2 + (n * 4) > len then fail := true
    else (
      let operand k = Int32.to_int_exn (Stdlib.Bytes.get_int32_le code (!p + 2 + (4 * k))) in
      if op = op_push then last_push := Some (operand 0)
      else (
        if op = op_callmethod || op = op_dg_new then
          Option.iter !last_push ~f:(fun i -> acc := (i, if op = op_dg_new then "DG" else "CM") :: !acc)
        else if op = op_callfunc then acc := (operand 0, "CF") :: !acc;
        last_push := None);
      p := !p + 2 + (n * 4))
  done;
  List.rev !acc

let sig_key (f : Ain.Function.t) =
  let args = List.take f.vars f.nr_args in
  f.name ^ "("
  ^ String.concat ~sep:","
      (List.map args ~f:(fun (v : Ain.Variable.t) -> Ain.Type.to_string v.value_type))
  ^ ")" ^ Ain.Type.to_string f.return_type

let kind_of_name n =
  if String.is_substring n ~substring:"<lambda" then
    if String.is_substring n ~substring:" readonly" then "lambda_ro" else "lambda"
  else if String.is_suffix n ~suffix:"::get" then "get"
  else if String.is_suffix n ~suffix:"::set" then "set"
  else if String.is_suffix n ~suffix:"::add" || String.is_suffix n ~suffix:"::remove" then "event"
  else if String.is_suffix n ~suffix:"@0" || String.is_suffix n ~suffix:"@1" || String.is_suffix n ~suffix:"@2" then "ctor"
  else if String.is_substring n ~substring:"@" then "method"
  else "func"

let () =
  let ain = Ain.load Stdlib.Sys.argv.(1) in
  let list_all = Array.length Stdlib.Sys.argv > 2 in
  let code = Ain.get_code ain in
  let funcs = ref [] in
  Ain.function_iter ain ~f:(fun f -> if f.address > 0 then funcs := f :: !funcs);
  let funcs = List.rev !funcs in
  (* families *)
  let fam : (string, int list) Hashtbl.t = Hashtbl.create (module String) in
  List.iter funcs ~f:(fun f ->
      Hashtbl.update fam (sig_key f) ~f:(function None -> [ f.index ] | Some l -> l @ [ f.index ]));
  let rank : (int, int * int) Hashtbl.t = Hashtbl.create (module Int) in
  Hashtbl.iter fam ~f:(fun l ->
      let n = List.length l in
      List.iteri l ~f:(fun r i -> Hashtbl.set rank ~key:i ~data:(r, n)));
  let fam_kinds = Hashtbl.create (module String) in
  let fam_sizes = Hashtbl.create (module Int) in
  Hashtbl.iteri fam ~f:(fun ~key:_ ~data:l ->
      if List.length l > 1 then (
        let f = Ain.get_function_by_index ain (List.hd_exn l) in
        Hashtbl.update fam_kinds (kind_of_name f.name) ~f:(function None -> 1 | Some c -> c + 1);
        Hashtbl.update fam_sizes (List.length l) ~f:(function None -> 1 | Some c -> c + 1)));
  Stdio.printf "== duplicate-copy families (exact name+signature) by kind ==\n";
  Hashtbl.iteri fam_kinds ~f:(fun ~key ~data -> Stdio.printf "  %-10s %d\n" key data);
  Stdio.printf "  sizes:";
  Hashtbl.iteri fam_sizes ~f:(fun ~key ~data -> Stdio.printf " %dx%d" data key);
  Stdio.printf "\n";
  if list_all then (
    Stdio.printf "== non-accessor families ==\n";
    Hashtbl.iteri fam ~f:(fun ~key ~data:l ->
        if List.length l > 1 then
          let f = Ain.get_function_by_index ain (List.hd_exn l) in
          match kind_of_name f.name with
          | "get" | "set" -> ()
          | k -> Stdio.printf "  [%s] %s x%d\n" k key (List.length l)));
  (* ranges *)
  let sorted = List.sort funcs ~compare:(fun a b -> Int.compare a.address b.address) in
  let code_len = Bytes.length code in
  let ranges = Hashtbl.create (module Int) in
  let rec loop = function
    | [] -> ()
    | [ last ] -> Hashtbl.set ranges ~key:last.Ain.Function.index ~data:(last.address, code_len)
    | a :: (b :: _ as rest) ->
        Hashtbl.set ranges ~key:a.Ain.Function.index ~data:(a.address, b.Ain.Function.address);
        loop rest
  in
  loop sorted;
  (* census *)
  let matrix = Hashtbl.create (module String) in
  let cands = ref [] and mixed = ref [] and contra = ref [] in
  List.iter funcs ~f:(fun f ->
      let s, e = Hashtbl.find_exn ranges f.index in
      let r0 = ref 0 and r1 = ref 0 and det = ref [] in
      List.iter (callees code s e) ~f:(fun (i, how) ->
          match Hashtbl.find rank i with
          | Some (r, n) when n > 1 ->
              let g = Ain.get_function_by_index ain i in
              if r = 0 then Int.incr r0 else Int.incr r1;
              det := Printf.sprintf "%s#%d(%s)" g.name r how :: !det
          | _ -> ());
      let own_r, own_n = Hashtbl.find_exn rank f.index in
      let ck = kind_of_name f.name ^ (if own_n > 1 then Printf.sprintf "#%d" own_r else "") in
      let cls =
        if !r0 + !r1 = 0 then "none"
        else if !r1 = 0 then "pure0"
        else if !r0 = 0 then "pure1"
        else "mixed"
      in
      Hashtbl.update matrix (ck ^ " " ^ cls) ~f:(function None -> 1 | Some c -> c + 1);
      let d = String.concat ~sep:" " (List.rev !det) in
      if own_n = 1 && String.equal cls "pure1" then cands := (f.name, d) :: !cands;
      if String.equal cls "mixed" then mixed := (ck, f.name, d) :: !mixed;
      if own_n > 1 && ((own_r = 0 && !r1 > 0) || (own_r > 0 && !r0 > 0)) then
        contra := (ck, f.name, d) :: !contra);
  Stdio.printf "== caller kind[#rank] x class ==\n";
  Hashtbl.to_alist matrix
  |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)
  |> List.iter ~f:(fun (k, c) -> Stdio.printf "  %-22s %d\n" k c);
  let show title l =
    Stdio.printf "== %s (%d) ==\n" title (List.length l);
    List.iteri (List.rev l) ~f:(fun i x -> if list_all || i < 40 then Stdio.printf "  %s\n" x)
  in
  show "single-copy callers targeting rank>=1 only (readonly candidates)"
    (List.map !cands ~f:(fun (n, d) -> n ^ "  ->  " ^ d));
  show "mixed callers" (List.map !mixed ~f:(fun (k, n, d) -> k ^ " " ^ n ^ "  ->  " ^ d));
  show "duplicate copies contradicting their own rank"
    (List.map !contra ~f:(fun (k, n, d) -> k ^ " " ^ n ^ "  ->  " ^ d))
