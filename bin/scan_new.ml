(* Compare NEW sites between two ains, per matched function.
   For the k-th NEW in a common function, compare the struct-type NAME
   and the constructor: NILCTOR (one side -1, other a real fn),
   CTORNAME (both real but different names), TYPE (struct names differ),
   COUNT (different number of NEW sites).

   Usage: scan_new ORIG.ain OURS.ain *)
open Base
open Common

let arg_count_table : int array = Array.create ~len:0x10000 (-1)

let () =
  for op_i = 0 to 0xFFFF do
    match try Some (Bytecode.opcode_of_int op_i) with _ -> None with
    | Some op ->
      arg_count_table.(op_i) <- List.length (Bytecode.args_of_opcode ~version:12 op)
    | None -> ()
  done

let op_new = Bytecode.int_of_opcode NEW

(* [(k, struct_type, ctor)] for each NEW *)
let new_sites code s e =
  let len = Bytes.length code in
  let acc = ref [] in
  let k = ref 0 in
  let p = ref s in
  let fail = ref false in
  while (not !fail) && !p < e && !p + 1 < len do
    let op = Stdlib.Bytes.get_int16_le code !p in
    let n = if op >= 0 && op < 0x10000 then arg_count_table.(op) else -1 in
    if n < 0 || !p + 2 + (n * 4) > len then fail := true
    else begin
      if op = op_new && n >= 2 then begin
        let st = Int32.to_int_exn (Stdlib.Bytes.get_int32_le code (!p + 2)) in
        let ctor = Int32.to_int_exn (Stdlib.Bytes.get_int32_le code (!p + 6)) in
        acc := (!k, st, ctor) :: !acc;
        Int.incr k
      end;
      p := !p + 2 + (n * 4)
    end
  done;
  List.rev !acc

let function_ranges ain =
  let acc = ref [] in
  Ain.function_iter ain ~f:(fun f ->
      (* Lambda naming differs between compilers (ours lacks the
         [Class@] prefix and line numbers shift) — exclude by substring
         so lambdas neither match by name nor bound parents' address
         ranges (see scan_dispatch.ml). *)
      if
        (not (String.is_substring f.name ~substring:"<lambda"))
        && (not (String.is_empty f.name))
        && f.address > 0
      then acc := f :: !acc);
  let sorted =
    !acc
    |> List.sort ~compare:(fun a b ->
           Int.compare a.Ain.Function.address b.Ain.Function.address)
  in
  let h = Hashtbl.create (module String) in
  let code_len = Bytes.length (Ain.get_code ain) in
  let rec loop = function
    | [] -> ()
    | [ last ] ->
      Hashtbl.set h ~key:last.Ain.Function.name
        ~data:(last.address, min (last.address + 1024) code_len)
    | a :: b :: rest ->
      Hashtbl.set h ~key:a.Ain.Function.name
        ~data:(a.address, min b.Ain.Function.address code_len);
      loop (b :: rest)
  in
  loop sorted;
  h

let struct_name ain idx =
  if idx < 0 || idx >= Ain.nr_structs ain then Printf.sprintf "<oob:%d>" idx
  else (Ain.get_struct_by_index ain idx).name

let fn_name ain idx =
  if idx < 0 then "<null>"
  else if idx >= Ain.nr_functions ain then Printf.sprintf "<oob:%d>" idx
  else (Ain.get_function_by_index ain idx).name

let () =
  let orig = Ain.load Stdlib.Sys.argv.(1) in
  let ours = Ain.load Stdlib.Sys.argv.(2) in
  let oc = Ain.get_code orig in
  let uc = Ain.get_code ours in
  let or_ = function_ranges orig in
  let ur_ = function_ranges ours in
  let issues = ref 0 in
  let report fn kind detail =
    Int.incr issues;
    Stdio.printf "%-9s %s  %s\n" kind fn detail
  in
  Hashtbl.iteri or_ ~f:(fun ~key:nm ~data:(os, oe) ->
      match Hashtbl.find ur_ nm with
      | None -> ()
      | Some (us, ue) ->
        let ob = new_sites oc os oe in
        let ub = new_sites uc us ue in
        if List.length ob <> List.length ub then
          report nm "COUNT"
            (Printf.sprintf "orig has %d NEW sites, ours %d" (List.length ob)
               (List.length ub))
        else
          List.iter2_exn ob ub ~f:(fun (k, ost, octor) (_, ust, uctor) ->
              let osn = struct_name orig ost and usn = struct_name ours ust in
              if not (String.equal osn usn) then
                report nm "TYPE"
                  (Printf.sprintf "site %d: orig NEW %s, ours NEW %s" k osn usn)
              else if octor < 0 && uctor >= 0 then
                report nm "NILCTOR"
                  (Printf.sprintf "site %d (%s): orig ctor=-1, ours ctor=%s" k osn
                     (fn_name ours uctor))
              else if octor >= 0 && uctor < 0 then
                report nm "NILCTOR"
                  (Printf.sprintf "site %d (%s): orig ctor=%s, ours ctor=-1" k osn
                     (fn_name orig octor))
              else if octor >= 0 && uctor >= 0 then begin
                let on = fn_name orig octor and un = fn_name ours uctor in
                if not (String.equal on un) then
                  report nm "CTORNAME"
                    (Printf.sprintf "site %d (%s): orig ctor=%s ours ctor=%s" k osn
                       on un)
              end));
  Stdio.printf "total flagged: %d\n" !issues
