(* Compare delegate-binding sites (PUSH fnidx; DG_NEW_FROM_METHOD)
   between two ains, per matched non-lambda function.

   For the k-th DG_NEW_FROM_METHOD in a common function, resolve the
   pushed function index on both sides and flag:
   - INVALID: ours' index out of range, or target has no body
     (address <= 0)
   - NAME: both targets are non-lambdas but names differ
   - KIND: one side binds a lambda, the other a named function
   - ARGS: targets' argument counts differ
   - COUNT: the two sides have a different number of binding sites

   Usage: scan_dispatch ORIG.ain OURS.ain *)
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

let dg_new_from_method = Bytecode.int_of_opcode DG_NEW_FROM_METHOD
let push_op = Bytecode.int_of_opcode PUSH

(* [(k, pushed_index)] for each DG_NEW_FROM_METHOD preceded by PUSH. *)
let binding_sites code s e =
  let len = Bytes.length code in
  let acc = ref [] in
  let k = ref 0 in
  let p = ref s in
  let last_push = ref None in
  let fail = ref false in
  while (not !fail) && !p < e && !p + 1 < len do
    let op = Stdlib.Bytes.get_int16_le code !p in
    let n = if op >= 0 && op < 0x10000 then arg_count_table.(op) else -1 in
    if n < 0 || !p + 2 + (n * 4) > len then fail := true
    else begin
      if op = push_op then
        last_push := Some (Stdlib.Bytes.get_int32_le code (!p + 2))
      else begin
        if op = dg_new_from_method then (
          acc := (!k, !last_push) :: !acc;
          Int.incr k);
        (* PUSH must be the immediately preceding instruction. *)
        last_push := None
      end;
      p := !p + 2 + (n * 4)
    end
  done;
  List.rev !acc

let function_ranges ain =
  let acc = ref [] in
  Ain.function_iter ain ~f:(fun f ->
      if
        (not (String.is_prefix f.name ~prefix:"<lambda"))
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

let is_lambda_name n = String.is_substring n ~substring:"<lambda"

let () =
  let orig = Ain.load Stdlib.Sys.argv.(1) in
  let ours = Ain.load Stdlib.Sys.argv.(2) in
  let oc = Ain.get_code orig in
  let uc = Ain.get_code ours in
  let or_ = function_ranges orig in
  let ur_ = function_ranges ours in
  let o_nfun = Ain.nr_functions orig in
  let u_nfun = Ain.nr_functions ours in
  let issues = ref 0 in
  let report fn kind detail =
    Int.incr issues;
    Stdio.printf "%-7s %s  %s\n" kind fn detail
  in
  Hashtbl.iteri or_ ~f:(fun ~key:nm ~data:(os, oe) ->
      match Hashtbl.find ur_ nm with
      | None -> ()
      | Some (us, ue) ->
        let ob = binding_sites oc os oe in
        let ub = binding_sites uc us ue in
        if List.length ob <> List.length ub then
          report nm "COUNT"
            (Printf.sprintf "orig has %d DG_NEW_FROM_METHOD sites, ours %d"
               (List.length ob) (List.length ub))
        else
          List.iter2_exn ob ub ~f:(fun (k, opush) (_, upush) ->
              match (opush, upush) with
              | None, None -> ()
              | Some oi, Some ui -> (
                  let oi = Int32.to_int_exn oi and ui = Int32.to_int_exn ui in
                  if oi < 0 || oi >= o_nfun then ()
                  else if ui < 0 || ui >= u_nfun then
                    report nm "INVALID"
                      (Printf.sprintf "site %d: ours pushes %d (nr_functions=%d)"
                         k ui u_nfun)
                  else
                    let of_ = Ain.get_function_by_index orig oi in
                    let uf = Ain.get_function_by_index ours ui in
                    if uf.address <= 0 then
                      report nm "DEAD"
                        (Printf.sprintf "site %d: ours binds %s (no body)" k
                           uf.name)
                    else
                      let ol = is_lambda_name of_.name
                      and ul = is_lambda_name uf.name in
                      if (not ol) && (not ul) then (
                        if not (String.equal of_.name uf.name) then
                          report nm "NAME"
                            (Printf.sprintf "site %d: orig->%s ours->%s" k
                               of_.name uf.name))
                      else if not (Bool.equal ol ul) then
                        report nm "KIND"
                          (Printf.sprintf "site %d: orig->%s ours->%s" k
                             of_.name uf.name)
                      else if of_.nr_args <> uf.nr_args then
                        report nm "ARGS"
                          (Printf.sprintf
                             "site %d: orig %s (%d args) ours %s (%d args)" k
                             of_.name of_.nr_args uf.name uf.nr_args))
              | Some _, None ->
                  report nm "SHAPE"
                    (Printf.sprintf "site %d: ours' DG_NEW_FROM_METHOD not preceded by PUSH" k)
              | None, Some _ -> ()));
  Stdio.printf "total flagged: %d\n" !issues
