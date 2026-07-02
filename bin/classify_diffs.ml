(* Classify per-function bytecode differences between two ain files:
   IDENTICAL / OPERAND (same opcodes, non-normalizable operand differs)
   / OPCODE (same length, different opcodes) / LENGTH (different op counts)
   / PARSE (unknown opcode encountered). *)
open Base
open Common

let arg_types_table : Bytecode.argtype list option array = Array.create ~len:0x10000 None

let () =
  for op_i = 0 to 0xFFFF do
    match try Some (Bytecode.opcode_of_int op_i) with _ -> None with
    | Some op ->
      arg_types_table.(op_i) <- Some (Bytecode.args_of_opcode ~version:12 op)
    | None -> arg_types_table.(op_i) <- None
  done

(* returns list of (op, args:(int32 * normalizable) list) or None on parse fail *)
let walk code s e =
  let len = Bytes.length code in
  let acc = ref [] in
  let p = ref s in
  let fail = ref false in
  while (not !fail) && !p < e && !p + 1 < len do
    let op = Stdlib.Bytes.get_int16_le code !p in
    (match (if op >= 0 && op < 0x10000 then arg_types_table.(op) else None) with
    | None -> fail := true
    | Some types ->
      let n = List.length types in
      if !p + 2 + (n * 4) > len then fail := true
      else begin
        let args =
          List.mapi types ~f:(fun i t ->
              let v = Stdlib.Bytes.get_int32_le code (!p + 2 + (i * 4)) in
              let normalizable =
                match t with
                | Bytecode.Function | Address | String | Message -> true
                | _ -> false
              in
              (v, normalizable))
        in
        acc := (op, args) :: !acc;
        p := !p + 2 + (n * 4)
      end)
  done;
  if !fail then None else Some (List.rev !acc)

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

let () =
  let orig = Ain.load Stdlib.Sys.argv.(1) in
  let ours = Ain.load Stdlib.Sys.argv.(2) in
  let oc = Ain.get_code orig in
  let uc = Ain.get_code ours in
  let or_ = function_ranges orig in
  let ur_ = function_ranges ours in
  let common = Hashtbl.keys or_ |> List.filter ~f:(Hashtbl.mem ur_) in
  let counts = Hashtbl.create (module String) in
  let examples = Hashtbl.create (module String) in
  let bump cls name =
    Hashtbl.update counts cls ~f:(function None -> 1 | Some c -> c + 1);
    Hashtbl.update examples cls ~f:(function
      | None -> [ name ]
      | Some l -> if List.length l < 5 then name :: l else l)
  in
  List.iter common ~f:(fun nm ->
      let os, oe = Hashtbl.find_exn or_ nm in
      let us, ue = Hashtbl.find_exn ur_ nm in
      match (walk oc os oe, walk uc us ue) with
      | None, _ | _, None -> bump "PARSE" nm
      | Some a, Some b ->
        if List.length a <> List.length b then bump "LENGTH" nm
        else if
          not (List.for_all2_exn a b ~f:(fun (o1, _) (o2, _) -> o1 = o2))
        then bump "OPCODE" nm
        else if
          List.for_all2_exn a b ~f:(fun (_, a1) (_, a2) ->
              (* arg lists have equal length because opcodes are equal *)
              List.for_all2_exn a1 a2 ~f:(fun (v1, n1) (v2, _) ->
                  n1 || Int32.equal v1 v2))
        then bump "IDENTICAL" nm
        else bump "OPERAND" nm);
  Stdio.printf "common functions: %d\n" (List.length common);
  List.iter [ "IDENTICAL"; "OPERAND"; "OPCODE"; "LENGTH"; "PARSE" ]
    ~f:(fun cls ->
      let c = Option.value (Hashtbl.find counts cls) ~default:0 in
      let ex =
        Option.value (Hashtbl.find examples cls) ~default:[]
        |> String.concat ~sep:", "
      in
      Stdio.printf "%-10s %6d   e.g. %s\n" cls c ex)
