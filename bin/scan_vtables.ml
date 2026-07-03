(* Compare interface-vtable machinery between two ains, per struct:

   1. TABLES: member layout (names in order), interface list
      (iface name + vtable_offset), vmethods (resolved to names).
   2. CODE: the vtable ARRAY each class builds at runtime. Anchor on
      [PUSHSTRUCTPAGE; PUSH midx; REF] where member midx of the
      enclosing class is "<vtable>", then parse
      [DUP; PUSH len; PUSH -1 x3; CALLHLL]  (alloc length)
      [DUP; PUSH slot; PUSH fnidx; ASSIGN; POP]*  (slot table)
      and compare alloc length and slot -> method-name maps.

   Flags: STRUCT (only in one side), LAYOUT, IFACE, VMETH,
   NOALLOC (orig builds a vtable, ours doesn't), LEN, SLOT, NAME.

   Usage: scan_vtables ORIG.ain OURS.ain *)
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

let op_push = Bytecode.int_of_opcode PUSH
let op_pushstructpage = Bytecode.int_of_opcode PUSHSTRUCTPAGE
let op_ref = Bytecode.int_of_opcode REF
let op_dup = Bytecode.int_of_opcode DUP
let op_callhll = Bytecode.int_of_opcode CALLHLL
let op_assign = Bytecode.int_of_opcode ASSIGN
let op_pop = Bytecode.int_of_opcode POP

type ins = { op : int; args : int array }

(* Decode [s, e) into a linear instruction list; empty on decode failure. *)
let decode code s e =
  let len = Bytes.length code in
  let acc = ref [] in
  let p = ref s in
  let fail = ref false in
  while (not !fail) && !p < e && !p + 1 < len do
    let op = Stdlib.Bytes.get_int16_le code !p in
    let n = if op >= 0 && op < 0x10000 then arg_count_table.(op) else -1 in
    if n < 0 || !p + 2 + (n * 4) > len then fail := true
    else begin
      let args =
        Array.init n ~f:(fun i ->
            Int32.to_int_exn (Stdlib.Bytes.get_int32_le code (!p + 2 + (i * 4))))
      in
      acc := { op; args } :: !acc;
      p := !p + 2 + (n * 4)
    end
  done;
  if !fail then [||] else Array.of_list (List.rev !acc)

let function_ranges ain =
  let acc = ref [] in
  Ain.function_iter ain ~f:(fun f ->
      if (not (String.is_empty f.name)) && f.address > 0 then acc := f :: !acc);
  let sorted =
    !acc
    |> List.sort ~compare:(fun a b ->
           Int.compare a.Ain.Function.address b.Ain.Function.address)
  in
  let code_len = Bytes.length (Ain.get_code ain) in
  let rec loop = function
    | [] -> []
    | [ last ] ->
      [ (last.Ain.Function.name, last.address, min (last.address + 4096) code_len) ]
    | a :: b :: rest ->
      (a.Ain.Function.name, a.address, min b.Ain.Function.address code_len)
      :: loop (b :: rest)
  in
  loop sorted

(* struct name -> index of its "<vtable>" member, for structs that have one *)
let vtable_members ain =
  let h = Hashtbl.create (module String) in
  Ain.struct_iter ain ~f:(fun s ->
      List.iter s.members ~f:(fun (m : Ain.Variable.t) ->
          if String.equal m.name "<vtable>" then
            Hashtbl.set h ~key:s.name ~data:m.index));
  h

let enclosing_class fname =
  match String.rsplit2 fname ~on:'@' with Some (cls, _) -> Some cls | None -> None

(* All vtable builds in one ain:
   class name -> (builder fn, alloc len, [(slot, fnidx)]) *)
let vtable_builds ain =
  let code = Ain.get_code ain in
  let vt = vtable_members ain in
  let out = Hashtbl.create (module String) in
  List.iter (function_ranges ain) ~f:(fun (fname, s, e) ->
      match enclosing_class fname with
      | None -> ()
      | Some cls -> (
        match Hashtbl.find vt cls with
        | None -> ()
        | Some midx ->
          let ins = decode code s e in
          let n = Array.length ins in
          let i = ref 0 in
          while !i + 2 < n do
            let a = ins.(!i) and b = ins.(!i + 1) and c = ins.(!i + 2) in
            if
              a.op = op_pushstructpage && b.op = op_push
              && b.args.(0) = midx && c.op = op_ref
            then begin
              (* alloc: DUP; PUSH len; PUSH -1 x3; CALLHLL *)
              let j = !i + 3 in
              let len_found =
                if
                  j + 5 < n
                  && ins.(j).op = op_dup
                  && ins.(j + 1).op = op_push
                  && ins.(j + 2).op = op_push && ins.(j + 2).args.(0) = -1
                  && ins.(j + 3).op = op_push && ins.(j + 3).args.(0) = -1
                  && ins.(j + 4).op = op_push && ins.(j + 4).args.(0) = -1
                  && ins.(j + 5).op = op_callhll
                then Some (ins.(j + 1).args.(0), j + 6)
                else None
              in
              match len_found with
              | None -> Int.incr i
              | Some (alloc_len, k0) ->
                (* slots: DUP; PUSH slot; PUSH fnidx; ASSIGN; POP *)
                let slots = ref [] in
                let k = ref k0 in
                let continue_ = ref true in
                while !continue_ && !k + 4 < n do
                  if
                    ins.(!k).op = op_dup
                    && ins.(!k + 1).op = op_push
                    && ins.(!k + 2).op = op_push
                    && ins.(!k + 3).op = op_assign
                    && ins.(!k + 4).op = op_pop
                  then begin
                    slots := (ins.(!k + 1).args.(0), ins.(!k + 2).args.(0)) :: !slots;
                    k := !k + 5
                  end
                  else continue_ := false
                done;
                Hashtbl.set out ~key:cls ~data:(fname, alloc_len, List.rev !slots);
                i := !k
            end
            else Int.incr i
          done));
  out

let fn_name ain idx =
  if idx < 0 then "<null>"
  else if idx >= Ain.nr_functions ain then Printf.sprintf "<oob:%d>" idx
  else (Ain.get_function_by_index ain idx).name

let struct_name ain idx =
  if idx < 0 || idx >= Ain.nr_structs ain then Printf.sprintf "<oob:%d>" idx
  else (Ain.get_struct_by_index ain idx).name

let () =
  let orig = Ain.load Stdlib.Sys.argv.(1) in
  let ours = Ain.load Stdlib.Sys.argv.(2) in
  let issues = ref 0 in
  let report cls kind detail =
    Int.incr issues;
    Stdio.printf "%-8s %s  %s\n" kind cls detail
  in
  (* --- 1. struct tables --- *)
  let ostructs = Hashtbl.create (module String) in
  Ain.struct_iter orig ~f:(fun s -> Hashtbl.set ostructs ~key:s.name ~data:s);
  let ustructs = Hashtbl.create (module String) in
  Ain.struct_iter ours ~f:(fun s -> Hashtbl.set ustructs ~key:s.name ~data:s);
  Hashtbl.iteri ostructs ~f:(fun ~key:nm ~data:os ->
      match Hashtbl.find ustructs nm with
      | None -> report nm "STRUCT" "only in orig"
      | Some us ->
        let omem = List.map os.members ~f:(fun m -> m.Ain.Variable.name) in
        let umem = List.map us.members ~f:(fun m -> m.Ain.Variable.name) in
        if not (List.equal String.equal omem umem) then
          report nm "LAYOUT"
            (Printf.sprintf "members orig=[%s] ours=[%s]"
               (String.concat ~sep:"," omem) (String.concat ~sep:"," umem));
        let oif =
          List.map os.interfaces ~f:(fun (i : Ain.Struct.interface) ->
              Printf.sprintf "%s@%d" (struct_name orig i.struct_type) i.vtable_offset)
        in
        let uif =
          List.map us.interfaces ~f:(fun (i : Ain.Struct.interface) ->
              Printf.sprintf "%s@%d" (struct_name ours i.struct_type) i.vtable_offset)
        in
        if not (List.equal String.equal oif uif) then
          report nm "IFACE"
            (Printf.sprintf "orig=[%s] ours=[%s]"
               (String.concat ~sep:"," oif) (String.concat ~sep:"," uif));
        let ovm = List.map os.vmethods ~f:(fn_name orig) in
        let uvm = List.map us.vmethods ~f:(fn_name ours) in
        if not (List.equal String.equal ovm uvm) then
          report nm "VMETH"
            (Printf.sprintf "orig=[%s] ours=[%s]"
               (String.concat ~sep:"; " ovm) (String.concat ~sep:"; " uvm)));
  Hashtbl.iteri ustructs ~f:(fun ~key:nm ~data:_ ->
      if not (Hashtbl.mem ostructs nm) then report nm "STRUCT" "only in ours");
  (* --- 2. runtime vtable builds --- *)
  let ob = vtable_builds orig in
  let ub = vtable_builds ours in
  Hashtbl.iteri ob ~f:(fun ~key:cls ~data:(ofn, olen, oslots) ->
      match Hashtbl.find ub cls with
      | None -> report cls "NOALLOC" (Printf.sprintf "orig builds vtable in %s, ours has no build" ofn)
      | Some (_, ulen, uslots) ->
        if olen <> ulen then
          report cls "LEN" (Printf.sprintf "alloc orig=%d ours=%d" olen ulen);
        let okeys = List.map oslots ~f:fst and ukeys = List.map uslots ~f:fst in
        if not (List.equal Int.equal okeys ukeys) then
          report cls "SLOT"
            (Printf.sprintf "slot sets differ: orig=[%s] ours=[%s]"
               (String.concat ~sep:"," (List.map okeys ~f:Int.to_string))
               (String.concat ~sep:"," (List.map ukeys ~f:Int.to_string)))
        else
          List.iter2_exn oslots uslots ~f:(fun (slot, oidx) (_, uidx) ->
              let onm = fn_name orig oidx and unm = fn_name ours uidx in
              if not (String.equal onm unm) then
                report cls "NAME" (Printf.sprintf "slot %d: orig->%s ours->%s" slot onm unm)));
  Hashtbl.iteri ub ~f:(fun ~key:cls ~data:(ufn, _, _) ->
      if not (Hashtbl.mem ob cls) then
        report cls "EXTRA" (Printf.sprintf "ours builds vtable in %s, orig has no build" ufn));
  Stdio.printf "total flagged: %d\n" !issues
