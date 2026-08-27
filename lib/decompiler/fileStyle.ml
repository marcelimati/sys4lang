(* Per-source-file compiler style markers.

   The original Rance10 .ain was linked from objects compiled by more
   than one build of the v12 compiler: within a source file a branch
   condition [if (!call())] is either always compiled with the NOT
   kept ([call; NOT; IFNZ then; JUMP else]) or always peeled
   ([call; IFZ then; JUMP else]); across files it is ~50/50 (76 of 90
   files with evidence are pure). The style is not derivable from the
   source, so it is recorded as a magic comment on the first line of
   the emitted .jaf ([// sys4c-codegen: not-peel=keep|peel]) that sys4c
   honors. *)
open Base

let not_peel : (string, bool) Hashtbl.t = Hashtbl.create (module String)

(* Second per-file bit: [if (c) return;] (single bare RETURN body, no
   else) compiled as the short skip form ([IFZ end; RETURN; end:]) vs
   the long form ([IFNZ then; JUMP end; then: RETURN; end:]) - pure in
   96 of 109 files with evidence (34 short files). *)
let if_ret_short : (string, bool) Hashtbl.t = Hashtbl.create (module String)

let is_cmp (i : Instructions.instruction) =
  match i with
  | EQUALE | NOTE | LT | GT | LTE | GTE | F_LT | F_GT | F_LTE | F_GTE
  | S_EQUALE | S_NOTE | F_EQUALE | F_NOTE | R_EQUALE | R_NOTE ->
      true
  | _ -> false

let is_call (i : Instructions.instruction) =
  match i with CALLMETHOD _ | CALLFUNC _ | CALLHLL _ -> true | _ -> false

let compute (files : (string * CodeSection.function_t list) list) =
  Hashtbl.clear not_peel;
  Hashtbl.clear if_ret_short;
  List.iter files ~f:(fun (fname, funcs) ->
      let kept = ref 0 and peeled = ref 0 in
      let ret_short = ref 0 and ret_long = ref 0 in
      List.iter funcs ~f:(fun f ->
          let code = Array.of_list (List.map f.code ~f:(fun l -> l.Loc.txt)) in
          Array.iteri code ~f:(fun i ins ->
              match ins with
              | IFZ _ | IFNZ _ when i >= 2 -> (
                  match (code.(i - 1), code.(i - 2)) with
                  | NOT, src when is_call src -> Int.incr kept
                  | src, _
                    when is_call src
                         && (match ins with IFZ _ -> true | _ -> false)
                         && i + 1 < Array.length code
                         && (match code.(i + 1) with JUMP _ -> true | _ -> false) ->
                      Int.incr peeled
                  | _ -> ())
              | _ -> ()));
      (* single-RETURN if bodies: [IFZ L; RETURN; L:] (short) vs
         [IFNZ L1; JUMP L2; L1: RETURN; L2:] (long) *)
      List.iter funcs ~f:(fun f ->
          let code = Array.of_list f.code in
          let n = Array.length code in
          Array.iteri code ~f:(fun i (l : Instructions.instruction Loc.loc) ->
              match l.txt with
              | IFZ target when i + 2 < n -> (
                  match (code.(i + 1).txt, code.(i + 2).addr) with
                  | RETURN, a when a = target -> Int.incr ret_short
                  | _ -> ())
              | IFNZ t1 when i + 3 < n -> (
                  match
                    ( code.(i + 1).txt,
                      code.(i + 2).txt,
                      code.(i + 2).addr,
                      code.(i + 3).addr )
                  with
                  | JUMP t2, RETURN, a1, a2 when a1 = t1 && a2 = t2 ->
                      Int.incr ret_long
                  | _ -> ())
              | _ -> ()));
      if !ret_short + !ret_long > 0 then
        Hashtbl.set if_ret_short ~key:fname ~data:(!ret_short > !ret_long);
      if !kept + !peeled > 0 then
        Hashtbl.set not_peel ~key:fname ~data:(!peeled > !kept))

let marker fname =
  let bits =
    List.filter_opt
      [
        Option.map (Hashtbl.find not_peel fname) ~f:(fun peel ->
            "not-peel=" ^ if peel then "peel" else "keep");
        Option.map (Hashtbl.find if_ret_short fname) ~f:(fun short ->
            "if-ret-short=" ^ if short then "1" else "0");
      ]
  in
  if List.is_empty bits then None
  else Some ("// sys4c-codegen: " ^ String.concat ~sep:";" bits)
