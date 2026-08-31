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
  List.iter files ~f:(fun (fname, funcs) ->
      let kept = ref 0 and peeled = ref 0 in
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
      if !kept + !peeled > 0 then
        Hashtbl.set not_peel ~key:fname ~data:(!peeled > !kept))

let marker fname =
  let bits =
    List.filter_opt
      [
        Option.map (Hashtbl.find not_peel fname) ~f:(fun peel ->
            "not-peel=" ^ if peel then "peel" else "keep");
      ]
  in
  if List.is_empty bits then None
  else Some ("// sys4c-codegen: " ^ String.concat ~sep:";" bits)
