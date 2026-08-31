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

(* Lambda bodies in a file can carry the OTHER long-if peel style than
   the file's plain functions (file 36: AddUserComponent's lambdas peel
   [if (!name.EndsWith(..))] while activity::detail::Release keeps its
   NOT). Evidence is pure per (file, context); emitted only when it
   differs from [not_peel]. *)
let lambda_not_peel : (string, bool) Hashtbl.t = Hashtbl.create (module String)

(* Second per-file bit: a negated condition OUTSIDE a long-form if -
   a while condition ([while (!x.Fn())] / [while (!flag)]: while-shaped
   loop [cond; IF? exit; body; JUMP head; exit:]) or a negated PLAIN
   operand in a short-form if ([if (!flag) stmt;]) - either keeps the
   NOT ([operand; NOT; IFZ skip]) or peels it ([operand; IFNZ skip]).
   Pure per file in Rance10 (loops: kept in 5 files / peeled in 18;
   plain short-ifs: kept in 3 / peeled in 15; no file on both sides)
   and independent of [not_peel] (25/36/84/163/384/429 are long-if
   keep but cond peel). Negated CALLS in a short-form if always peel
   (45 sites, 0 kept - both builds), and long-form ifs follow
   [not_peel]; this bit covers the rest. *)
let cond_peel : (string, bool) Hashtbl.t = Hashtbl.create (module String)

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
  Hashtbl.clear lambda_not_peel;
  Hashtbl.clear cond_peel;
  List.iter files ~f:(fun (fname, funcs) ->
      let kept = ref 0 and peeled = ref 0 in
      let lam_kept = ref 0 and lam_peeled = ref 0 in
      let cond_kept = ref 0 and cond_peeled = ref 0 in
      List.iter funcs ~f:(fun f ->
          let in_lambda = phys_equal f.CodeSection.func.kind Ain.Function.Lambda in
          let kept = if in_lambda then lam_kept else kept
          and peeled = if in_lambda then lam_peeled else peeled in
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
      (* Evidence sites: while-shaped loop exits (branch at [i]
         targeting [t] forward, the instruction right before [t] a
         JUMP back to at or before the branch) count any negated
         operand; short-form ifs (forward target, instruction before
         it neither that JUMP-back nor the long form's JUMP-over)
         count only PLAIN operands (calls peel in both builds). *)
      let is_read (i : Instructions.instruction) =
        match i with
        | SH_STRUCTREF _ | SH_LOCALREF _ | SH_GLOBALREF _ | REF -> true
        | _ -> false
      in
      List.iter funcs ~f:(fun f ->
          let code = Array.of_list f.code in
          let n = Array.length code in
          let idx_of_addr = Hashtbl.create (module Int) in
          Array.iteri code ~f:(fun i (l : Instructions.instruction Loc.loc) ->
              Hashtbl.set idx_of_addr ~key:l.addr ~data:i);
          Array.iteri code ~f:(fun i (l : Instructions.instruction Loc.loc) ->
              match l.txt with
              | (IFZ target | IFNZ target) when i >= 1 -> (
                  match Hashtbl.find idx_of_addr target with
                  | Some j when j > i + 1 && j <= n ->
                      let back_jump =
                        match code.(j - 1).txt with
                        | JUMP back -> (
                            match Hashtbl.find idx_of_addr back with
                            | Some bj -> if bj <= i then `Loop else `Over
                            | None -> `Over)
                        | _ -> `None
                      in
                      let long_form =
                        i + 2 < n
                        && (match code.(i + 1).txt with
                           | JUMP _ -> true
                           | _ -> false)
                        && code.(i + 2).addr = target
                      in
                      let prev = code.(i - 1).txt in
                      let prev2 =
                        if i >= 2 then Some code.(i - 2).txt else None
                      in
                      (match back_jump with
                      | `Loop -> (
                          match (prev, prev2, l.txt) with
                          | NOT, Some src, _
                            when is_call src || is_read src ->
                              Int.incr cond_kept
                          | src, _, IFNZ _ when is_call src || is_read src
                            ->
                              Int.incr cond_peeled
                          | _ -> ())
                      | `None when not long_form -> (
                          match (prev, prev2, l.txt) with
                          | NOT, Some src, _ when is_read src ->
                              Int.incr cond_kept
                          | src, _, IFNZ _ when is_read src ->
                              Int.incr cond_peeled
                          | _ -> ())
                      | _ -> ())
                  | _ -> ())
              | _ -> ()));
      if !cond_kept + !cond_peeled > 0 then
        Hashtbl.set cond_peel ~key:fname ~data:(!cond_peeled > !cond_kept);
      (* the plain-function bit falls back to lambda evidence and vice
         versa; the lambda bit is emitted only when it differs *)
      let func_bit =
        if !kept + !peeled > 0 then Some (!peeled > !kept)
        else if !lam_kept + !lam_peeled > 0 then Some (!lam_peeled > !lam_kept)
        else None
      in
      let lam_bit =
        if !lam_kept + !lam_peeled > 0 then Some (!lam_peeled > !lam_kept)
        else None
      in
      Option.iter func_bit ~f:(fun b -> Hashtbl.set not_peel ~key:fname ~data:b);
      match (func_bit, lam_bit) with
      | Some fb, Some lb when Bool.(fb <> lb) ->
          Hashtbl.set lambda_not_peel ~key:fname ~data:lb
      | _ -> ())

let marker fname =
  let bits =
    List.filter_opt
      [
        Option.map (Hashtbl.find not_peel fname) ~f:(fun peel ->
            "not-peel=" ^ if peel then "peel" else "keep");
        Option.map (Hashtbl.find lambda_not_peel fname) ~f:(fun peel ->
            "lambda-not-peel=" ^ if peel then "peel" else "keep");
        Option.map (Hashtbl.find cond_peel fname) ~f:(fun peel ->
            "cond-peel=" ^ if peel then "1" else "0");
      ]
  in
  if List.is_empty bits then None
  else Some ("// sys4c-codegen: " ^ String.concat ~sep:";" bits)
