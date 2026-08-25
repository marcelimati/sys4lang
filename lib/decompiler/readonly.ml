(* v12 readonly inference.

   The v12 compiler emits two copies of every property getter (and of
   some ref-returning methods): the second copy is compiled with a
   readonly [this]. Inside any body, a getter/method call whose receiver
   is readonly targets the second ("#1") copy. Readonly-ness comes from
   declarations — [readonly ref T] parameters, members and locals, and
   [readonly] methods — none of which survive in the .ain: the type
   codes are identical, only the callee indices differ.

   This pass recovers those declarations from the callee choices:
   - a call to a rank-0 copy proves every object along the receiver
     chain (this / local / member / single-copy call result) mutable;
   - a call to a rank>=1 copy demands at least one readonly object
     along the chain. Clauses are resolved by elimination against the
     mutability facts, then the remainder by a fixed preference
     (member > local > this > function result).

   Results are exposed for the printer via [is_local_readonly],
   [is_member_readonly] and [is_method_readonly]. *)
open Base
open Ast

let readonly_locals : (string, unit) Hashtbl.t = Hashtbl.create (module String)
let mutable_locals : (string, unit) Hashtbl.t = Hashtbl.create (module String)
let readonly_members : (string, unit) Hashtbl.t = Hashtbl.create (module String)
let mutable_members : (string, unit) Hashtbl.t = Hashtbl.create (module String)
let readonly_this : (int, unit) Hashtbl.t = Hashtbl.create (module Int)
let mutable_this : (int, unit) Hashtbl.t = Hashtbl.create (module Int)
let readonly_result : (int, unit) Hashtbl.t = Hashtbl.create (module Int)
let mutable_result : (int, unit) Hashtbl.t = Hashtbl.create (module Int)

(* function id -> (rank within its exact-signature family, family size) *)
let copy_rank : (int, int * int) Hashtbl.t = Hashtbl.create (module Int)

let rank id = Option.value (Hashtbl.find copy_rank id) ~default:(0, 1)
let is_readonly_copy id = fst (rank id) >= 1
let has_copies id = snd (rank id) > 1

let sig_key (f : Ain.Function.t) =
  String.concat ~sep:"|"
    (f.name
    :: Type.show_ain_type f.return_type
    :: List.map (Ain.Function.args f) ~f:(fun v -> Type.show_ain_type v.type_))

let build_ranks () =
  Hashtbl.clear copy_rank;
  let fam = Hashtbl.create (module String) in
  (* Interface prototypes (no body) are duplicated too — vtable calls
     through an interface resolve to them. *)
  Array.iter Ain.ain.func ~f:(fun f ->
      Hashtbl.add_multi fam ~key:(sig_key f) ~data:f.id);
  Hashtbl.iter fam ~f:(fun ids ->
      let ids = List.rev ids in
      let n = List.length ids in
      List.iteri ids ~f:(fun r id -> Hashtbl.set copy_rank ~key:id ~data:(r, n)))

(* Array HLL twins: [At]/[At#1] share an identical signature; the
   second is the readonly one. Rank of an HLL function within its
   identical-signature group, and the group size. *)
let hll_rank (lib_name : string) (hf : Ain.HLL.function_t) =
  match
    Array.find Ain.ain.hll0 ~f:(fun l -> String.equal l.name lib_name)
  with
  | None -> (0, 1)
  | Some lib ->
      let same (g : Ain.HLL.function_t) =
        String.equal g.name hf.name
        && Poly.equal g.return_type hf.return_type
        && Poly.equal (Ain.HLL.arg_types g) (Ain.HLL.arg_types hf)
      in
      let group = Array.filter lib.functions ~f:same in
      let r =
        Array.findi group ~f:(fun _ g -> phys_equal g hf)
        |> Option.value_map ~default:0 ~f:fst
      in
      (r, Array.length group)

let local_key (f : Ain.Function.t) i = Printf.sprintf "%d:%d" f.id i
let member_key si mi = Printf.sprintf "%d:%d" si mi

let var_index (f : Ain.Function.t) (v : Ain.Variable.t) =
  Array.findi f.vars ~f:(fun _ x -> phys_equal x v) |> Option.map ~f:fst

(* Struct member records are physically shared with [Ain.ain.strt]. *)
let member_cands : (string, (int * int * Ain.Variable.t) list) Hashtbl.t =
  Hashtbl.create (module String)

let member_of (v : Ain.Variable.t) =
  let cands =
    Hashtbl.find_or_add member_cands v.name ~default:(fun () ->
        Array.foldi Ain.ain.strt ~init:[] ~f:(fun si acc s ->
            Array.foldi s.members ~init:acc ~f:(fun mi acc m ->
                if String.equal m.name v.name then (si, mi, m) :: acc else acc)))
  in
  List.find_map cands ~f:(fun (si, mi, m) ->
      if phys_equal m v then Some (si, mi) else None)

(* ---- public queries ---- *)

let is_local_readonly (f : Ain.Function.t) (v : Ain.Variable.t) =
  match var_index f v with
  | Some i -> Hashtbl.mem readonly_locals (local_key f i)
  | None -> false

let is_member_readonly (s : Ain.Struct.t) (v : Ain.Variable.t) =
  match Array.findi s.members ~f:(fun _ x -> phys_equal x v) with
  | Some (mi, _) -> Hashtbl.mem readonly_members (member_key s.id mi)
  | None -> false

(* [readonly] suffix on a method/function definition: an inferred
   readonly [this] / readonly result, or the second copy of a
   duplicated method. *)
let is_method_readonly (f : Ain.Function.t) =
  match f.kind with
  | Normal ->
      Hashtbl.mem readonly_this f.id
      || Hashtbl.mem readonly_result f.id
      || is_readonly_copy f.id
  | _ -> false

(* ---- inference ---- *)

type atom = AThis of int | ALocal of string | AMember of string | AResult of int

type ctx = {
  fn : Ain.Function.t;
  parents : Ain.Function.t list; (* ParentPage 0 = hd *)
  this_fn : int; (* owning non-lambda function id *)
  this_known_ro : bool;
  in_copy : bool; (* body of a rank>=1 copy: locals not inferred *)
  foreach_alias : (Ain.Variable.t * expr) list;
}

(* Decompiled function with its nested lambdas (mirrors
   [CodeGen.function_t] without depending on it). *)
type fn_tree = {
  func : Ain.Function.t;
  body : statement Loc.loc;
  lambdas : fn_tree list;
}

let clauses : atom list list ref = ref []
let contradictions = ref 0
let heuristic_picks = ref 0

(* [None] = known readonly; [Some atoms] = readonly iff one of [atoms]. *)
let rec atoms ctx (e : expr) : atom list option =
  match e with
  | Page StructPage -> if ctx.this_known_ro then None else Some [ AThis ctx.this_fn ]
  | Load lv | RefTo lv -> atoms_lv ctx lv
  | TempRef (_, e) | Option e | InterfaceCast (_, e) | Copy e -> atoms ctx e
  | Call (Method (_, g), _) when has_copies g.id ->
      if is_readonly_copy g.id then None else Some []
  | Call (Method (_, g), _) | Call (Function g, _) -> Some [ AResult g.id ]
  | Call (HllFunc _, r :: _) -> atoms ctx r
  | _ -> Some []

and atoms_lv ctx (lv : lvalue) : atom list option =
  match lv with
  | Var (LocalPage, v) -> (
      match List.find ctx.foreach_alias ~f:(fun (x, _) -> phys_equal x v) with
      | Some (_, arr) -> atoms ctx arr
      | None -> (
          if ctx.in_copy then Some []
          else
            match var_index ctx.fn v with
            | Some i -> Some [ ALocal (local_key ctx.fn i) ]
            | None -> Some []))
  | Var (ParentPage lvl, v) -> (
      match List.nth ctx.parents lvl with
      | Some pf -> (
          match var_index pf v with
          | Some i when not (is_readonly_copy pf.id) ->
              Some [ ALocal (local_key pf i) ]
          | _ -> Some [])
      | None -> Some [])
  | Var (StructPage, v) -> (
      let this_atoms = if ctx.this_known_ro then None else Some [ AThis ctx.this_fn ] in
      match (this_atoms, member_of v) with
      | None, _ -> None
      | Some a, Some (si, mi) -> Some (AMember (member_key si mi) :: a)
      | Some a, None -> Some a)
  | Var (GlobalPage, _) -> Some []
  | Member (obj, v) -> (
      match atoms ctx obj with
      | None -> None
      | Some a -> (
          match member_of v with
          | Some (si, mi) -> Some (AMember (member_key si mi) :: a)
          | None -> Some a))
  | Elem (arr, _) | Slot (arr, _) -> atoms ctx arr
  | Pointee e -> atoms ctx e
  | IncDec (_, _, lv) -> atoms_lv ctx lv
  | NullPlace -> Some []

let mark_mutable = function
  | AThis id -> Hashtbl.set mutable_this ~key:id ~data:()
  | ALocal k -> Hashtbl.set mutable_locals ~key:k ~data:()
  | AMember k -> Hashtbl.set mutable_members ~key:k ~data:()
  | AResult id -> Hashtbl.set mutable_result ~key:id ~data:()

let mark_readonly = function
  | AThis id -> Hashtbl.set readonly_this ~key:id ~data:()
  | ALocal k -> Hashtbl.set readonly_locals ~key:k ~data:()
  | AMember k -> Hashtbl.set readonly_members ~key:k ~data:()
  | AResult id -> Hashtbl.set readonly_result ~key:id ~data:()

let is_mutable = function
  | AThis id -> Hashtbl.mem mutable_this id
  | ALocal k -> Hashtbl.mem mutable_locals k
  | AMember k -> Hashtbl.mem mutable_members k
  | AResult id -> Hashtbl.mem mutable_result id

let is_readonly = function
  | AThis id -> Hashtbl.mem readonly_this id
  | ALocal k -> Hashtbl.mem readonly_locals k
  | AMember k -> Hashtbl.mem readonly_members k
  | AResult id -> Hashtbl.mem readonly_result id

let debug = Option.is_some (Stdlib.Sys.getenv_opt "SYS4DC_READONLY_DEBUG")
let clause_origin : (atom list, string) Hashtbl.Poly.t = Hashtbl.Poly.create ()

let atom_to_string = function
  | AThis id -> "this@" ^ Ain.ain.func.(id).name
  | ALocal k -> "local " ^ k
  | AMember k -> "member " ^ k
  | AResult id -> "result@" ^ Ain.ain.func.(id).name

let evidence ctx ~where (r, n) recv =
  if n > 1 then
    match (r, atoms ctx recv) with
    | 0, Some a -> List.iter a ~f:mark_mutable
    | 0, None ->
        Int.incr contradictions;
        if debug then Stdio.eprintf "  contradiction (rank0 on readonly): %s
" where
    | _, None -> ()
    | _, Some [] ->
        Int.incr contradictions;
        if debug then Stdio.eprintf "  contradiction (rank1, no atoms): %s
" where
    | _, Some a ->
        clauses := a :: !clauses;
        if debug then Hashtbl.set clause_origin ~key:a ~data:where

let collect_function ctx (body : statement Loc.loc) =
  let expr_cb (e : expr) =
    match e with
    | Call (Method (recv, c), _) when has_copies c.id ->
        evidence ctx ~where:(ctx.fn.name ^ " -> " ^ c.name) (rank c.id) recv
    | Call (HllFunc (lib, hf), recv :: _) ->
        evidence ctx ~where:(ctx.fn.name ^ " -> " ^ lib ^ "." ^ hf.name)
          (hll_rank lib hf) recv
    | _ -> ()
  in
  walk ~expr_cb body

let rec collect (parents : Ain.Function.t list) this_fn this_known_ro
    (f : fn_tree) =
  let aliases = ref [] in
  walk
    ~stmt_cb:(fun s ->
      match s with
      | ForEach { var; array; _ } -> aliases := (var, array) :: !aliases
      | _ -> ())
    f.body;
  let is_lambda = match f.func.kind with Lambda -> true | _ -> false in
  let this_fn = if is_lambda then this_fn else f.func.id in
  let this_known_ro =
    if is_lambda then this_known_ro else is_readonly_copy f.func.id
  in
  let ctx =
    {
      fn = f.func;
      parents;
      this_fn;
      this_known_ro;
      in_copy = is_readonly_copy this_fn;
      foreach_alias = !aliases;
    }
  in
  collect_function ctx f.body;
  List.iter f.lambdas ~f:(collect (f.func :: parents) this_fn this_known_ro)

let resolve () =
  let pending = ref !clauses in
  let progress = ref true in
  while !progress do
    progress := false;
    pending :=
      List.filter !pending ~f:(fun cl ->
          if List.exists cl ~f:is_readonly then false
          else
            match List.filter cl ~f:(fun a -> not (is_mutable a)) with
            | [] ->
                Int.incr contradictions;
                if debug then
                  Stdio.eprintf "  contradiction (all mutable): %s [%s]
"
                    (Option.value (Hashtbl.find clause_origin cl) ~default:"?")
                    (String.concat ~sep:" | " (List.map cl ~f:atom_to_string));
                false
            | [ a ] ->
                mark_readonly a;
                progress := true;
                false
            | _ -> true)
  done;
  (* Remaining clauses: fixed preference. *)
  let prio = function
    | AMember _ -> 0
    | ALocal _ -> 1
    | AThis _ -> 2
    | AResult _ -> 3
  in
  List.iter !pending ~f:(fun cl ->
      if not (List.exists cl ~f:is_readonly) then
        match
          List.filter cl ~f:(fun a -> not (is_mutable a))
          |> List.sort ~compare:(fun a b -> Int.compare (prio a) (prio b))
        with
        | a :: _ as cands ->
            Int.incr heuristic_picks;
            if debug then
              Stdio.eprintf "  heuristic: %s picks %s of [%s]
"
                (Option.value (Hashtbl.find clause_origin cl) ~default:"?")
                (atom_to_string a)
                (String.concat ~sep:" | " (List.map cands ~f:atom_to_string));
            mark_readonly a
        | [] -> ())

let infer (funcs : fn_tree list) =
  build_ranks ();
  clauses := [];
  contradictions := 0;
  heuristic_picks := 0;
  List.iter funcs ~f:(fun f -> collect [] f.func.id false f);
  let n_clauses = List.length !clauses in
  resolve ();
  if n_clauses > 0 then
  Stdio.eprintf
    "readonly inference: %d clauses, %d locals, %d members, %d methods, %d results, %d heuristic, %d contradictions\n"
    n_clauses
    (Hashtbl.length readonly_locals)
    (Hashtbl.length readonly_members)
    (Hashtbl.length readonly_this)
    (Hashtbl.length readonly_result)
    !heuristic_picks !contradictions
