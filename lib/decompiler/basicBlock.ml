(* Copyright (C) 2024 kichikuou <KichikuouChrome@gmail.com>
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

open Base
open Loc
open Ast
open Instructions

type terminator = BlockEval.terminator =
  | Seq
  | Jump of int (* addr *)
  | Branch of int * expr (* (addr, cond) - jumps if cond == 0 *)
  | Switch0 of int * expr
  | DoWhile0 of int (* addr of branching basic block *)
[@@deriving show { with_path = false }]

let seq_terminator = BlockEval.seq_terminator

type fragment = terminator loc * Ast.statement loc list
[@@deriving show { with_path = false }]

type 'a basic_block = {
  addr : int;
  end_addr : int;
  labels : label loc list;
  code : 'a;
  mutable nr_jump_srcs : int;
}
[@@deriving show { with_path = false }]

type t = fragment basic_block [@@deriving show { with_path = false }]

let ( == ) = phys_equal

(* -------------------------------------------------------------------------
   Basic block construction
   ------------------------------------------------------------------------- *)

let branch_target = function
  | JUMP addr -> Some addr
  | IFZ addr -> Some addr
  | IFNZ addr -> Some addr
  | SH_IF_LOC_LT_IMM (_, _, addr) -> Some addr
  | SH_IF_LOC_GT_IMM (_, _, addr) -> Some addr
  | SH_IF_LOC_GE_IMM (_, _, addr) -> Some addr
  | SH_IF_LOC_NE_IMM (_, _, addr) -> Some addr
  | SH_IF_STRUCTREF_Z (_, addr) -> Some addr
  | SH_IF_STRUCT_A_NOT_EMPTY (_, addr) -> Some addr
  | SH_IF_SREF_NE_STR0 (_, addr) -> Some addr
  | SH_IF_STRUCTREF_GT_IMM (_, _, addr) -> Some addr
  | SH_IF_STRUCTREF_NE_IMM (_, _, addr) -> Some addr
  | SH_IF_STRUCTREF_EQ_IMM (_, _, addr) -> Some addr
  | SH_IF_STRUCTREF_NE_LOCALREF (_, _, addr) -> Some addr
  | _ -> None

let make_basic_blocks func_end_addr code =
  let head_addrs = Hashtbl.create (module Int) in
  let add d labels addr =
    let labels =
      List.map labels ~f:(fun label -> { txt = label; addr; end_addr = addr })
    in
    Hashtbl.update head_addrs addr ~f:(function
      | None -> (d, labels)
      | Some (n, labels') -> (n + d, labels @ labels'))
  in
  let add_case_addrs sw_id is_str =
    let sw = Ain.ain.swi0.(sw_id) in
    Array.iter sw.cases ~f:(function case ->
        let label =
          if is_str then
            CaseStr (sw_id, Ain.ain.str0.(Int32.to_int_exn case.value))
          else CaseInt (sw_id, case.value)
        in
        add 1 [ label ] (Int32.to_int_exn case.address));
    add 1 [ Default sw_id ] (Int32.to_int_exn sw.default_address)
  in
  let rec scan = function
    | { txt = SWITCH n; _ } :: tl ->
        add_case_addrs n false;
        add_and_scan tl
    | { txt = STRSWITCH n; _ } :: tl ->
        add_case_addrs n true;
        add_and_scan tl
    | { txt = op; _ } :: tl -> (
        match branch_target op with
        | Some addr ->
            add 1 [] addr;
            add_and_scan tl
        | None -> scan tl)
    | [] -> ()
  and add_and_scan code =
    match code with
    | hd :: _ ->
        add 0 [] hd.addr;
        scan code
    | [] -> ()
  in
  add_and_scan code;
  let rec aux acc = function
    | (inst : instruction loc) :: tl ->
        let insts, rest =
          List.split_while tl ~f:(function { addr; _ } ->
              not (Hashtbl.mem head_addrs addr))
        in
        let end_addr =
          match rest with { addr; _ } :: _ -> addr | [] -> func_end_addr
        in
        let nr_jump_srcs, labels = Hashtbl.find_exn head_addrs inst.addr in
        let basic_block =
          {
            addr = inst.addr;
            end_addr;
            labels;
            code = inst :: insts;
            nr_jump_srcs;
          }
        in
        aux (basic_block :: acc) rest
    | [] -> List.rev acc
  in
  aux [] code

(* -------------------------------------------------------------------------
   Expression reconstruction across basic blocks

   Short-circuit and conditional expressions (&&, ||, ?:, and the ain v11+
   null-conditional forms obj?.member / a ?? b) are compiled into
   conditional branches, so a single expression can span several basic
   blocks:

       <a> IFZ Lelse; <b> JUMP Lend; Lelse: <c>; Lend: ...    (a ? b : c)

   BlockEval.analyze evaluates one block at a time; when it reaches the
   terminator while an expression is still open, values remain on the
   symbolic stack. This section reconnects such blocks.

   Blocks are processed in address order. The evaluation state at the end
   of a block that does not complete a statement is propagated along its
   outgoing edges as an "inflow" of each target block. Expression code
   never branches backwards, so a target block is always processed after
   all of its inflows are known. When the block ends with a branch, the
   branch condition is pushed onto the state's condition list, recording
   the decision that leads to each path. A block that receives two inflows
   is the join point of a conditional expression; merge_inflows compares
   the two states and reconstructs the operator that produced the fork
   (see the merge rules below).

   Shared-tail invariant: two states flowing into the same join point were
   forked from a common state, and everything below the operands of the
   forking operator must be untouched on both paths. The merge rules verify
   this cheaply with phys_equal ( == ) on the tails of the condition /
   stack / stmts lists.

   A block whose state is settled (empty stack, no pending conditions) at
   its terminator completes a statement. It is emitted as an output block;
   statement-level control flow between output blocks is reconstructed
   later by ControlFlow. One ambiguity remains here: the leading branches
   of a value-producing && / || / ?: that starts a statement also execute
   on a settled state, so they are indistinguishable from statement-level
   control flow at this point. They are provisionally emitted as well and
   reclaimed later by merge_emitted_branches when the join point reveals
   the mistake. *)

(* Symbolic evaluation state carried along a forward CFG edge. *)
type state = {
  condition : expr list;
      (* conditions of the branches taken since the last settled state,
         most recent first *)
  stack : expr list; (* the symbolic value stack *)
  stmts : Ast.statement loc list; (* generated statements, most recent first *)
}
[@@deriving show { with_path = false }]

let empty_state = { condition = []; stack = []; stmts = [] }
let make_option = function Option _ as obj -> obj | obj -> Option obj
let strip_option = function Option obj -> obj | obj -> obj

(* ---- Merge rules for null-checked forks (ain v11+ ?. and ?? operators) ----

   The v11+ compiler expands obj?.member and a ?? b into a null check
   followed by a fork:

       <obj> DUP; PUSH -1; EQUALE; IFNZ Lnull
       <evaluate member using obj>    ; leaves the value slots, if any,
       PUSH 0                         ; and a "was not null" marker on top
       JUMP Ljoin
     Lnull:
       POP; PUSH -1; ...              ; placeholders of the same depth
     Ljoin:

   so the two states reaching the join point are distinguished by their
   most recent conditions: !(obj == -1) on the non-null path and
   (obj == -1) on the null path. At the join, the ok path's marker and the
   null path's top placeholder merge into the Option-typed value
   Option(obj), and the slots below merge into the member value.

   Each rule below inverts one shape of the forked code. All rules take
     [obj]   the null-checked expression (possibly already Option-wrapped
             by the merge of an inner ?. of a chain),
     [conds] the conditions remaining after consuming the null check,
     [ok]    the state of the non-null path,
     [null]  the state of the null path,
   and return the merged state, or None if the shape does not match. *)

(* a ?? b -- both paths leave a proper value (not a placeholder):
     ok: [a | t]   null: [b | t]
     => [a{obj -> Option obj} ?? b | t] *)
let null_coalesce ~obj ~conds (ok : state) (null : state) =
  match (ok.stack, null.stack) with
  | e1 :: es1, e2 :: es2
    when Ain.ain.vers >= 11 && es1 == es2 && ok.stmts == null.stmts ->
      let obj = strip_option obj in
      Some
        {
          condition = conds;
          stack =
            BinaryOp (PSEUDO_NULL_COALESCE, insert_option e1 obj, e2) :: es1;
          stmts = ok.stmts;
        }
  | _ -> None

(* obj?.member evaluating to a value:
     ok: [0; v | t]        null: [-1; -1 | t]        (plain value)
     ok: [0; num; v | t]   null: [-1; -1; -1 | t]    (fat value)
     ok: [0; Void; v | t]  null: [-1; -1; -1 | t]    (interface value)
     => [Option obj; ... | t] *)
let nullable_member_value ~obj ~conds (ok : state) (null : state) =
  match (ok.stack, null.stack) with
  | Number 0l :: e :: es1, Number -1l :: Number -1l :: es2 when es1 == es2 ->
      Some
        {
          condition = conds;
          stack = make_option obj :: e :: es1;
          stmts = ok.stmts;
        }
  | ( Number 0l :: (Number _ as n) :: e :: es1,
      Number -1l :: Number -1l :: Number -1l :: es2 )
    when es1 == es2 ->
      Some
        {
          condition = conds;
          stack = make_option obj :: n :: e :: es1;
          stmts = ok.stmts;
        }
  | Number 0l :: Void :: e :: es1, Number -1l :: Number -1l :: Number -1l :: es2
    when es1 == es2 ->
      (* Interfaces are null-checked on their loaded value, but the merged
         expression refers to the reference itself. *)
      let obj = match obj with Load o -> RefTo o | _ -> obj in
      Some
        {
          condition = conds;
          stack = make_option obj :: Void :: e :: es1;
          stmts = ok.stmts;
        }
  | _ -> None

(* obj?.member consumed within a statement -- the use of the member was
   already emitted as a statement, but only on the ok path; rewrite it to
   record the null check.
     obj?.void_method():
       ok: [0 | t] stmts = stmt :: S   null: [-1 | t] stmts = S
       (the marker may also be an Option produced by an inner ?. merge)
     obj?.member op= value:
       ok: [] stmts = stmt :: S        null: [] stmts = S
     => stmt{obj -> Option obj} *)
let nullable_member_statement ~obj ~conds (ok : state) (null : state) =
  match (ok.stack, ok.stmts, null.stack) with
  | ( e1 :: es1,
      ({ txt = Expression expr; _ } as stmt) :: stmts1,
      Number -1l :: es2 )
    when es1 == es2 && stmts1 == null.stmts
         &&
         match e1 with
         | Number 0l -> true
         | Option e -> contains_interface_expr e obj
         | _ -> false ->
      let obj = strip_option obj in
      Some
        {
          condition = conds;
          stack = Option obj :: es1;
          stmts =
            { stmt with txt = Expression (insert_option expr obj) } :: stmts1;
        }
  | [], ({ txt = Expression expr; _ } as stmt) :: stmts1, []
    when stmts1 == null.stmts -> (
      match obj with
      | Option obj ->
          Some
            {
              condition = conds;
              stack = [];
              stmts =
                { stmt with txt = Expression (insert_option expr obj) }
                :: stmts1;
            }
      | _ -> None)
  | _ -> None

(* obj?.e1 ?? e2 where e2 is itself null-checked (obj2?. ...):
     ok: [0; e1 | t]   null: [Option obj2; e2 | t]
     => [Option obj2; e1{obj -> Option obj} ?? e2 | t] *)
let chained_null_coalesce ~obj ~conds (ok : state) (null : state) =
  match (obj, ok.stack, null.stack) with
  | Option obj, Number 0l :: e1 :: es1, Option obj2 :: e2 :: es2
    when es1 == es2 && ok.stmts == null.stmts ->
      Some
        {
          condition = conds;
          stack =
            Option obj2
            :: BinaryOp (PSEUDO_NULL_COALESCE, insert_option e1 obj, e2)
            :: es2;
          stmts = ok.stmts;
        }
  | _ -> None

(* obj?.ref_member ?? ... -- the ok path evaluated a reference e through the
   null-checked inner value e':
     ok: [Option e'; e | t]   null: [-1; -1 | t]
     when e contains e' and e' refers to obj
     => [Option obj; e{e' -> Option e'} | t] *)
let nullable_ref_chain ~obj ~conds (ok : state) (null : state) =
  match (ok.stack, null.stack) with
  | Option e' :: e :: es1, Number -1l :: Number -1l :: es2
    when es1 == es2 && contains_expr e e' && contains_interface_expr e' obj ->
      let e = if Poly.equal e e' then e else insert_option e e' in
      Some
        {
          condition = conds;
          stack = make_option obj :: e :: es1;
          stmts = ok.stmts;
        }
  | _ -> None

(* obj?.fat_value -- like nullable_member_value, but the marker was already
   Option-wrapped by the merge of an inner ?. of the chain:
     ok: [Option e; e2; e | t]   null: [-1; -1; -1 | t]   (e refers to obj)
     => [Option obj; e2; e | t] *)
let chained_nullable_fat_value ~obj ~conds (ok : state) (null : state) =
  match (ok.stack, null.stack) with
  | Option e :: e2 :: e' :: es1, Number -1l :: Number -1l :: Number -1l :: es2
    when Poly.equal e e' && es1 == es2
         && contains_interface_expr e (strip_option obj) ->
      Some
        {
          condition = conds;
          stack = make_option obj :: e2 :: e' :: es1;
          stmts = ok.stmts;
        }
  | _ -> None

(* The ok path stored obj into a <dummy : 右辺値参照化用> variable and left a
   reference to it on the stack; undo the store and use obj directly.
     ok: [slot; LocalPage | t] stmts = (dummy = obj) :: S
     null: [0; -1 | t]         stmts = S
     => [Void; obj | t] *)
let strip_rvalue_ref_dummy (func : Ain.Function.t) ~obj ~conds (ok : state)
    (null : state) =
  match (obj, ok.stack, ok.stmts, null.stack) with
  | ( Option obj,
      Number slot :: Page LocalPage :: es1,
      { txt = Expression (AssignOp (ASSIGN, Var (LocalPage, v), rhs)); _ }
      :: stmts,
      Number 0l :: Number -1l :: es2 )
    when rhs == obj && es1 == es2 && stmts == null.stmts
         && func.vars.(Int32.to_int_exn slot) == v ->
      Some { condition = conds; stack = Void :: rhs :: es1; stmts }
  | _ -> None

let merge_null_checked (ctx : BlockEval.context) ~obj ~conds ok null =
  let rules =
    [
      null_coalesce;
      nullable_member_value;
      nullable_member_statement;
      chained_null_coalesce;
      nullable_ref_chain;
      chained_nullable_fat_value;
      strip_rvalue_ref_dummy ctx.func;
    ]
  in
  List.find_map rules ~f:(fun rule -> rule ~obj ~conds ok null)

(* ---- Merge rules for the plain conditional operators (?:, &&, ||) ----

   [first] is the state of the earlier-created edge (from the lower-address
   block) and [second] that of the later one. *)
let merge_conditional (first : state) (second : state) =
  match (first, second) with
  (* a ? b : c -- both arms leave one value:
       first: {a} [b | t]   second: {!a} [c | t] *)
  | ( { condition = c1 :: cs1; stack = e1 :: es1; _ },
      { condition = c2 :: cs2; stack = e2 :: es2; _ } )
    when are_negations c1 c2 && cs1 == cs2 && es1 == es2
         && first.stmts == second.stmts ->
      let e =
        match c1 with
        (* ain v11+ compiles ?: with IFNZ, negating the fall-through
           condition; flip the ternary to recover the source orientation. *)
        | UnaryOp (NOT, _) when Ain.ain.vers >= 11 -> TernaryOp (c2, e2, e1)
        | _ -> TernaryOp (c1, e1, e2)
      in
      Some { condition = cs1; stack = e :: es1; stmts = first.stmts }
  (* Same, for arms leaving a two-slot (fat) value. *)
  | ( { condition = c1 :: cs1; stack = e12 :: e11 :: es1; _ },
      { condition = c2 :: cs2; stack = e22 :: e21 :: es2; _ } )
    when are_negations c1 c2 && cs1 == cs2 && es1 == es2
         && first.stmts == second.stmts ->
      let stack =
        match c1 with
        | UnaryOp (NOT, _) ->
            TernaryOp (c2, e22, e12) :: TernaryOp (c2, e21, e11) :: es1
        | _ -> TernaryOp (c1, e12, e22) :: TernaryOp (c1, e11, e21) :: es1
      in
      Some { condition = cs1; stack; stmts = first.stmts }
  (* Two branches of a short-circuit chain jumping to the same address:
     the target is reached if !a (branching on the first operand) or
     a && !b (branching on the second). Used while evaluating a && b and
     a || b; the branch conditions merge into a disjunction. *)
  | { condition = c1 :: cs1; _ }, { condition = c2 :: c1' :: cs2; _ }
    when are_negations c1 c1' && cs1 == cs2
         && first.stack == second.stack
         && first.stmts == second.stmts ->
      Some { first with condition = BinaryOp (PSEUDO_LOGOR, c1, c2) :: cs1 }
  (* a && b as a value: the fall-through path (both conditions hold) pushed
     1; the short-circuit path (both branches, merged above into a
     disjunction) pushed 0. *)
  | ( { condition = c2 :: c1 :: cs1; stack = Number 1l :: es1; _ },
      {
        condition = BinaryOp (PSEUDO_LOGOR, c1', c2') :: cs2;
        stack = Number 0l :: es2;
        _;
      } )
    when are_negations c1 c1' && are_negations c2 c2' && cs1 == cs2
         && es1 == es2
         && first.stmts == second.stmts ->
      Some
        {
          condition = cs1;
          stack = BinaryOp (PSEUDO_LOGAND, c1, c2) :: es1;
          stmts = first.stmts;
        }
  (* a || b as a value: as above with 0 and 1 exchanged; here the merged
     disjunction c1' || c2' is the source expression itself. *)
  | ( { condition = c2 :: c1 :: cs1; stack = Number 0l :: es1; _ },
      {
        condition = BinaryOp (PSEUDO_LOGOR, c1', c2') :: cs2;
        stack = Number 1l :: es2;
        _;
      } )
    when are_negations c1 c1' && are_negations c2 c2' && cs1 == cs2
         && es1 == es2
         && first.stmts == second.stmts ->
      Some
        {
          condition = cs1;
          stack = BinaryOp (PSEUDO_LOGOR, c1', c2') :: es1;
          stmts = first.stmts;
        }
  | _ -> None

(* Merges two states flowing into the same join point. [first] is the inflow
   created earlier. The merged inflow keeps [first]'s block metadata, so the
   resulting block covers the whole expression region. *)
let merge_inflows ctx addr (first : state basic_block)
    (second : state basic_block) =
  let s1 = first.code and s2 = second.code in
  let merged =
    match (s1.condition, s2.condition) with
    | ( UnaryOp (NOT, BinaryOp (EQUALE, obj, Number -1l)) :: cs,
        BinaryOp (EQUALE, obj', Number -1l) :: conds )
      when obj == obj' && cs == conds ->
        merge_null_checked ctx ~obj ~conds s1 s2
    | ( BinaryOp (EQUALE, obj', Number -1l) :: conds,
        UnaryOp (NOT, BinaryOp (EQUALE, obj, Number -1l)) :: cs )
      when obj == obj' && cs == conds ->
        merge_null_checked ctx ~obj ~conds s2 s1
    | _ -> None
  in
  let merged =
    match merged with Some _ as m -> m | None -> merge_conditional s1 s2
  in
  match merged with
  | Some code -> { first with code }
  | None ->
      Printf.failwithf "cannot merge inflows at 0x%x:\nfirst = %s\nsecond = %s"
        addr
        ([%show: state basic_block] first)
        ([%show: state basic_block] second)
        ()

(* ---- Reclaiming provisionally emitted branch blocks ----

   A branch on a settled state is normally statement-level control flow and
   is emitted as an output block. However, the leading branches of a
   value-producing && / || / ?: look exactly the same when the operator
   starts a statement (nothing was on the stack when they executed):

       <a> IFZ Lfalse; <b> IFZ Lfalse; PUSH 1; JUMP Lend
       Lfalse: PUSH 0
       Lend: ...                                        (x = a && b;)

   The mistake becomes visible at the join point: the block after the one
   just processed has two value-carrying inflows that cannot be merged
   without the emitted branch conditions. The functions below un-emit the
   branch blocks and replay them through the standard merge rules: the two
   pending inflows are rewritten to the states that expression-level
   processing would have produced, and merge_conditional reconstructs the
   operator. *)

(* An inflow can be reclaimed if it is an untouched value chain forked at
   the un-emitted branch: no conditions or statements of its own, and one
   or two values on the stack. *)
let is_reclaimable_inflow (inflow : state basic_block) =
  match inflow.code with
  | { condition = []; stack = [ _ ] | [ _; _ ]; stmts = [] } -> true
  | _ -> false

(* The two states a Branch (_, cond) block evaluated in state (conds, [],
   stmts) would have dispatched: (fall-through edge, jump edge). *)
let branch_edge_states cond ~conds ~stmts =
  ( { condition = cond :: conds; stack = []; stmts },
    { condition = negate cond :: conds; stack = []; stmts } )

(* Two emitted branches jumping to the block that produced [latest]: the
   shape of a value-producing && / ||. The fall-through chain (which
   produced [second]) went through both branches; the target block joins
   the two jump edges, which merge into a short-circuit disjunction. *)
let reclaim_two_branches emitted (latest : state basic_block)
    (second : state basic_block) =
  match emitted with
  | { code = { txt = Branch (target', c2); _ }, []; _ }
    :: ({ code = { txt = Branch (target, c1); _ }, stmts; _ } as first)
    :: emitted'
    when latest.addr = target && latest.addr = target' ->
      let fall1, jump1 = branch_edge_states c1 ~conds:[] ~stmts in
      let fall2, jump2 = branch_edge_states c2 ~conds:fall1.condition ~stmts in
      Option.bind (merge_conditional jump1 jump2) ~f:(fun disjunction ->
          merge_conditional
            { fall2 with stack = second.code.stack }
            { disjunction with stack = latest.code.stack })
      |> Option.map ~f:(fun code ->
          ({ first with end_addr = latest.end_addr; code }, emitted'))
  | _ -> None

(* One emitted branch jumping to the arm that produced [latest] (or
   [second]): the shape of a value-producing ?:. *)
let reclaim_one_branch emitted (latest : state basic_block)
    (second : state basic_block) =
  match emitted with
  | ({ code = { txt = Branch (target, cond); _ }, stmts; _ } as first)
    :: emitted'
    when latest.addr = target || second.addr = target ->
      let fall, jump = branch_edge_states cond ~conds:[] ~stmts in
      let latest_edge, second_edge =
        if latest.addr = target then (jump, fall) else (fall, jump)
      in
      merge_conditional
        { second_edge with stack = second.code.stack }
        { latest_edge with stack = latest.code.stack }
      |> Option.map ~f:(fun code ->
          ({ first with end_addr = latest.end_addr; code }, emitted'))
  | _ -> None

(* -------------------------------------------------------------------------
   Driver
   ------------------------------------------------------------------------- *)

type driver = {
  ctx : BlockEval.context;
  inflows : (int, state basic_block list) Hashtbl.t;
      (* Evaluation states propagated along forward edges but not consumed
         yet, keyed by target address; most recently created edge first.
         Each inflow is the output block under construction: it carries the
         metadata (addr, labels, ...) of the block that will represent the
         whole expression region in the output. *)
}

let add_inflow t addr inflow =
  (* Expression code never branches backwards. *)
  assert (t.ctx.end_address <= addr);
  Hashtbl.add_multi t.inflows ~key:addr ~data:inflow

(* Replaces the two most recently created inflows of [addr] with [inflow]. *)
let replace_latest_inflows t addr inflow =
  Hashtbl.update t.inflows addr ~f:(function
    | Some (_ :: _ :: rest) -> inflow :: rest
    | Some _ -> Printf.failwithf "only one inflow at address %d" addr ()
    | None -> Printf.failwithf "no inflows at address %d" addr ())

(* Evaluates one basic block starting from the given state. *)
let eval_block t (flow : state basic_block) code end_addr =
  let ctx = t.ctx in
  ctx.condition <- flow.code.condition;
  ctx.stack <- flow.code.stack;
  ctx.stmts <- flow.code.stmts;
  ctx.instructions <- code;
  ctx.address <-
    (match flow.code.stmts with [] -> flow.addr | stmt :: _ -> stmt.end_addr);
  ctx.end_address <- end_addr;
  BlockEval.analyze ctx

let rec process t emitted = function
  | [] -> List.rev emitted
  | bb :: rest -> (
      (* The output block being built: bb itself when no expression is in
         progress, or the pending block of the expression region flowing
         into bb. *)
      let flow =
        match Hashtbl.find_and_remove t.inflows bb.addr with
        | None -> { bb with code = empty_state }
        | Some inflows ->
            (* Latest edge first: merge from the innermost fork outwards. *)
            List.reduce_exn inflows ~f:(fun merged earlier ->
                merge_inflows t.ctx bb.addr earlier merged)
      in
      let bb =
        {
          bb with
          addr = flow.addr;
          labels = flow.labels;
          nr_jump_srcs = flow.nr_jump_srcs;
        }
      in
      match eval_block t flow bb.code bb.end_addr with
      | term, [], stmts when List.is_empty t.ctx.condition ->
          (* The statement is complete; bb becomes an output block. *)
          merge_emitted_branches t
            ({ bb with code = (term, stmts) } :: emitted)
            rest
      | { txt = Branch (addr, cond); _ }, stack, stmts ->
          (* A branch in the middle of an expression: propagate the state to
             both targets, recording the branch condition taken. *)
          add_inflow t addr
            {
              flow with
              code =
                { condition = negate cond :: t.ctx.condition; stack; stmts };
            };
          add_inflow t bb.end_addr
            {
              flow with
              code = { condition = cond :: t.ctx.condition; stack; stmts };
            };
          merge_emitted_branches t emitted rest
      | { txt = Jump addr; _ }, stack, stmts ->
          add_inflow t addr
            { flow with code = { condition = t.ctx.condition; stack; stmts } };
          merge_emitted_branches t emitted rest
      | { txt = Seq; _ }, stack, stmts ->
          add_inflow t bb.end_addr
            { flow with code = { condition = t.ctx.condition; stack; stmts } };
          merge_emitted_branches t emitted rest
      | { txt = Switch0 _ | DoWhile0 _; _ }, _, _ ->
          failwith "switch in the middle of an expression")

(* Detects join points whose inflows expose provisionally emitted branch
   blocks (see the comment above is_reclaimable_inflow) and reclaims them.
   A two-branch shape is tried first (value-producing && / ||), then a
   single branch (value-producing ?:), whose result may itself be an arm
   of an enclosing conditional, so it is retried. *)
and merge_emitted_branches t emitted rest =
  assert (List.is_empty t.ctx.stmts);
  let inflow_pair =
    match rest with
    | [] -> None
    | bb :: _ -> (
        match Hashtbl.find t.inflows bb.addr with
        | Some (latest :: second :: _)
          when is_reclaimable_inflow latest && is_reclaimable_inflow second ->
            Some (latest, second)
        | _ -> None)
  in
  match inflow_pair with
  | None -> process t emitted rest
  | Some (latest, second) -> (
      match reclaim_two_branches emitted latest second with
      | Some (inflow, emitted') ->
          replace_latest_inflows t (List.hd_exn rest).addr inflow;
          process t emitted' rest
      | None -> (
          match reclaim_one_branch emitted latest second with
          | Some (inflow, emitted') ->
              replace_latest_inflows t (List.hd_exn rest).addr inflow;
              merge_emitted_branches t emitted' rest
          | None -> process t emitted rest))

let rec replace_delegate_calls acc = function
  | { addr = addr1; txt = DG_CALLBEGIN dg_type; _ }
    :: { addr = addr2; txt = DG_CALL (dg_type', addr4); _ }
    :: { addr = addr3; txt = JUMP addr2' as jump_op; end_addr }
    :: rest
    when dg_type = dg_type' && addr2 = addr2'
         && addr4 = addr3 + Instructions.width jump_op ->
      replace_delegate_calls
        ({ addr = addr1; end_addr; txt = PSEUDO_DG_CALL dg_type } :: acc)
        rest
  | insn :: rest -> replace_delegate_calls (insn :: acc) rest
  | [] -> List.rev acc

let from_instructions (f : CodeSection.function_t) code =
  let ctx : BlockEval.context =
    {
      func = f.func;
      struc = (match f.owner with Some (Struct s) -> Some s | _ -> None);
      parent = f.parent;
      instructions = [];
      address = -1;
      end_address = -1;
      stack = [];
      stmts = [];
      condition = [];
    }
  in
  let t = { ctx; inflows = Hashtbl.create (module Int) } in
  code |> replace_delegate_calls []
  |> make_basic_blocks f.end_addr
  |> process t []

let from_stmt (stmt : statement loc) =
  {
    addr = stmt.addr;
    end_addr = stmt.end_addr;
    labels = [];
    code = (seq_terminator, [ stmt ]);
    nr_jump_srcs = 0;
  }

let from_generated_constructor (s : Ain.Struct.t) (f : CodeSection.function_t) =
  match f.code with
  | { txt = PUSHSTRUCTPAGE; _ }
    :: { txt = PUSH varno; _ }
    :: { txt = REF; _ }
    :: { txt = DUP; _ }
    :: { txt = PUSH d1; _ }
    :: { txt = PUSH d2; _ }
    :: { txt = PUSH d3; _ }
    :: { txt = PUSH d4; _ }
    :: { txt = CALLHLL (lib, func, _); _ }
    :: code
    when let var = s.members.(Int32.to_int_exn varno) in
         let lib = Ain.ain.hll0.(lib) in
         let func = lib.functions.(func) in
         String.(
           var.name = "<vtable>" && lib.name = "Array" && func.name = "Alloc")
    ->
      let var = Load (Var (StructPage, s.members.(Int32.to_int_exn varno))) in
      let alloc =
        Expression
          (Call
             ( HllFunc ("Array", Ain.ain.hll0.(lib).functions.(func)),
               [ var; Number d1; Number d2; Number d3; Number d4 ] ))
      in
      let rec parse_vtable_initializer acc = function
        | { txt = DUP; _ }
          :: { txt = PUSH i; _ }
          :: { txt = PUSH m; _ }
          :: { txt = ASSIGN; _ }
          :: { txt = POP; _ }
          :: rest ->
            parse_vtable_initializer
              (Expression (AssignOp (ASSIGN, Slot (var, Number i), Number m))
              :: acc)
              rest
        | { txt = POP; _ } :: rest -> (acc, rest)
        | _ -> failwith "unexpected code in vtable initializer"
      in
      let stmts, rest = parse_vtable_initializer [ alloc ] code in
      let stmts =
        List.map stmts ~f:(fun stmt ->
            from_stmt
              {
                txt = stmt;
                addr = f.end_addr (* FIMXE *);
                end_addr = f.end_addr;
              })
      in
      List.rev_append stmts (from_instructions f rest)
  | _ -> from_instructions f f.code

let from_enum_stringifier (f : CodeSection.function_t) =
  match List.map ~f:(fun i -> i.txt) f.code with
  | PUSHLOCALPAGE :: PUSH varno :: REF :: code ->
      let var = Load (Var (LocalPage, f.func.vars.(Int32.to_int_exn varno))) in
      let rec parse = function
        | DUP :: PUSH n :: EQUALE :: IFZ _ :: POP :: S_PUSH s :: RETURN :: rest
          ->
            TernaryOp
              ( BinaryOp (EQUALE, var, Number n),
                String Ain.ain.str0.(s),
                parse rest )
        | [ POP; S_PUSH s; RETURN ] -> String Ain.ain.str0.(s)
        | _ -> failwith ("unexpected code in enum stringifier " ^ f.name)
      in
      from_stmt
        {
          txt = Return (Some (parse code));
          addr = (List.hd_exn f.code).addr;
          end_addr = f.end_addr;
        }
  | _ -> failwith ("unexpected prologue in enum stringifier " ^ f.name)

let create (f : CodeSection.function_t) =
  match (f.owner, f.name) with
  | Some (Enum _), _ -> (
      match f.name with
      | "String" -> [ from_enum_stringifier f ]
      | _ -> [] (* Enum functions other than String are ignored *))
  | Some (Struct s), ("0" | "2") -> from_generated_constructor s f
  | _ -> from_instructions f f.code

let generate_var_decls (func : Ain.Function.t) bbs =
  if Ain.ain.vers <= 1 then
    (* For ain v0/v1, we declare all locals at the top instead. *)
    bbs
  else
    let uninitialized_vars =
      ref (List.drop (Array.to_list func.vars) func.nr_args)
    in
    let mark_use var =
      uninitialized_vars :=
        List.filter !uninitialized_vars ~f:(fun v -> not (phys_equal v var))
    in
    let is_uninitialized var =
      if Stdlib.List.memq var !uninitialized_vars then (
        mark_use var;
        true)
      else false
    in
    let replace_stmt = function
      | VarDecl (var, None) as stmt ->
          mark_use var;
          stmt
      | Expression (AssignOp (insn, Var (LocalPage, var), expr))
        when is_uninitialized var ->
          VarDecl (var, Some (insn, expr))
      | Expression (Call (Builtin (A_ALLOC, Var (LocalPage, var)), _) as expr)
        when is_uninitialized var ->
          VarDecl (var, Some (ASSIGN, expr))
      | Expression
          (Call
             ( HllFunc ("Array", { name = "Alloc"; _ }),
               Load (Var (_, var)) :: dims ))
        when is_uninitialized var ->
          let dims =
            List.take_while dims ~f:(function Number -1l -> false | _ -> true)
          in
          VarDecl
            ( var,
              Some (ASSIGN, Call (Builtin (A_ALLOC, Var (LocalPage, var)), dims))
            )
      | Expression
          ( Call (Builtin (A_FREE, Var (LocalPage, var)), [])
          | Call
              (HllFunc ("Array", { name = "Free"; _ }), [ Load (Var (_, var)) ])
            )
        when is_uninitialized var && not (Ain.Variable.is_dummy var) ->
          VarDecl (var, None)
      | Expression (Call (Builtin2 (DG_CLEAR, Load (Var (LocalPage, var))), []))
        when is_uninitialized var ->
          VarDecl (var, None)
      | stmt -> stmt
    in
    List.map bbs ~f:(function { code = terminator, stmts; _ } as bb ->
        let stmts' =
          List.rev_map (List.rev stmts) ~f:(fun stmt ->
              { stmt with txt = replace_stmt stmt.txt })
        in
        { bb with code = (terminator, stmts') })

(* Ain v0/v1: declare every local at the top of the function body. *)
let prepend_var_decls (func : Ain.Function.t) (body : Ast.statement loc) =
  if Ain.ain.vers > 1 then body
  else
    let decls =
      List.drop (Array.to_list func.vars) func.nr_args
      |> List.filter ~f:(fun v -> not (Ain.Variable.is_dummy v))
      |> List.map ~f:(fun v ->
          { txt = VarDecl (v, None); addr = body.addr; end_addr = body.addr })
    in
    match body.txt with
    | Block stmts -> { body with txt = Block (stmts @ List.rev decls) }
    | _ -> { body with txt = Block (body :: List.rev decls) }
