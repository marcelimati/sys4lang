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
open BasicBlock

(* -------------------------------------------------------------------------
   Statement-level control flow reconstruction

   The input is the basic block list of one function, in address order.
   Expression-level control flow (&&, ||, ?:) has already been folded into
   expressions by BasicBlock, so the remaining terminators are statement
   level: fall-through (Seq), goto (Jump), if (Branch) and switch (Switch0).
   This module rebuilds structured statements from them; jumps that fit no
   structure survive as goto statements.

   The blocks are held in a mutable doubly-linked list (CFG). Structured
   statements are recovered by reduction: when the blocks forming a control
   structure are recognized, the body blocks are spliced out of the list and
   collapsed into a single statement, and the whole structure is folded into
   the block where it starts, which becomes a plain fall-through block.

   1. Reduction scan (analyze / reduce). The scan visits the blocks
      backwards, so it reaches the blocks inside a structure before the
      block that heads it; when a head is visited, everything in its body
      region is already reduced, and each rule only has to match a flat
      block-level pattern. Backward conditional branches (do-while loops)
      are the exception since their body precedes the branch:
      reduce_backward_branch only plants a DoWhile0 marker in front of the
      loop head, and the actual reduction happens when the scan arrives at
      the marker (reduce_do_while).

   2. Region collapse (collapse). A fully reduced region becomes one
      statement in three steps:
        a. recover_forever_loops: remaining backward jumps close
           `for (;;)` loops;
        b. recover_optimized_else: on if-then-optimized binaries, else
           clauses are rebuilt from `if (cond) { ...; goto L; }` shapes;
        c. linearize: the surviving blocks are emitted in order, turning
           Jump terminators into gotos and jump targets into labels.

   Label bookkeeping: a block that was a jump target may still be the
   target of jumps that no rule structured away (they survive as gotos), so
   linearize gives every such block an address label. Whether a label is
   actually referenced is not tracked here; Transform.rename_labels removes
   the labels that end up without a matching goto.
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Small helpers
   ------------------------------------------------------------------------- *)

(* Removes the JUMP instruction terminating [bb] (6 = code size of JUMP). *)
let remove_jump bb =
  match bb with
  | { code = { txt = Jump _; _ }, stmts; _ } ->
      { bb with code = (seq_terminator, stmts); end_addr = bb.end_addr - 6 }
  | _ -> failwith "no Jump terminator to remove"

(* Turns the statements of an inc clause into a single (comma) expression. *)
let rec stmt_list_to_expr = function
  | [ ({ txt = Expression e; _ } as stmt) ] -> { stmt with txt = e }
  | { txt = Expression e; end_addr; _ } :: stmts ->
      let lhs = stmt_list_to_expr stmts in
      { txt = BinaryOp (PSEUDO_COMMA, lhs.txt, e); addr = lhs.addr; end_addr }
  | stmts ->
      Printf.failwithf "Cannot convert statement %s to an expression"
        (show_statement (Block stmts))
        ()

let empty_else = { txt = Block []; addr = -1; end_addr = -1 }

(* -------------------------------------------------------------------------
   Break / continue substitution
   ------------------------------------------------------------------------- *)

(* Rewrites jumps to [continue_addr] / [break_addr] into continue / break
   statements, both in the block terminators and in the statements already
   collapsed into the blocks. The rewrite descends into if branches (and,
   for continue, into switch bodies) but not into nested loops: their
   break/continue were already resolved when they were reduced, and a jump
   from them into the enclosing loop's control points remains a goto. *)
let substitute_break_continue ?continue_addr ?break_addr cfg =
  let matches addr = function Some a -> a = addr | None -> false in
  let rec replace_stmt ~break_addr stmt =
    match stmt.txt with
    | Goto (addr, _) when matches addr continue_addr ->
        { stmt with txt = Continue }
    | Goto (addr, _) when matches addr break_addr -> { stmt with txt = Break }
    | IfElse (e, stmt1, stmt2) ->
        {
          stmt with
          txt =
            IfElse
              (e, replace_stmt ~break_addr stmt1, replace_stmt ~break_addr stmt2);
        }
    | Block stmts ->
        { stmt with txt = Block (List.map stmts ~f:(replace_stmt ~break_addr)) }
    | Switch (id, e, body) when Option.is_some continue_addr ->
        (* break inside a nested switch belongs to that switch *)
        { stmt with txt = Switch (id, e, replace_stmt ~break_addr:None body) }
    | _ -> stmt
  in
  let replace_bb bb =
    let term, stmts = bb.code in
    let stmts = List.map stmts ~f:(replace_stmt ~break_addr) in
    match term with
    | { txt = Jump target; _ } when matches target continue_addr ->
        {
          bb with
          code = (seq_terminator, { term with txt = Continue } :: stmts);
        }
    | { txt = Jump target; _ } when matches target break_addr ->
        { bb with code = (seq_terminator, { term with txt = Break } :: stmts) }
    | _ -> { bb with code = (term, stmts) }
  in
  let rec aux node =
    match CFG.value node with
    | None -> ()
    | Some bb ->
        CFG.set node (replace_bb bb);
        aux (CFG.next node)
  in
  aux (CFG.first cfg)

(* -------------------------------------------------------------------------
   Linearization: emitting fully reduced blocks as statements
   ------------------------------------------------------------------------- *)

(* Concatenates the remaining blocks into a single statement. Jump
   terminators become gotos, and every block that was a jump target
   receives an address label. (Statement lists of Ast.Block are in reverse
   order.) *)
let linearize bbs =
  List.concat_map (List.rev bbs) ~f:(fun bb ->
      let stmts =
        match bb.code with
        | ({ txt = Jump label; _ } as term), stmts ->
            { term with txt = Goto (label, bb.end_addr) } :: stmts
        | { txt = Seq; _ }, stmts -> stmts
        | _ ->
            Printf.failwithf "Cannot convert basic block to statement: %s"
              ([%show: BasicBlock.t] bb)
              ()
      in
      let labels =
        if bb.is_jump_target then
          { txt = Address bb.addr; addr = bb.addr; end_addr = bb.addr }
          :: bb.labels
        else bb.labels
      in
      if List.is_empty labels then stmts
      else
        stmts
        @ List.map labels ~f:(fun l ->
            { txt = Label l.txt; addr = l.addr; end_addr = l.addr }))
  |> make_block

(* -------------------------------------------------------------------------
   Else clause recovery for if-then-optimized binaries

   Some compiler versions omit the jump over the else clause when the then
   clause ends with a statement that never falls through. On such binaries
   the reduction scan only recognizes the if-then form, so an if statement
   with an else clause is decompiled at this point as

       if (cond) { then-clause...; goto L; }
       else-clause...
     L:

   This pass rebuilds the else clause: the goto is deleted and the blocks
   up to L (or to the end of the region, when L leaves it) become the else
   branch. The scan runs backwards and retries the block it just rewrote,
   so nested if-elses of this shape are rebuilt from the innermost one
   outwards.
   ------------------------------------------------------------------------- *)

let recover_optimized_else cfg =
  if Ain.ain.ifthen_optimized then
    let region_end_addr =
      match CFG.value (CFG.last cfg) with Some bb -> bb.end_addr | None -> -1
    in
    (* Matches a block whose most recent statement is
       `if (cond) { then_block; goto goto_addr; }` with an empty else. *)
    let match_goto_if bb =
      match bb.code with
      | ( { txt = Seq; _ },
          { txt = IfElse (cond, then_stmt, { txt = Block []; _ }); addr; _ }
          :: stmts ) -> (
          match then_stmt.txt with
          | Block ({ txt = Goto (goto_addr, _); _ } :: then_block) ->
              Some (addr, cond, goto_addr, then_block, stmts)
          | Goto (goto_addr, _) -> Some (addr, cond, goto_addr, [], stmts)
          | _ -> None)
      | _ -> None
    in
    (* Makes the blocks in [next node, else_end) the else clause of the
       goto-if at [node]. *)
    let rebuild node (if_addr, cond, then_block, stmts) ~else_end ~end_addr =
      let bb = CFG.value_exn node in
      let else_stmt =
        CFG.splice cfg (CFG.next node) else_end |> CFG.to_list |> linearize
      in
      CFG.set node
        {
          bb with
          code =
            ( seq_terminator,
              {
                txt = IfElse (cond, make_block then_block, else_stmt);
                addr = if_addr;
                end_addr = else_stmt.end_addr;
              }
              :: stmts );
          end_addr;
        }
    in
    let rec scan node =
      match CFG.value node with
      | None -> ()
      | Some bb -> (
          match match_goto_if bb with
          | None -> scan (CFG.prev node)
          | Some (if_addr, cond, goto_addr, then_block, stmts) ->
              if goto_addr = region_end_addr then (
                rebuild node
                  (if_addr, cond, then_block, stmts)
                  ~else_end:None ~end_addr:region_end_addr;
                scan node)
              else
                let target =
                  CFG.(find_forward ~f:(by_address goto_addr) cfg (next node))
                in
                if CFG.is_end target then scan (CFG.prev node)
                else (
                  rebuild node
                    (if_addr, cond, then_block, stmts)
                    ~else_end:target ~end_addr:(CFG.value_exn target).addr;
                  scan node))
    in
    scan (CFG.last cfg)

(* Collapses a region that is known to contain no unstructured backward
   jump (the body of a forever loop, or a region recover_forever_loops has
   already run on). *)
let collapse_no_loops cfg =
  recover_optimized_else cfg;
  linearize (CFG.to_list cfg)

(* -------------------------------------------------------------------------
   Forever loop recovery

   A Jump terminator still remaining after the reduction scan is an
   unstructured goto. When it goes backwards, the region in between can be
   closed into a `for (;;)` loop.
   ------------------------------------------------------------------------- *)

(* True if the blocks in [begin_node, end_node) contain a break/continue
   statement that belongs to an enclosing loop or switch. (One nested in a
   loop or switch of the region itself belongs to that construct and is
   fine.) *)
let rec has_break_continue begin_node end_node =
  let rec test stmt =
    match stmt with
    | Break | Continue -> true
    | IfElse (_, stmt1, stmt2) -> test stmt1.txt || test stmt2.txt
    | Block stmts -> List.exists stmts ~f:(fun { txt; _ } -> test txt)
    | _ -> false
  in
  if CFG.node_equal begin_node end_node then false
  else
    let _, stmts = (CFG.value_exn begin_node).code in
    List.exists stmts ~f:(fun { txt; _ } -> test txt)
    || has_break_continue (CFG.next begin_node) end_node

(* Returns true if any variable is declared between block_begin and block_end
   and used after block_end. *)
let has_escaping_vars cfg block_begin block_end =
  let vars = ref [] in
  CFG.iterate cfg block_begin block_end (fun { code = _, stmts; _ } ->
      List.iter stmts ~f:(function
        | { txt = VarDecl (v, _); _ } -> vars := v :: !vars
        | _ -> ()));
  if List.is_empty !vars then false
  else
    let result = ref false in
    CFG.iterate cfg block_end None (fun bb ->
        (match bb with
          | { code = { txt = Seq | Jump _ | DoWhile0 _; _ }, stmts; _ } -> stmts
          | { code = ({ txt = Branch (_, e); _ } as term), stmts; _ } ->
              { term with txt = Expression e } :: stmts
          | { code = ({ txt = Switch0 (_, e); _ } as term), stmts; _ } ->
              { term with txt = Expression e } :: stmts)
        |> make_block
        |> Ast.walk ~lvalue_cb:(function
          | Var (_, v) when Stdlib.List.memq v !vars -> result := true
          | _ -> ()));
    !result

(*  bbt: ...
    ...
    bbk: ..., JUMP bbt
    => for (;;) { bbt..bbk }
   Not applied if the region contains a break/continue of an enclosing
   structure (wrapping it in a loop would change their target), or declares
   a variable used after the region (the loop would end its scope too
   early):
     label1:
       int x = 42;
       goto label1;
       f(x);
*)
let recover_forever_loops cfg =
  let rec scan node =
    match CFG.value node with
    | None -> ()
    | Some ({ code = { txt = Jump addr; _ }, _; _ } as bb) ->
        let target = CFG.(find_backward ~f:(by_address addr) cfg node) in
        if
          CFG.is_end target
          || has_break_continue target (CFG.next node)
          || has_escaping_vars cfg target (CFG.next node)
        then scan (CFG.next node)
        else
          let target_bb = CFG.value_exn target in
          let loop_node = CFG.insert_before cfg target target_bb in
          (* The loop head block moves into the loop body; its labels stay
             outside, on loop_node. *)
          CFG.set target { target_bb with labels = []; is_jump_target = false };
          CFG.set node (remove_jump bb);
          let region = CFG.splice cfg target (CFG.next node) in
          substitute_break_continue region ~continue_addr:addr
            ~break_addr:bb.end_addr;
          let body = collapse_no_loops region in
          CFG.set loop_node
            {
              target_bb with
              end_addr = bb.end_addr;
              code =
                ( seq_terminator,
                  [ { body with txt = For (None, None, None, body) } ] );
            };
          scan (CFG.next loop_node)
    | Some _ -> scan (CFG.next node)
  in
  scan (CFG.first cfg)

(* Collapses a fully reduced region into a single statement. *)
let collapse cfg =
  recover_forever_loops cfg;
  collapse_no_loops cfg

(* Splices out the blocks in [begin_node, end_node), rewrites jumps to
   [continue_addr] / [break_addr] into continue / break statements, and
   collapses the result into a loop body statement. *)
let collapse_body ?continue_addr ?break_addr cfg begin_node end_node =
  let region = CFG.splice cfg begin_node end_node in
  substitute_break_continue region ?continue_addr ?break_addr;
  collapse region

(* -------------------------------------------------------------------------
   Reduction rules

   Each rule matches one control-structure shape at its head block [node0],
   collapses the body region, and folds the structure into node0. The
   comments picture the blocks in address order; "bbk" is the join point
   where execution resumes after the structure.
   ------------------------------------------------------------------------- *)

(* switch statement.
    bb0: Switch0 (expr)
    bb1: JUMP bbk
    bb2..bbk-1: switch body
    bbk: ...
    => switch (expr) { bb2..bbk-1 }
   Case labels pointing at bbk (cases that jump past the body) are moved
   onto an empty block appended to the body. *)
let reduce_switch cfg node0 =
  let node1 = CFG.next node0 in
  let bb0 = CFG.value_exn node0 in
  let bb1 = CFG.value_exn node1 in
  match (bb0, bb1) with
  | ( { code = { txt = Switch0 (id, expr); addr = switch_addr; _ }, stmts0; _ },
      { code = { txt = Jump switch_end_addr; _ }, []; _ } ) ->
      let body_head = CFG.next node1 in
      let body_end =
        CFG.(find_forward ~f:(by_address switch_end_addr) cfg body_head)
      in
      let body_end_bb = CFG.value_exn body_end in
      let case_labels, other_labels =
        List.partition_tf body_end_bb.labels ~f:(fun l ->
            match l.txt with
            | CaseInt (id', _) | CaseStr (id', _) | Default id' -> id = id'
            | Address _ -> false)
      in
      if not (List.is_empty case_labels) then
        CFG.insert_before cfg body_end
          {
            addr = switch_end_addr;
            end_addr = switch_end_addr;
            code = (seq_terminator, []);
            labels = case_labels;
            is_jump_target = false;
          }
        |> ignore;
      let body =
        collapse_body cfg body_head body_end ~break_addr:switch_end_addr
      in
      CFG.set node0
        {
          bb0 with
          code =
            ( seq_terminator,
              {
                txt = Switch (id, expr, body);
                addr = switch_addr;
                end_addr = body.end_addr;
              }
              :: stmts0 );
          end_addr = switch_end_addr;
        };
      CFG.set body_end { body_end_bb with labels = other_labels };
      CFG.remove cfg node1
  | _ -> failwith "unexpected basic block after Switch0"

(* if statement on an if-then-optimized binary: the then clause simply
   falls through to the branch target.
    bb0: expr, Branch bbk
    bb1..bbk-1: then clause
    bbk:
    => if (expr) { bb1..bbk-1 } *)
let reduce_if_then cfg node0 branch_target =
  let bb0 = CFG.value_exn node0 in
  match bb0 with
  | {
   code = { txt = Branch (join_addr, expr); addr = expr_addr; _ }, stmts0;
   _;
  } ->
      let then_stmt =
        CFG.splice cfg (CFG.next node0) branch_target |> collapse
      in
      CFG.set node0
        {
          bb0 with
          code =
            ( seq_terminator,
              {
                txt = IfElse (expr, then_stmt, empty_else);
                addr = expr_addr;
                end_addr = then_stmt.end_addr;
              }
              :: stmts0 );
          end_addr = join_addr;
        }
  | _ -> failwith "cannot happen"

(* if statement without else, unoptimized: the then clause ends with an
   explicit jump to the join point.
    bb0: expr, Branch bbk
    bb1..bbk-1: then clause ..., JUMP bbk
    bbk:
    => if (expr) { bb1..bbk-1 } *)
let reduce_if_no_else cfg node0 branch_target ~expr ~expr_addr =
  let bb0 = CFG.value_exn node0 in
  let _, stmts0 = bb0.code in
  let join_addr = (CFG.value_exn branch_target).addr in
  let jump_node = CFG.prev branch_target in
  CFG.set jump_node (remove_jump (CFG.value_exn jump_node));
  let then_stmt = CFG.splice cfg (CFG.next node0) branch_target |> collapse in
  CFG.set node0
    {
      bb0 with
      code =
        ( seq_terminator,
          {
            txt = IfElse (expr, then_stmt, empty_else);
            addr = expr_addr;
            end_addr = join_addr;
          }
          :: stmts0 );
      end_addr = join_addr;
    }

(* if statement with an else clause.
    bb0: expr, Branch bbj
    bb1..bbj-1: then clause ..., JUMP bbk
    bbj..bbk-1: else clause
    bbk:
    => if (expr) { bb1..bbj-1 } else { bbj..bbk-1 } *)
let reduce_if_else cfg node0 branch_target ~expr ~expr_addr ~else_end_addr =
  let bb0 = CFG.value_exn node0 in
  let _, stmts0 = bb0.code in
  let else_end =
    CFG.(find_forward ~f:(by_address else_end_addr) cfg (next branch_target))
  in
  if CFG.is_end else_end then
    Printf.failwithf "basic block %d not found" else_end_addr ();
  let jump_node = CFG.prev branch_target in
  CFG.set jump_node (remove_jump (CFG.value_exn jump_node));
  let then_stmt = CFG.splice cfg (CFG.next node0) branch_target |> collapse in
  let else_stmt = CFG.splice cfg branch_target else_end |> collapse in
  CFG.set node0
    {
      bb0 with
      code =
        ( seq_terminator,
          {
            txt = IfElse (expr, then_stmt, else_stmt);
            addr = expr_addr;
            end_addr = else_end_addr;
          }
          :: stmts0 );
      end_addr = else_end_addr;
    }

(* while loop.
    bb0: expr, Branch bbk
    bb1..bbk-1: body ..., JUMP bb0
    bbk:
    => while (expr) { bb1..bbk-1 } *)
let reduce_while cfg node0 branch_target ~expr ~expr_addr =
  let bb0 = CFG.value_exn node0 in
  let break_addr = (CFG.value_exn branch_target).addr in
  let jump_node = CFG.prev branch_target in
  CFG.set jump_node (remove_jump (CFG.value_exn jump_node));
  let body =
    collapse_body cfg (CFG.next node0) branch_target ~continue_addr:bb0.addr
      ~break_addr
  in
  CFG.set node0
    {
      bb0 with
      code =
        ( seq_terminator,
          [
            {
              txt = While (expr, body);
              addr = expr_addr;
              end_addr = break_addr;
            };
          ] );
      end_addr = break_addr;
    }

(* In Pastel Chime 3, there is code that jumps from within a nested for-loop
   to the inc clause of the outer for-loop. Since the inc clause cannot have
   a label, insert a label at the end of the (outer) for-loop body if any
   goto to the inc clause survived break/continue substitution. *)
let insert_label_for_inc addr body =
  let needs_label = ref false in
  walk_statement body ~f:(function
    | Goto (a, _) when a = addr -> needs_label := true
    | _ -> ());
  if not !needs_label then body
  else
    match body.txt with
    | Block stmts ->
        {
          body with
          txt =
            Block
              ({
                 txt = Label (Address addr);
                 addr = body.addr;
                 end_addr = body.addr;
               }
              :: stmts);
        }
    | _ -> failwith "insert_label_for_inc: not implemented"

(* for loop.
    bb0: cond_expr, Branch bbk
    bb1: JUMP bb3
    bb2: inc_expr, JUMP bb0
    (ain11+ compilers generate an extra `JUMP bb0` block here)
    bb3..bbk-1: body ..., JUMP bb2
    bbk:
    => for (; cond_expr; inc_expr) { bb3..bbk-1 }
   Falls back to if-then when the blocks do not have this shape. *)
let reduce_for cfg node0 branch_target ~expr ~expr_addr ~inc_addr =
  let bb0 = CFG.value_exn node0 in
  let break_addr = (CFG.value_exn branch_target).addr in
  let node1 = CFG.next node0 in
  let node2 = CFG.next node1 in
  let is_forloop_body_addr addr =
    let node2_endaddr = (CFG.value_exn node2).end_addr in
    addr = node2_endaddr
    || addr = node2_endaddr + 6
       &&
       let node3 = CFG.next node2 in
       match CFG.value node3 with
       | Some { code = { txt = Jump l; _ }, []; _ } when l = bb0.addr ->
           (* Remove the extra `JUMP bb0` block *)
           CFG.remove cfg node3;
           true
       | _ -> false
  in
  match (CFG.value_exn node1, CFG.value_exn node2) with
  | ( { code = { txt = Jump body_addr; _ }, []; _ },
      { addr = inc_addr'; code = { txt = Jump loopback_addr; _ }, inc; _ } )
    when loopback_addr = bb0.addr && inc_addr = inc_addr'
         && is_forloop_body_addr body_addr ->
      let inc_expr =
        if List.is_empty inc then None else Some (stmt_list_to_expr inc).txt
      in
      let jump_node = CFG.prev branch_target in
      CFG.set jump_node (remove_jump (CFG.value_exn jump_node));
      let body =
        collapse_body cfg (CFG.next node2) branch_target ~continue_addr:inc_addr
          ~break_addr
      in
      let body = insert_label_for_inc inc_addr body in
      CFG.set node0
        {
          bb0 with
          code =
            ( seq_terminator,
              [
                {
                  txt = For (None, Some expr, inc_expr, body);
                  addr = expr_addr;
                  end_addr = break_addr;
                };
              ] );
          end_addr = break_addr;
        };
      CFG.remove cfg node1;
      CFG.remove cfg node2
  | _ ->
      if Ain.ain.ifthen_optimized then reduce_if_then cfg node0 branch_target
      else failwith "unexpected flow structure"

(* Dispatches a forward Branch to one of the if/while/for rules, mostly by
   where the jump just before the branch target goes. *)
let rec reduce_forward_branch cfg node0 branch_target =
  let bb0 = CFG.value_exn node0 in
  let jump_node = CFG.prev branch_target in
  match (bb0.code, CFG.value jump_node) with
  | ( (({ txt = Branch (join_addr, expr); _ } as term), stmts0),
      Some { code = { txt = Jump label1; _ }, []; addr = jump_addr; _ } )
    when bb0.end_addr = jump_addr && label1 > join_addr && Ain.ain.vers >= 12 ->
      (* Ain v12+ if-statement pattern: Rewrite
            bb0:
              ...
              IFZ branch_target_addr
              JUMP label1
            branch_target_addr:
         to
            bb0:
              ...
              IFNZ label1
      *)
      CFG.remove cfg jump_node;
      CFG.set node0
        {
          bb0 with
          code = ({ term with txt = Branch (label1, negate expr) }, stmts0);
        };
      let target = CFG.(find_forward ~f:(by_address label1) cfg (next node0)) in
      reduce_forward_branch cfg node0 target
  | ( ({ txt = Branch (join_addr, expr); addr = expr_addr; _ }, stmts0),
      Some { code = { txt = Jump label1; _ }, _; _ } ) ->
      (* bb0:
            ...
            IFZ join_addr
            ...
            JUMP label1
         join_addr:
      *)
      if label1 = join_addr then
        reduce_if_no_else cfg node0 branch_target ~expr ~expr_addr
      else if label1 > join_addr then
        if Ain.ain.ifthen_optimized then reduce_if_then cfg node0 branch_target
        else
          reduce_if_else cfg node0 branch_target ~expr ~expr_addr
            ~else_end_addr:label1
      else if label1 = bb0.addr && List.is_empty stmts0 then
        reduce_while cfg node0 branch_target ~expr ~expr_addr
      else if bb0.addr < label1 && label1 < join_addr then
        reduce_for cfg node0 branch_target ~expr ~expr_addr ~inc_addr:label1
      else if Ain.ain.ifthen_optimized && label1 <= bb0.addr then
        reduce_if_then cfg node0 branch_target
      else
        Printf.failwithf "unrecognized control structure:\n%s"
          ([%show: fragment basic_block list]
             (CFG.splice cfg node0 None |> CFG.to_list))
          ()
  | _ -> reduce_if_then cfg node0 branch_target

(* do-while loop (seen in Pascha C++).
    bb0: body ...
    bbk: expr, Branch bb0
    => do { bb0..bbk-1 } while (!expr)
   The body precedes the branch, so it is not reduced yet when the backward
   scan visits bbk. Only a DoWhile0 marker is planted here, in front of the
   loop head; the scan reduces the body blocks first and then triggers
   reduce_do_while at the marker. *)
let reduce_backward_branch cfg nodek branch_target =
  let bbk = CFG.value_exn nodek in
  let bb0 = CFG.value_exn branch_target in
  CFG.insert_before cfg branch_target
    {
      addr = bb0.addr;
      end_addr = bb0.addr;
      code = ({ txt = DoWhile0 bbk.addr; addr = -1; end_addr = -1 }, []);
      labels = [];
      is_jump_target = false;
    }
  |> ignore

let reduce_do_while cfg marker_node =
  match CFG.value_exn marker_node with
  | { code = { txt = DoWhile0 bbk_addr; _ }, []; _ } -> (
      let node0 = CFG.next marker_node in
      let nodek = CFG.(find_forward ~f:(by_address bbk_addr) cfg node0) in
      let bb0 = CFG.value_exn node0 in
      let bbk = CFG.value_exn nodek in
      match bbk with
      | { code = ({ txt = Branch (_, expr); _ } as term), stmts; _ } ->
          CFG.set nodek { bbk with code = (seq_terminator, stmts) };
          let body =
            collapse_body cfg node0 (CFG.next nodek) ~continue_addr:bbk.addr
              ~break_addr:bbk.end_addr
          in
          CFG.set marker_node
            {
              bb0 with
              code =
                ( seq_terminator,
                  [
                    {
                      txt = DoWhile (body, { term with txt = negate expr });
                      addr = body.end_addr;
                      end_addr = bbk.end_addr;
                    };
                  ] );
              end_addr = bbk.end_addr;
            }
      | _ -> failwith "cannot happen")
  | _ -> failwith "cannot happen"

(* for loop without conditional expression.
    bb0: JUMP bb2
    bb1: inc_stmt, JUMP bb0
    bb2..bbk: body ..., JUMP bb1
    => for (;; inc_stmt) { bb2..bbk } *)
let reduce_jump cfg node0 =
  let bb0 = CFG.value_exn node0 in
  let node1 = CFG.next node0 in
  match (bb0, CFG.value node1) with
  | ( { code = { txt = Jump body_addr; _ }, []; _ },
      Some
        ({
           code = { txt = Jump cond_addr; _ }, inc_stmts;
           end_addr = body_addr';
           _;
         } as bb1) )
    when body_addr = body_addr' && cond_addr = bb0.addr -> (
      let node2 = CFG.next node1 in
      match CFG.(find_forward ~f:(by_jump_target bb1.addr) cfg node2) with
      | Some _ as nodek ->
          let break_addr = (CFG.value_exn nodek).end_addr in
          let inc_expr =
            if List.is_empty inc_stmts then None
            else Some (stmt_list_to_expr inc_stmts)
          in
          CFG.set nodek (remove_jump (CFG.value_exn nodek));
          let body =
            collapse_body cfg node2 (CFG.next nodek) ~continue_addr:bb1.addr
              ~break_addr
          in
          let for_addr =
            match inc_expr with Some { addr; _ } -> addr | None -> body.addr
          in
          let inc_expr = Option.map inc_expr ~f:(fun { txt; _ } -> txt) in
          CFG.set node0
            {
              bb0 with
              end_addr = break_addr;
              code =
                ( seq_terminator,
                  [
                    {
                      txt = For (None, None, inc_expr, body);
                      addr = for_addr;
                      end_addr = break_addr;
                    };
                  ] );
            };
          CFG.remove cfg node1
      | None -> ())
  | _ -> ()

(* -------------------------------------------------------------------------
   Driver
   ------------------------------------------------------------------------- *)

let reduce cfg node0 =
  let bb0 = CFG.value_exn node0 in
  match bb0 with
  | { code = { txt = Switch0 _; _ }, _; _ } -> reduce_switch cfg node0
  | { code = { txt = Branch (addr, _); _ }, _; _ } ->
      let target = CFG.(find_forward ~f:(by_address addr) cfg (next node0)) in
      if not (CFG.is_end target) then reduce_forward_branch cfg node0 target
      else
        let target = CFG.(find_backward ~f:(by_address addr) cfg node0) in
        if not (CFG.is_end target) then reduce_backward_branch cfg node0 target
        else Printf.failwithf "basic block %d not found" addr ()
  | { code = { txt = Jump _; _ }, _; _ } -> reduce_jump cfg node0
  | { code = { txt = DoWhile0 _; _ }, _; _ } -> reduce_do_while cfg node0
  | _ -> ()

let analyze bbs =
  let cfg = CFG.of_list bbs in
  (* Add a dummy exit block. *)
  let end_addr =
    match CFG.value (CFG.last cfg) with Some bb -> bb.end_addr | None -> -1
  in
  CFG.insert_last cfg
    {
      addr = end_addr;
      end_addr;
      code = (seq_terminator, []);
      labels = [];
      is_jump_target = false;
    }
  |> ignore;
  let rec scan node =
    if CFG.is_end node then collapse cfg
    else (
      reduce cfg node;
      scan (CFG.prev node))
  in
  scan (CFG.last cfg)
