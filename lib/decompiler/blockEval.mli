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

(* Symbolic evaluation of the instruction sequence of a single basic block. *)

open Loc

type terminator =
  | Seq
  | Jump of int (* addr *)
  | Branch of int * Ast.expr (* (addr, cond) - jumps if cond == 0 *)
  | Switch0 of int * Ast.expr
  | DoWhile0 of int (* addr of branching basic block *)
[@@deriving show { with_path = false }]

val seq_terminator : terminator loc

type context = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  parent : CodeSection.function_t option;
  mutable instructions : Instructions.instruction loc list;
      (* the instructions left to evaluate *)
  mutable address : int; (* start address of the current statement *)
  mutable end_address : int; (* end address of the current basic block *)
  mutable stack : Ast.expr list; (* the symbolic value stack *)
  mutable stmts : Ast.statement loc list;
      (* generated statements, most recent first *)
  mutable condition : Ast.expr list;
      (* conditions of the branches taken to reach this block, most recent
         first (see BasicBlock) *)
}

(* Evaluates ctx.instructions, simulating their effect on ctx.stack and
   emitting completed statements to ctx.stmts. Returns the terminator of the
   basic block along with the final value stack and the generated statements
   (most recent first), leaving ctx.stack and ctx.stmts empty. *)
val analyze : context -> terminator loc * Ast.expr list * Ast.statement loc list
