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

(* The immutable environment of the function being evaluated. *)
type env = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  parent : CodeSection.function_t option;
}

(* The symbolic evaluation state carried across basic blocks. *)
type state = {
  condition : Ast.expr list;
      (* conditions of the branches taken since the last settled state, most
         recent first *)
  stack : Ast.expr list; (* the symbolic value stack *)
  stmts : Ast.statement loc list; (* generated statements, most recent first *)
}

val empty_state : state

(* Evaluates [instructions], simulating their effect on the value stack and
   emitting completed statements. [address] is the start address of the current
   statement and [end_address] the end address of the basic block. Returns the
   terminator of the basic block and the resulting state: its stack and stmts
   are the final ones (stmts most recent first); its condition is carried
   through unchanged. *)
val analyze :
  env ->
  address:int ->
  end_address:int ->
  instructions:Instructions.instruction loc list ->
  state ->
  terminator loc * state
