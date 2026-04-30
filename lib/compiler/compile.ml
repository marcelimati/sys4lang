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

open Common
open Base
open Jaf

type source =
  | Jaf of string * declaration list
  | Hll of string * string * declaration list

type program = source list

let parse_file lexer parser file read_file =
  let source = read_file file in
  let lexbuf = Lexing.from_string source in
  Lexing.set_filename lexbuf file;
  try parser lexer lexbuf with
  | Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf
  | e -> raise e

(* pass 1: Parse jaf/hll files and create symbol table entries.
   v11 user-bodied property/event accessors are scanned across all
   parsed jaf files BEFORE [register_type_declarations] runs so that
   [expand_property_decl] / [expand_struct_decls] can elide the
   matching auto-stubs and backing fields when they fire. The scan
   has to see every top-level [T Class::Name { ... }] block in the
   project — properties may be declared in [classes.jaf] but their
   bodies live in per-class files.

   Two-phase: parse all jaf files first, then scan, then register. *)
let parse_pass ctx sources read_file =
  let parsed =
    List.map sources ~f:(function
      | Pje.Jaf f ->
          let jaf = parse_file Lexer.token Parser.jaf f read_file in
          `Jaf (f, jaf)
      | Pje.Hll (f, import_name) ->
          let hll = parse_file Lexer.token Parser.hll f read_file in
          let hll_name = Stdlib.Filename.(chop_extension (basename f)) in
          `Hll (hll_name, import_name, hll)
      | _ -> failwith "unreachable")
  in
  List.iter parsed ~f:(function
    | `Jaf (_, jaf) -> Declarations.scan_user_bodied_accessors ctx jaf
    | `Hll _ -> ());
  List.map parsed ~f:(function
    | `Jaf (f, jaf) ->
        Declarations.register_type_declarations ctx jaf;
        Jaf (f, jaf)
    | `Hll (hll_name, import_name, hll) -> Hll (hll_name, import_name, hll))

(* pass 2: Resolve type specifiers *)
let type_resolve_pass ctx program =
  let array_init_visitor = new ArrayInit.visitor ctx in
  List.iter program ~f:(function
    | Jaf (_, jaf) ->
        Declarations.resolve_types ctx jaf;
        Declarations.define_types ctx jaf;
        List.iter ~f:array_init_visitor#visit_declaration jaf
    | Hll (hll_name, import_name, hll) ->
        Declarations.resolve_hll_types ctx hll;
        Declarations.resolve_types ctx hll;
        Declarations.define_library ctx hll hll_name import_name);
  let initializers = array_init_visitor#generate_initializers () in
  program @ [ Jaf ("", initializers) ]

(* pass 3: Type checking *)
let type_check_pass ctx program =
  List.iter program ~f:(function
    | Jaf (_, jaf) ->
        TypeAnalysis.check_types_exn ctx jaf;
        ConstEval.evaluate_constant_expressions ctx jaf;
        VariableAlloc.allocate_variables ctx jaf
    | Hll _ -> ())

(* pass 4: Code generation *)
let codegen_pass ctx program debug_info =
  List.iter program ~f:(function
    | Jaf (jaf_name, jaf) ->
        (* TODO: disable in release builds *)
        SanityCheck.check_invariants ctx jaf;
        Codegen.compile ctx jaf_name jaf debug_info
    | Hll _ -> ())

(* v11 struct vtable population. After all functions have been
   registered, walk every struct and collect the indices of functions
   whose name starts with [Class@]. The v11 VM reads [Struct.vmethods]
   to resolve virtual method calls — without this the field is empty
   and [CALLMETHOD] dispatch finds nothing. Pre-v11 doesn't use
   [vmethods] for dispatch, so the pass is a no-op there. *)
let populate_vtables ctx =
  if Ain.version ctx.ain > 8 then
    Ain.struct_iter ctx.ain ~f:(fun (s : Ain.Struct.t) ->
        let prefix = s.name ^ "@" in
        let methods = ref [] in
        Ain.function_iter ctx.ain ~f:(fun (f : Ain.Function.t) ->
            if String.is_prefix f.name ~prefix then
              methods := f.index :: !methods);
        Ain.write_struct ctx.ain { s with vmethods = List.rev !methods })

(* Emit minimal stub bytecode for any function still flagged as
   un-emitted ([address] of [-1] or [-2]). These are typically ghost
   lambda entries pre-allocated by the v11 delegate-callback
   registration plus stub-aware [add_function] reuse: the slot exists
   in the function table but no compile_function ever ran on it.
   Without a body, [CALLMETHOD] / [CALLFUNC] resolved to that slot
   would jump into uninitialised bytecode. Emit a [FUNC; PUSH 0;
   RETURN; ENDFUNC] shape so the slot is safe. The "NULL" function is
   special and skipped. *)
let emit_undefined_function_stubs ctx =
  Ain.function_iter ctx.ain ~f:(fun (f : Ain.Function.t) ->
      if
        (f.address = -1 || f.address = -2)
        && not (String.equal f.name "NULL")
      then (
        let buf = CBuffer.create 64 in
        let addr = Ain.code_size ctx.ain in
        CBuffer.write_int16 buf 0x61;
        (* FUNC *)
        CBuffer.write_int32 buf f.index;
        (match f.return_type with
        | Ain.Type.Void -> ()
        | Ain.Type.Float ->
            CBuffer.write_int16 buf 0x03;
            CBuffer.write_float buf 0.0
        | Ain.Type.String ->
            CBuffer.write_int16 buf 0x0a;
            CBuffer.write_int32 buf 0
        | _ ->
            CBuffer.write_int16 buf 0x00;
            (* PUSH *)
            CBuffer.write_int32 buf 0);
        CBuffer.write_int16 buf 0x2f;
        (* RETURN *)
        CBuffer.write_int16 buf 0x7e;
        (* ENDFUNC *)
        CBuffer.write_int32 buf f.index;
        Ain.append_bytecode ctx.ain buf;
        Ain.write_function ctx.ain { f with address = addr + 6 }))

(* v11 foreach is desugared into a [while] loop before any
   type-resolution / type-checking happens, so later passes only see
   the regular control-flow shape. *)
let desugar_pass program =
  List.iter program ~f:(function
    | Jaf (_, jaf) -> Jaf.desugar_foreach jaf
    | Hll _ -> ())

let compile ctx sources debug_info read_file =
  let program = parse_pass ctx sources read_file in
  desugar_pass program;
  let program = type_resolve_pass ctx program in
  type_check_pass ctx program;
  populate_vtables ctx;
  codegen_pass ctx program debug_info;
  emit_undefined_function_stubs ctx
