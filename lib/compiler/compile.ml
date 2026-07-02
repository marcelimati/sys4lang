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

let parse_source lexer parser file source =
  let lexbuf = Lexing.from_string source in
  Lexing.set_filename lexbuf file;
  try parser lexer lexbuf with
  | Lexer.Error | Parser.Error -> CompileError.syntax_error lexbuf
  | e -> raise e

let parse_file lexer parser file read_file =
  parse_source lexer parser file (read_file file)

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
  (* Pre-read each source once, scan for v12 templated identifiers
     (`IDENT<` with no whitespace before the `<`), then parse. The scan
     populates [LexerState.templated] so the lexer can consume
     `Foo<X, Y>` as a single TEMPLATE_IDENTIFIER token without breaking
     comparison expressions. *)
  LexerState.clear ();
  let read_sources =
    List.map sources ~f:(function
      | (Pje.Jaf f | Pje.Hll (f, _)) as src ->
          let source = read_file f in
          LexerState.scan_source source;
          (src, source)
      | _ -> failwith "unreachable")
  in
  let parsed =
    List.map read_sources ~f:(function
      | (Pje.Jaf f, source) ->
          let jaf = parse_source Lexer.token Parser.jaf f source in
          `Jaf (f, jaf)
      | (Pje.Hll (f, import_name), source) ->
          let hll = parse_source Lexer.token Parser.hll f source in
          let hll_name = Stdlib.Filename.(chop_extension (basename f)) in
          `Hll (hll_name, import_name, hll)
      | _ -> failwith "unreachable")
  in
  List.iter parsed ~f:(function
    | `Jaf (_, jaf) -> Declarations.scan_user_bodied_accessors ctx jaf
    | `Hll _ -> ());
  (* v11+: cross-file scan to compute interface inheritance from method
     overlap, so subsequent [register_type_declarations] can skip
     methods that are inherited from an ancestor interface. *)
  let all_iface_methods = Hashtbl.create (module String) in
  List.iter parsed ~f:(function
    | `Jaf (_, jaf) ->
        Declarations.collect_interface_methods_in_file all_iface_methods jaf
    | `Hll _ -> ());
  Declarations.compute_interface_inheritance ctx all_iface_methods;
  List.map parsed ~f:(function
    | `Jaf (f, jaf) ->
        Declarations.register_type_declarations ctx jaf;
        Jaf (f, jaf)
    | `Hll (hll_name, import_name, hll) -> Hll (hll_name, import_name, hll))

(* pass 2: Resolve type specifiers *)
let type_resolve_pass ctx program =
  let array_init_visitor = new ArrayInit.visitor ctx in
  (* v12-only passes. [allocate_missing_function_indices] allocates
     ain slots for fundecls that [register_type_declarations] left
     with [index = None] — primarily v12 interface methods and
     property accessors. v11 keeps those entries unallocated and
     never looks them up; running the pass on v11 adds spurious
     function-table entries for auto-event accessor stubs.
     [resolve_interface_lists] populates the v12 [interfaces]
     metadata that doesn't exist pre-v12. *)
  if Ain.version_gte ctx.ain (12, 0) then
    Declarations.allocate_missing_function_indices ctx;
  List.iter program ~f:(function
    | Jaf (_, jaf) ->
        Declarations.resolve_types ctx jaf;
        if Ain.version_gte ctx.ain (12, 0) then
          Declarations.resolve_interface_lists ctx jaf;
        Declarations.define_types ctx jaf;
        List.iter ~f:array_init_visitor#visit_declaration jaf
    | Hll (hll_name, import_name, hll) ->
        Declarations.resolve_hll_types ctx hll;
        Declarations.resolve_types ctx hll;
        Declarations.define_library ctx hll hll_name import_name);
  (* v12: after types are resolved, write proper FUNC signatures for
     interface prototype methods that allocate_missing_function_indices
     left as default Void/0/0. *)
  if Ain.version_gte ctx.ain (12, 0) then
    Declarations.write_interface_method_signatures ctx;
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
let populate_vtables ctx program =
  if Ain.version ctx.ain > 8 then (
    Ain.struct_iter ctx.ain ~f:(fun (s : Ain.Struct.t) ->
        let prefix = s.name ^ "@" in
        let methods = ref [] in
        Ain.function_iter ctx.ain ~f:(fun (f : Ain.Function.t) ->
            if String.is_prefix f.name ~prefix then
              methods := f.index :: !methods);
        Ain.write_struct ctx.ain { s with vmethods = List.rev !methods });
    if Ain.version_gte ctx.ain (12, 0) then
      List.iter program ~f:(function
        | Hll _ -> ()
        | Jaf (_, decls) ->
            List.iter decls ~f:(function
              | StructDef s ->
                let methods =
                    Hashtbl.find ctx.v12_struct_methods s.name
                    |> Option.value ~default:[]
                    |> List.filter_map ~f:(fun (f : Jaf.fundecl) -> f.index)
                  in
                  if not (List.is_empty methods) then
                    Option.iter (Hashtbl.find ctx.structs s.name)
                      ~f:(fun jaf_s ->
                        let ain_s =
                          Ain.get_struct_by_index ctx.ain jaf_s.index
                        in
                        Ain.write_struct ctx.ain
                          { ain_s with vmethods = methods })
              | _ -> ()))
  )

(* v11+ [class C implements I1, I2, ...]: each interface's methods
   occupy a contiguous block in C's vtable. [struct.interfaces[k].
   vtable_offset] is the index in C's vtable where Ik's first method
   sits, computed as the running sum of [vmethods.length] for I0..Ik-1.

   [Declarations.resolve_interface_lists] emits the interface list with
   placeholder vtable_offset=0. Recompute after [populate_vtables] so
   each interface's method count is known.

   Without this, every interface dispatch ((I2)c).method() resolves
   into Ik=I1's slot range — wrong function called, runtime fault.
   Original Rance10 has total_vtable_offsets=2736 across 251 structs;
   our pre-fix output had 0. *)
let fix_interface_vtable_offsets ctx =
  if Ain.version_gte ctx.ain (11, 0) then
    Ain.struct_iter ctx.ain ~f:(fun (s : Ain.Struct.t) ->
        if not (List.is_empty s.interfaces) then begin
          let _, fixed_rev =
            List.fold s.interfaces ~init:(0, [])
              ~f:(fun (offset, acc) (iface : Ain.Struct.interface) ->
                let iface_struct =
                  Ain.get_struct_by_index ctx.ain iface.struct_type
                in
                let nmethods = List.length iface_struct.vmethods in
                let updated =
                  { iface with vtable_offset = offset }
                in
                (offset + nmethods, updated :: acc))
          in
          let fixed = List.rev fixed_rev in
          Ain.write_struct ctx.ain { s with interfaces = fixed }
        end)

(* v12: for each class that implements interfaces, the boot-time
   constructor [Class@0] must allocate and populate the [<vtable>]
   array (an [array<int>] member added by [expand_struct_decls] as
   the first slot). Original Rance10's [AchieveIcon@0]:

     PUSHSTRUCTPAGE; PUSH 0 (<vtable> slot); REF; DUP
     PUSH 4; PUSH -1; PUSH -1; PUSH -1
     CALLHLL Array(5), Alloc(0), 10
     DUP; PUSH 0; PUSH <impl_idx_0>; ASSIGN; POP   ; vtable[0] = impl
     ... (repeat for each slot)
     POP; RETURN; ENDFUNC

   Without this, [obj.<vtable>] is an uninitialised array (NULL),
   and the first virtual-method dispatch deref's NULL. Strongly
   suspected to be the 0x609F15 NULL+0x34 crash cause.

   This pass runs after [fix_interface_vtable_offsets] so vmethods
   and per-interface vtable_offsets are known. For each struct with
   interfaces:
     1. Find [<vtable>] slot in s.members (it's slot 0 if expand
        added one).
     2. Build vtable[0..total_methods-1] mapping each interface
        method to its class implementation by name.
     3. Synthesize @0 (or augment existing) with init bytecode. *)
let populate_interface_vtables ctx =
  if not (Ain.version_gte ctx.ain (12, 0)) then ()
  else
    let array_lib =
      match Ain.get_library_index ctx.ain "Array" with
      | Some i -> i
      | None -> -1
    in
    let array_alloc =
      if array_lib < 0 then -1
      else
        match Ain.get_library_function_index ctx.ain array_lib "Alloc" with
        | Some i -> i
        | None -> -1
    in
    if array_lib < 0 || array_alloc < 0 then ()
    else
      Ain.struct_iter ctx.ain ~f:(fun (s : Ain.Struct.t) ->
          if List.is_empty s.interfaces then ()
          else
            (* Find <vtable> slot index. *)
            let vtable_slot = ref (-1) in
            List.iteri s.members ~f:(fun i (v : Ain.Variable.t) ->
                if String.equal v.name "<vtable>" then vtable_slot := i);
            if !vtable_slot < 0 then ()
            else
              let total_methods =
                List.fold s.interfaces ~init:0
                  ~f:(fun acc (iface : Ain.Struct.interface) ->
                    let iface_s =
                      Ain.get_struct_by_index ctx.ain iface.struct_type
                    in
                    acc + List.length iface_s.vmethods)
              in
              if total_methods = 0 then ()
              else
                (* Build vtable: for each interface method, find the
                   implementing function in this class by name. *)
                let vtable = Array.create ~len:total_methods 0 in
                List.iter s.interfaces ~f:(fun (iface : Ain.Struct.interface) ->
                    let iface_s =
                      Ain.get_struct_by_index ctx.ain iface.struct_type
                    in
                    List.iteri iface_s.vmethods ~f:(fun i iface_fn_idx ->
                        let iface_fn =
                          Ain.get_function_by_index ctx.ain iface_fn_idx
                        in
                        let prefix = iface_s.name ^ "@" in
                        let short_name =
                          if String.is_prefix iface_fn.name ~prefix then
                            String.chop_prefix_exn iface_fn.name ~prefix
                          else iface_fn.name
                        in
                        let impl_name = s.name ^ "@" ^ short_name in
                        match Ain.get_function ctx.ain impl_name with
                        | Some impl_fn ->
                            vtable.(iface.vtable_offset + i) <- impl_fn.index
                        | None -> ()));
                (* Allocate or reuse @0 slot. *)
                let at0_name = s.name ^ "@0" in
                let at0 =
                  match Ain.get_function ctx.ain at0_name with
                  | Some f -> f
                  | None -> Ain.add_function ctx.ain at0_name
                in
                let buf = CBuffer.create 256 in
                let addr = Ain.code_size ctx.ain in
                CBuffer.write_int16 buf 0x61;  (* FUNC *)
                CBuffer.write_int32 buf at0.index;
                (* <vtable>.Alloc(total_methods) *)
                CBuffer.write_int16 buf 0x5b;  (* PUSHSTRUCTPAGE *)
                CBuffer.write_int16 buf 0x00;  (* PUSH *)
                CBuffer.write_int32 buf !vtable_slot;
                CBuffer.write_int16 buf 0x02;  (* REF *)
                CBuffer.write_int16 buf 0x7a;  (* DUP *)
                CBuffer.write_int16 buf 0x00;  (* PUSH total_methods *)
                CBuffer.write_int32 buf total_methods;
                CBuffer.write_int16 buf 0x00; CBuffer.write_int32 buf (-1);
                CBuffer.write_int16 buf 0x00; CBuffer.write_int32 buf (-1);
                CBuffer.write_int16 buf 0x00; CBuffer.write_int32 buf (-1);
                CBuffer.write_int16 buf 0x5a;  (* CALLHLL *)
                CBuffer.write_int32 buf array_lib;
                CBuffer.write_int32 buf array_alloc;
                CBuffer.write_int32 buf 10;
                (* Populate: vtable[i] = impl_idx *)
                Array.iteri vtable ~f:(fun i impl_idx ->
                    CBuffer.write_int16 buf 0x7a;  (* DUP *)
                    CBuffer.write_int16 buf 0x00;  (* PUSH i *)
                    CBuffer.write_int32 buf i;
                    CBuffer.write_int16 buf 0x00;  (* PUSH impl_idx *)
                    CBuffer.write_int32 buf impl_idx;
                    CBuffer.write_int16 buf 0x19;  (* ASSIGN *)
                    CBuffer.write_int16 buf 0x01); (* POP *)
                CBuffer.write_int16 buf 0x01;  (* POP (the ref) *)
                CBuffer.write_int16 buf 0x2f;  (* RETURN *)
                CBuffer.write_int16 buf 0x7e;  (* ENDFUNC *)
                CBuffer.write_int32 buf at0.index;
                Ain.append_bytecode ctx.ain buf;
                Ain.write_function ctx.ain
                  { at0 with address = addr + 6 };
                Ain.write_struct ctx.ain { s with constructor = at0.index })

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
  let v12 = Ain.version_gte ctx.ain (12, 0) in
  Ain.function_iter ctx.ain ~f:(fun (f : Ain.Function.t) ->
      (* v12: only stub functions that have a synth body in ctx.functions
         (e.g. enum Numof/GetList/etc. with [Return (Some (ConstInt n))]).
         Interface methods and templated-class prototype slots should stay
         at address=-1 — that's what the original v12 compiler does for
         the ~1764 prototype entries in Rance10. Stubbing them all
         changes the FUNC table structure the VM walks at load. *)
      let jaf_fundecl = Hashtbl.find ctx.functions f.name in
      let has_synth_body =
        match jaf_fundecl with
        | Some { body = Some _; _ } -> true
        | _ -> false
      in
      let should_stub =
        (f.address = -1 || f.address = -2)
        && not (String.equal f.name "NULL")
        && (if v12 then has_synth_body else true)
      in
      if should_stub then (
        let buf = CBuffer.create 64 in
        let addr = Ain.code_size ctx.ain in
        CBuffer.write_int16 buf 0x61;
        (* FUNC *)
        CBuffer.write_int32 buf f.index;
        (* If a synth fundecl was registered for this slot with a
           [Some [Return (Some (ConstInt n))]] body, honour the
           constant rather than emitting [PUSH 0]. Specifically lets
           synth enum [Numof()] stubs return the real declared value
           count — without this, [Array.Alloc(EnumIndex::Numof(),...)]
           in [Class@0] constructors creates zero-sized arrays and the
           game NULL-derefs at the first array access (observed crash:
           0xC0000005 at offset 0x34 of NULL). *)
        let synth_const_return =
          match jaf_fundecl with
          | Some { body = Some [ { node = Return (Some
              { node = ConstInt n; _ }); _ } ]; _ } -> Some n
          | _ -> None
        in
        (match (f.return_type, synth_const_return) with
        | Ain.Type.Void, _ -> ()
        | (Ain.Type.Int | Ain.Type.Bool | Ain.Type.LongInt), Some n ->
            CBuffer.write_int16 buf 0x00;
            (* PUSH *)
            CBuffer.write_int32 buf n
        | Ain.Type.Float, _ ->
            (* F_PUSH = 0x40, not 0x03 (which is INV). Pre-fix this
               branch never fired because nothing called it; now that
               synth enum-method stubs declare proper return types,
               wrong opcode would emit [INV; PUSHfloat] which the VM
               cannot run. *)
            CBuffer.write_int16 buf 0x40;
            CBuffer.write_float buf 0.0
        | Ain.Type.String, _ ->
            (* S_PUSH = 0x41, not 0x0a (which is SUB). Same story as
               Float — surfaced by [Enum@String] synth stubs after
               proper signatures were wired up. *)
            CBuffer.write_int16 buf 0x41;
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
let desugar_pass ctx program =
  List.iter program ~f:(function
    | Jaf (_, jaf) ->
        Jaf.desugar_foreach jaf;
        Declarations.desugar_initvals ~v12:(Ain.version_gte ctx.ain (12, 0)) jaf
    | Hll _ -> ())

(* v12: original Rance10's CODE section starts with 6 EOF opcodes
   (operands 0..5) before the first FUNC. Filename indices 0..5 are
   reserved placeholders ("0".."5" in the filename table). Our compile
   was emitting only 1 EOF per real file, leading to a 36-byte
   CODE-prologue gap and shifted addresses for every function.

   Pre-register 5 extra placeholder filenames ("1".."5") and emit
   their EOF opcodes BEFORE any real codegen. Filename "0" naturally
   becomes the first real file's name; we shift it by appending
   "1".."5" at the START of the filename array so subsequent EOFs
   use indices >= 6. *)
let emit_v12_code_prologue ctx =
  if Ain.version_gte ctx.ain (12, 0) then begin
    let buf = CBuffer.create 48 in
    (* Register filenames 0..4 as placeholders and emit 5 EOFs. The
       first compiled file naturally takes index 5 and emits the 6th
       EOF when its compilation ends. Original Rance10's CODE has
       exactly 6 EOFs (at 0x00..0x1E) before FUNC 1 at 0x24. *)
    for i = 0 to 4 do
      let idx = Ain.add_file ctx.ain (Int.to_string i) in
      (* EOF opcode = 0x62, 4-byte file index operand *)
      CBuffer.write_int16 buf 0x62;
      CBuffer.write_int32 buf idx
    done;
    Ain.append_bytecode ctx.ain buf
  end

let compile ctx sources debug_info read_file =
  let program = parse_pass ctx sources read_file in
  desugar_pass ctx program;
  let program = type_resolve_pass ctx program in
  type_check_pass ctx program;
  populate_vtables ctx program;
  fix_interface_vtable_offsets ctx;
  emit_v12_code_prologue ctx;
  codegen_pass ctx program debug_info;
  (* populate_interface_vtables replaces existing @0 body which
     contains user-bodied constructor logic — not safe to use.
     populate_interface_vtables ctx;  *)
  emit_undefined_function_stubs ctx;
  (* v12 Rance10's NULL function (index 0) is a zero-sized sentinel
     placed at code_size — the very end of code. Calls to NULL
     dispatch PC past the last byte; the VM treats that as a clean
     return rather than executing. Without this fixup, NULL ends up
     mid-code with arbitrary content (an EOF marker from a file
     boundary, etc.) and calling it triggers
     「ファイルの終端に処理が到達しました」at runtime. Run AFTER
     emit_undefined_function_stubs so no further bytecode appends
     change code_size and push NULL back into the middle. *)
  (if Ain.version_gte ctx.ain (12, 0) then
     match Ain.get_function ctx.ain "NULL" with
     | None -> ()
     | Some f ->
         Ain.write_function ctx.ain
           { f with address = Ain.code_size ctx.ain });
  (* v12: OBJG names are sorted by Shift-JIS bytes in original Rance10
     output. Reorder before writing and remap every global's
     group_index to the new sorted position. *)
  if Ain.version_gte ctx.ain (12, 0) then Ain.sort_global_groups ctx.ain
