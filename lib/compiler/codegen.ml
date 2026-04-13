(* Copyright (C) 2021 Nunuhara Cabbage <nunuhara@haniwa.technology>
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
open Bytecode
open CompileError

type cflow_type = CFlowLoop of int | CFlowSwitch of Ain.Switch.t
type cflow_stmt = {
  kind : cflow_type;
  mutable break_addrs : int list;
  scopes_at_start : int; (* Stack.length scopes at loop/switch entry *)
  mutable inline_deleted_dummies : int list;
  (* DummyRef vars that RefAssign cleaned up inline (and removed from the
     scope). On continue/break the original v11 compiler re-emits
     SH_LOCALDELETE for these, even though the slot is already empty, so
     we track them here and replay on loop exit. *)
}
type scope = { mutable vars : Ain.Variable.t list }

type label_data = {
  mutable address : int option;
  mutable gotos : (int * statement) list;
}

let is_variable_ref = function
  | Ident _ | Member (_, _, ClassVariable _) | Subscript _ -> true
  | _ -> false

let incdec_instruction = function
  | (PreInc | PostInc | ForeachInc), LongInt -> LI_INC
  | (PreDec | PostDec | ForeachDec), LongInt -> LI_DEC
  | (PreInc | PostInc | ForeachInc), _ -> INC
  | (PreDec | PostDec | ForeachDec), _ -> DEC
  | _ -> compiler_bug "invalid inc/dec expression" None

class jaf_compiler ctx debug_info =
  object (self)
    (* The function currently being compiled. *)
    val mutable current_function : Ain.Function.t option = None

    (* The bytecode output buffer. *)
    val mutable buffer = CBuffer.create 2048
    (* Set of lambda function indices whose JUMP+body was already emitted *)
    val pre_emitted_lambdas : (int, unit) Hashtbl.Poly.t = Hashtbl.Poly.create ()

    (* Address of the start of the current buffer. *)
    val mutable start_address : int = 0

    (* Current address within the code section. *)
    val mutable current_address : int = 0

    (* Last opcode written, for dead code detection. *)
    val mutable last_opcode : Bytecode.opcode option = None

    (* The currently active control flow constructs. *)
    val mutable cflow_stmts = Stack.create ()

    (* The currentl active scopes. *)
    val scopes = Stack.create ()

    (* Labels/gotos record for the current function. *)
    val mutable labels = Hashtbl.create (module String)

    (** Try to replace a trailing NOT instruction with IFNZ.
        Returns true if successful (IFNZ written), false if no NOT found. *)
    (* Track if the last instruction emitted was NOT, for IFNZ optimization *)
    val mutable last_was_not = false
    val mutable not_buffer_pos = 0
    (* v11: position of ITOB emitted by emit_not, for rewinding *)
    val mutable not_itob_pos = -1

    method private emit_not =
      last_was_not <- true;
      not_buffer_pos <- buffer.CBuffer.pos;
      self#write_instruction0 NOT;
      (* v11: add ITOB after NOT.  This is needed for condition contexts
         (If/While/Ternary IFZ) because intermediate instructions between
         NOT and IFZ would clear last_was_not.  For non-condition contexts
         (assignment to non-Bool), rewind_not_itob removes it. *)
      if Ain.version ctx.ain > 8 then (
        not_itob_pos <- buffer.CBuffer.pos;
        self#write_instruction0 ITOB)

    (** Rewind the ITOB emitted by emit_not when it's not needed
        (e.g., NOT result assigned to a non-Bool variable). *)
    method private rewind_not_itob =
      if not_itob_pos >= 0
         && buffer.CBuffer.pos = not_itob_pos + 2 then (
        buffer.CBuffer.pos <- not_itob_pos;
        current_address <- current_address - 2;
        not_itob_pos <- -1)

    method try_replace_not_with_ifnz =
      (* v11: disable NOT+IFZ→IFNZ optimization. The original compiler
         always uses NOT+ITOB+IFZ, and the ITOB normalization may be required. *)
      if Ain.version ctx.ain > 8 then (
        last_was_not <- false;
        false)
      else if last_was_not && buffer.CBuffer.pos = not_buffer_pos + 2 then (
        (* Rewind the NOT instruction *)
        buffer.CBuffer.pos <- not_buffer_pos;
        current_address <- current_address - 2;
        last_was_not <- false;
        (* Write IFNZ instead *)
        self#write_instruction1 IFNZ 0;
        true)
      else (
        last_was_not <- false;
        false)

    (** Begin a scope. Variables created within a scope are deleted when the
        scope ends. *)
    method start_scope = Stack.push scopes { vars = [] }

    (** End a scope. Deletes variable created within the scope.
        v11: when ending a scope inside a loop, track cleaned-up ref vars
        so outer loop break/continue can replay the cleanup. Only track
        when the scope is at the loop body level (scope depth = loop's
        scopes_at_start + 1), not for deeper nested scopes like if-blocks. *)
    method end_scope =
      let scope = Stack.pop_exn scopes in
      match Stack.top scopes with
      | None -> ()
          (* Function-level scope: vars cleaned by VM on return *)
      | Some _ ->
          List.iter scope.vars ~f:(fun v ->
              self#compile_delete_var v;
              if Ain.version ctx.ain > 8 then
                match v.value_type with
                | Ain.Type.Ref _ | Struct _ ->
                    self#track_inline_deleted_dummy v.index
                | _ -> ())

    (** Add a variable to the current scope. *)
    method scope_add_var v =
      match Stack.top scopes with
      | Some scope -> scope.vars <- v :: scope.vars
      | None -> compiler_bug "tried to add variable to null scope" None

    (** Remove a variable from the current scope (already cleaned up). *)
    method scope_remove_var (v : Ain.Variable.t) =
      match Stack.top scopes with
      | Some scope ->
          scope.vars <-
            List.filter scope.vars ~f:(fun (sv : Ain.Variable.t) ->
                sv.index <> v.index)
      | None -> ()

    (** Delete DummyRef vars created since vars_before count, and remove from scope *)
    method cleanup_condition_dummyrefs vars_before =
      if Ain.version ctx.ain > 8 then
        match Stack.top scopes with
        | Some scope ->
            let n_new = List.length scope.vars - vars_before in
            if n_new > 0 then
              (* Reverse order: delete outer DummyRefs first, inner last.
                 scope.vars has newest (inner) first, so reverse to get outer first. *)
              let new_vars = List.rev (List.take scope.vars n_new) in
              (* Emit SH_LOCALDELETE but keep vars in scope so end_scope
                 also cleans them at break/continue/return, matching original. *)
              List.iter new_vars ~f:(fun v ->
                  self#compile_delete_var v)
        | None -> ()

    (** Add a label for the current function. *)
    method add_label name stmt =
      Hashtbl.update labels name ~f:(function
        | None -> { address = Some current_address; gotos = [] }
        | Some { address = None; gotos } ->
            { address = Some current_address; gotos }
        | Some _ -> compile_error "Duplicate label" (ASTStatement stmt))

    (** Add a goto address location for the current function *)
    method add_goto name addr_loc stmt =
      let d =
        Hashtbl.find_or_add labels name ~default:(fun _ ->
            { address = None; gotos = [] })
      in
      d.gotos <- (addr_loc, stmt) :: d.gotos

    (** Resolve all goto addresses in the current function. *)
    method resolve_gotos =
      Hashtbl.iter labels ~f:(fun { address; gotos } ->
          match address with
          | Some addr ->
              List.iter gotos ~f:(fun (addr_loc, _) ->
                  self#write_address_at addr_loc addr)
          | None ->
              compile_error "Unresolved label"
                (ASTStatement (snd (List.last_exn gotos))));
      Hashtbl.clear labels

    (** Begin a loop. *)
    method start_loop addr =
      Stack.push cflow_stmts
        { kind = CFlowLoop addr; break_addrs = [];
          scopes_at_start = Stack.length scopes;
          inline_deleted_dummies = [] }

    (** Begin a switch statement. *)
    method start_switch ty node =
      let op, case_type =
        match ty with
        | Jaf.Bool | Int | LongInt -> (SWITCH, Ain.Switch.IntCase)
        | String -> (STRSWITCH, Ain.Switch.StringCase)
        | _ -> compiler_bug "invalid switch type" (Some node)
      in
      let switch = Ain.add_switch ctx.ain case_type in
      Stack.push cflow_stmts
        { kind = CFlowSwitch switch; break_addrs = [];
          scopes_at_start = Stack.length scopes;
          inline_deleted_dummies = [] };
      self#write_instruction1 op switch.index

    (** End the current control flow construct. Updates 'break' addresses.
        Propagates inline_deleted_dummies to enclosing loop so that outer
        break/continue can replay cleanup for inner-scope ref vars. *)
    method end_cflow_stmt =
      let stmt = Stack.pop_exn cflow_stmts in
      List.iter stmt.break_addrs ~f:(fun addr ->
          self#write_address_at addr current_address);
      if Ain.version ctx.ain > 8 then
        match Stack.top cflow_stmts with
        | Some outer ->
            outer.inline_deleted_dummies <-
              stmt.inline_deleted_dummies @ outer.inline_deleted_dummies
        | None -> ()

    (** End the current loop. Updates 'break' addresses. *)
    method end_loop =
      (match Stack.top cflow_stmts with
      | Some { kind = CFlowLoop _; _ } -> ()
      | _ -> compiler_bug "Mismatched start/end of control flow construct" None);
      self#end_cflow_stmt

    (** End the current switch statement. Updates 'break' addresses. *)
    method end_switch =
      (match Stack.top cflow_stmts with
      | Some { kind = CFlowSwitch switch; _ } -> Ain.write_switch ctx.ain switch
      | _ -> compiler_bug "Mismatched start/end of control flow construct" None);
      self#end_cflow_stmt

    method add_switch_case expr node =
      let (switch : Ain.Switch.t) = self#current_switch node in
      let const_expr = match expr with
        | DummyRef (_, { node = e; _ }) -> e
        | e -> e
      in
      let value =
        match const_expr with
        | ConstInt n -> (
            match switch.case_type with
            | Ain.Switch.IntCase -> n
            | Ain.Switch.StringCase ->
                compile_error "int case in string switch" node)
        | ConstString s -> (
            match switch.case_type with
            | Ain.Switch.StringCase -> Ain.add_string ctx.ain s
            | Ain.Switch.IntCase ->
                compile_error "string case in int switch" node)
        | _ -> compile_error "invalid expression in switch case" node
      in
      switch.cases <-
        List.append switch.cases [ (Int32.of_int_exn value, current_address) ]

    method set_switch_default node =
      let switch = self#current_switch node in
      switch.default_address <- current_address

    (** Emit SH_LOCALDELETE for all ref/struct/array vars currently live in
        scopes that were pushed AFTER the enclosing loop started. Used by
        Continue/Break to clean up ref locals declared inside the loop body
        before jumping out. Does not pop the scopes — the natural flow still
        runs end_scope on block exit, so we mustn't pre-pop.

        Loops live at scopes_at_loop (inclusive). So any scope at index
        scopes_at_loop..top-1 was pushed inside the loop and needs cleanup.
        For the loop's own scope (index scopes_at_loop-1), we only cleanup
        for Continue — its vars persist across iterations... actually no,
        for/while/dowhile compile_block their init separately so the loop's
        body is itself a nested scope. The scopes_at_start captures the
        depth at start_loop, which is AFTER the init's compile_block has
        already ended. So scopes_at_start is the depth BEFORE any body
        nesting. All scopes at >= scopes_at_start are inside the loop. *)
    method private emit_loop_exit_cleanup =
      match Stack.top cflow_stmts with
      | Some { scopes_at_start; inline_deleted_dummies; _ } ->
          (* Replay inline-deleted DummyRef cleanups first (matching
             original v11 compiler's pattern: inline cleanup + re-cleanup
             at each loop-exit branch). *)
          List.iter inline_deleted_dummies ~f:(fun idx ->
              self#write_instruction1 SH_LOCALDELETE idx);
          let all_scopes = Stack.to_list scopes in
          (* Stack.to_list returns top-first. The number of "inner" scopes
             to clean is (current_depth - scopes_at_start). Take that many
             from the top. *)
          let n_inner = Stack.length scopes - scopes_at_start in
          if n_inner > 0 then (
            let inner = List.take all_scopes n_inner in
            (* Deepest (innermost) scope first, matching the order that
               end_scope would run them. *)
            List.iter inner ~f:(fun scope ->
                List.iter scope.vars ~f:self#compile_delete_var))
      | None -> ()

    method private track_inline_deleted_dummy idx =
      match Stack.top cflow_stmts with
      | Some s -> s.inline_deleted_dummies <- idx :: s.inline_deleted_dummies
      | None -> ()

    (** Retrieves the continue address for the current loop (i.e. the address
        that 'continue' statements should jump to). *)
    method get_continue_addr node =
      let rec get_first_continue = function
        | { kind = CFlowLoop addr; _ } :: _ -> addr
        | _ :: rest -> get_first_continue rest
        | [] -> compile_error "'continue' statement outside of loop" node
      in
      match Stack.top cflow_stmts with
      | Some { kind = CFlowLoop addr; _ } -> addr
      | Some { kind = CFlowSwitch _; _ } ->
          get_first_continue (Stack.to_list cflow_stmts)
      | _ -> compile_error "'continue' statement outside of loop" node

    (** Retrieves the index for the current switch statement. *)
    method current_switch node =
      match Stack.top cflow_stmts with
      | Some { kind = CFlowSwitch switch; _ } -> switch
      | _ -> compile_error "switch case outside of switch statement" node

    (** Push the location of a 32-bit integer that should be updated to the
        address of the current scope's end point. *)
    method push_break_addr addr node =
      match Stack.top cflow_stmts with
      | Some stmt -> stmt.break_addrs <- addr :: stmt.break_addrs
      | None -> compile_error "'break' statement outside of loop" node

    method compile_CALLHLL lib_name fun_name t parent =
      match Ain.get_library_index ctx.ain lib_name with
      | Some lib_no -> (
          match Ain.get_library_function_index ctx.ain lib_no fun_name with
          | Some fun_no -> self#write_instruction3 CALLHLL lib_no fun_no t
          | None -> compile_error "No HLL function found for built-in" parent)
      | None -> compile_error "No HLL library found for built-in" parent

    method array_element_type_code (ty : jaf_type) =
      match ty with
      | Array t | Ref (Array t) ->
          Ain.Type.int_of_data_type (Ain.version ctx.ain) (jaf_to_ain_type t)
      | _ -> -1

    method write_instruction0 op =
      CBuffer.write_int16 buffer (int_of_opcode op);
      current_address <- current_address + 2;
      last_opcode <- Some op;
      (match op with NOT -> () | _ -> last_was_not <- false)

    method write_instruction1 op arg0 =
      match (Ain.version_lt ctx.ain (11, 0), op) with
      | true, S_MOD ->
          self#write_instruction1 PUSH arg0;
          self#write_instruction0 S_MOD
      | _ ->
          CBuffer.write_int16 buffer (int_of_opcode op);
          CBuffer.write_int32 buffer arg0;
          current_address <- current_address + 6;
          last_opcode <- Some op;
          last_was_not <- false

    method write_instruction1_float op arg0 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_float buffer arg0;
      current_address <- current_address + 6;
      last_opcode <- Some op;
      last_was_not <- false

    method write_instruction2 op arg0 arg1 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_int32 buffer arg0;
      CBuffer.write_int32 buffer arg1;
      current_address <- current_address + 10;
      last_opcode <- Some op;
      last_was_not <- false

    method write_instruction3 op arg0 arg1 arg2 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_int32 buffer arg0;
      CBuffer.write_int32 buffer arg1;
      CBuffer.write_int32 buffer arg2;
      current_address <- current_address + 14;
      last_opcode <- Some op;
      last_was_not <- false

    method write_address_at dst addr =
      CBuffer.write_int32_at buffer (dst - start_address) addr

    method write_buffer =
      if current_address > start_address then (
        Ain.append_bytecode ctx.ain buffer;
        CBuffer.clear buffer;
        start_address <- current_address)

    method get_local i =
      match current_function with
      | Some f ->
          if i < List.length f.vars then List.nth_exn f.vars i
          else
            (* Variable index out of range - likely from foreach desugaring
               or overloaded function index mismatch. Use a dummy. *)
            Ain.Variable.make ~index:i "<dummy>" Ain.Type.Int
      | None -> compiler_bug "get_local outside of function" None

    method member_type (expr : expression) =
      match expr.node with
      | Member
          ( { ty = Struct (_, struct_no) | Ref (Struct (_, struct_no))
               | Wrap (Struct (_, struct_no)); _ },
            _,
            ClassVariable member_no ) ->
          let struct_type = Ain.get_struct_by_index ctx.ain struct_no in
          (List.nth_exn struct_type.members member_no).value_type
      | Member ({ ty = HLLParam | Ref HLLParam; _ }, _, _) ->
          Ain.Type.Int (* HLLParam: type unknown, use int as placeholder *)
      | Member (_, _, UnresolvedMember) ->
          Ain.Type.Int (* Unresolved: use int as placeholder *)
      | _ -> compiler_bug "member of non-struct" (Some (ASTExpression expr))

    method compile_lock_peek =
      if Ain.version_lt ctx.ain (6, 0) then (
        self#write_instruction1 CALLSYS (int_of_syscall LockPeek);
        self#write_instruction0 POP)

    method compile_unlock_peek =
      if Ain.version_lt ctx.ain (6, 0) then (
        self#write_instruction1 CALLSYS (int_of_syscall UnlockPeek);
        self#write_instruction0 POP)

    method compile_delete_var (v : Ain.Variable.t) =
      match v.value_type with
      | Ref _ | Struct _ -> self#write_instruction1 SH_LOCALDELETE v.index
      | Array _ when Ain.version ctx.ain > 8 ->
          (* v11: use CALLHLL Array Free instead of SH_LOCALDELETE for arrays.
             SH_LOCALDELETE destroys the variable, breaking reuse in loop iterations. *)
          (match Ain.get_library_index ctx.ain "Array" with
           | Some lib_no ->
               (match Ain.get_library_function_index ctx.ain lib_no "Free" with
                | Some fun_no ->
                    let elem_type =
                      Ain.Type.int_of_data_type (Ain.version ctx.ain) (
                        match v.value_type with
                        | Array t -> t | _ -> Ain.Type.Int)
                    in
                    self#compile_local_ref v.index;
                    self#write_instruction0 REF;
                    self#write_instruction3 CALLHLL lib_no fun_no elem_type
                | None -> self#write_instruction1 SH_LOCALDELETE v.index)
           | None -> self#write_instruction1 SH_LOCALDELETE v.index)
      | Array _ ->
          self#compile_local_ref v.index;
          self#write_instruction0 A_FREE
      | _ -> ()

    (** Emit the code to put the value of a variable onto the stack (including
        member variables and array elements). Assumes a page + page-index is
        already on the stack. *)
    method compile_dereference (t : Ain.Type.t) =
      match t with
      | Wrap t ->
          (* Wrap (fat ref): REFREF+REF to unwrap *)
          self#write_instruction0 REFREF;
          self#write_instruction0 REF;
          (* Wrapped strings need A_REF in v11 for string dereference *)
          (match t with
           | String when Ain.version ctx.ain > 8 -> self#write_instruction0 A_REF
           | _ -> ())
      | Ref (Int | Float | Bool | LongInt | FuncType _) ->
          self#write_instruction0 REFREF;
          self#write_instruction0 REF
      | Int | Float | Bool | LongInt | FuncType _ -> self#write_instruction0 REF
      | String | Ref String ->
          if Ain.version ctx.ain > 8 then (
            self#write_instruction0 REF;
            self#write_instruction0 A_REF)
          else self#write_instruction0 S_REF
      | Array _ | Ref (Array _) ->
          self#write_instruction0 REF;
          self#write_instruction0 A_REF
      | Struct _ | Ref (Struct _) when Ain.version ctx.ain > 8 ->
          self#write_instruction0 REF;
          self#write_instruction0 A_REF
      | Struct no | Ref (Struct no) -> self#write_instruction1 SR_REF no
      | Delegate _ | Ref (Delegate _) ->
          if Ain.version ctx.ain > 8 then (
            self#write_instruction0 REF;
            self#write_instruction0 A_REF)
          else (
            self#write_instruction0 REF;
            self#write_instruction0 DG_COPY)
      | HLLParam | Ref HLLParam ->
          (* HLLParam: type unknown at compile time, use REF as default *)
          self#write_instruction0 REF
      | Void | IMainSystem | Ref _ | Option _
      | Unknown87 _ | IFace _ | Enum2 _ | Enum _ | HLLFunc | HLLFunc2 | Unknown98
      | IFaceWrap _ | Function | Method | NullType ->
          compiler_bug "dereference not supported for type" None

    method compile_local_ref i =
      self#write_instruction0 PUSHLOCALPAGE;
      self#write_instruction1 PUSH i

    method compile_global_ref i =
      self#write_instruction0 PUSHGLOBALPAGE;
      self#write_instruction1 PUSH i

    method compile_identifier_ref id_type =
      match id_type with
      | LocalVariable (i, _) -> self#compile_local_ref (self#get_local i).index
      | CapturedVariable (i, level) ->
          (* Lambda capture: use X_GETENV to access parent's page *)
          self#write_instruction0 PUSHLOCALPAGE;
          for _ = 1 to level do
            self#write_instruction0 X_GETENV
          done;
          self#write_instruction1 PUSH i
      | GlobalVariable i ->
          self#compile_global_ref (Ain.get_global_by_index ctx.ain i).index
      | _ -> compiler_bug "Invalid identifier type" None

    method compile_variable_ref (e : expression) =
      match e.node with
      | Ident (_, id_type) -> self#compile_identifier_ref id_type
      | Member (e, _, ClassVariable member_no) ->
          self#compile_lvalue e;
          (match e.ty with
           | Wrap _ ->
               self#write_instruction0 REFREF;
               self#write_instruction0 REF
           | _ -> ());
          self#write_instruction1 PUSH member_no
      | Subscript (obj, index) ->
          self#compile_lvalue obj;
          self#compile_expression index
      | _ -> compiler_bug "Invalid variable ref" (Some (ASTExpression e))

    method compile_delete_ref ty =
      self#write_instruction0 DUP2;
      if is_ref_scalar ty then (
        self#write_instruction0 REFREF;
        self#write_instruction0 POP)
      else self#write_instruction0 REF;
      self#write_instruction0 DELETE

    (** Emit the code to put a location (variable, struct member, or array
        element) onto the stack, e.g. to prepare for an assignment or to pass a
        variable by reference. *)
    method compile_lvalue (e : expression) =
      let compile_lvalue_after (t : Ain.Type.t) =
        match t with
        | Wrap String when Ain.version ctx.ain > 8 ->
            (* Wrap<string> lvalue: REFREF+REF to unwrap for S_ASSIGN *)
            self#write_instruction0 REFREF;
            self#write_instruction0 REF
        | Wrap (Int | Float | Bool | LongInt) when Ain.version ctx.ain > 8 ->
            (* Wrap<scalar> lvalue: REFREF to unwrap the fat ref to the
               underlying page+index (for foreach loop variable assigns). *)
            self#write_instruction0 REFREF
        | Wrap _ -> () (* Other wrap lvalue: just page+index *)
        | Ref (Int | Float | Bool | LongInt) -> self#write_instruction0 REFREF
        | Ref (String | Array _ | Struct _) -> self#write_instruction0 REF
        | String | Array _ | Struct _ | Delegate _ ->
            self#write_instruction0 REF
        | _ -> ()
      in
      match e.node with
      | Ident (_, LocalVariable (i, _)) -> (
          match self#get_local i with
          | {
           value_type =
             String | Array _ | Struct _ | Ref (String | Array _ | Struct _);
           _;
          }
            when ctx.version < 630 ->
              self#write_instruction1 SH_LOCALREF i
          | v ->
              self#compile_local_ref v.index;
              compile_lvalue_after v.value_type)
      | Ident (_, CapturedVariable (i, level)) ->
          (* Lambda capture lvalue: X_GETENV to access parent page *)
          self#write_instruction0 PUSHLOCALPAGE;
          for _ = 1 to level do
            self#write_instruction0 X_GETENV
          done;
          self#write_instruction1 PUSH i
      | Ident (_, GlobalVariable i) -> (
          match Ain.get_global_by_index ctx.ain i with
          | {
           value_type =
             String | Array _ | Struct _ | Ref (String | Array _ | Struct _);
           _;
          }
            when ctx.version < 630 ->
              self#write_instruction1 SH_GLOBALREF i
          | v ->
              self#compile_global_ref v.index;
              compile_lvalue_after v.value_type)
      | Member (obj, _, ClassVariable member_no) -> (
          match (obj.node, e.ty) with
          | ( This,
              ( Ref (String | Array _ | Struct _)
              | String | Array _ | Struct _ | Delegate _ ) )
            when ctx.version < 630 ->
              self#write_instruction1 SH_STRUCTREF member_no
          | _ ->
              self#compile_lvalue obj;
              (match obj.ty with
               | Wrap _ ->
                   self#write_instruction0 REFREF;
                   self#write_instruction0 REF
               | _ -> ());
              self#write_instruction1 PUSH member_no;
              compile_lvalue_after (self#member_type e))
      | Subscript (obj, index) ->
          self#compile_lvalue obj;
          self#compile_expression index;
          compile_lvalue_after (jaf_to_ain_type e.ty)
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression e))
      | DummyRef (var_no, ref_expr) -> (
          self#scope_add_var (self#get_local var_no);
          match ref_expr with
          | { node = New { ty = Struct (_, s_no); _ }; _ } when Ain.version ctx.ain > 8 ->
              (* v11: REF+CHECKUDO then NEW with constructor index *)
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#write_instruction0 CHECKUDO;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              let ctor = (Ain.get_struct_by_index ctx.ain s_no).constructor in
              self#write_instruction2 NEW s_no ctor;
              self#write_instruction0 ASSIGN
          | { node = New { ty = Struct (_, s_no); _ }; _ } ->
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction1 PUSH s_no;
              self#compile_lock_peek;
              self#write_instruction0 NEW;
              self#write_instruction0 ASSIGN;
              self#compile_unlock_peek
          | _ when Ain.version ctx.ain > 8
                   && not (match (self#get_local var_no).value_type with
                           | Ain.Type.Ref (Int | Bool | Float | LongInt) -> true
                           | _ -> is_ref_scalar ref_expr.ty) ->
              (* v11 non-scalar ref: expr first, then CHECKUDO + SWAP + ASSIGN *)
              let emit_checkudo () =
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH var_no;
                self#write_instruction0 REF;
                self#write_instruction0 CHECKUDO;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction0 SWAP;
                self#write_instruction1 PUSH var_no;
                self#write_instruction0 SWAP;
                self#write_instruction0 ASSIGN
              in
              (* OptionalCall (?. method): DummyRef handling must be inside
                 the not-null branch, before the JUMP to merge point *)
              (match ref_expr.node with
              | Call ({ node = OptionalMember (obj, _, _); _ }, args, MethodCall (_, method_no)) ->
                  self#compile_lvalue obj;
                  self#write_instruction0 DUP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let ifnz_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  (* Not null: call method + DummyRef handling *)
                  self#compile_method_call args method_no;
                  emit_checkudo ();
                  (* Second null check on the result *)
                  self#write_instruction0 DUP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let ifnz2_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  self#write_instruction1 PUSH 0;
                  let jump_end_inner = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at ifnz2_addr current_address;
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1);
                  self#write_address_at jump_end_inner current_address;
                  let jump_end_outer = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at ifnz_addr current_address;
                  (* Null branch: pop null object, push default ref *)
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1);
                  self#write_address_at jump_end_outer current_address
              | _ ->
                  self#compile_expression ref_expr;
                  emit_checkudo ())
          | _ when Ain.version ctx.ain > 8 ->
              (* v11 scalar ref (2 VM stack slots): use DUP_X2;POP rotation
                 matching the original pattern exactly.
                 After R_ASSIGN, REF dereferences the stored ref to get the value. *)
              self#compile_expression ref_expr;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#write_instruction0 CHECKUDO;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction0 R_ASSIGN
          | _ ->
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#compile_expression ref_expr;
              self#write_instruction0
                (if is_ref_scalar ref_expr.ty then R_ASSIGN else ASSIGN))
      | RvalueRef e ->
          (* TODO: Insert <dummy : 右辺値参照化用> variable *)
          self#compile_expression e
      | Member (obj, _, ClassMethod (name, no))
        when String.is_suffix name ~suffix:"::get"
             || String.is_suffix name ~suffix:"::set" ->
          (* Property getter/setter as lvalue *)
          self#compile_lvalue obj;
          if Ain.version ctx.ain > 8 then
            self#write_instruction1 PUSH no
          else self#write_instruction1 CALLMETHOD no
      | Member (e, _, UnresolvedMember) | OptionalMember (e, _, _) ->
          (* Unresolved/optional member - compile object *)
          self#compile_expression e
      | This -> self#write_instruction0 PUSHSTRUCTPAGE
      | Null -> (
          match e.ty with
          | Ref t ->
              self#write_instruction1 PUSH (-1);
              if is_numeric t then self#write_instruction1 PUSH 0
          | ty ->
              compiler_bug
                ("unimplemented: NULL lvalue of type " ^ jaf_type_to_string ty)
                (Some (ASTExpression e)))
      | Ternary (test, con, alt) ->
          self#compile_expression test;
          if Ain.version ctx.ain > 8
             && not (TypeAnalysis.is_bool_producing_expr test)
             && (match test.ty with Bool -> false | _ -> true)
             && (match test.node with
                 | ConstInt _ -> false
                 | Call (_, _, (HLLCall _ | SystemCall _)) -> false
                 | _ -> true) then (
            last_was_not <- false;
            self#write_instruction0 ITOB)
          else if Ain.version ctx.ain > 8 && last_was_not then (
            last_was_not <- false;
            self#write_instruction0 ITOB);
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_lvalue con;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifz_addr current_address;
          self#compile_lvalue alt;
          self#write_address_at jump_addr current_address
      | Call _ ->
          (* HLL call returning ref - compile the call, ref stays on stack *)
          self#compile_expression e
      | Cast (_, inner) ->
          (* Cast wrapping an lvalue - compile the inner *)
          self#compile_lvalue inner
      | _ ->
          compiler_bug
            ("invalid lvalue: " ^ expr_to_string e)
            (Some (ASTExpression e))

    (** Emit the code to pop a value off the stack. *)
    method compile_pop (t : jaf_type) parent =
      match t with
      | Void -> ()
      | Int | Float | Bool | LongInt | FuncType _ | Ref _ | TyFunction _
      | TyMethod _ | Untyped | Wrap _ ->
          self#write_instruction0 POP
      | HLLParam ->
          (* v11: X_SET result needs DELETE to release the old value *)
          if Ain.version ctx.ain > 8 then self#write_instruction0 DELETE
          else self#write_instruction0 POP
      | String ->
          if Ain.version ctx.ain > 8 then self#write_instruction0 DELETE
          else self#write_instruction0 S_POP
      | Delegate _ ->
          if Ain.version ctx.ain > 8 then self#write_instruction0 DELETE
          else self#write_instruction0 DG_POP
      | Struct _ ->
          if Ain.version ctx.ain > 8 then self#write_instruction0 DELETE
          else self#write_instruction0 SR_POP
      | Array _ ->
          if Ain.version ctx.ain > 8 then self#write_instruction0 DELETE
          else self#write_instruction0 POP
      | IMainSystem | HLLFunc | HLLFunc2 | NullType
      | Unresolved _ | MemberPtr _ | TypeUnion _ ->
          compiler_bug
            ("compile_pop: unsupported value type " ^ jaf_type_to_string t)
            (Some parent)

    method private can_use_raw_string_assign_rhs (e : expression) =
      match e.node with
      | Ident _ | Member _ | Subscript _ | DummyRef _ | RvalueRef _ | Call _ | This ->
          true
      | Cast (_, inner) -> self#can_use_raw_string_assign_rhs inner
      | Ternary (_, con, alt) ->
          self#can_use_raw_string_assign_rhs con
          && self#can_use_raw_string_assign_rhs alt
      | _ -> false

    method compile_argument (expr : expression option) (t : Ain.Type.t) =
      match expr with
      | None -> compiler_bug "missing argument" None
      | Some expr -> (
          match t with
          | Ref _ -> self#compile_lvalue expr
          | HLLParam when Ain.version ctx.ain > 8
                        && (match expr.node with
                            | Ident (_, LocalVariable (i, _)) ->
                                (match (self#get_local i).value_type with
                                 | Ain.Type.Ref (Struct _ | Array _ | String) -> true
                                 | _ -> false)
                            | _ -> false) ->
              (* v11 HLLParam arg backed by a ref-typed local: push the ref
                 value (one slot) via compile_lvalue, not the dereferenced
                 value via compile_expression. The original compiler emits
                 REF only - compile_expression would add an extra A_REF that
                 over-derefs and feeds the wrong value to the HLL function. *)
              self#compile_lvalue expr
          | Method ->
              (* XXX: for delegate builtins *)
              self#compile_expression expr
          | Delegate _ -> (
              self#compile_expression expr;
              match expr.ty with
              | TyMethod _ ->
                  (* Skip if Cast already emitted DG_NEW_FROM_METHOD
                     (e.g. String->Delegate cast via DG_STR_TO_METHOD) *)
                  let already_wrapped = match expr.node with
                    | Cast (_, { ty = String; _ }) -> Ain.version ctx.ain > 8
                    | _ -> false in
                  if not already_wrapped then
                    self#write_instruction0 DG_NEW_FROM_METHOD
              | _ -> ())
          | _ -> self#compile_expression expr)

    method compile_function_arguments args (f : Ain.Function.t) =
      let params = Ain.Function.logical_parameters f in
      let compile_arg arg (var : Ain.Variable.t) =
        self#compile_argument arg var.value_type
      in
      List.iter2_exn args (List.take params (List.length args)) ~f:compile_arg

    (** Emit the code to call a method. The object upon which the method is to
        be called should already be on the stack before this code is executed.
    *)
    method compile_method_call args method_no =
      let f = Ain.get_function_by_index ctx.ain method_no in
      if Ain.version ctx.ain > 8 then (
        (* v11+: PUSH func_index, then args, then CALLMETHOD nr_args.
           Use f.nr_args to account for void slots from scalar refs. *)
        self#write_instruction1 PUSH method_no;
        self#compile_function_arguments args f;
        self#write_instruction1 CALLMETHOD f.nr_args)
      else (
        self#compile_function_arguments args f;
        self#write_instruction1 CALLMETHOD method_no)

    (** Emit the code to compute an expression. Computing an expression produces
        a value (of the expression's value type) on the stack. *)
    method compile_expression (expr : expression) =
      match expr.node with
      | ConstInt i -> self#write_instruction1 PUSH i
      | ConstFloat f -> self#write_instruction1_float F_PUSH f
      | ConstChar s -> (
          Stdlib.Uchar.(
            let dec = Stdlib.String.get_utf_8_uchar s 0 in
            if
              not
                (utf_decode_is_valid dec
                && String.length s = utf_decode_length dec)
            then compile_error "Invalid character constant" (ASTExpression expr);
            match Sjis.from_uchar_le (utf_decode_uchar dec) with
            | Some c -> self#write_instruction1 PUSH c
            | None ->
                compile_error "Invalid character constant" (ASTExpression expr))
          )
      | ConstString s ->
          let no = Ain.add_string ctx.ain s in
          self#write_instruction1 S_PUSH no
      | Ident (_, LocalVariable (i, _)) -> (
          match (self#get_local i).value_type with
          | (Int | Float | Bool | LongInt | FuncType _) when ctx.version < 630
            ->
              self#write_instruction1 SH_LOCALREF i
          | t ->
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH i;
              self#compile_dereference t)
      | Ident (_, CapturedVariable (i, level)) ->
          (* Lambda capture: X_GETENV to access parent page, then deref *)
          self#write_instruction0 PUSHLOCALPAGE;
          for _ = 1 to level do
            self#write_instruction0 X_GETENV
          done;
          self#write_instruction1 PUSH i;
          self#write_instruction0 REF;
          (* For reference types, A_REF to dereference the ref *)
          (match expr.ty with
          | Ref _ | Array _ | String | Struct _ | Delegate _ ->
              self#write_instruction0 A_REF
          | _ -> ())
      | FuncAddr (_, Some no) ->
          (* v11: method references are 2 slots: object_page + func_index.
             Free function refs use -1 as null object page. *)
          if Ain.version ctx.ain > 8 then
            self#write_instruction1 PUSH (-1);
          self#write_instruction1 PUSH no
      | FuncAddr (_, None) ->
          compiler_bug "unresolved FuncAddr" (Some (ASTExpression expr))
      | MemberAddr (_, _, v) -> self#write_instruction1 PUSH v
      | Ident (_, GlobalVariable i) -> (
          match (Ain.get_global_by_index ctx.ain i).value_type with
          | (Int | Float | Bool | LongInt | FuncType _) when ctx.version < 630
            ->
              self#write_instruction1 SH_GLOBALREF i
          | t ->
              self#write_instruction0 PUSHGLOBALPAGE;
              self#write_instruction1 PUSH i;
              self#compile_dereference t)
      | Ident (_, GlobalConstant) ->
          compiler_bug "global constant not eliminated"
            (Some (ASTExpression expr))
      | Ident (_, FunctionName _) ->
          compiler_bug "tried to compile function identifier"
            (Some (ASTExpression expr))
      | Ident (_, HLLName) ->
          compiler_bug "tried to compile HLL identifier"
            (Some (ASTExpression expr))
      | Ident (_, System) ->
          compiler_bug "tried to compile system identifier"
            (Some (ASTExpression expr))
      | Ident (_, BuiltinFunction _) ->
          compiler_bug "tried to compile built-in function identifier"
            (Some (ASTExpression expr))
      | Ident (_, UnresolvedIdent) ->
          compiler_bug "identifier type is none" (Some (ASTExpression expr))
      | Unary (UPlus, e) -> self#compile_expression e
      | Unary (UMinus, e) ->
          self#compile_expression e;
          self#write_instruction0 (match e.ty with Float -> F_INV | _ -> INV)
      | Unary (LogNot, e) ->
          self#compile_expression e;
          if Ain.version ctx.ain > 8 then
            self#emit_not
          else
            self#write_instruction0 NOT
      | Unary (BitNot, e) ->
          self#compile_expression e;
          self#write_instruction0 COMPL
      | Unary (((ForeachInc | ForeachDec) as op), e) ->
          (* Foreach counter increment: emit INC then reload, matching
             the original compiler's pattern (no DUP2). *)
          self#compile_lvalue e;
          self#write_instruction0 (incdec_instruction (op, e.ty));
          self#compile_lvalue e;
          self#write_instruction0 REF
      | Unary (((PreInc | PreDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 (incdec_instruction (op, e.ty));
          self#write_instruction0 REF
      | Unary (((PostInc | PostDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction0 DUP_X2;
          self#write_instruction0 POP;
          self#write_instruction0 (incdec_instruction (op, e.ty))
      | Binary (LogOr, a, b) ->
          self#compile_expression a;
          let lhs_true_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          self#compile_expression b;
          let rhs_true_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          self#write_instruction1 PUSH 0;
          let false_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at lhs_true_addr current_address;
          self#write_address_at rhs_true_addr current_address;
          self#write_instruction1 PUSH 1;
          self#write_address_at false_addr current_address
      | Binary (LogAnd, a, b) ->
          self#compile_expression a;
          let lhs_false_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_expression b;
          let rhs_false_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#write_instruction1 PUSH 1;
          let true_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at lhs_false_addr current_address;
          self#write_address_at rhs_false_addr current_address;
          self#write_instruction1 PUSH 0;
          self#write_address_at true_addr current_address
      | Binary (op, a, b) -> (
          (match op with
          | RefEqual | RefNEqual when is_scalar a.ty || is_scalar b.ty
                                         || is_ref_scalar a.ty || is_ref_scalar b.ty ->
              (* Scalar/scalar-ref comparison - compile as expressions (dereferences refs) *)
              self#compile_expression a;
              self#compile_expression b
          | RefEqual | RefNEqual ->
              self#compile_lvalue a;
              self#compile_lvalue b
          | _ ->
              self#compile_expression a;
              self#compile_expression b);
          match (a.ty, op) with
          | (Int | LongInt | Bool), Equal -> self#write_instruction0 EQUALE
          | (Int | LongInt | Bool), NEqual -> self#write_instruction0 NOTE
          | Int, Plus -> self#write_instruction0 ADD
          | Int, Minus -> self#write_instruction0 SUB
          | Int, Times -> self#write_instruction0 MUL
          | Int, Divide -> self#write_instruction0 DIV
          | Int, Modulo -> self#write_instruction0 MOD
          | (Int | LongInt), LT -> self#write_instruction0 LT
          | (Int | LongInt), GT -> self#write_instruction0 GT
          | (Int | LongInt), LTE -> self#write_instruction0 LTE
          | (Int | LongInt), GTE -> self#write_instruction0 GTE
          | (Int | Bool), BitOr ->
              self#write_instruction0 OR;
              if Ain.version ctx.ain > 8
                 && (match a.ty with Bool -> true | _ -> false)
              then self#write_instruction0 ITOB
          | (Int | Bool), BitXor ->
              self#write_instruction0 XOR;
              if Ain.version ctx.ain > 8
                 && (match a.ty with Bool -> true | _ -> false)
              then self#write_instruction0 ITOB
          | (Int | Bool), BitAnd ->
              self#write_instruction0 AND;
              if Ain.version ctx.ain > 8
                 && (match a.ty with Bool -> true | _ -> false)
              then self#write_instruction0 ITOB
          | (Int | Bool), LShift -> self#write_instruction0 LSHIFT
          | (Int | Bool), RShift -> self#write_instruction0 RSHIFT
          | Int, (LogOr | LogAnd) ->
              compiler_bug "invalid integer operator"
                (Some (ASTExpression expr))
          | LongInt, Plus -> self#write_instruction0 LI_ADD
          | LongInt, Minus -> self#write_instruction0 LI_SUB
          | LongInt, Times -> self#write_instruction0 LI_MUL
          | LongInt, Divide -> self#write_instruction0 LI_DIV
          | LongInt, Modulo -> self#write_instruction0 LI_MOD
          | Float, Plus -> self#write_instruction0 F_ADD
          | Float, Minus -> self#write_instruction0 F_SUB
          | Float, Times -> self#write_instruction0 F_MUL
          | Float, Divide -> self#write_instruction0 F_DIV
          | Float, Equal -> self#write_instruction0 F_EQUALE
          | Float, NEqual -> self#write_instruction0 F_NOTE
          | Float, LT -> self#write_instruction0 F_LT
          | Float, GT -> self#write_instruction0 F_GT
          | Float, LTE -> self#write_instruction0 F_LTE
          | Float, GTE -> self#write_instruction0 F_GTE
          | ( Float,
              ( Modulo | BitOr | BitXor | BitAnd | LShift | RShift | LogOr
              | LogAnd ) ) ->
              compiler_bug "invalid floating point operator"
                (Some (ASTExpression expr))
          | String, Plus -> self#write_instruction0 S_ADD
          | String, Equal -> self#write_instruction0 S_EQUALE
          | String, NEqual -> self#write_instruction0 S_NOTE
          | String, LT -> self#write_instruction0 S_LT
          | String, GT -> self#write_instruction0 S_GT
          | String, LTE -> self#write_instruction0 S_LTE
          | String, GTE -> self#write_instruction0 S_GTE
          | String, Modulo ->
              let int_of_t (t : Ain.Type.t) =
                match t with
                | Int -> 2
                | Float -> 3
                | String -> 4
                | Bool -> 48
                | LongInt -> 56
                | HLLParam -> 2 (* assume int *)
                | _ ->
                    compiler_bug "invalid type for string formatting"
                      (Some (ASTExpression expr))
              in
              self#write_instruction1 S_MOD (int_of_t (jaf_to_ain_type b.ty))
          | ( String,
              ( Minus | Times | Divide | BitOr | BitXor | BitAnd | LShift
              | RShift | LogOr | LogAnd ) ) ->
              compiler_bug "invalid string operator" (Some (ASTExpression expr))
          | Ref t, RefEqual when Ain.version ctx.ain > 8 && is_numeric t ->
              (* v11 scalar ref: already dereferenced by compile_expression, use EQUALE *)
              self#write_instruction0 EQUALE
          | Ref t, RefNEqual when Ain.version ctx.ain > 8 && is_numeric t ->
              self#write_instruction0 NOTE
          | Ref t, RefEqual ->
              self#write_instruction0
                (if is_numeric t then R_EQUALE else EQUALE)
          | Ref t, RefNEqual ->
              self#write_instruction0 (if is_numeric t then R_NOTE else NOTE)
          | (Int | LongInt | Bool), RefEqual -> self#write_instruction0 EQUALE
          | (Int | LongInt | Bool), RefNEqual -> self#write_instruction0 NOTE
          | (Struct _ | String | Array _ | Delegate _ | Wrap _), RefEqual ->
              self#write_instruction0 EQUALE
          | (Struct _ | String | Array _ | Delegate _ | Wrap _), RefNEqual ->
              self#write_instruction0 NOTE
          | FuncType _, Equal -> self#write_instruction0 EQUALE
          | FuncType _, NEqual -> self#write_instruction0 NOTE
          | HLLParam, Equal -> self#write_instruction0 EQUALE
          | HLLParam, NEqual -> self#write_instruction0 NOTE
          | HLLParam, _ -> self#write_instruction0 EQUALE (* placeholder *)
          | _ ->
              compiler_bug
                (Printf.sprintf "invalid binary expression: %s"
                   (Jaf.jaf_type_to_string a.ty))
                (Some (ASTExpression expr)))
      | Assign (EqAssign, { node = Member (obj, mname, ClassMethod (name, _no)); _ }, rhs)
        when String.is_suffix name ~suffix:"::get"
             || String.is_suffix name ~suffix:"::set" ->
          (* Property setter - look up the ::set method and compile as method call.
             DUP_X2 preserves the assigned value as the expression result. *)
          let setter_name =
            if String.is_suffix name ~suffix:"::get" then
              String.chop_suffix_exn name ~suffix:"::get" ^ "::set"
            else name
          in
          let setter_idx =
            match Ain.get_function ctx.ain setter_name with
            | Some f -> f.index
            | None ->
                (* Try member name resolution *)
                (match Ain.get_function ctx.ain
                   (String.chop_suffix_exn setter_name ~suffix:("@" ^ mname ^ "::set")
                    ^ "@" ^ mname ^ "::set") with
                | Some f -> f.index
                | None -> _no)
          in
          self#compile_lvalue obj;
          if Ain.version ctx.ain > 8 then (
            (* v11: PUSH setter_idx; compile arg; DUP_X2; [A_REF]; CALLMETHOD 1; DELETE
               The A_REF after DUP_X2 dereferences the duplicated value for the method call.
               DELETE properly releases the result (not just POP). *)
            let f = Ain.get_function_by_index ctx.ain setter_idx in
            self#write_instruction1 PUSH setter_idx;
            self#compile_function_arguments [Some rhs] f;
            self#write_instruction0 DUP_X2;
            (* v11: A_REF after DUP_X2 for string/ref args to dereference the copy *)
            (match rhs.ty with
            | String | Ref _ | Struct _ | Array _ -> self#write_instruction0 A_REF
            | _ -> ());
            self#write_instruction1 CALLMETHOD (List.length [Some rhs]);
            (* DELETE for string/ref results, POP for scalars *)
            (match rhs.ty with
            | String | Ref _ | Struct _ | Array _ -> self#write_instruction0 DELETE
            | _ -> self#write_instruction0 POP))
          else
            self#compile_method_call [Some rhs] setter_idx
      | Assign (op, lhs, rhs) -> (
          self#compile_lvalue lhs;
          self#compile_expression rhs;
          (* v11: emit_not adds NOT;ITOB for condition contexts.  The
             original compiler keeps ITOB when assigning to a Bool LHS
             (normalizing the NOT result) but omits it for non-Bool LHS.
             Rewind the ITOB for non-Bool assignments. *)
          if Ain.version ctx.ain > 8
             && (match rhs.node with
                 | Unary (LogNot, _) -> true
                 | Cast (_, { node = Unary (LogNot, _); _ }) -> true
                 | _ -> false)
             && not (match lhs.ty with Bool -> true | _ -> false) then
            self#rewind_not_itob;
          match (op, rhs.ty) with
          | EqAssign, (Int | Bool | TyFunction _ | FuncType _) ->
              self#write_instruction0 ASSIGN
          | PlusAssign, (Int | Bool) -> self#write_instruction0 PLUSA
          | MinusAssign, (Int | Bool) -> self#write_instruction0 MINUSA
          | TimesAssign, (Int | Bool) -> self#write_instruction0 MULA
          | DivideAssign, (Int | Bool) -> self#write_instruction0 DIVA
          | ModuloAssign, (Int | Bool) -> self#write_instruction0 MODA
          | OrAssign, (Int | Bool) -> self#write_instruction0 ORA
          | XorAssign, (Int | Bool) -> self#write_instruction0 XORA
          | AndAssign, (Int | Bool) -> self#write_instruction0 ANDA
          | LShiftAssign, (Int | Bool) -> self#write_instruction0 LSHIFTA
          | RShiftAssign, (Int | Bool) -> self#write_instruction0 RSHIFTA
          | CharAssign, Int -> self#write_instruction0 C_ASSIGN
          | EqAssign, LongInt -> self#write_instruction0 LI_ASSIGN
          | PlusAssign, LongInt -> self#write_instruction0 LI_PLUSA
          | MinusAssign, LongInt -> self#write_instruction0 LI_MINUSA
          | TimesAssign, LongInt -> self#write_instruction0 LI_MULA
          | DivideAssign, LongInt -> self#write_instruction0 LI_DIVA
          | ModuloAssign, LongInt -> self#write_instruction0 LI_MODA
          | AndAssign, LongInt -> self#write_instruction0 LI_ANDA
          | OrAssign, LongInt -> self#write_instruction0 LI_ORA
          | XorAssign, LongInt -> self#write_instruction0 LI_XORA
          | LShiftAssign, LongInt -> self#write_instruction0 LI_LSHIFTA
          | RShiftAssign, LongInt -> self#write_instruction0 LI_RSHIFTA
          | EqAssign, Float -> self#write_instruction0 F_ASSIGN
          | PlusAssign, Float -> self#write_instruction0 F_PLUSA
          | MinusAssign, Float -> self#write_instruction0 F_MINUSA
          | TimesAssign, Float -> self#write_instruction0 F_MULA
          | DivideAssign, Float -> self#write_instruction0 F_DIVA
          | EqAssign, String -> (
              match lhs.ty with
              | FuncType (Some (_, ft_i)) ->
                  self#write_instruction1 PUSH ft_i;
                  self#write_instruction0 FT_ASSIGNS
              | Delegate (Some (_, dg_i)) ->
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 SWAP;
                  (if Ain.version ctx.ain > 8 then (
                     self#write_instruction1 DG_STR_TO_METHOD dg_i;
                     self#write_instruction0 DG_NEW_FROM_METHOD;
                     self#write_instruction0 DG_ASSIGN;
                     self#write_instruction0 DELETE)
                   else (
                     self#write_instruction1 PUSH dg_i;
                     self#write_instruction0 DG_STR_TO_METHOD;
                     self#write_instruction0 DG_SET))
              | String | HLLParam -> self#write_instruction0 S_ASSIGN
              | _ ->
                  compiler_bug "invalid string assignment"
                    (Some (ASTExpression expr)))
          | PlusAssign, String -> (
              match lhs.ty with
              | Delegate (Some (_, dg_i)) ->
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 SWAP;
                  (if Ain.version ctx.ain > 8 then (
                     self#write_instruction1 DG_STR_TO_METHOD dg_i;
                     self#write_instruction0 DG_NEW_FROM_METHOD;
                     self#write_instruction0 DG_PLUSA;
                     self#write_instruction0 DELETE)
                   else (
                     self#write_instruction1 PUSH dg_i;
                     self#write_instruction0 DG_STR_TO_METHOD;
                     self#write_instruction0 DG_ADD))
              | String -> self#write_instruction0 S_PLUSA2
              | _ ->
                  compiler_bug "invalid string assignment"
                    (Some (ASTExpression expr)))
          | EqAssign, TyMethod _ ->
              if Ain.version ctx.ain > 8 then (
                (match rhs.node with
                | Member (_, _, ClassMethod _) | Cast (_, { node = Member (_, _, ClassMethod _); _ })
                | Lambda _ | FuncAddr _
                | Cast (_, { node = FuncAddr _; _ })
                | Cast (_, { node = Lambda _; _ }) ->
                    self#write_instruction0 DG_NEW_FROM_METHOD
                | _ -> ());
                self#write_instruction0 DG_ASSIGN;
                self#write_instruction0 DELETE)
              else self#write_instruction0 DG_SET
          | EqAssign, Delegate _ ->
              self#write_instruction0 DG_ASSIGN;
              if Ain.version ctx.ain > 8 then
                self#write_instruction0 DELETE
          | PlusAssign, TyMethod _ ->
              if Ain.version ctx.ain > 8 then (
                (match rhs.node with
                | Member (_, _, ClassMethod _) | Cast (_, { node = Member (_, _, ClassMethod _); _ })
                | Lambda _ | FuncAddr _
                | Cast (_, { node = FuncAddr _; _ })
                | Cast (_, { node = Lambda _; _ }) ->
                    self#write_instruction0 DG_NEW_FROM_METHOD
                | _ -> ());
                self#write_instruction0 DG_PLUSA;
                self#write_instruction0 DELETE)
              else self#write_instruction0 DG_ADD
          | PlusAssign, Delegate _ -> self#write_instruction0 DG_PLUSA
          | MinusAssign, TyMethod _ -> self#write_instruction0 DG_ERASE
          | MinusAssign, Delegate _ -> self#write_instruction0 DG_MINUSA
          | EqAssign, Struct (_, sno) | EqAssign, Ref (Struct (_, sno)) ->
              if Ain.version ctx.ain <= 1 || Ain.version ctx.ain > 8 then
                self#write_instruction0 SR_ASSIGN
              else (
                self#write_instruction1 PUSH sno;
                self#write_instruction0 SR_ASSIGN)
          | EqAssign, HLLParam ->
              if Ain.version ctx.ain > 8 then
                (* X_SET handles delete-old + assign-new + SP_INC.
                   Result stays on stack for compile_pop to clean up. *)
                self#write_instruction0 X_SET
              else self#write_instruction0 ASSIGN
          | PlusAssign, HLLParam -> self#write_instruction0 PLUSA
          | EqAssign, Array _ | EqAssign, Ref (Array _) ->
              if Ain.version ctx.ain > 8 then
                self#write_instruction0 X_SET
              else self#write_instruction0 ASSIGN
          | _, _ ->
              compiler_bug "invalid assignment" (Some (ASTExpression expr)))
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_expression b
      | Ternary (test, con, alt) ->
          self#compile_expression test;
          if Ain.version ctx.ain > 8
             && not (TypeAnalysis.is_bool_producing_expr test)
             && (match test.ty with Bool -> false | _ -> true)
             && (match test.node with
                 | ConstInt _ -> false
                 | Call (_, _, (HLLCall _ | SystemCall _)) -> false
                 | _ -> true) then (
            last_was_not <- false;
            self#write_instruction0 ITOB)
          else if Ain.version ctx.ain > 8 && last_was_not then (
            last_was_not <- false;
            self#write_instruction0 ITOB);
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_expression con;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifz_addr current_address;
          self#compile_expression alt;
          self#write_address_at jump_addr current_address
      | Cast (dst_t, e) -> (
          let src_t = e.ty in
          self#compile_expression e;
          match (src_t, dst_t) with
          | Int, Int -> ()
          | LongInt, LongInt -> ()
          | (Int | LongInt), Bool -> self#write_instruction0 ITOB
          | (Int | LongInt), Float -> self#write_instruction0 ITOF
          | (Bool | Int), LongInt -> self#write_instruction0 ITOLI
          | LongInt, Int -> ()
          | (Bool | Int | LongInt), String -> self#write_instruction0 I_STRING
          | Bool, (Bool | Int) -> ()
          | Float, Float -> ()
          | Float, Int -> self#write_instruction0 FTOI
          | Float, LongInt ->
              self#write_instruction0 FTOI;
              self#write_instruction0 ITOLI
          | Float, String ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 FTOS
          | String, String -> ()
          | String, Int -> self#write_instruction0 STOI
          | String, Delegate (Some (_, dg_i)) ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 SWAP;
              if Ain.version ctx.ain > 8 then (
                self#write_instruction1 DG_STR_TO_METHOD dg_i;
                self#write_instruction0 DG_NEW_FROM_METHOD)
              else (
                self#write_instruction1 PUSH dg_i;
                self#write_instruction0 DG_STR_TO_METHOD)
          | TyFunction _, TyMethod _ ->
              (* v11: FuncAddr already pushes PUSH -1 as the page, so
                 skip the extra PUSH -1 + SWAP for FuncAddr expressions *)
              if Ain.version ctx.ain > 8 && (match e.node with FuncAddr _ -> true | _ -> false) then ()
              else (
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 SWAP)
          | HLLParam, _ | _, HLLParam -> ()
              (* HLLParam is a wildcard - no cast needed at runtime *)
          | _ ->
              compiler_bug
                (Printf.sprintf "invalid cast from %s to %s"
                   (jaf_type_to_string src_t) (jaf_type_to_string dst_t))
                (Some (ASTExpression expr)))
      | Subscript (obj, index) -> (
          self#compile_lvalue obj;
          self#compile_expression index;
          match obj.ty with
          | String -> self#write_instruction0 C_REF
          | _ -> self#compile_dereference (jaf_to_ain_type expr.ty))
      | Member ({ node = This; _ }, _, ClassVariable member_no)
        when ctx.version < 630 && Ain.Type.is_scalar (self#member_type expr) ->
          self#write_instruction1 SH_STRUCTREF member_no
      | Member (e, _, ClassVariable member_no) ->
          self#compile_lvalue e;
          (match e.ty with
           | Wrap _ ->
               self#write_instruction0 REFREF;
               self#write_instruction0 REF
           | _ -> ());
          self#write_instruction1 PUSH member_no;
          self#compile_dereference (self#member_type expr)
      | Member (_, _, ClassConst _) ->
          compiler_bug "class constant not eliminated"
            (Some (ASTExpression expr))
      | Member (e, _, ClassMethod (name, no)) ->
          if String.is_suffix name ~suffix:"::get" then (
            (* Property getter - call it *)
            self#compile_lvalue e;
            self#compile_method_call [] no)
          else (
            self#compile_lvalue e;
            self#write_instruction1 PUSH no)
      | Member (_, _, HLLFunction (_, _)) ->
          compiler_bug "tried to compile HLL member expression"
            (Some (ASTExpression expr))
      | Member (_, _, SystemFunction _) ->
          compiler_bug "tried to compile system call member expression"
            (Some (ASTExpression expr))
      | Member (_, _, (BuiltinMethod _ | BuiltinHLL _)) ->
          compiler_bug "tried to compile built-in method member expression"
            (Some (ASTExpression expr))
      | Member (e, _, UnresolvedMember) ->
          (* Unresolved member - compile the object expression *)
          self#compile_expression e
      (* regular function call *)
      | Call (_, args, FunctionCall function_no) ->
          let f = Ain.get_function_by_index ctx.ain function_no in
          self#compile_function_arguments args f;
          self#write_instruction1 CALLFUNC function_no
      (* method call *)
      | Call ({ node = OptionalMember (e, _, _); _ }, args, MethodCall (_, method_no))
        when Ain.version ctx.ain > 8 ->
          (* v11 ?. null-safe method call. Two patterns depending on
             whether e is a DummyRef (function call result) or a simple
             member/variable (direct lvalue). *)
          let is_dummyref = match e.node with
            | DummyRef _ -> true | _ -> false in
          if is_dummyref then (
            (* Pattern 2: e is DummyRef (function call).
               compile_lvalue stores result in dummy via CHECKUDO.
               DUP the value for null check. Null branch cleans dummy. *)
            self#compile_lvalue e;
            self#write_instruction0 DUP;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE;
            let ifnz_addr = current_address + 2 in
            self#write_instruction1 IFNZ 0;
            self#compile_method_call args method_no;
            self#write_instruction1 PUSH 0;
            let jump_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#write_address_at ifnz_addr current_address;
            self#write_instruction0 POP;
            self#write_instruction1 PUSH (-1);
            (* Cleanup dummy before popping null flag *)
            (match e.node with
             | DummyRef (dummy_idx, _) ->
                 self#write_instruction1 SH_LOCALDELETE dummy_idx
             | _ -> ());
            self#write_instruction0 POP;
            self#write_address_at jump_addr current_address)
          else (
            (* Pattern 1: e is a simple lvalue (member, variable).
               DUP2 saves [page,idx] for second REF on non-null. *)
            self#compile_variable_ref e;
            self#write_instruction0 DUP2;
            self#write_instruction0 REF;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE;
            let ifnz_addr = current_address + 2 in
            self#write_instruction1 IFNZ 0;
            self#write_instruction0 REF;
            self#compile_method_call args method_no;
            self#write_instruction1 PUSH 0;
            let jump_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#write_address_at ifnz_addr current_address;
            self#write_instruction0 POP;
            self#write_instruction0 POP;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 POP;
            self#write_address_at jump_addr current_address)
      | Call ({ node = Member (e, _, _); _ }, args, MethodCall (_, method_no))
        ->
          (* v11: pre-emit Lambda JUMP+body before the receiver *)
          if Ain.version ctx.ain > 8 then (
            let rec find_lambda (e : expression) = match e.node with
              | Lambda f -> Some f | Cast (_, inner) -> find_lambda inner | _ -> None in
            List.iter args ~f:(fun arg ->
                match arg with
                | Some expr -> (match find_lambda expr with
                    | Some f ->
                        let lambda_idx = Option.value_exn f.index in
                        let jump_addr = current_address + 2 in
                        self#write_instruction1 JUMP 0;
                        self#compile_function f;
                        self#write_address_at jump_addr current_address;
                        Hashtbl.set pre_emitted_lambdas ~key:lambda_idx ~data:()
                    | None -> ())
                | _ -> ()));
          self#compile_lvalue e;
          (* Wrap receivers need REFREF+REF to unwrap before method call *)
          (match e.ty with
           | Wrap _ ->
               self#write_instruction0 REFREF;
               self#write_instruction0 REF
           | _ -> ());
          self#compile_method_call args method_no
      (* HLL function call *)
      | Call (_, args, HLLCall (lib_no, fun_no)) ->
          (* v11: pre-emit Lambda JUMP+body before arguments for HLL calls *)
          if Ain.version ctx.ain > 8 then (
            let rec find_lambda (e : expression) = match e.node with
              | Lambda f -> Some f | Cast (_, inner) -> find_lambda inner | _ -> None in
            List.iter args ~f:(fun arg ->
                match arg with
                | Some expr -> (match find_lambda expr with
                    | Some f ->
                        let lambda_idx = Option.value_exn f.index in
                        let jump_addr = current_address + 2 in
                        self#write_instruction1 JUMP 0;
                        self#compile_function f;
                        self#write_address_at jump_addr current_address;
                        Hashtbl.set pre_emitted_lambdas ~key:lambda_idx ~data:()
                    | None -> ())
                | _ -> ()));
          let f = Ain.function_of_hll_function_index ctx.ain lib_no fun_no in
          self#compile_function_arguments args f;
          if Ain.version ctx.ain > 8 then
            (* v11+: third arg is element type for Array library calls only *)
            let lib = Ain.get_library_by_index ctx.ain lib_no in
            let type_id =
              if String.equal lib.name "Array" then
                match args with
                | Some { ty = Array t | Ref (Array t); _ } :: _ ->
                    Ain.Type.int_of_data_type (Ain.version ctx.ain) (jaf_to_ain_type t)
                | _ -> -1
              else -1
            in
            self#write_instruction3 CALLHLL lib_no fun_no type_id;
            (* v11: if HLL returns ref (like Array.Last, Array.EmplaceBack),
               the result is 2 slots. When used in a value context (expr.ty
               is not Ref), we DON'T deref here - let the DummyRef handler
               in compile_lvalue handle it. But if there's NO DummyRef wrapper
               and the expression type is scalar, we need A_REF to deref. *)
            ()
          else self#write_instruction2 CALLHLL lib_no fun_no
      (* system call *)
      | Call (_, args, SystemCall sys) ->
          let f = Builtin.function_of_syscall sys in
          self#compile_function_arguments args f;
          if Ain.version ctx.ain > 8 then (
            (* v11+: system calls are via HLL "system" library *)
            let lib_no =
              Option.value_exn (Ain.get_library_index ctx.ain "system")
            in
            let syscall_name = Bytecode.string_of_syscall sys in
            let fun_no =
              Option.value_exn
                (Ain.get_library_function_index ctx.ain lib_no syscall_name)
            in
            self#write_instruction3 CALLHLL lib_no fun_no (-1))
          else self#write_instruction1 CALLSYS f.index
      (* built-in method call *)
      | Call ({ node = Member (e, _, _); _ }, args, BuiltinCall builtin) -> (
          let receiver_ty = ref Void in
          (* v11: pre-emit Lambda JUMP+body before receiver for builtin calls *)
          if Ain.version ctx.ain > 8 then (
            let rec find_lambda (e : expression) = match e.node with
              | Lambda f -> Some f | Cast (_, inner) -> find_lambda inner | _ -> None in
            List.iter args ~f:(fun arg ->
                match arg with
                | Some expr -> (match find_lambda expr with
                    | Some f ->
                        let lambda_idx = Option.value_exn f.index in
                        let jump_addr = current_address + 2 in
                        self#write_instruction1 JUMP 0;
                        self#compile_function f;
                        self#write_address_at jump_addr current_address;
                        Hashtbl.set pre_emitted_lambdas ~key:lambda_idx ~data:()
                    | None -> ())
                | _ -> ()));
          (match builtin with
          | (StringLength | StringLengthByte) when is_variable_ref e.node ->
              self#compile_variable_ref e
          | IntString | FloatString | StringInt | StringLength
          | StringLengthByte | StringEmpty | StringFind | StringGetPart ->
              self#compile_expression e
          | StringPushBack | StringPopBack | StringErase | DelegateNumof
          | DelegateExist | DelegateErase | DelegateClear ->
              receiver_ty := e.ty;
              self#compile_lvalue e
          | ArrayAlloc | ArrayFree ->
              receiver_ty := e.ty;
              self#compile_variable_ref e;
              if Ain.version ctx.ain > 8 then
                self#write_instruction0 REF
          | ArrayRealloc | ArrayNumof | ArrayCopy
          | ArrayFill | ArrayPushBack | ArrayPopBack | ArrayEmpty | ArrayErase
          | ArrayInsert | ArraySort | ArraySortBy | ArrayReverse | ArrayFind
          | ArrayAny ->
              receiver_ty := e.ty;
              self#compile_variable_ref e;
              if Ain.version ctx.ain > 8 then (
                self#write_instruction0 REF;
                self#write_instruction0 A_REF)
          | Assert ->
              compiler_bug "invalid assert expression"
                (Some (ASTExpression expr)));
          let f = Builtin.function_of_builtin ctx builtin !receiver_ty in
          self#compile_function_arguments args f;
          match builtin with
          | IntString -> self#write_instruction0 I_STRING
          | FloatString -> self#write_instruction0 FTOS
          | StringInt -> self#write_instruction0 STOI
          | StringLength ->
              self#write_instruction0
                (if is_variable_ref e.node then S_LENGTH else S_LENGTH2)
          | StringLengthByte ->
              self#write_instruction0
                (if is_variable_ref e.node then S_LENGTHBYTE else S_LENGTHBYTE2)
          | StringEmpty -> self#write_instruction0 S_EMPTY
          | StringFind -> self#write_instruction0 S_FIND
          | StringGetPart -> self#write_instruction0 S_GETPART
          | StringPushBack -> self#write_instruction0 S_PUSHBACK2
          | StringPopBack -> self#write_instruction0 S_POPBACK2
          | StringErase ->
              self#write_instruction1 PUSH 1;
              self#write_instruction0 S_ERASE2
          | ArrayAlloc when Ain.version ctx.ain > 8 ->
              (* Pad to 4 dimensions with -1 *)
              let n_dims = List.length args in
              for _ = 1 to 4 - n_dims do
                self#write_instruction1 PUSH (-1)
              done;
              self#compile_CALLHLL "Array" "Alloc"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayAlloc ->
              self#write_instruction1 PUSH (List.length args);
              self#write_instruction0 A_ALLOC
          | ArrayRealloc when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Realloc"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayRealloc ->
              self#write_instruction1 PUSH 1;
              self#write_instruction0 A_REALLOC
          | ArrayFree when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Free"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayFree -> self#write_instruction0 A_FREE
          | ArrayNumof when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Numof"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayNumof -> self#write_instruction0 A_NUMOF
          | ArrayCopy when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Copy"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayCopy -> self#write_instruction0 A_COPY
          | ArrayFill when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Fill"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayFill -> self#write_instruction0 A_FILL
          | ArrayPushBack when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "PushBack"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayPushBack -> self#write_instruction0 A_PUSHBACK
          | ArrayPopBack when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "PopBack"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayPopBack -> self#write_instruction0 A_POPBACK
          | ArrayEmpty when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Empty"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayEmpty -> self#write_instruction0 A_EMPTY
          | ArrayErase when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Erase"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayErase -> self#write_instruction0 A_ERASE
          | ArrayInsert when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Insert"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayInsert -> self#write_instruction0 A_INSERT
          | ArraySort when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Sort"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArraySort -> self#write_instruction0 A_SORT
          | ArraySortBy when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "SortMem"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArraySortBy -> self#write_instruction0 A_SORT_MEM
          | ArrayReverse when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Reverse"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayReverse -> self#write_instruction0 A_REVERSE
          | ArrayFind when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Find"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayFind -> self#write_instruction0 A_FIND
          | ArrayAny when Ain.version ctx.ain > 8 ->
              Stdio.eprintf "  ARRAYANY: func=%d\n"
                (match current_function with Some f -> f.index | None -> -1);
              self#compile_CALLHLL "Array" "Any"
                (self#array_element_type_code !receiver_ty)
                (ASTExpression expr)
          | ArrayAny -> self#write_instruction0 A_FIND (* fallback for pre-v11 *)
          | DelegateNumof -> self#write_instruction0 DG_NUMOF
          | DelegateExist -> self#write_instruction0 DG_EXIST
          | DelegateErase -> self#write_instruction0 DG_ERASE
          | DelegateClear -> self#write_instruction0 DG_CLEAR
          | Assert ->
              compiler_bug "invalid built-in method call"
                (Some (ASTExpression expr)));
      (* built-in function call *)
      | Call ({ node = Ident _; _ }, args, BuiltinCall builtin) -> (
          let f = Builtin.function_of_builtin ctx builtin Void in
          self#compile_function_arguments args f;
          match builtin with
          | Assert -> self#write_instruction0 ASSERT
          | _ ->
              compiler_bug "invalid built-in function call"
                (Some (ASTExpression expr)))
      (* functype call *)
      | Call (e, args, FuncTypeCall no) ->
          let compile_arg arg (var : Ain.Variable.t) =
            self#compile_argument arg var.value_type;
            if is_ref_scalar (ain_to_jaf_type ctx.ain var.value_type) then (
              self#write_instruction0 DUP2_X1;
              self#write_instruction0 POP;
              self#write_instruction0 POP)
            else self#write_instruction0 SWAP
          in
          let f = Ain.get_functype_by_index ctx.ain no in
          self#compile_expression e;
          List.iter2_exn args
            (Ain.FunctionType.logical_parameters f)
            ~f:compile_arg;
          self#write_instruction1 PUSH no;
          self#write_instruction0 CALLFUNC2
      | Call (e, args, DelegateCall no) ->
          let f = Ain.function_of_delegate_index ctx.ain no in
          self#compile_lvalue e;
          (* v11: captured delegate variables need REF to dereference *)
          if Ain.version ctx.ain > 8 then
            (match e.node with
            | Ident (_, CapturedVariable _) -> self#write_instruction0 REF
            | _ -> ());
          self#compile_function_arguments args f;
          self#write_instruction1 DG_CALLBEGIN no;
          let loop_addr = current_address in
          self#write_instruction2 DG_CALL no 0;
          self#write_instruction1 JUMP loop_addr;
          self#write_address_at (loop_addr + 6) current_address
      | Call (e, _args, UnresolvedCall) when Poly.(e.ty = HLLParam) ->
          (* HLLParam call - type unknown, compile callee and push 0 as placeholder *)
          self#compile_expression e;
          self#write_instruction1 PUSH 0
      | Call (_, _, _) ->
          compiler_bug "invalid call expression" (Some (ASTExpression expr))
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression expr))
      | RvalueRef _ ->
          compiler_bug "RvalueRef in rvalue context" (Some (ASTExpression expr))
      | DummyRef (var_no, inner) -> (
          match expr.ty with
          | Ref (Struct _) when Ain.version ctx.ain > 8 ->
              self#compile_lvalue expr;
              self#write_instruction0 A_REF
          | Ref (Struct (_, no)) ->
              self#compile_lvalue expr;
              self#write_instruction1 SR_REF2 no
          | (Struct _ | String | Array _) when Ain.version ctx.ain > 8 ->
              (* DummyRef with deref'd type but Ref(...) ain variable —
                 ref-returning call/subscript whose type was deref'd by
                 type analysis. compile_lvalue stores via CHECKUDO, A_REF
                 dereferences to get the value. *)
              (match (self#get_local var_no).value_type with
              | Ain.Type.Ref (Struct _ | String | Array _) ->
                  self#compile_lvalue expr;
                  self#write_instruction0 A_REF
              | _ -> self#compile_expression inner)
          | _ when Ain.version ctx.ain > 8
                   && (is_ref_scalar expr.ty || is_ref_scalar inner.ty
                       || (match (self#get_local var_no).value_type with
                           | Ain.Type.Ref (Int | Bool | Float | LongInt) -> true
                           | _ -> false)) ->
              (* v11 scalar ref DummyRef: compile_lvalue stores the 2-slot ref
                 via CHECKUDO+DUP_X2+R_ASSIGN, then REF dereferences to value.
                 Check expr.ty, inner.ty, AND the DummyRef variable's ain type
                 since type analysis may have deref'd all expression types. *)
              self#compile_lvalue expr;
              self#write_instruction0 REF
          | _ ->
              (* Non-ref DummyRef - compile inner directly *)
              self#compile_expression inner)
      | This -> (
          match expr.ty with
          | Struct _ when Ain.version ctx.ain > 8 ->
              self#write_instruction0 PUSHSTRUCTPAGE;
              self#write_instruction0 REF;
              self#write_instruction0 A_REF
          | Struct (_, no) ->
              self#write_instruction0 PUSHSTRUCTPAGE;
              self#write_instruction1 SR_REF2 no
          | _ ->
              compiler_bug "unexpected type of this" (Some (ASTExpression expr))
          )
      | Null -> (
          match expr.ty with
          | Ref _ | Struct _ | Array _ -> self#write_instruction1 PUSH (-1)
          | FuncType _ | IMainSystem | HLLParam -> self#write_instruction1 PUSH 0
          | Delegate _ -> self#write_instruction0 DG_NEW
          | String -> self#write_instruction1 S_PUSH 0
          | Int | Bool | Float | LongInt -> self#write_instruction1 PUSH 0
          | NullType -> self#write_instruction1 PUSH 0
          | ty ->
              compiler_bug
                ("unimplemented: NULL rvalue of type " ^ jaf_type_to_string ty)
                (Some (ASTExpression expr)))
      | Lambda f ->
          let lambda_idx = Option.value_exn f.index in
          let pre_emitted = Hashtbl.mem pre_emitted_lambdas lambda_idx in
          if not pre_emitted then (
            (* Normal lambda: emit JUMP + body + lambda ref *)
            let jump_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#compile_function f;
            self#write_address_at jump_addr current_address);
          (* Emit lambda reference (page + index) *)
          if Ain.version ctx.ain > 8 then
            (match current_function with
             | Some f when String.is_substring f.name ~substring:"@" ->
                 self#write_instruction0 PUSHSTRUCTPAGE
             | _ -> self#write_instruction1 PUSH (-1))
          else
            self#write_instruction0 PUSHSTRUCTPAGE;
          self#write_instruction1 PUSH lambda_idx;
          if pre_emitted then
            Hashtbl.remove pre_emitted_lambdas lambda_idx
      | NullCoalesce (a, b) ->
          let is_optional = match a.node with
            | Call ({ node = OptionalMember _; _ }, _, _) -> true
            | _ -> false
          in
          if Ain.version ctx.ain > 8 && not is_optional
             && (match a.ty with Ref _ -> true | _ -> false) then (
            (* v11 ref-backed ?? works on raw ref values, not eagerly
               dereferenced values. That preserves the original compiler's
               DummyRef materialization for cases like Array.Last() ?? "". *)
            self#compile_lvalue a;
            self#write_instruction0 DUP;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE;
            let ifz_addr = current_address + 2 in
            self#write_instruction1 IFZ 0;
            self#write_instruction0 POP;
            self#compile_lvalue b;
            self#write_address_at ifz_addr current_address;
            match expr.ty with
            | Int | Float | Bool | LongInt | FuncType _ | HLLParam ->
                self#write_instruction0 REF
            | String | Struct _ | Array _ | Delegate _ ->
                self#write_instruction0 A_REF
            | _ ->
                compiler_bug
                  ("unsupported v11 null-coalesce ref result type "
                  ^ jaf_type_to_string expr.ty)
                  (Some (ASTExpression expr)))
          else (
            (* Pre-v11 and value-only ?? use the direct stack pattern. *)
            let a_inner = match a.node with
              | DummyRef (_, inner) -> inner | _ -> a in
            self#compile_expression a_inner;
            if is_optional then (
              (* Two-slot: [value, flag]. Check flag, discard if not null *)
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifnz_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              (* Not null: flag consumed by EQUALE, value stays *)
              let jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifnz_addr current_address;
              (* Null: discard null value, use default *)
              self#write_instruction0 POP;
              self#compile_expression b;
              self#write_address_at jump_addr current_address)
            else (
              (* Unwrap DummyRef from b as well *)
              let b = match b.node with
                | DummyRef (_, inner) -> inner | _ -> b in
              (* One-slot: DUP + check *)
              self#write_instruction0 DUP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifz_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              self#compile_expression b;
              self#write_address_at ifz_addr current_address))
      | OptionalMember (obj, name, mt) ->
          (* ?. null-safe member access:
             compile obj; DUP; null check; if not null do access; else push default *)
          self#compile_expression obj;
          self#write_instruction0 DUP;
          self#write_instruction1 PUSH (-1);
          self#write_instruction0 EQUALE;
          let ifnz_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          (* Not null: do the member access on the object already on stack *)
          (match mt with
          | ClassMethod (mname, _) when String.is_suffix mname ~suffix:"::get" ->
              (* Property getter: call it *)
              let no = match mt with ClassMethod (_, n) -> n | _ -> 0 in
              self#compile_method_call [] no
          | ClassVariable var_no ->
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF
          | ClassMethod (_, no) ->
              self#write_instruction1 PUSH no
          | _ ->
              (* Fallback: just treat as regular member *)
              let member_expr = { expr with node = Member (obj, name, mt) } in
              self#compile_expression member_expr);
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifnz_addr current_address;
          (* Null branch: pop the null value and push default *)
          self#write_instruction0 POP;
          (match expr.ty with
          | Ref _ | Struct _ | Delegate _ -> self#write_instruction1 PUSH (-1)
          | String -> self#write_instruction1 S_PUSH 0
          | Float -> self#write_instruction1_float F_PUSH 0.0
          | _ -> self#write_instruction1 PUSH 0);
          self#write_address_at jump_addr current_address
      | OptionalCall ({ node = Member (obj, _, _); _ }, args, call_type) ->
          (* ?. null-safe method call:
             compile obj; DUP; null check (-1); if null push default; else do call *)
          self#compile_lvalue obj;
          self#write_instruction0 DUP;
          self#write_instruction1 PUSH (-1);
          self#write_instruction0 EQUALE;
          let ifnz_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          (* Not null: do the method call *)
          (match call_type with
          | MethodCall (_, method_no) ->
              self#compile_method_call args method_no
          | _ ->
              compiler_bug "OptionalCall with non-method call"
                (Some (ASTExpression expr)));
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifnz_addr current_address;
          (* Null branch: pop the null object and push default return value *)
          self#write_instruction0 POP;
          (match expr.ty with
          | Ref _ | Struct _ | Delegate _ ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1)
          | String -> self#write_instruction1 S_PUSH 0
          | Float -> self#write_instruction1_float F_PUSH 0.0
          | _ -> self#write_instruction1 PUSH 0);
          self#write_address_at jump_addr current_address
      | OptionalCall _ ->
          compiler_bug "OptionalCall without Member" (Some (ASTExpression expr))

    method compile_expr_and_pop ?(before_pop = fun () -> ()) (expr : expression) =
      match expr.node with
      | Assign (EqAssign, lhs, rhs)
        when Ain.version ctx.ain > 8
             && (match lhs.node with
                 | Member (_, name, ClassVariable _) ->
                     String.is_prefix name ~prefix:"<"
                     && String.is_suffix name ~suffix:">"
                 | _ -> false)
             && (match lhs.ty with String -> true | _ -> false)
             && (match rhs.ty with String -> true | _ -> false)
             && self#can_use_raw_string_assign_rhs rhs ->
          (* v11 statement-form string assign uses the rhs raw ref directly:
             `... REF; ... REF; S_ASSIGN; POP`. Emitting the fully
             dereferenced rhs (`A_REF`) and then `DELETE` over-releases the
             source string and does not match the original compiler. *)
          self#compile_lvalue lhs;
          self#compile_lvalue rhs;
          before_pop ();
          self#write_instruction0 S_ASSIGN;
          self#write_instruction0 POP
      | Assign (EqAssign, { node = Member (obj, mname, ClassMethod (name, _no)); _ }, rhs)
        when Ain.version ctx.ain > 8
             && (String.is_suffix name ~suffix:"::get"
                 || String.is_suffix name ~suffix:"::set") ->
          (* v11 property setter as statement: no DUP_X2, just call and POP void *)
          let setter_name =
            if String.is_suffix name ~suffix:"::get" then
              String.chop_suffix_exn name ~suffix:"::get" ^ "::set"
            else name
          in
          let setter_idx =
            match Ain.get_function ctx.ain setter_name with
            | Some f -> f.index
            | None ->
                (match Ain.get_function ctx.ain
                   (String.chop_suffix_exn setter_name ~suffix:("@" ^ mname ^ "::set")
                    ^ "@" ^ mname ^ "::set") with
                | Some f -> f.index
                | None -> _no)
          in
          self#compile_lvalue obj;
          (* v11: must emit DUP_X2 + POP even in statement context *)
          let f = Ain.get_function_by_index ctx.ain setter_idx in
          self#write_instruction1 PUSH setter_idx;
          self#compile_function_arguments [Some rhs] f;
          self#write_instruction0 DUP_X2;
          (match rhs.ty with
          | String | Ref _ | Struct _ | Array _ -> self#write_instruction0 A_REF
          | _ -> ());
          self#write_instruction1 CALLMETHOD (List.length [Some rhs]);
          before_pop ();
          (match rhs.ty with
          | String | Ref _ | Struct _ | Array _ -> self#write_instruction0 DELETE
          | _ -> self#write_instruction0 POP)
      | Assign (EqAssign, _, rhs) when Ain.version ctx.ain > 8
             && (match rhs.ty with
                 | Delegate _ | TyMethod _ -> true | _ -> false) ->
          (* v11 delegate/method EqAssign: DG_ASSIGN+DELETE already cleans up.
             PlusAssign/MinusAssign need compile_pop for DELETE. *)
          self#compile_expression expr;
          before_pop ()
      | Assign
          ( EqAssign,
            { node = Ident (_, LocalVariable (i, _)); _ },
            { node = ConstInt n; _ } )
        when ctx.version < 630
             && not (Ain.Type.is_ref (self#get_local i).value_type) ->
          self#write_instruction2 SH_LOCALASSIGN i n
      | Unary
          ( ((PreInc | PostInc | PreDec | PostDec) as op),
            { node = Ident (_, LocalVariable (i, _)); _ } )
        when ctx.version < 630
             && (not (Ain.Type.is_ref (self#get_local i).value_type))
             && Poly.(expr.ty <> LongInt) ->
          self#write_instruction1
            (match op with PreInc | PostInc -> SH_LOCALINC | _ -> SH_LOCALDEC)
            i
      | Unary (((ForeachInc | ForeachDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 (incdec_instruction (op, e.ty))
      | Unary (((PreInc | PreDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 (incdec_instruction (op, e.ty));
          self#write_instruction0 POP;
          self#write_instruction0 POP
      | Seq (a, b) ->
          self#compile_expr_and_pop ~before_pop a;
          self#compile_expr_and_pop ~before_pop b
      | DummyRef _ ->
          self#compile_lvalue expr;
          before_pop ();
          self#compile_pop expr.ty (ASTExpression expr)
      | _ ->
          self#compile_expression expr;
          before_pop ();
          (* v11: SR_ASSIGN result needs DELETE, not POP, even for Ref(Struct _) *)
          let pop_ty =
            if Ain.version ctx.ain > 8 then
              match (expr.node, expr.ty) with
              | Assign (EqAssign, _, _), Ref (Struct _) -> Jaf.Struct ("", 0)
              | _ -> expr.ty
            else expr.ty
          in
          self#compile_pop pop_ty (ASTExpression expr)

    (** Check if a variable index is in the current scope. *)
    method private is_var_in_scope idx =
      match Stack.top scopes with
      | Some scope ->
          List.exists scope.vars ~f:(fun (v : Ain.Variable.t) -> v.index = idx)
      | None -> false

    (** Emit the code for a statement. Statements are stack-neutral, i.e. the
        state of the stack is unchanged after executing a statement. *)
    method compile_statement (stmt : statement) =
      DebugInfo.add_loc debug_info current_address stmt.loc;
      (* delete locals that will be out-of-scope after this statement,
         but skip vars already cleaned up by cleanup_condition_dummyrefs *)
      List.iter (List.rev stmt.delete_vars) ~f:(fun i ->
          if self#is_var_in_scope i then
            self#compile_delete_var (self#get_local i));
      match stmt.node with
      | EmptyStatement -> ()
      | Declarations decls ->
          List.iter decls.vars ~f:self#compile_variable_declaration
      | Expression e ->
          let vars_before_expr =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          (* v11: DummyRef cleanup ordering depends on the expression result
             type.  For non-struct complex types (strings, delegates, arrays,
             HLLParam) whose compile_pop emits DELETE, the original compiler
             puts DELETE BEFORE SH_LOCALDELETE.  For all other types (POP or
             struct DELETE), SH_LOCALDELETE comes first. *)
          let cleanup_after_pop =
            Ain.version ctx.ain > 8
            && (match e.ty with
                | String | Delegate _ | HLLParam | Array _ -> true
                | _ -> false)
          in
          if cleanup_after_pop then (
            self#compile_expr_and_pop e;
            self#cleanup_condition_dummyrefs vars_before_expr)
          else
            self#compile_expr_and_pop
              ~before_pop:(fun () ->
                self#cleanup_condition_dummyrefs vars_before_expr)
              e
      | Compound stmts -> self#compile_block stmts
      | Label name -> self#add_label name stmt
      | If (test, con, alt) ->
          let vars_before =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          self#compile_expression test;
          self#cleanup_condition_dummyrefs vars_before;
          if Ain.version ctx.ain > 8
             && not (TypeAnalysis.is_bool_producing_expr test)
             && (match test.ty with Bool -> false | _ -> true)
             && (match test.node with
                 | ConstInt _ -> false
                 | Call (_, _, (HLLCall _ | SystemCall _)) -> false
                 | _ -> true) then (
            last_was_not <- false;
            self#write_instruction0 ITOB)
          else if Ain.version ctx.ain > 8 && last_was_not then (
            last_was_not <- false;
            self#write_instruction0 ITOB);
          self#write_instruction1 IFZ 0;
          let ifz_addr = current_address - 4 in
          self#compile_statement con;
          (match alt.node with
          | EmptyStatement ->
              (* No else block - no JUMP needed *)
              self#write_address_at ifz_addr current_address
          | _ ->
              let jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifz_addr current_address;
              self#compile_statement alt;
              self#write_address_at jump_addr current_address)
      | While (test, body) ->
          (* loop test *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          let vars_before_w =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          self#compile_expression test;
          self#cleanup_condition_dummyrefs vars_before_w;
          if Ain.version ctx.ain > 8
             && not (TypeAnalysis.is_bool_producing_expr test)
             && (match test.ty with Bool -> false | _ -> true)
             && (match test.node with
                 | ConstInt _ -> false
                 | Call (_, _, (HLLCall _ | SystemCall _)) -> false
                 | _ -> true) then (
            last_was_not <- false;
            self#write_instruction0 ITOB)
          else if Ain.version ctx.ain > 8 && last_was_not then (
            last_was_not <- false;
            self#write_instruction0 ITOB);
          let break_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          (* loop body *)
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          self#write_address_at break_addr current_address;
          self#end_loop
      | DoWhile (test, body) ->
          (* skip loop test *)
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          (* loop test *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          let vars_before_dw =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          self#compile_expression test;
          self#cleanup_condition_dummyrefs vars_before_dw;
          if Ain.version ctx.ain > 8
             && not (TypeAnalysis.is_v11_comparison_expr test)
             && (match test.node with
                 | ConstInt _ -> false
                 | Call (_, _, (HLLCall _ | SystemCall _)) -> false
                 | _ -> true) then (
            last_was_not <- false;
            self#write_instruction0 ITOB)
          else if Ain.version ctx.ain > 8 && last_was_not then (
            last_was_not <- false;
            self#write_instruction0 ITOB);
          let break_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          (* loop body *)
          self#write_address_at jump_addr current_address;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          self#write_address_at break_addr current_address;
          self#end_loop
      | For (decl, None, None, body) ->
          (* loop init *)
          self#compile_block [ decl ];
          (* loop body *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          self#end_loop
      | For (decl, test, inc, body) ->
          (* loop init *)
          self#compile_block [ decl ];
          (* loop test *)
          let test_addr = current_address in
          let break_addr =
            Option.map test ~f:(fun e ->
                self#compile_expression e;
                let break_addr = current_address + 2 in
                self#write_instruction1 IFZ 0;
                break_addr)
          in
          let body_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          (* loop increment *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          (* self#set_continue_addr loop_addr; *)
          Option.iter inc ~f:self#compile_expr_and_pop;
          self#write_instruction1 JUMP test_addr;
          (* Emit duplicate JUMP to match original compiler's for-loop pattern.
             This is dead code but the original always emits it. *)
          self#write_instruction1 JUMP test_addr;
          (* loop body *)
          self#write_address_at body_addr current_address;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          Option.iter break_addr ~f:(fun break_addr ->
              self#write_address_at break_addr current_address);
          self#end_loop
      | ForEach _ ->
          (* foreach should be desugared before codegen *)
          failwith "foreach should have been desugared"
      | Goto name ->
          self#add_goto name (current_address + 2) stmt;
          self#write_instruction1 JUMP 0
      | Continue ->
          self#emit_loop_exit_cleanup;
          self#write_instruction1 JUMP
            (self#get_continue_addr (ASTStatement stmt))
      | Break ->
          self#emit_loop_exit_cleanup;
          self#push_break_addr (current_address + 2) (ASTStatement stmt);
          self#write_instruction1 JUMP 0
      | Switch (expr, stmts) ->
          self#compile_expression expr;
          self#start_switch expr.ty (ASTExpression expr);
          self#push_break_addr (current_address + 2) (ASTStatement stmt);
          self#write_instruction1 JUMP 0;
          List.iter stmts ~f:self#compile_statement;
          self#end_switch
      | Case { node; _ } -> self#add_switch_case node (ASTStatement stmt)
      | Default -> self#set_switch_default (ASTStatement stmt)
      | Return None -> self#write_instruction0 RETURN
      | Return (Some e) ->
          (match ((Option.value_exn current_function).return_type, e.node) with
          | Ref _, Null -> self#compile_lvalue e
          | Ref (Int | Float | Bool | LongInt | FuncType _), _ ->
              self#compile_lvalue e;
              self#write_instruction0 DUP_U2;
              self#write_instruction0 SP_INC
          | Ref (String | Struct _ | Array _), _ ->
              self#compile_lvalue e;
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC
          | Ref _, _ ->
              compile_error "return statement not implemented for ref type"
                (ASTStatement stmt)
          | _ -> self#compile_expression e);
          (* v11: emit ITOB after a trailing NOT to match original compiler,
             which always normalizes bool return values from NOT. *)
          if Ain.version ctx.ain > 8 && last_was_not then (
            last_was_not <- false;
            self#write_instruction0 ITOB);
          self#write_instruction0 RETURN
      | Jump funcname ->
          let no = Ain.add_string ctx.ain funcname in
          self#write_instruction1 S_PUSH no;
          self#write_instruction0 CALLONJUMP;
          self#write_instruction0 SJUMP
      | Jumps e ->
          self#compile_expression e;
          self#write_instruction0 CALLONJUMP;
          self#write_instruction0 SJUMP
      | Message msg ->
          let msg_no = Ain.add_message ctx.ain msg in
          self#write_instruction1 MSG msg_no
      | RefAssign (lhs, rhs) ->
          self#compile_lock_peek;
          self#compile_variable_ref lhs;
          (match lhs.ty with
          | Wrap _ -> (
              (* Wrap ref-assign: no delete_ref needed.
                 For Subscript rhs, use compile_variable_ref to avoid
                 extra element dereference from compile_lvalue_after. *)
              (match rhs.node with
               | Subscript _ -> self#compile_variable_ref rhs
               | _ -> self#compile_lvalue rhs);
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 POP)
          | _ when is_ref_scalar lhs.ty -> (
              self#compile_delete_ref lhs.ty;
              (* v11 skips the pre-lvalue DUP2: it uses DUP_U2 after the
                 rhs is pushed instead. *)
              (if Ain.version ctx.ain <= 8 then
                 match rhs.node with Null -> () | _ -> self#write_instruction0 DUP2);
              self#compile_lvalue rhs;
              if Ain.version ctx.ain > 8 then (
                (* v11 scalar ref: DUP_U2; SP_INC; R_ASSIGN; POP; POP *)
                (match rhs.node with
                | Null -> ()
                | _ ->
                    self#write_instruction0 DUP_U2;
                    self#write_instruction0 SP_INC);
                self#write_instruction0 R_ASSIGN;
                self#write_instruction0 POP;
                self#write_instruction0 POP)
              else (
                self#write_instruction0 R_ASSIGN;
                self#write_instruction0 POP;
                match rhs.node with
                | Null -> self#write_instruction0 POP
                | _ ->
                    self#write_instruction0 POP;
                    self#write_instruction0 REF;
                    self#write_instruction0 SP_INC))
          | Ref (String | Struct _ | Array _ | HLLParam) -> (
              if Ain.version ctx.ain > 8 then (
                let vars_before =
                  match Stack.top scopes with
                  | Some scope -> List.length scope.vars
                  | None -> 0
                in
                self#compile_delete_ref lhs.ty;
                self#compile_lvalue rhs;
                (match rhs.node with
                | Null ->
                    self#write_instruction0 ASSIGN;
                    self#write_instruction0 POP
                | DummyRef (dummy_idx, { node = New _; _ }) ->
                    (* v11 `ref X = new T()`: original emits
                       ASSIGN; SP_INC; SH_LOCALDELETE dummy.
                       compile_lvalue for the DummyRef-wrapped New already
                       stored the new struct into the dummy slot, so the
                       stack is [..., page_lhs, idx_lhs, value]. ASSIGN
                       writes the value into the lhs ref slot, SP_INC
                       balances refcount, and SH_LOCALDELETE clears the
                       dummy. *)
                    self#write_instruction0 ASSIGN;
                    self#write_instruction0 SP_INC;
                    self#write_instruction1 SH_LOCALDELETE dummy_idx
                | _ ->
                    self#write_instruction0 DUP;
                    self#write_instruction0 SP_INC;
                    self#write_instruction0 ASSIGN;
                    self#write_instruction0 POP;
                    (* Clean up ALL DummyRef vars created during rhs
                       evaluation.  The original compiler deletes outermost
                       first (higher index), then intermediates.  scope.vars
                       has inner-most at head (added last by nested
                       compile_lvalue), so reverse to get outer-first order.
                       Handles chained calls like a.GetX().GetY() where
                       intermediate DummyRefs must also be freed. *)
                    (match Stack.top scopes with
                     | Some scope ->
                         let n_new = List.length scope.vars - vars_before in
                         if n_new > 0 then
                           List.iter (List.rev (List.take scope.vars n_new))
                             ~f:(fun v -> self#compile_delete_var v)
                     | None -> ())))
              else (
                self#compile_delete_ref lhs.ty;
                (match rhs.node with Null -> () | _ -> self#write_instruction0 DUP2);
                self#compile_lvalue rhs;
                self#write_instruction0 ASSIGN;
                match rhs.node with
                | Null -> self#write_instruction0 POP
                | _ ->
                    self#write_instruction0 DUP_X2;
                    self#write_instruction0 POP;
                    self#write_instruction0 REF;
                    self#write_instruction0 SP_INC;
                    self#write_instruction0 POP))
          | _ ->
              compiler_bug "Invalid LHS in reference assignment"
                (Some (ASTStatement stmt)));
          self#compile_unlock_peek
      | ObjSwap (a, b) ->
          self#compile_variable_ref a;
          self#compile_variable_ref b;
          let type_no =
            Ain.Type.int_of_data_type (Ain.version ctx.ain)
              (jaf_to_ain_type a.ty)
          in
          if Ain.version ctx.ain > 8 then
            (* v11: type is instruction arg only, NOT on stack *)
            self#write_instruction1 OBJSWAP type_no
          else (
            (* pre-v11: type is on stack *)
            self#write_instruction1 PUSH type_no;
            self#write_instruction0 OBJSWAP)

    (** Emit the code for a variable declaration. If the variable has an
        initval, the initval expression is computed and assigned to the
        variable. Otherwise a default value is assigned. *)
    method compile_variable_declaration (decl : variable) =
      if decl.is_const then ()
      else if decl.is_private && Option.is_none decl.initval then (
        (* Alloc-only: add to scope for cleanup, but emit no init code *)
        let v = self#get_local (Option.value_exn decl.index) in
        self#scope_add_var v)
      else
        let v = self#get_local (Option.value_exn decl.index) in
        self#scope_add_var v;
        match v.value_type with
        | Ref _ -> (
            match decl.initval with
            | Some e when Ain.version ctx.ain > 8
                       && decl.is_private
                       && (match e.node with DummyRef _ -> false | _ -> true)
                       && not (is_ref_scalar e.ty) ->
                (* v11 two-phase private ref init (used by desugared foreach
                   containers) initializes an empty slot. The original compiler
                   therefore uses rhs-first CHECKUDO+ASSIGN+SP_INC instead of
                   the normal delete-old-value path. *)
                let vars_before =
                  match Stack.top scopes with
                  | Some scope -> List.length scope.vars
                  | None -> 0
                in
                self#compile_lvalue e;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#write_instruction0 REF;
                self#write_instruction0 CHECKUDO;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction0 SWAP;
                self#write_instruction1 PUSH v.index;
                self#write_instruction0 SWAP;
                self#write_instruction0 ASSIGN;
                self#write_instruction0 SP_INC;
                self#cleanup_condition_dummyrefs vars_before
            | Some e when Ain.version ctx.ain > 8
                       && (match e.node with DummyRef _ -> false | _ -> true)
                       && not (is_ref_scalar e.ty) ->
                (* v11: non-DummyRef non-scalar ref variable init. The
                   original compiler emits dest-push + DUP2;REF;DELETE
                   (via compile_delete_ref) + rhs + ASSIGN + SP_INC. *)
                let vars_before =
                  match Stack.top scopes with
                  | Some scope -> List.length scope.vars
                  | None -> 0
                in
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#compile_delete_ref decl.type_spec.ty;
                (* Use compile_lvalue for the rhs so we push the raw ref
                   (page+idx -> value) without the extra A_REF that
                   compile_expression would add for struct/array types.
                   The outer ASSIGN expects the ref value, not the
                   dereferenced contents. *)
                self#compile_lvalue e;
                self#write_instruction0 ASSIGN;
                self#write_instruction0 SP_INC;
                self#cleanup_condition_dummyrefs vars_before
            | Some e when Ain.version ctx.ain > 8
                       && (match e.node with DummyRef _ -> false | _ -> true) ->
                (* v11: scalar ref init — use CHECKUDO + R_ASSIGN pattern. *)
                let vars_before =
                  match Stack.top scopes with
                  | Some scope -> List.length scope.vars
                  | None -> 0
                in
                self#compile_expression e;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#write_instruction0 REF;
                self#write_instruction0 CHECKUDO;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction0 SWAP;
                self#write_instruction1 PUSH v.index;
                self#write_instruction0 SWAP;
                self#write_instruction0 R_ASSIGN;
                self#write_instruction0 SP_INC;
                self#cleanup_condition_dummyrefs vars_before
            | Some ({ node = DummyRef (dummy_idx, _); _ } as e)
              when Ain.version ctx.ain > 8
                   && (match v.value_type with
                       | Ref (Struct _ | String | Array _ | HLLParam) -> true
                       | _ -> false)
                   && (match e.node with
                       | DummyRef (_, { node = New _; _ }) -> false
                       | _ -> true) ->
                (* v11 `ref X y = method()` decl: original emits
                   compile_delete_ref (DUP2;REF;DELETE) then compile the
                   method + emit_checkudo (inner ASSIGN into dummy) then
                   outer ASSIGN; SP_INC; SH_LOCALDELETE dummy. This is
                   distinct from the RefAssign reassign pattern
                   (DUP;SP_INC;ASSIGN;POP) because a freshly-declared
                   local's slot is empty — no refcount bump on the old
                   value is needed. *)
                self#compile_lock_peek;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#compile_delete_ref decl.type_spec.ty;
                self#compile_lvalue e;
                self#write_instruction0 ASSIGN;
                self#write_instruction0 SP_INC;
                self#write_instruction1 SH_LOCALDELETE dummy_idx
            | _ ->
                let lhs =
                  {
                    node = Ident (decl.name, LocalVariable (v.index, decl.location));
                    ty = decl.type_spec.ty;
                    loc = decl.location;
                  }
                and rhs =
                  match decl.initval with
                  | Some e -> e
                  | None -> make_expr ~ty:decl.type_spec.ty Null
                in
                self#compile_statement
                  {
                    node = RefAssign (lhs, rhs);
                    delete_vars = [];
                    loc = decl.location;
                  })
        | Int | Bool | LongInt | Float | FuncType _ | String ->
            (* Original v11 compiler emits default-init for int/bool/float
               locals even when they will be overwritten - keep parity. *)
            let lhs =
              {
                node = Ident (decl.name, LocalVariable (v.index, decl.location));
                ty = decl.type_spec.ty;
                loc = decl.location;
              }
            in
            let rhs =
              match decl.initval with
              | Some e -> e
              | None ->
                  let value =
                    match v.value_type with
                    | Int | Bool | LongInt -> ConstInt 0
                    | Float -> ConstFloat 0.0
                    | FuncType _ | String -> Null
                    | _ -> failwith "unreachable"
                  in
                  make_expr ~ty:decl.type_spec.ty value
            in
            let vars_before =
              match Stack.top scopes with
              | Some scope -> List.length scope.vars
              | None -> 0
            in
            if Ain.version ctx.ain > 8 then
              self#compile_expr_and_pop
                ~before_pop:(fun () ->
                  self#cleanup_condition_dummyrefs vars_before)
                {
                  node = Assign (EqAssign, lhs, rhs);
                  ty = rhs.ty;
                  loc = decl.location;
                }
            else (
              self#compile_expr_and_pop
                {
                  node = Assign (EqAssign, lhs, rhs);
                  ty = rhs.ty;
                  loc = decl.location;
                };
              self#cleanup_condition_dummyrefs vars_before)
        | Struct sno -> (
            (* FIXME: use verbose versions *)
            self#write_instruction1 SH_LOCALDELETE v.index;
            self#write_instruction2 SH_LOCALCREATE v.index sno;
            match decl.initval with
            | Some e ->
                self#compile_lvalue
                  {
                    node =
                      Ident (decl.name, LocalVariable (v.index, decl.location));
                    ty = decl.type_spec.ty;
                    loc = decl.location;
                  };
                self#compile_expression e;
                if not (Ain.version ctx.ain <= 1 || Ain.version ctx.ain > 8)
                then self#write_instruction1 PUSH sno;
                self#write_instruction0 SR_ASSIGN;
                self#compile_pop decl.type_spec.ty (ASTVariable decl)
            | None -> ())
        | Array _ ->
            let has_dims = List.length decl.array_dim > 0 in
            self#compile_local_ref v.index;
            if has_dims then (
              if Ain.version ctx.ain > 8 then (
                self#write_instruction0 REF;
                List.iter decl.array_dim ~f:self#compile_expression;
                (* Pad to 4 dimensions with -1 *)
                for _ = 1 to 4 - List.length decl.array_dim do
                  self#write_instruction1 PUSH (-1)
                done;
                self#compile_CALLHLL "Array" "Alloc"
                  (self#array_element_type_code decl.type_spec.ty)
                  (ASTVariable decl))
              else (
                List.iter decl.array_dim ~f:self#compile_expression;
                self#write_instruction1 PUSH (List.length decl.array_dim);
                self#write_instruction0 A_ALLOC))
            else if Ain.version ctx.ain > 8 then (
              self#write_instruction0 REF;
              self#compile_CALLHLL "Array" "Free"
                (self#array_element_type_code decl.type_spec.ty)
                (ASTVariable decl))
            else self#write_instruction0 A_FREE
        | Delegate _ -> (
            self#compile_local_ref v.index;
            self#write_instruction0 REF;
            match decl.initval with
            | Some ({ ty = String; _ } as e) ->
                self#compile_expression e;
                if Ain.version ctx.ain > 8 then
                  self#write_instruction0 DG_ASSIGN
                else self#write_instruction0 DG_SET
            | Some ({ ty = TyMethod _; _ } as e) ->
                self#compile_expression e;
                if Ain.version ctx.ain > 8 then
                  self#write_instruction0 DG_ASSIGN
                else self#write_instruction0 DG_SET
            | Some ({ ty = Delegate _; _ } as e) ->
                self#compile_expression e;
                self#write_instruction0 DG_ASSIGN;
                if Ain.version ctx.ain > 8 then self#write_instruction0 DELETE
                else self#write_instruction0 DG_POP
            | Some _ ->
                compiler_bug "invalid delegate initval"
                  (Some (ASTVariable decl))
            | None -> self#write_instruction0 DG_CLEAR)
        | Wrap _ -> () (* Wrap vars are initialized by RefAssign, not declaration *)
        | Void -> () (* void companion for wrap vars - no initialization needed *)
        | IMainSystem | HLLParam | Option _
        | Unknown87 _ | IFace _ | Enum2 _ | Enum _ | HLLFunc | HLLFunc2 | Unknown98
        | IFaceWrap _ | Function | Method | NullType ->
            compile_error "Unimplemented variable type" (ASTVariable decl)

    (** Emit the code for a block of statements. *)
    method compile_block (stmts : statement list) =
      self#start_scope;
      List.iter stmts ~f:self#compile_statement;
      self#end_scope

    (** Emit the code for a default return value. *)
    method compile_default_return (t : Ain.Type.t) decl =
      match t with
      | Ref (String | Struct _ | Array _) -> self#write_instruction1 PUSH (-1)
      | Ref (Int | Float | Bool | LongInt) ->
          self#write_instruction1 PUSH (-1);
          self#write_instruction1 PUSH 0
      | Void -> ()
      | Int | Bool | LongInt | FuncType _ -> self#write_instruction1 PUSH 0
      | Float -> self#write_instruction1 F_PUSH 0
      | String -> self#write_instruction1 S_PUSH 0
      | Struct _ | Array _ | Delegate _ -> self#write_instruction1 PUSH (-1)
      | _ -> compile_error "default return value not implemented for type" decl

    (** Emit the code for a function. *)
    method compile_function (decl : fundecl) =
      let index = Option.value_exn decl.index in
      let func =
        {
          (Ain.get_function_by_index ctx.ain index) with
          address = current_address + 6;
        }
      in
      let prev_function = current_function in
      current_function <- Some func;
      let prev_cflow_stmts = cflow_stmts in
      cflow_stmts <- Stack.create ();
      let prev_labels = labels in
      labels <- Hashtbl.create (module String);
      self#write_instruction1 FUNC index;
      self#compile_block (Option.value_exn decl.body);
      if not func.is_label then (
        self#compile_default_return func.return_type
          (ASTDeclaration (Function decl));
        self#write_instruction0 RETURN);
      (* ENDFUNC is not generated for the "NULL" function and methods except
         auto-generated array initializers (name "0" or "2"). *)
      (match decl with
      | { name = "NULL"; _ } -> ()
      | { class_name = None; _ }
      | { name = "0"; _ }
      | { name = "2"; _ }
      | { is_lambda = true; _ } ->
          self#write_instruction1 ENDFUNC index
      | _ -> ());
      self#resolve_gotos;
      (* TODO: optimize forwarding stubs (FUNC+setup+JUMP → FUNC+JUMP) *)
      Ain.write_function ctx.ain func;
      current_function <- prev_function;
      cflow_stmts <- prev_cflow_stmts;
      labels <- prev_labels

    (** Compile a list of declarations. *)
    method compile jaf_name (decls : declaration list) =
      start_address <- Ain.code_size ctx.ain;
      current_address <- start_address;
      let compile_decl = function
        | Jaf.Function f -> self#compile_function f
        | Global _ | GlobalGroup _ | FuncTypeDef _ | DelegateDef _ -> ()
        | StructDef d ->
            let compile_struct_decl (d : struct_declaration) =
              match d with
              | AccessSpecifier _ -> ()
              | MemberDecl _ -> () (* TODO: member initvals? *)
              | Constructor f | Destructor f | Method f ->
                  if Option.is_some f.body then self#compile_function f
            in
            List.iter d.decls ~f:compile_struct_decl
        | Enum e ->
            (* TODO: built-in enum methods *)
            compile_error "Enums not implemented" (ASTDeclaration (Enum e))
      in
      List.iter decls ~f:compile_decl;
      let jaf_name = String.tr ~target:'/' ~replacement:'\\' jaf_name in
      self#write_instruction1 EOF (Ain.add_file ctx.ain jaf_name);
      self#write_buffer
  end

let compile ctx jaf_name decls debug_info =
  (new jaf_compiler ctx debug_info)#compile jaf_name decls
