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
  (* v11: [Stack.length scopes] at loop/switch entry — used by
     [emit_loop_exit_cleanup] to know which scopes are inner to the
     loop and need their dummy slots released before a break /
     continue. *)
  scopes_at_start : int;
  (* v11: DummyRef slot indexes that [cleanup_condition_dummyrefs]
     released inline during this loop / switch body. The original
     compiler re-emits [SH_LOCALDELETE] for them at every break /
     continue path and at the switch fall-through merge point, even
     though the slots are already empty (the VM tolerates idempotent
     releases). The "cumulative SH_LOCALDELETE" block visible in
     switch fall-through code comes from this list. *)
  mutable inline_deleted_dummies : int list;
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

    (* Address of the start of the current buffer. *)
    val mutable start_address : int = 0

    (* Current address within the code section. *)
    val mutable current_address : int = 0

    (* The currently active control flow constructs. *)
    val mutable cflow_stmts = Stack.create ()

    (* v11: indexes of DummyRef slots that
       [cleanup_condition_dummyrefs] has already emitted
       [SH_LOCALDELETE] for inline (typically immediately after a
       loop / [if] condition's dummies become dead). Consulted by
       [compile_statement] so a goto / break / return's [delete_vars]
       list doesn't double-emit [SH_LOCALDELETE] for them. *)
    val mutable inline_deleted_dummies : int list = []

    (* v11: lambda body indexes whose JUMP-over-body has already been
       written by [pre_emit_lambda_args] before the enclosing call
       evaluates its arguments. The [Lambda] expression case consults
       this to skip the inline JUMP+body path — re-emitting would
       register the body at a shifted address and corrupt the
       function table. *)
    val pre_emitted_lambdas : (int, unit) Hashtbl.t =
      Hashtbl.create (module Int)

    (* v11 property-setter argument context. Set true while compiling
       arguments for a property setter call (the [DUP_X2 + CALLMETHOD
       + DELETE/POP] idiom). Suppresses [compile_argument]'s [A_REF]
       after the dummy ASSIGN for [Ref (Struct|Array)] args, since the
       setter idiom owns the page-ref via [DUP_X2] + the slot's
       [SH_LOCALDELETE] without an extra incref. *)
    val mutable in_prop_setter_arg : bool = false

    (* The currentl active scopes. *)
    val scopes = Stack.create ()

    (* Labels/gotos record for the current function. *)
    val mutable labels = Hashtbl.create (module String)

    (** Begin a scope. Variables created within a scope are deleted when the
        scope ends. *)
    method start_scope = Stack.push scopes { vars = [] }

    (** End a scope. Deletes variable created within the scope. *)
    method end_scope =
      let scope = Stack.pop_exn scopes in
      (* delete scope-local variables *)
      (* NOTE: Variables are deleted automatically by the VM upon function
               return. This code is emitted only to ensure that destructors are
               called at the correct time; hence function-scoped variables need
               not be deleted here. *)
      match Stack.top scopes with
      | None -> ()
      | Some _ -> List.iter scope.vars ~f:self#compile_delete_var

    (** Add a variable to the current scope. *)
    method scope_add_var v =
      match Stack.top scopes with
      | Some scope -> scope.vars <- v :: scope.vars
      | None -> compiler_bug "tried to add variable to null scope" None

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

    (** v11: emit [ITOB] before the [IFZ] that consumes a condition
        expression unless the expression is already known to produce a
        0/1 bool. Pre-v11 [IFZ] tolerates non-zero values; v11 [IFZ]
        leaves non-comparison expressions (e.g. a plain [int] or
        dereffed ref) at whatever numeric value they evaluated to,
        and the [Bool] type's runtime cast makes the branch unstable
        without normalisation. No-op on pre-v11. *)
    method maybe_emit_condition_itob (test : expression) =
      if
        Ain.version ctx.ain > 8
        && (not (TypeAnalysis.is_bool_producing_expr test))
        && (match test.ty with Bool -> false | _ -> true)
        &&
        match test.node with
        | ConstInt _ -> false
        | Call (_, _, (HLLCall _ | SystemCall _)) -> false
        | _ -> true
      then self#write_instruction0 ITOB

    (** v11: ain-level return type of a [Call] node, or [None] for
        anything else. Used to detect ref-returning calls so the
        surrounding assignment / argument-pass site can insert an
        [A_REF] before the dummy slot's [SH_LOCALDELETE] frees the
        only owner. *)
    method ain_call_return_type (expr : expression) =
      match expr.node with
      | Call (_, _, (FunctionCall fno | MethodCall (_, fno))) ->
          Some (Ain.get_function_by_index ctx.ain fno).return_type
      | Call (_, _, HLLCall (lib_no, fun_no)) ->
          let lib = Ain.get_library_by_index ctx.ain lib_no in
          Some (List.nth_exn lib.functions fun_no).return_type
      | _ -> None

    (** v11: release every DummyRef slot allocated since [vars_before]
        in the topmost scope, in LIFO (newest-first) order. Records
        each released index in [inline_deleted_dummies] (so a goto /
        return doesn't double-release them) and on the enclosing
        loop / switch's tracker (so break / continue / fall-through
        replay [SH_LOCALDELETE] for them). The VM's [SH_LOCALDELETE]
        is idempotent on already-empty slots, which matches alice's
        observed behaviour of redundantly re-emitting at every exit
        path. *)
    method cleanup_condition_dummyrefs vars_before =
      if Ain.version ctx.ain > 8 then
        match Stack.top scopes with
        | None -> ()
        | Some scope ->
            let n_new = List.length scope.vars - vars_before in
            if n_new > 0 then (
              let new_vars = List.take scope.vars n_new in
              List.iter new_vars ~f:self#compile_delete_var;
              List.iter new_vars ~f:(fun v ->
                  inline_deleted_dummies <-
                    v.index :: inline_deleted_dummies);
              match Stack.top cflow_stmts with
              | None -> ()
              | Some s ->
                  List.iter new_vars ~f:(fun v ->
                      s.inline_deleted_dummies <-
                        v.index :: s.inline_deleted_dummies))

    (** v11: replay [SH_LOCALDELETE] for every dummy slot that
        [cleanup_condition_dummyrefs] has released in the current
        loop / switch body. Called immediately before a break /
        continue's [JUMP] so the cumulative cleanup matches alice's
        bytecode shape. *)
    method emit_loop_exit_cleanup =
      if Ain.version ctx.ain > 8 then
        match Stack.top cflow_stmts with
        | None -> ()
        | Some s ->
            List.iter s.inline_deleted_dummies ~f:(fun idx ->
                self#write_instruction1 SH_LOCALDELETE idx)

    (** Begin a loop. *)
    method start_loop addr =
      Stack.push cflow_stmts
        {
          kind = CFlowLoop addr;
          break_addrs = [];
          scopes_at_start = Stack.length scopes;
          inline_deleted_dummies = [];
        }

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
        {
          kind = CFlowSwitch switch;
          break_addrs = [];
          scopes_at_start = Stack.length scopes;
          inline_deleted_dummies = [];
        };
      self#write_instruction1 op switch.index

    (** End the current control flow construct. Updates 'break' addresses.
        v11 [inline_deleted_dummies] is intentionally NOT propagated to
        the enclosing loop / switch — alice's outer break does not
        replay [SH_LOCALDELETE] for slots already released inside a
        nested switch. *)
    method end_cflow_stmt =
      let stmt = Stack.pop_exn cflow_stmts in
      let _ = stmt.inline_deleted_dummies in
      List.iter stmt.break_addrs ~f:(fun addr ->
          self#write_address_at addr current_address)

    (** End the current loop. Updates 'break' addresses. *)
    method end_loop =
      (match Stack.top cflow_stmts with
      | Some { kind = CFlowLoop _; _ } -> ()
      | _ -> compiler_bug "Mismatched start/end of control flow construct" None);
      self#end_cflow_stmt

    (** End the current switch statement. Updates 'break' addresses.
        v11 fall-through path cleanup: alice emits a cumulative
        [SH_LOCALDELETE] block for every DummyRef slot released
        inside any switch case, immediately before the post-switch
        code. Each [break] already runs [emit_loop_exit_cleanup] and
        targets the address AFTER this fall-through block, so the
        block is only reached when no case matched (or the matched
        case fell through without a break). The redundant releases
        are harmless because [SH_LOCALDELETE] is idempotent. *)
    method end_switch =
      (match Stack.top cflow_stmts with
      | Some { kind = CFlowSwitch switch; _ } -> Ain.write_switch ctx.ain switch
      | _ -> compiler_bug "Mismatched start/end of control flow construct" None);
      (if Ain.version ctx.ain > 8 then
         match Stack.top cflow_stmts with
         | None -> ()
         | Some s ->
             List.iter s.inline_deleted_dummies ~f:(fun idx ->
                 self#write_instruction1 SH_LOCALDELETE idx));
      self#end_cflow_stmt

    method add_switch_case expr node =
      let (switch : Ain.Switch.t) = self#current_switch node in
      let value =
        match expr with
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

    (** Element-type code for the [Array] HLL's polymorphic-type
        operand. Used as the third operand of [CALLHLL Array.*] in
        v11; [-1] when the receiver isn't actually an array. *)
    method array_element_type_code (ty : Jaf.jaf_type) =
      match ty with
      | Array t | Ref (Array t) ->
          Ain.Type.int_of_data_type (Ain.version ctx.ain) (jaf_to_ain_type t)
      | _ -> -1

    method write_instruction0 op =
      CBuffer.write_int16 buffer (int_of_opcode op);
      current_address <- current_address + 2

    method write_instruction1 op arg0 =
      match (Ain.version_lt ctx.ain (11, 0), op) with
      | true, S_MOD ->
          self#write_instruction1 PUSH arg0;
          self#write_instruction0 S_MOD
      | _ ->
          CBuffer.write_int16 buffer (int_of_opcode op);
          CBuffer.write_int32 buffer arg0;
          current_address <- current_address + 6

    method write_instruction1_float op arg0 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_float buffer arg0;
      current_address <- current_address + 6

    method write_instruction2 op arg0 arg1 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_int32 buffer arg0;
      CBuffer.write_int32 buffer arg1;
      current_address <- current_address + 10

    method write_instruction3 op arg0 arg1 arg2 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_int32 buffer arg0;
      CBuffer.write_int32 buffer arg1;
      CBuffer.write_int32 buffer arg2;
      current_address <- current_address + 14

    method write_address_at dst addr =
      CBuffer.write_int32_at buffer (dst - start_address) addr

    method write_buffer =
      if current_address > start_address then (
        Ain.append_bytecode ctx.ain buffer;
        CBuffer.clear buffer;
        start_address <- current_address)

    method get_local i =
      match current_function with
      | Some f -> List.nth_exn f.vars i
      | None -> compiler_bug "get_local outside of function" None

    method member_type (expr : expression) =
      match expr.node with
      | Member
          ( { ty =
                Struct (_, struct_no)
                | Ref (Struct (_, struct_no))
                | Wrap (Struct (_, struct_no))
                | Wrap (Ref (Struct (_, struct_no)));
              _;
            },
            _,
            ClassVariable member_no ) ->
          let struct_type = Ain.get_struct_by_index ctx.ain struct_no in
          (List.nth_exn struct_type.members member_no).value_type
      | Member ({ ty = HLLParam | Ref HLLParam; _ }, _, _) ->
          (* v11 [hll_param] member access: concrete struct type is
             unknown at compile time (resolved by the HLL bridge at
             runtime). Return [Int] as a placeholder. *)
          Ain.Type.Int
      | Member (_, _, UnresolvedMember) ->
          (* typeAnalysis left this member unresolved (typically a
             wildcard receiver). Fall through like above. *)
          Ain.Type.Int
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
      | Array _ ->
          self#compile_local_ref v.index;
          self#write_instruction0 A_FREE
      | _ -> ()

    (** Emit the code to put the value of a variable onto the stack (including
        member variables and array elements). Assumes a page + page-index is
        already on the stack. *)
    method compile_dereference (t : Ain.Type.t) =
      match t with
      | Wrap inner ->
          (* v11 fat-ref: [REFREF] then [REF] appropriate for the inner
             type. Strings need the extra [A_REF] the v11 VM requires
             for string dereference. *)
          self#write_instruction0 REFREF;
          self#write_instruction0 REF;
          (match inner with
          | String when Ain.version ctx.ain > 8 ->
              self#write_instruction0 A_REF
          | _ -> ())
      | Ref (Int | Float | Bool | LongInt | FuncType _) ->
          self#write_instruction0 REFREF;
          self#write_instruction0 REF
      | Int | Float | Bool | LongInt | FuncType _ -> self#write_instruction0 REF
      | String | Ref String ->
          (* v11 uses [REF; A_REF] instead of [S_REF] for string
             dereference — [S_REF] doesn't incref/copy in v11 and the
             VM panics when the returned string is freed. *)
          if Ain.version ctx.ain > 8 then (
            self#write_instruction0 REF;
            self#write_instruction0 A_REF)
          else self#write_instruction0 S_REF
      | Array _ | Ref (Array _) ->
          self#write_instruction0 REF;
          self#write_instruction0 A_REF
      | (Struct _ | Ref (Struct _)) when Ain.version ctx.ain > 8 ->
          (* v11 struct dereference is [REF; A_REF], not [SR_REF no].
             [SR_REF] doesn't incref the destination in v11 and the VM
             panics when the caller frees the returned struct. *)
          self#write_instruction0 REF;
          self#write_instruction0 A_REF
      | Struct no | Ref (Struct no) -> self#write_instruction1 SR_REF no
      | Delegate _ | Ref (Delegate _) ->
          (* v11: delegate deref is [REF; A_REF] (same pattern as
             struct / array). [DG_COPY] is pre-v11 only; in v11 it
             doesn't incref the returned delegate and the VM panics
             when the caller frees it. *)
          if Ain.version ctx.ain > 8 then (
            self#write_instruction0 REF;
            self#write_instruction0 A_REF)
          else (
            self#write_instruction0 REF;
            self#write_instruction0 DG_COPY)
      | (HLLParam | Ref HLLParam) when Ain.version ctx.ain > 8 ->
          (* v11 [hll_param] is the polymorphic wildcard; a single
             [REF] returns the underlying value without an A_REF
             incref (the callee doesn't take ownership). *)
          self#write_instruction0 REF
      | Void | IMainSystem | HLLFunc2 | HLLParam | Ref _ | Option _
      | Unknown87 _ | IFace _ | Enum2 _ | Enum _ | HLLFunc | Unknown98
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
          (* v11 lambda capture: walk [level] frames up via [X_GETENV]
             from the current local page, then push the outer frame's
             variable index. *)
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
          (* v11 lambda capture lvalue: walk [level] frames up via
             [X_GETENV], push the outer-frame variable index, then
             dereference using the lambda-side type — the captured
             value is read like any local but lives in an outer
             frame's local page. *)
          self#write_instruction0 PUSHLOCALPAGE;
          for _ = 1 to level do
            self#write_instruction0 X_GETENV
          done;
          self#write_instruction1 PUSH i;
          compile_lvalue_after (jaf_to_ain_type e.ty)
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
              (* v11 foreach loop var typed [Wrap (Struct _)] needs the
                 Wrap fat-ref unwrapped to the struct page-ref before
                 the member offset is pushed. *)
              (match obj.ty with
              | Wrap _ when Ain.version ctx.ain > 8 ->
                  self#write_instruction0 REFREF;
                  self#write_instruction0 REF
              | _ -> ());
              self#write_instruction1 PUSH member_no;
              compile_lvalue_after (self#member_type e))
      | Subscript (obj, index) ->
          self#compile_lvalue obj;
          (* Same Wrap-receiver unwrap for subscript into [Wrap<array>]. *)
          (match obj.ty with
          | Wrap _ when Ain.version ctx.ain > 8 ->
              self#write_instruction0 REFREF;
              self#write_instruction0 REF
          | _ -> ());
          self#compile_expression index;
          compile_lvalue_after (jaf_to_ain_type e.ty)
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression e))
      | DummyRef (var_no, ref_expr) -> (
          self#scope_add_var (self#get_local var_no);
          let call_returns_ref =
            match self#ain_call_return_type ref_expr with
            | Some (Ain.Type.Ref _) -> true
            | _ -> false
          in
          let dummy_is_ref_scalar =
            is_ref_scalar
              (ain_to_jaf_type ctx.ain (self#get_local var_no).value_type)
          in
          match ref_expr with
          | { node = New { ty = Struct (_, s_no); _ }; _ }
            when Ain.version ctx.ain > 8 ->
              (* v11 NEW is a 2-operand opcode (struct-id + ctor-id).
                 Prepare the dummy slot, release any previous value via
                 [REF; CHECKUDO], then [PUSHLOCALPAGE; PUSH i; NEW s c;
                 ASSIGN] stores the freshly constructed object. The
                 pre-v11 form [PUSH s; NEW] would leave the operand
                 bytes unread by the v11 disassembler. *)
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#write_instruction0 CHECKUDO;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              let ctor =
                (Ain.get_struct_by_index ctx.ain s_no).constructor
              in
              self#write_instruction2 NEW s_no ctor;
              self#write_instruction0 ASSIGN
          | _
            when Ain.version ctx.ain > 8
                 && not
                      (is_ref_scalar ref_expr.ty
                      || (call_returns_ref && dummy_is_ref_scalar)) ->
              (* v11 rvalue-into-dummy (non-scalar): variableAlloc
                 wrapped a non-referenceable rvalue so it can serve as a
                 [ref T] argument. Evaluate the rvalue first, release
                 whatever the dummy currently holds via [REF; CHECKUDO],
                 then SWAP-dance an [ASSIGN] so the stored value is
                 left on the stack for the surrounding caller / null
                 check. Original SDK: [.LOCALREF dummy; CHECKUDO;
                 .LOCALASSIGN2 dummy]. *)
              let emit_checkudo_assign () =
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
              (match ref_expr.node with
              | Call
                  ( { node = OptionalMember (obj, _, _); _ },
                    args,
                    MethodCall (_, method_no) ) ->
                  (* Inline [obj?.Method()] handling for ref-returning
                     methods stored into a dummy: the CHECKUDO+ASSIGN
                     belongs INSIDE the not-null branch (after the
                     method call), and a second null-check on the
                     result converts a NULL method result to the
                     [(-1, -1)] fat-null pair. Trailing fat-null
                     normalization collapses [(page, -1)] to a single
                     [-1] for callers expecting a single page-ref. *)
                  self#compile_lvalue obj;
                  self#write_instruction0 DUP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let ifnz_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  self#compile_method_call args method_no;
                  emit_checkudo_assign ();
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
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1);
                  self#write_address_at jump_end_outer current_address;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let ifnz3_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  let jump_norm_end = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at ifnz3_addr current_address;
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_address_at jump_norm_end current_address
              | _ ->
                  self#compile_expression ref_expr;
                  emit_checkudo_assign ())
          | _ when Ain.version ctx.ain > 8 ->
              (* v11 ref-scalar (2 VM stack slots per ref value):
                 same pattern but with [DUP_X2; POP] in place of [SWAP]
                 to rotate through 2-slot values, and [R_ASSIGN]
                 instead of [ASSIGN]. *)
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
              (* Pre-v11 path: PUSH struct id, then 0-arg NEW which
                 reads the id off the stack. *)
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              (match ref_expr with
              | { node = New { ty = Struct (_, s_no); _ }; _ } ->
                  self#write_instruction1 PUSH s_no;
                  self#compile_lock_peek;
                  self#write_instruction0 NEW;
                  self#write_instruction0 ASSIGN;
                  self#compile_unlock_peek
              | _ ->
                  self#compile_expression ref_expr;
                  self#write_instruction0
                    (if is_ref_scalar ref_expr.ty then R_ASSIGN else ASSIGN)))
      | RvalueRef e ->
          (* TODO: Insert <dummy : 右辺値参照化用> variable *)
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
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_lvalue con;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifz_addr current_address;
          self#compile_lvalue alt;
          self#write_address_at jump_addr current_address
      (* Chained optional access [obj?.X.Y]: the outer [.Y] lvalue's
         receiver is the whole [obj?.X] chain. Compile the
         [OptionalMember] as an rvalue so the null-check AND the [.X]
         access happen — both are needed before [.Y] dereferences. *)
      | OptionalMember _ ->
          self#compile_expression e
      (* v11 HLL/method/func calls returning a [ref T] can be used as
         an lvalue (e.g. [ref X y = call();] or [arr.EmplaceBack() =
         value]). Compile the call and the returned reference sits on
         the stack as the lvalue. typeAnalysis has already accepted
         the call as a valid assignment target. *)
      | Call (_, _, (HLLCall _ | FunctionCall _ | MethodCall _ | BuiltinCall _))
        ->
          self#compile_expression e
      | Member (obj, _, ClassMethod (name, no))
        when String.is_suffix name ~suffix:"::get"
             || String.is_suffix name ~suffix:"::set" ->
          (* v11 property-method as lvalue (e.g. in a [RefAssign]
             target): push receiver then the method idx; the
             surrounding assignment path emits the [CALLMETHOD].
             Pre-v11 eagerly emits [CALLMETHOD] since its assignment
             flow doesn't defer. *)
          self#compile_lvalue obj;
          if Ain.version ctx.ain > 8 then self#write_instruction1 PUSH no
          else self#write_instruction1 CALLMETHOD no
      | _ ->
          compiler_bug
            ("invalid lvalue: " ^ expr_to_string e)
            (Some (ASTExpression e))

    (** Emit the code to pop a value off the stack. *)
    method compile_pop (t : jaf_type) parent =
      match t with
      | Void -> ()
      | Ref (String | Struct _ | Array _ | HLLParam)
        when Ain.version_gte ctx.ain (11, 0) ->
          (* v11 non-scalar refs occupy a single stack slot that holds
             a page-ref. [POP] would drop the slot without decrementing
             the refcount, leaking the page. [DELETE] releases the
             ref properly. *)
          self#write_instruction0 DELETE
      | Int | Float | Bool | LongInt | FuncType _ | Ref _ | TyFunction _
      | TyMethod _ ->
          self#write_instruction0 POP
      | String when Ain.version_gte ctx.ain (11, 0) ->
          self#write_instruction0 DELETE
      | String -> self#write_instruction0 S_POP
      | Delegate _ when Ain.version_gte ctx.ain (11, 0) ->
          self#write_instruction0 DELETE
      | Delegate _ -> self#write_instruction0 DG_POP
      | Struct _ when Ain.version_gte ctx.ain (11, 0) ->
          self#write_instruction0 DELETE
      | Struct _ -> self#write_instruction0 SR_POP
      | Array _ when Ain.version_gte ctx.ain (11, 0) ->
          self#write_instruction0 DELETE
      | HLLParam when Ain.version_gte ctx.ain (11, 0) ->
          self#write_instruction0 DELETE
      | IMainSystem | HLLParam | Array _ | Wrap _ | HLLFunc | HLLFunc2
      | NullType | Untyped | Unresolved _ | MemberPtr _ | TypeUnion _ ->
          compiler_bug
            ("compile_pop: unsupported value type " ^ jaf_type_to_string t)
            (Some parent)

    method compile_argument (expr : expression option) (t : Ain.Type.t) =
      match expr with
      | None -> compiler_bug "missing argument" None
      | Some expr -> (
          let rec dummy_ref_inner (arg_expr : expression) =
            match arg_expr.node with
            | DummyRef (_, inner) -> Some inner
            | Cast (_, inner) | RvalueRef inner -> dummy_ref_inner inner
            | _ -> None
          in
          let dummy_inner_returns_ref =
            match dummy_ref_inner expr with
            | Some inner -> (
                match self#ain_call_return_type inner with
                | Some (Ain.Type.Ref _) -> true
                | _ -> ( match inner.ty with Ref _ -> true | _ -> false))
            | None -> false
          in
          match t with
          | (Struct _ | Array _) when Ain.version ctx.ain > 8 ->
              (* v11 struct / array arg: the language-level [Ref] is
                 collapsed by typeAnalysis, but the call site still
                 needs the page-ref. Push the value and append [A_REF]
                 when the source is a [DummyRef]'d ref-returning call
                 so the dummy's [SH_LOCALDELETE] doesn't free the only
                 owner. *)
              self#compile_expression expr;
              if dummy_inner_returns_ref then self#write_instruction0 A_REF
          | Ref _ ->
              self#compile_lvalue expr;
              (* v11 [Wrap T] lvalue (foreach loop var, etc.): the
                 [compile_lvalue_after] tail for non-string Wrap leaves
                 page+slot of the wrap on the stack. A [ref T] callee
                 wants the underlying page-ref instead — unpack the
                 wrap with [REFREF; REF]. Without this, passing a
                 [foreach] loop var (typed [Wrap HLLParam]) to a
                 [ref Struct] parameter pushes one extra slot and the
                 callee pops one fewer arg than declared. *)
              (match expr.ty with
              | Wrap (String | Int | Float | Bool | LongInt) -> ()
              | Wrap _ when Ain.version ctx.ain > 8 ->
                  self#write_instruction0 REFREF;
                  self#write_instruction0 REF
              | _ -> ())
          | Method ->
              (* XXX: for delegate builtins *)
              self#compile_expression expr
          | Delegate _ -> (
              self#compile_expression expr;
              match expr.ty with
              | TyMethod _ -> self#write_instruction0 DG_NEW_FROM_METHOD
              | _ -> ())
          | Bool when Ain.version ctx.ain > 8 ->
              (* v11 distinguishes [Int] and [Bool] at the value-slot
                 level. The type checker accepts them as
                 interchangeable, but HLL (and other typed) calls with
                 a [bool] parameter need a normalised 0/1 value when
                 the source is an int-valued computation. The original
                 compiler skips [ITOB] when the arg is already
                 statically 0/1 — a bool-typed expression, a literal
                 [ConstInt 0|1], or a comparison / logical op whose
                 result is naturally 0/1 — and inserts it otherwise. *)
              self#compile_expression expr;
              let is_bool_shape (e : expression) =
                match (e.ty, e.node) with
                | Bool, _ -> true
                | _, ConstInt (0 | 1) -> true
                | ( _,
                    Binary
                      ( ( Equal | NEqual | LT | GT | LTE | GTE | LogOr
                        | LogAnd ),
                        _,
                        _ ) ) ->
                    true
                | _, Unary (LogNot, _) -> true
                | _ -> false
              in
              if not (is_bool_shape expr) then self#write_instruction0 ITOB
          | HLLParam when Ain.version ctx.ain > 8 -> (
              (* v11 [hll_param]: when the arg is a local whose ain
                 slot is a [Ref (Struct|Array|String)], push the raw
                 1-slot ref via [compile_lvalue] instead of the
                 [compile_expression] deref path. HLL callees expect
                 the bare page-ref; the extra dereference would leave
                 the dereffed value on the stack, corrupting the call
                 frame. When the arg is a [DummyRef]'d ref-returning
                 call, append [A_REF] so the dummy's eventual
                 [SH_LOCALDELETE] doesn't free the page before the
                 HLL bridge reads it. *)
              match expr.node with
              | _ when is_variable_ref expr.node -> (
                  match expr.ty with
                  | Ref (Struct _ | Array _ | String) ->
                      self#compile_lvalue expr
                  | _ -> self#compile_expression expr)
              | _ ->
                  self#compile_expression expr;
                  let inner_is_call =
                    match dummy_ref_inner expr with
                    | Some { node = Call _; _ } -> true
                    | _ -> false
                  in
                  if dummy_inner_returns_ref && inner_is_call then
                    self#write_instruction0 A_REF)
          | _ -> self#compile_expression expr)

    (** v11: write [JUMP-over-body; body] for every [Lambda] argument
        BEFORE any arg evaluation runs, recording each pre-emitted
        lambda's index in [pre_emitted_lambdas]. The [Lambda]
        expression case consults that set so its inline [JUMP+body]
        path doesn't run a second time. Pre-emitting places the
        lambda body outside the call's argument-eval range, which
        the original v11 compiler and the v11 VM expect — emitting
        the body inline puts it inside another function's byte range,
        shifting every downstream address. *)
    method pre_emit_lambda_args args =
      if Ain.version ctx.ain > 8 then
        let rec find_lambda (e : expression) =
          match e.node with
          | Lambda f -> Some f
          | Cast (_, inner) -> find_lambda inner
          | _ -> None
        in
        List.iter args ~f:(function
          | Some expr -> (
              match find_lambda expr with
              | Some f ->
                  let lambda_idx = Option.value_exn f.index in
                  if not (Hashtbl.mem pre_emitted_lambdas lambda_idx) then (
                    let jump_addr = current_address + 2 in
                    self#write_instruction1 JUMP 0;
                    self#compile_function f;
                    self#write_address_at jump_addr current_address;
                    Hashtbl.set pre_emitted_lambdas ~key:lambda_idx ~data:())
              | None -> ())
          | None -> ())

    method compile_function_arguments args (f : Ain.Function.t) =
      let compile_arg arg (var : Ain.Variable.t) =
        self#compile_argument arg var.value_type
      in
      List.iter2_exn args (Ain.Function.logical_parameters f) ~f:compile_arg

    (** Emit the code to call a method. The object upon which the method is to
        be called should already be on the stack before this code is executed.
    *)
    method compile_method_call args method_no =
      let f = Ain.get_function_by_index ctx.ain method_no in
      if Ain.version ctx.ain > 8 then (
        (* v11 [CALLMETHOD] takes the argument count as its operand;
           the method's function index is supplied via a preceding
           [PUSH], so the VM can dispatch virtually by popping it.
           [nr_args] from the ain function header accounts for the
           ref void-slot padding that [compile_function_arguments]
           would otherwise shift past. *)
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
          (* v11 captured-variable rvalue: PUSHLOCALPAGE + level *
             X_GETENV walks frames up to the enclosing scope, then
             read the var by index using the lambda-side type. *)
          self#write_instruction0 PUSHLOCALPAGE;
          for _ = 1 to level do
            self#write_instruction0 X_GETENV
          done;
          self#write_instruction1 PUSH i;
          self#compile_dereference (jaf_to_ain_type expr.ty)
      | FuncAddr (_, Some no) ->
          (* v11 method-refs are 2-slot values (object_page +
             func_index). Free functions use [-1] as the null
             object-page sentinel. Pre-v11 passes a single slot
             (func_index only). *)
          if Ain.version ctx.ain > 8 then self#write_instruction1 PUSH (-1);
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
          self#write_instruction0 NOT
      | Unary (BitNot, e) ->
          self#compile_expression e;
          self#write_instruction0 COMPL
      | Unary (((ForeachInc | ForeachDec) as op), e) ->
          (* Rvalue context: evaluate the counter-modify expression
             and leave the new value on the stack. [INC]/[DEC]
             increments in-place and consumes the [page, idx] pair,
             so reload the counter via [compile_lvalue; REF] for the
             updated value. A plain [REF] here would dereference stale
             stack contents (whatever was left after [INC] consumed
             the pair). *)
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
          (* v11 ref/wrap === / !== handling. See the operator case
             below for the EQUALE-vs-R_EQUALE selection — together they
             match alice.exe's emission. *)
          | RefEqual | RefNEqual ->
              self#compile_lvalue a;
              let lhs_is_call_or_dummy =
                match a.node with
                | Call _ | DummyRef _ -> true
                | _ -> false
              in
              (match a.ty with
              | Wrap (Struct _ | Array _ | HLLParam | Delegate _)
                when Ain.version ctx.ain > 8 ->
                  (* foreach loop var (typed [Wrap HLLParam] by the
                     desugarer) over an array of struct/array/delegate
                     refs: compile_lvalue_after's [Wrap _ -> ()] left
                     raw page+slot on the stack — unwrap to the
                     contained page-ref so EQUALE/NOTE compares
                     identity at the right granularity. *)
                  self#write_instruction0 REFREF;
                  self#write_instruction0 REF
              | Wrap (Int | Float | Bool | LongInt)
                when Ain.version ctx.ain > 8 && lhs_is_call_or_dummy ->
                  (* Wrap-of-scalar where the lhs is a ref-returning
                     call (often via DummyRef): deref to the scalar so
                     the rhs literal can be compared with EQUALE. *)
                  self#write_instruction0 REF
              | Ref t
                when is_numeric t && Ain.version ctx.ain > 8
                     && lhs_is_call_or_dummy ->
                  self#write_instruction0 REF
              | _ -> ());
              (match b.ty with
              | _ when (match b.node with This -> true | _ -> false) ->
                  self#compile_lvalue b
              | Ref _ -> self#compile_lvalue b
              | _ -> self#compile_expression b)
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
          | (Int | Bool), BitOr -> self#write_instruction0 OR
          | (Int | Bool), BitXor -> self#write_instruction0 XOR
          | (Int | Bool), BitAnd -> self#write_instruction0 AND
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
                | _ ->
                    compiler_bug "invalid type for string formatting"
                      (Some (ASTExpression expr))
              in
              self#write_instruction1 S_MOD (int_of_t (jaf_to_ain_type b.ty))
          | ( String,
              ( Minus | Times | Divide | BitOr | BitXor | BitAnd | LShift
              | RShift | LogOr | LogAnd ) ) ->
              compiler_bug "invalid string operator" (Some (ASTExpression expr))
          | (Ref t | Wrap t), RefEqual ->
              (* For [ref_var === NULL]/[ref_var === other_ref], both
                 sides are 2-slot fat-ref pairs and R_EQUALE compares
                 ref identity. For [call_returning_ref() === literal]
                 the case above dereffed the lhs to a scalar and we
                 want the scalar EQUALE. *)
              let lhs_is_call_or_dummy =
                match a.node with
                | Call _ | DummyRef _ -> true
                | _ -> false
              in
              if is_numeric t && not lhs_is_call_or_dummy then
                self#write_instruction0 R_EQUALE
              else self#write_instruction0 EQUALE
          | (Ref t | Wrap t), RefNEqual ->
              let lhs_is_call_or_dummy =
                match a.node with
                | Call _ | DummyRef _ -> true
                | _ -> false
              in
              if is_numeric t && not lhs_is_call_or_dummy then
                self#write_instruction0 R_NOTE
              else self#write_instruction0 NOTE
          | FuncType _, Equal -> self#write_instruction0 EQUALE
          | FuncType _, NEqual -> self#write_instruction0 NOTE
          | _ ->
              compiler_bug "invalid binary expression"
                (Some (ASTExpression expr)))
      | Assign (op, lhs, rhs) -> (
          self#compile_lvalue lhs;
          self#compile_expression rhs;
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
                  (* v11 [DG_STR_TO_METHOD] takes the delegate type as
                     a 1-int operand; the follow-up sequence wraps
                     into a delegate via [DG_NEW_FROM_METHOD] then
                     [DG_ASSIGN; DELETE]. Pre-v11 took no operand and
                     used [DG_SET]. *)
                  if Ain.version ctx.ain > 8 then (
                    self#write_instruction1 DG_STR_TO_METHOD dg_i;
                    self#write_instruction0 DG_NEW_FROM_METHOD;
                    self#write_instruction0 DG_ASSIGN;
                    self#write_instruction0 DELETE)
                  else (
                    self#write_instruction1 PUSH dg_i;
                    self#write_instruction0 DG_STR_TO_METHOD;
                    self#write_instruction0 DG_SET)
              | String ->
                  (* v11 [local_string = method_returning_ref_string()]:
                     the rhs's [DummyRef]'d ref-returning call leaves a
                     page-ref on the stack but the dummy's [ASSIGN]
                     stored it without an incref. Insert an [A_REF]
                     before [S_ASSIGN] so the dummy's eventual
                     [SH_LOCALDELETE] doesn't free the only owner. *)
                  (if Ain.version ctx.ain > 8 then
                     match rhs.node with
                     | DummyRef (_, ({ node = Call _; _ } as inner)) -> (
                         match self#ain_call_return_type inner with
                         | Some (Ain.Type.Ref _) ->
                             self#write_instruction0 A_REF
                         | _ -> ())
                     | _ -> ());
                  self#write_instruction0 S_ASSIGN
              | _ ->
                  compiler_bug "invalid string assignment"
                    (Some (ASTExpression expr)))
          | PlusAssign, String -> (
              match lhs.ty with
              | Delegate (Some (_, dg_i)) ->
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 SWAP;
                  if Ain.version ctx.ain > 8 then (
                    self#write_instruction1 DG_STR_TO_METHOD dg_i;
                    self#write_instruction0 DG_NEW_FROM_METHOD;
                    self#write_instruction0 DG_PLUSA;
                    self#write_instruction0 DELETE)
                  else (
                    self#write_instruction1 PUSH dg_i;
                    self#write_instruction0 DG_STR_TO_METHOD;
                    self#write_instruction0 DG_ADD)
              | String -> self#write_instruction0 S_PLUSA2
              | _ ->
                  compiler_bug "invalid string assignment"
                    (Some (ASTExpression expr)))
          | EqAssign, TyMethod _ ->
              if Ain.version ctx.ain > 8 then (
                (* v11 assigns full delegates via [DG_ASSIGN], not the
                   single-entry [DG_SET]. If the rhs is a raw method
                   pointer (Member / Lambda / FuncAddr, possibly cast),
                   wrap it in a one-entry delegate via
                   [DG_NEW_FROM_METHOD] first. A Cast from [String] has
                   already been wrapped by the Cast case above. *)
                (match rhs.node with
                | Member (_, _, ClassMethod _)
                | Cast (_, { node = Member (_, _, ClassMethod _); _ })
                | Lambda _ | FuncAddr _
                | Cast (_, { node = FuncAddr _; _ })
                | Cast (_, { node = Lambda _; _ }) ->
                    self#write_instruction0 DG_NEW_FROM_METHOD
                | _ -> ());
                self#write_instruction0 DG_ASSIGN;
                self#write_instruction0 DELETE)
              else self#write_instruction0 DG_SET
          | EqAssign, Delegate _ -> self#write_instruction0 DG_ASSIGN
          | PlusAssign, TyMethod _ ->
              if Ain.version ctx.ain > 8 then (
                (match rhs.node with
                | Member (_, _, ClassMethod _)
                | Cast (_, { node = Member (_, _, ClassMethod _); _ })
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
              (* Pre-v11 [SR_ASSIGN] reads the struct type id from a
                 prior [PUSH]; v11 dropped that operand. v11 also
                 wants an explicit [A_REF] before [SR_ASSIGN] when the
                 rhs is a [DummyRef]'d call result — the call leaves a
                 single page-ref on the stack, the dummy's [ASSIGN]
                 stores it without an incref, and without an [A_REF]
                 the dummy's [SH_LOCALDELETE] frees the only owner.
                 Applies to plain function calls, HLL/array calls,
                 property getters, and chained method calls. *)
              if Ain.version ctx.ain <= 8 then
                self#write_instruction1 PUSH sno
              else (
                ignore sno;
                match rhs.node with
                | DummyRef (_, { node = Call _; _ }) ->
                    self#write_instruction0 A_REF
                | _ -> ());
              self#write_instruction0 SR_ASSIGN
          (* v11 array copy-assign: [X_SET] deletes the lhs's old
             contents, assigns the rhs, and leaves the result on the
             stack for the enclosing [compile_expr_and_pop] to clean
             up. Also used for the [hll_param] wildcard. *)
          | EqAssign, (Array _ | Ref (Array _) | HLLParam)
            when Ain.version_gte ctx.ain (11, 0) ->
              (match rhs.node with
              | DummyRef (_, { node = Call _; _ }) ->
                  self#write_instruction0 A_REF
              | _ -> ());
              self#write_instruction0 X_SET
          | _, _ ->
              compiler_bug "invalid assignment" (Some (ASTExpression expr)))
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_expression b
      | Ternary (test, con, alt) ->
          self#compile_expression test;
          self#maybe_emit_condition_itob test;
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
                (* v11 [DG_STR_TO_METHOD] takes the delegate-type id as
                   a direct operand and produces a method-pointer; wrap
                   it via [DG_NEW_FROM_METHOD] so the surrounding assign
                   can use [DG_ASSIGN] / [DG_PLUSA] (the full-delegate
                   forms) instead of [DG_SET]. *)
                self#write_instruction1 DG_STR_TO_METHOD dg_i;
                self#write_instruction0 DG_NEW_FROM_METHOD)
              else (
                self#write_instruction1 PUSH dg_i;
                self#write_instruction0 DG_STR_TO_METHOD)
          | TyFunction _, TyMethod _ ->
              (* v11 [FuncAddr] already emits the 2-slot method-ref
                 form ([PUSH -1; PUSH no]) directly — skip the
                 page+swap dance that was needed pre-v11 (when
                 [FuncAddr] pushed a single slot). Cast from any other
                 expression shape still needs the explicit wrap. *)
              if
                Ain.version ctx.ain > 8
                && (match e.node with FuncAddr _ -> true | _ -> false)
              then ()
              else (
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 SWAP)
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
          (* v11 Wrap receiver: unwrap the fat-ref before indexing
             into the wrapped struct. Without this at rvalue sites
             [read x.wrap.m] reads the wrapper itself instead of the
             wrapped value. *)
          (match e.ty with
          | Wrap _ when Ain.version ctx.ain > 8 ->
              self#write_instruction0 REFREF;
              self#write_instruction0 REF
          | _ -> ());
          self#write_instruction1 PUSH member_no;
          self#compile_dereference (self#member_type expr)
      | Member (_, _, ClassConst _) ->
          compiler_bug "class constant not eliminated"
            (Some (ASTExpression expr))
      | Member (e, _, ClassMethod (_, no)) ->
          self#compile_lvalue e;
          self#write_instruction1 PUSH no
      | Member (_, _, HLLFunction (_, _)) ->
          compiler_bug "tried to compile HLL member expression"
            (Some (ASTExpression expr))
      | Member (_, _, SystemFunction _) ->
          compiler_bug "tried to compile system call member expression"
            (Some (ASTExpression expr))
      | Member (_, _, (BuiltinMethod _ | BuiltinHLL _)) ->
          compiler_bug "tried to compile built-in method member expression"
            (Some (ASTExpression expr))
      | Member (_, _, UnresolvedMember) ->
          compiler_bug "member expression has no member_type"
            (Some (ASTExpression expr))
      | Member (_, _, ClassProperty _) ->
          (* Type analysis rewrites reads/writes on property members
             into explicit get/set method calls before codegen runs. *)
          compiler_bug "property member expression not rewritten"
            (Some (ASTExpression expr))
      | Member (_, _, ClassEvent _) ->
          (* Type analysis rewrites [obj.E += h] / [-= h] for user-bodied
             events into explicit add/remove method calls before codegen
             runs. A bare [obj.E] read on a user-bodied event has no
             defined semantics. *)
          compiler_bug "event member expression not rewritten"
            (Some (ASTExpression expr))
      (* regular function call *)
      | Call (_, args, FunctionCall function_no) ->
          let f = Ain.get_function_by_index ctx.ain function_no in
          self#compile_function_arguments args f;
          self#write_instruction1 CALLFUNC function_no
      (* method call *)
      (* v11 optional method call: [obj?.Method(args)]. Two receiver
         shapes:
         - [DummyRef _] receiver (e.g. transient call result): push
           via [compile_lvalue], DUP, null-check; on null skip the
           call and push the type-appropriate fat-null sentinel.
         - variable receiver: [compile_variable_ref], [DUP2; REF],
           null-check; same fall-through but a 2-slot pop is needed
           for the page+index pair.
         Both branches push a [-1] / [-1; -1] pair on the null path so
         the surrounding stack discipline matches the call's return
         arity (Void → 1 slot, non-Void → 2 slots). *)
      | Call
          ( { node = OptionalMember (e, _, _); _ },
            args,
            MethodCall (_, method_no) )
        when Ain.version ctx.ain > 8 ->
          let method_return_type =
            (Ain.get_function_by_index ctx.ain method_no).return_type
          in
          let push_null_sentinel () =
            match method_return_type with
            | Ain.Type.Void -> self#write_instruction1 PUSH (-1)
            | _ ->
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH (-1)
          in
          let is_dummyref =
            match e.node with DummyRef _ -> true | _ -> false
          in
          if is_dummyref then (
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
            push_null_sentinel ();
            self#write_address_at jump_addr current_address)
          else (
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
            push_null_sentinel ();
            self#write_address_at jump_addr current_address)
      | Call
          ( { node = Member (e, mname, _); _ },
            args,
            MethodCall (_, method_no) ) ->
          self#pre_emit_lambda_args args;
          self#compile_lvalue e;
          (* v11 Wrap receiver: unwrap the fat-ref before CALLMETHOD
             so the method dispatches on the wrapped struct, not the
             wrapper slot. *)
          (match e.ty with
          | Wrap _ when Ain.version ctx.ain > 8 ->
              self#write_instruction0 REFREF;
              self#write_instruction0 REF
          | _ -> ());
          (* v11 property-setter idiom: every [this.X = value] /
             [obj.X = value] property write expands to a
             [Name::set(value)] call that the original compiler emits
             with the assignment-expression-value bookkeeping pair —
             [DUP_X2] before [CALLMETHOD] shuffles the rhs under the
             receiver/method, and a trailing [DELETE]/[POP] discards
             it. The duplicated value is immediately discarded but the
             VM relies on the pattern (likely for refcount /
             assignment-tracking). *)
          let is_prop_setter =
            Ain.version ctx.ain > 8
            && String.is_suffix mname ~suffix:"::set"
            && List.length args = 1
            &&
            let f = Ain.get_function_by_index ctx.ain method_no in
            Poly.equal f.return_type Ain.Type.Void
          in
          if is_prop_setter then (
            let f = Ain.get_function_by_index ctx.ain method_no in
            self#write_instruction1 PUSH method_no;
            let prev = in_prop_setter_arg in
            Exn.protect
              ~f:(fun () ->
                in_prop_setter_arg <- true;
                self#compile_function_arguments args f)
              ~finally:(fun () -> in_prop_setter_arg <- prev);
            self#write_instruction0 DUP_X2;
            (* String setters need an extra [A_REF] before [CALLMETHOD]
               so the trailing [DELETE] correctly releases the
               duplicated page-ref left on the stack. Other types
               (Bool/Int/Float/Struct) don't need this — scalars
               carry no refcount and Struct comes through a DummyRef
               whose [SH_LOCALDELETE] handles cleanup. *)
            let is_string_setter =
              match List.hd (Ain.Function.logical_parameters f) with
              | Some { value_type = String; _ } -> true
              | _ -> false
            in
            if is_string_setter then self#write_instruction0 A_REF;
            self#write_instruction1 CALLMETHOD f.nr_args;
            if is_string_setter then self#write_instruction0 DELETE
            else self#write_instruction0 POP)
          else self#compile_method_call args method_no
      (* v11 optional HLL/method call: [array?.Duplicate(x)] etc. lower
         to [CALLHLL] rather than [CALLMETHOD], so the OptionalMember
         method-call arm above doesn't catch them. *)
      | Call
          ( { node = OptionalMember (e, _, _); _ },
            args,
            HLLCall (lib_no, fun_no) )
        when Ain.version ctx.ain > 8 -> (
          self#pre_emit_lambda_args args;
          let f = Ain.function_of_hll_function_index ctx.ain lib_no fun_no in
          match args with
          | [] ->
              compiler_bug "optional HLL call without receiver argument"
                (Some (ASTExpression expr))
          | _receiver :: rest_args ->
              let params = Ain.Function.logical_parameters f in
              let rest_params =
                match params with _ :: tl -> tl | [] -> []
              in
              self#compile_variable_ref e;
              self#write_instruction0 DUP2;
              self#write_instruction0 REF;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifnz_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#write_instruction0 REF;
              List.iter2_exn rest_args rest_params ~f:(fun arg var ->
                  self#compile_argument arg var.value_type);
              let lib = Ain.get_library_by_index ctx.ain lib_no in
              let type_id =
                if String.equal lib.name "Array" then
                  match e.ty with
                  | Array t | Ref (Array t) ->
                      Ain.Type.int_of_data_type (Ain.version ctx.ain)
                        (jaf_to_ain_type t)
                  | _ -> -1
                else -1
              in
              self#write_instruction3 CALLHLL lib_no fun_no type_id;
              self#write_instruction1 PUSH 0;
              let jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifnz_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              (match f.return_type with
              | Ain.Type.Void -> self#write_instruction1 PUSH (-1)
              | _ ->
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1));
              self#write_address_at jump_addr current_address)
      (* HLL function call *)
      | Call (_, args, HLLCall (lib_no, fun_no)) ->
          self#pre_emit_lambda_args args;
          let f = Ain.function_of_hll_function_index ctx.ain lib_no fun_no in
          self#compile_function_arguments args f;
          if Ain.version ctx.ain > 8 then
            (* v11 [CALLHLL] carries an extra type-id operand. For Array
               library methods it's the element type of the receiver;
               for everything else the runtime ignores it and -1 is
               fine. *)
            let lib = Ain.get_library_by_index ctx.ain lib_no in
            let type_id =
              if String.equal lib.name "Array" then
                match args with
                | Some { ty = Array t | Ref (Array t); _ } :: _ ->
                    Ain.Type.int_of_data_type (Ain.version ctx.ain)
                      (jaf_to_ain_type t)
                | _ -> -1
              else -1
            in
            self#write_instruction3 CALLHLL lib_no fun_no type_id
          else self#write_instruction2 CALLHLL lib_no fun_no
      (* system call *)
      | Call (_, args, SystemCall sys) ->
          let f = Builtin.function_of_syscall sys in
          self#compile_function_arguments args f;
          if Ain.version ctx.ain > 8 then (
            (* v11 routes syscalls through the [system] HLL library
               instead of the [CALLSYS] opcode. [CALLSYS] in v11 is
               either invalid or reused for something else; calling
               it at boot aborts the VM. Falls back to [CALLSYS] when
               the [system] library or matching name isn't registered
               (e.g. on a synthesised test ain that doesn't import
               [system.hll]). *)
            match Ain.get_library_index ctx.ain "system" with
            | Some lib_no -> (
                let syscall_name = Bytecode.string_of_syscall sys in
                match
                  Ain.get_library_function_index ctx.ain lib_no syscall_name
                with
                | Some fun_no ->
                    self#write_instruction3 CALLHLL lib_no fun_no (-1)
                | None -> self#write_instruction1 CALLSYS f.index)
            | None -> self#write_instruction1 CALLSYS f.index)
          else self#write_instruction1 CALLSYS f.index
      (* built-in method call *)
      | Call ({ node = Member (e, _, _); _ }, args, BuiltinCall builtin) -> (
          self#pre_emit_lambda_args args;
          let receiver_ty = ref Void in
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
          | ArrayAlloc | ArrayRealloc | ArrayFree | ArrayNumof | ArrayCopy
          | ArrayFill | ArrayPushBack | ArrayPopBack | ArrayEmpty | ArrayErase
          | ArrayInsert | ArraySort | ArraySortBy | ArrayReverse | ArrayFind ->
              receiver_ty := e.ty;
              self#compile_variable_ref e
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
              (* v11 [Array.Alloc] is 4-dimensional — pad missing dims
                 with [-1] so the HLL sees a complete parameter list. *)
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
              (* FIXME: this built-in should be variadic *)
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
          | DelegateNumof -> self#write_instruction0 DG_NUMOF
          | DelegateExist -> self#write_instruction0 DG_EXIST
          | DelegateErase -> self#write_instruction0 DG_ERASE
          | DelegateClear -> self#write_instruction0 DG_CLEAR
          | Assert ->
              compiler_bug "invalid built-in method call"
                (Some (ASTExpression expr)))
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
          self#compile_function_arguments args f;
          self#write_instruction1 DG_CALLBEGIN no;
          let loop_addr = current_address in
          self#write_instruction2 DG_CALL no 0;
          self#write_instruction1 JUMP loop_addr;
          self#write_address_at (loop_addr + 6) current_address
      | Call (e, _args, UnresolvedCall) when Poly.(e.ty = HLLParam) ->
          (* v11 [hll_param] call — the callee type stays unresolved
             through typeAnalysis because [hll_param] is a runtime-
             polymorphic slot. Compile the callee and push a zero
             placeholder so downstream stack shape is correct; the
             actual dispatch happens via the HLL bridge at runtime. *)
          self#compile_expression e;
          self#write_instruction1 PUSH 0
      | Call (_, _, _) ->
          compiler_bug "invalid call expression" (Some (ASTExpression expr))
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression expr))
      | RvalueRef _ ->
          compiler_bug "RvalueRef in rvalue context" (Some (ASTExpression expr))
      | DummyRef _ ->
          self#compile_lvalue expr;
          (* In v11, [compile_lvalue]'s dummy-populate path already emits
             the appropriate deref for struct/array dummies, so the stack
             is already the shape [compile_expression] would have produced
             via [SR_REF2]. Pre-v11 still needs [SR_REF2]. *)
          if Ain.version ctx.ain > 8 then
            (match expr.ty with
            | Int | Float | Bool | LongInt | FuncType _ ->
                self#write_instruction0 REF
            | _ -> ())
          else
            (match expr.ty with
            | Ref (Struct (_, no)) | Struct (_, no) ->
                self#write_instruction1 SR_REF2 no
            | _ -> ())
      | This -> (
          match expr.ty with
          | Struct (_, no) when Ain.version ctx.ain <= 8 ->
              self#write_instruction0 PUSHSTRUCTPAGE;
              self#write_instruction1 SR_REF2 no
          | Struct _ ->
              (* v11: [PUSHSTRUCTPAGE] already pushes the current
                 struct page-ref (one slot, ready for use), unlike
                 [PUSHLOCALPAGE; PUSH idx] which yields a page+slot
                 lvalue pair. Emit just [A_REF] to incref the
                 page-ref before downstream consumes it; an
                 [SR_REF2 no] would treat the page-ref as a
                 page+slot pair and deref into garbage. *)
              self#write_instruction0 PUSHSTRUCTPAGE;
              self#write_instruction0 A_REF
          | _ ->
              compiler_bug "unexpected type of this" (Some (ASTExpression expr))
          )
      | Null -> (
          match expr.ty with
          | FuncType _ | IMainSystem | HLLParam ->
              self#write_instruction1 PUSH 0
          | Delegate _ -> self#write_instruction0 DG_NEW
          | String -> self#write_instruction1 S_PUSH 0
          | Ref (String | Struct _ | Array _ | HLLParam)
            when Ain.version ctx.ain > 8 ->
              (* v11 non-scalar ref is a single-slot page-ref. [PUSH -1]
                 is the null-page sentinel. Pushing a second [PUSH 0]
                 would leave an unmatched slot on the stack that
                 downstream POP / DELETE never accounts for. *)
              self#write_instruction1 PUSH (-1)
          | Struct _ | Array _ when Ain.version ctx.ain > 8 ->
              self#write_instruction1 PUSH (-1)
          | Ref _ ->
              (* Scalar ref (2-slot page+index) or pre-v11. *)
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH 0
          | Int | Bool | Float | LongInt | NullType ->
              self#write_instruction1 PUSH 0
          | ty ->
              compiler_bug
                ("unimplemented: NULL rvalue of type " ^ jaf_type_to_string ty)
                (Some (ASTExpression expr)))
      | Lambda f ->
          let lambda_idx = Option.value_exn f.index in
          (* v11 pre-emit: if the enclosing call has already written
             the lambda body via [pre_emit_lambda_args], don't emit it
             again — re-registering would shift downstream addresses
             and double the function-table entry. Just push the
             receiver+index. *)
          if not (Hashtbl.mem pre_emitted_lambdas lambda_idx) then (
            let jump_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#compile_function f;
            self#write_address_at jump_addr current_address);
          self#write_instruction0 PUSHSTRUCTPAGE;
          self#write_instruction1 PUSH lambda_idx
      | OptionalMember (obj, name, mt) ->
          (* [a?.b] rvalue: evaluate [a]; if the result is the [-1]
             null sentinel, push the type-appropriate default; else
             access [.b] on [a]. *)
          self#compile_expression obj;
          self#write_instruction0 DUP;
          self#write_instruction1 PUSH (-1);
          self#write_instruction0 EQUALE;
          let ifnz_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          (match mt with
          | ClassMethod (_, no) -> self#write_instruction1 PUSH no
          | ClassVariable var_no ->
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF
          | _ ->
              let member_expr = { expr with node = Member (obj, name, mt) } in
              self#compile_expression member_expr);
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifnz_addr current_address;
          self#write_instruction0 POP;
          (match expr.ty with
           | Ref _ | Struct _ | Delegate _ -> self#write_instruction1 PUSH (-1)
           | String -> self#write_instruction1 S_PUSH 0
           | Float -> self#write_instruction1_float F_PUSH 0.0
           | _ -> self#write_instruction1 PUSH 0);
          self#write_address_at jump_addr current_address
      | NullCoalesce (a, b) ->
          let a_inner =
            match a.node with DummyRef (_, inner) -> inner | _ -> a
          in
          let unwrap_dummy (e : expression) =
            match e.node with DummyRef (_, inner) -> inner | _ -> e
          in
          let is_optional_result e =
            match (unwrap_dummy e).node with
            | Call ({ node = OptionalMember _; _ }, _, _) -> true
            | _ -> false
          in
          let is_optional =
            match a_inner.node with
            | Call ({ node = OptionalMember _; _ }, _, _) -> true
            | _ -> false
          in
          if
            Ain.version ctx.ain > 8
            && (not is_optional)
            && match a.ty with Ref _ -> true | _ -> false
          then (
            (* v11 ref-typed [a ?? b]: [a] is a [Ref T] lvalue. Push
               via [compile_lvalue], duplicate (DUP for non-scalar
               1-slot, DUP_U2 for scalar 2-slot), null-check via PUSH
               -1; EQUALE. On null, drop the dup'd value and evaluate
               [b]; otherwise keep [a]. The trailing REF (scalar) /
               A_REF (non-scalar) deref the page-ref to the surface
               value the consumer expects. *)
            let scalar_ref_result =
              match expr.ty with
              | Int | Float | Bool | LongInt | FuncType _ | HLLParam -> true
              | _ -> false
            in
            self#compile_lvalue a;
            self#write_instruction0
              (if scalar_ref_result then DUP_U2 else DUP);
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE;
            let ifz_addr = current_address + 2 in
            self#write_instruction1 IFZ 0;
            if scalar_ref_result then (
              self#write_instruction0 POP;
              self#write_instruction0 POP)
            else self#write_instruction0 POP;
            (match (scalar_ref_result, b.node) with
            | true, DummyRef (dummy_idx, inner) ->
                self#compile_expression inner;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction0 SWAP;
                self#write_instruction1 PUSH dummy_idx;
                self#write_instruction0 SWAP;
                self#write_instruction0 ASSIGN;
                self#write_instruction0 POP;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH dummy_idx
            | _ -> self#compile_lvalue b);
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
            self#compile_expression a_inner;
            if is_optional then (
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifz_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              self#compile_expression b;
              if is_optional_result b then (
                let jump_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at ifz_addr current_address;
                self#write_instruction1 PUSH 0;
                self#write_address_at jump_addr current_address)
              else self#write_address_at ifz_addr current_address)
            else
              let b =
                match b.node with
                | DummyRef (_, inner) -> inner
                | _ -> b
              in
              (match a_inner.node with
              | NullCoalesce _ -> ()
              | _ -> self#write_instruction0 DUP);
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifz_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              self#compile_expression b;
              if is_optional_result b then (
                let jump_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at ifz_addr current_address;
                self#write_instruction1 PUSH 0;
                self#write_address_at jump_addr current_address)
              else self#write_address_at ifz_addr current_address)

    method compile_expr_and_pop ?(before_pop = fun () -> ()) (expr : expression)
        =
      match expr.node with
      | Assign
          ( EqAssign,
            { node = Ident (_, LocalVariable (i, _)); _ },
            { node = ConstInt n; _ } )
        when ctx.version < 630
             && not (Ain.Type.is_ref (self#get_local i).value_type) ->
          self#write_instruction2 SH_LOCALASSIGN i n
      | Unary
          ( (( PreInc | PostInc | PreDec | PostDec | ForeachInc
             | ForeachDec ) as op),
            { node = Ident (_, LocalVariable (i, _)); _ } )
        when ctx.version < 630
             && (not (Ain.Type.is_ref (self#get_local i).value_type))
             && Poly.(expr.ty <> LongInt) ->
          self#write_instruction1
            (match op with
             | PreInc | PostInc | ForeachInc -> SH_LOCALINC
             | _ -> SH_LOCALDEC)
            i
      | Unary (((ForeachInc | ForeachDec) as op), e) ->
          (* Statement-context foreach counter inc/dec: [INC]/[DEC]
             consume the [page, index] pair left by [compile_lvalue]
             in place. The pre-v11 [DUP2; INC; POP; POP] dance is
             unnecessary — original and experimental compilers emit
             just the two-op sequence. *)
          self#compile_lvalue e;
          self#write_instruction0 (incdec_instruction (op, e.ty))
      | Unary (((PreInc | PreDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 (incdec_instruction (op, e.ty));
          self#write_instruction0 POP;
          self#write_instruction0 POP
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_expr_and_pop ~before_pop b
      (* v11 [obj?.Method()] / [obj?.HllCall()] used as a statement: the
         optional chain leaves a fat-null sentinel int on the stack
         (0 for success, -1 for null) that must be discarded. The
         expression's [ty] is [Void] (the called method returns void),
         and the default [compile_pop Void] is a no-op — emit an
         explicit [POP] so the stack stays balanced. *)
      | Call ({ node = OptionalMember _; _ }, _, (MethodCall _ | HLLCall _))
        when Ain.version ctx.ain > 8 && Poly.equal expr.ty Void ->
          self#compile_expression expr;
          before_pop ();
          self#write_instruction0 POP
      | DummyRef _ ->
          self#compile_lvalue expr;
          before_pop ();
          self#compile_pop expr.ty (ASTExpression expr)
      | _ ->
          self#compile_expression expr;
          before_pop ();
          self#compile_pop expr.ty (ASTExpression expr)

    (** Emit the code for a statement. Statements are stack-neutral, i.e. the
        state of the stack is unchanged after executing a statement. *)
    method compile_statement (stmt : statement) =
      DebugInfo.add_loc debug_info current_address stmt.loc;
      (* delete locals that will be out-of-scope after this statement *)
      List.iter (List.rev stmt.delete_vars) ~f:(fun i ->
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
          (* v11 cleanup ordering for the dummy slots produced by this
             expression statement:
             - For [String]/[Delegate]/[HLLParam]/[Array] (reference-
               shaped values), [compile_pop] emits a [DELETE]-style
               release that needs to fire BEFORE the slot's
               [SH_LOCALDELETE], otherwise the strong ref leaks.
             - For everything else, [compile_pop] emits a plain [POP]
               which doesn't touch refcounts; alice releases the slot
               BEFORE the [POP] so the dummy is gone while the value
               is still on the stack. *)
          let cleanup_after_pop =
            Ain.version ctx.ain > 8
            &&
            match e.ty with
            | String | Delegate _ | HLLParam | Array _ -> true
            | _ -> false
          in
          if cleanup_after_pop then (
            self#compile_expr_and_pop e;
            self#cleanup_condition_dummyrefs vars_before_expr)
          else if Ain.version ctx.ain > 8 then
            self#compile_expr_and_pop
              ~before_pop:(fun () ->
                self#cleanup_condition_dummyrefs vars_before_expr)
              e
          else self#compile_expr_and_pop e
      | Compound stmts -> self#compile_block stmts
      | Label name -> self#add_label name stmt
      | If (test, con, alt) ->
          let vars_before =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          self#compile_expression test;
          (* v11: release condition-local dummies before the IFZ so
             both the taken and not-taken branch see them cleaned up. *)
          self#cleanup_condition_dummyrefs vars_before;
          self#maybe_emit_condition_itob test;
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_statement con;
          (match alt.node with
          | EmptyStatement when Ain.version ctx.ain > 8 ->
              (* v11 omits the trailing JUMP-over-alt when there's no
                 else branch. Pre-v11 always emits the JUMP — keep
                 that layout for pre-v11 since some pre-v11 expected
                 bytecode/address tests rely on it. *)
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
          let vars_before =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          self#compile_expression test;
          (* v11: release condition-local dummies before the IFZ so
             both the continue and the exit branch see them cleaned
             up, not just the body-executes path. *)
          self#cleanup_condition_dummyrefs vars_before;
          self#maybe_emit_condition_itob test;
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
          let vars_before =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          self#compile_expression test;
          self#cleanup_condition_dummyrefs vars_before;
          self#maybe_emit_condition_itob test;
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
                self#maybe_emit_condition_itob e;
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
          (* loop body *)
          self#write_address_at body_addr current_address;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          Option.iter break_addr ~f:(fun break_addr ->
              self#write_address_at break_addr current_address);
          self#end_loop
      | ForEach _ ->
          (* [Compile.desugar_pass] rewrites ForEach into a [While]
             before any later pass; reaching codegen with [ForEach]
             still in the AST means the desugar pass was skipped. *)
          compiler_bug "ForEach not desugared before codegen"
            (Some (ASTStatement stmt))
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
              (match e.ty with
              | Wrap _ when Ain.version ctx.ain > 8 ->
                  (* v11 [Wrap T] return: unwrap the fat-ref to the
                     underlying page-ref before [DUP; SP_INC]. *)
                  self#write_instruction0 REFREF;
                  self#write_instruction0 REF
              | _ -> ());
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC
          | Ref _, _ ->
              compile_error "return statement not implemented for ref type"
                (ASTStatement stmt)
          | _ ->
              self#compile_expression e;
              (* v11: when returning a [String]/[Struct]/[Array]
                 produced by a ref-returning call OR a [new]
                 expression (both stored in a [DummyRef] slot via
                 [compile_lvalue]), the dummy's [SH_LOCALDELETE] on
                 function exit would free the page before the caller
                 reads the return value. Emit [A_REF] after the dummy
                 ASSIGN so the stack value retains an owning ref the
                 caller takes over. Chained-call receivers don't need
                 it — there's no [SH_LOCALDELETE] between the dummy
                 and the consuming [CALLMETHOD]. *)
              if Ain.version ctx.ain > 8 then (
                let rec inner_expr (e : expression) =
                  match e.node with
                  | DummyRef (_, inner) -> inner_expr inner
                  | _ -> e
                in
                let inner = inner_expr e in
                let needs_a_ref =
                  match e.node with
                  | DummyRef _ -> (
                      match inner.node with
                      | New _ -> true
                      | Call _ -> (
                          match self#ain_call_return_type inner with
                          | Some (Ain.Type.Ref _) -> true
                          | _ -> false)
                      | _ -> false)
                  | _ -> false
                in
                if needs_a_ref then
                  match (Option.value_exn current_function).return_type with
                  | String | Struct _ | Array _ ->
                      self#write_instruction0 A_REF
                  | _ -> ()));
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
              (* v11 [Wrap T] LHS: foreach loop-var rebind. Different
                 rhs shapes need different idioms — Subscript /
                 [DummyRef New _] / Null / fallthrough each have a
                 specific bytecode pattern alice emits. *)
              match rhs.node with
              | Subscript _ ->
                  self#compile_variable_ref rhs;
                  self#write_instruction0 R_ASSIGN;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP
              | DummyRef (dummy_idx, { node = New _; _ })
                when Ain.version ctx.ain > 8 ->
                  self#write_instruction0 REFREF;
                  self#write_instruction0 DUP2;
                  self#write_instruction0 REF;
                  self#write_instruction0 DELETE;
                  self#compile_lvalue rhs;
                  self#write_instruction0 DUP;
                  self#write_instruction0 SP_INC;
                  self#write_instruction0 ASSIGN;
                  self#write_instruction0 POP;
                  self#write_instruction1 SH_LOCALDELETE dummy_idx
              | Null when Ain.version ctx.ain > 8 ->
                  (* v11 [foreach loop-var <- NULL]: unwrap the Wrap
                     fat-ref, release the current binding, then store
                     the null sentinel. Emitting bare [R_ASSIGN] with
                     a missing rhs leaves only [page; slot] on the
                     stack and trips "R_ASSIGN: unexpected stack
                     structure" at decompile. *)
                  self#write_instruction0 REFREF;
                  self#write_instruction0 DUP2;
                  self#write_instruction0 REF;
                  self#write_instruction0 DELETE;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 ASSIGN;
                  self#write_instruction0 POP
              | _ ->
                  self#write_instruction0 R_ASSIGN;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP)
          | _ when is_ref_scalar lhs.ty && Ain.version ctx.ain > 8 -> (
              (* v11 scalar-ref RefAssign: release the old target,
                 compute the rhs ref, then [DUP_U2; SP_INC; R_ASSIGN;
                 POP; POP]. [DUP_U2] duplicates the page+idx pair
                 *under* the rhs value so [SP_INC] increfs it before
                 [R_ASSIGN] stores the ref. Skipping [DUP_U2]/[SP_INC]
                 leaves the new reference's refcount one short and
                 the local-page release on RETURN aborts. *)
              self#compile_delete_ref lhs.ty;
              self#compile_lvalue rhs;
              match rhs.node with
              | Null ->
                  self#write_instruction0 R_ASSIGN;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP
              | _ ->
                  self#write_instruction0 DUP_U2;
                  self#write_instruction0 SP_INC;
                  self#write_instruction0 R_ASSIGN;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP)
          | _ when is_ref_scalar lhs.ty -> (
              self#compile_delete_ref lhs.ty;
              (match rhs.node with
              | Null -> ()
              | _ -> self#write_instruction0 DUP2);
              self#compile_lvalue rhs;
              (* NOTE: SDK compiler emits [DUP_U2; SP_INC; R_ASSIGN; POP; POP] here *)
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              match rhs.node with
              | Null -> self#write_instruction0 POP
              | _ ->
                  self#write_instruction0 POP;
                  self#write_instruction0 REF;
                  self#write_instruction0 SP_INC)
          | Ref (String | Struct _ | Array _ | HLLParam)
            when Ain.version ctx.ain > 8 ->
              (* v11 [ref X = rvalue]: rhs has been wrapped in a
                 [DummyRef] (variableAlloc) so [compile_lvalue] stores
                 the produced value into the dummy slot, then
                 [ASSIGN; SP_INC; SH_LOCALDELETE dummy] writes into
                 the lhs ref, balances refcount, and releases the
                 dummy. Also releases any extra DummyRef slots
                 allocated during a chained rhs like [a.GetX().GetY()]
                 — each intermediate call's ref-returning result has
                 its own dummy and all must be released or the local
                 page's refcount never reaches zero. *)
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
              | DummyRef (_, { node = New _; _ }) ->
                  self#write_instruction0 ASSIGN;
                  self#write_instruction0 SP_INC
              | _ ->
                  self#write_instruction0 DUP;
                  self#write_instruction0 SP_INC;
                  self#write_instruction0 ASSIGN;
                  self#write_instruction0 POP);
              (match Stack.top scopes with
              | Some scope ->
                  let n_new = List.length scope.vars - vars_before in
                  if n_new > 0 then
                    List.iter
                      (List.rev (List.take scope.vars n_new))
                      ~f:self#compile_delete_var
              | None -> ())
          | Ref (String | Struct _ | Array _) -> (
              self#compile_delete_ref lhs.ty;
              (match (lhs.ty, rhs.node) with
              | _, Null -> ()
              | _ -> self#write_instruction0 DUP2);
              self#compile_lvalue rhs;
              (* NOTE: SDK compiler emits [DUP; SP_INC; ASSIGN; POP] here *)
              self#write_instruction0 ASSIGN;
              match rhs.node with
              | Null -> self#write_instruction0 POP
              | _ ->
                  self#write_instruction0 DUP_X2;
                  self#write_instruction0 POP;
                  self#write_instruction0 REF;
                  self#write_instruction0 SP_INC;
                  self#write_instruction0 POP)
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
          (* Pre-v11 [OBJSWAP] reads its type off the stack; v11+
             encodes it as a direct int operand. *)
          if Ain.version ctx.ain > 8 then
            self#write_instruction1 OBJSWAP type_no
          else (
            self#write_instruction1 PUSH type_no;
            self#write_instruction0 OBJSWAP)

    (** Emit the code for a variable declaration. If the variable has an
        initval, the initval expression is computed and assigned to the
        variable. Otherwise a default value is assigned. *)
    method compile_variable_declaration (decl : variable) =
      if decl.is_const then ()
      else if
        Ain.version ctx.ain > 8
        && decl.is_private
        && Option.is_none decl.initval
      then
        (* v11 two-phase private declaration (the foreach desugar
           pre-allocates counter / container / loop-var slots): phase
           1 has no initval — register the slot for cleanup; phase 2
           has an initval and emits the real init via the normal
           path. Skipping code emission here prevents a spurious
           default-init that shifts every downstream address and
           trips the VM's refcount bookkeeping at RETURN. Pre-v11
           keeps the default-init path since its foreach desugar
           emits a single combined declaration. *)
        let v = self#get_local (Option.value_exn decl.index) in
        self#scope_add_var v
      else
        let v = self#get_local (Option.value_exn decl.index) in
        self#scope_add_var v;
        match v.value_type with
        | Ref _ when Ain.version ctx.ain > 8 -> (
            (* v11 ref-init paths. Each handles a specific shape; the
               final fallback rewrites to a [RefAssign] like pre-v11. *)
            let vars_before () =
              match Stack.top scopes with
              | Some scope -> List.length scope.vars
              | None -> 0
            in
            match decl.initval with
            | None ->
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#write_instruction0 DUP2;
                self#write_instruction0 REF;
                self#write_instruction0 DELETE;
                (match ain_to_jaf_type ctx.ain v.value_type with
                | Ref (Int | Bool | LongInt | Float | FuncType _) ->
                    self#write_instruction1 PUSH (-1);
                    (match ain_to_jaf_type ctx.ain v.value_type with
                    | Ref Float -> self#write_instruction1_float F_PUSH 0.0
                    | _ -> self#write_instruction1 PUSH 0);
                    self#write_instruction0 R_ASSIGN;
                    self#write_instruction0 POP;
                    self#write_instruction0 POP
                | Ref String ->
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction0 ASSIGN;
                    self#write_instruction0 SP_INC
                | Ref (Struct _ | Array _ | HLLParam) ->
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction0 ASSIGN;
                    self#write_instruction0 POP
                | _ ->
                    compiler_bug "invalid ref declaration default"
                      (Some (ASTVariable decl)))
            | Some e
              when decl.is_private
                   && (match e.node with DummyRef _ -> false | _ -> true)
                   && not (is_ref_scalar e.ty) ->
                (* Two-phase private ref init (foreach containers): the
                   slot is already empty, so skip the delete-old-value
                   path and use rhs-first CHECKUDO + ASSIGN + SP_INC. *)
                let vb = vars_before () in
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
                self#cleanup_condition_dummyrefs vb
            | Some e
              when match v.value_type with
                   | Ref (Array _) -> true
                   | _ -> false ->
                (* Array-ref init: push raw ref via [compile_lvalue]
                   into the freshly-declared slot using ASSIGN; SP_INC. *)
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#compile_delete_ref decl.type_spec.ty;
                self#compile_lvalue e;
                self#write_instruction0 ASSIGN;
                self#write_instruction0 SP_INC
            | Some e
              when is_ref_scalar (ain_to_jaf_type ctx.ain v.value_type)
                   && (match e.node with DummyRef _ -> false | _ -> true) ->
                (* Scalar-ref init [ref int x = arr[i]]: dest-lvalue +
                   delete-empty-target + R_ASSIGN + SP_INC. *)
                let vb = vars_before () in
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#compile_delete_ref decl.type_spec.ty;
                self#compile_lvalue e;
                self#write_instruction0 R_ASSIGN;
                self#write_instruction0 POP;
                self#write_instruction0 SP_INC;
                self#cleanup_condition_dummyrefs vb
            | Some e
              when (match e.node with DummyRef _ -> false | _ -> true)
                   && not (is_ref_scalar e.ty) ->
                (* Non-DummyRef non-scalar ref init: push dest +
                   compile_delete_ref (DUP2;REF;DELETE) + rhs lvalue +
                   ASSIGN + SP_INC. [compile_lvalue] keeps the raw ref
                   on the stack without the extra A_REF that
                   [compile_expression] would add for struct/array. *)
                let vb = vars_before () in
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#compile_delete_ref decl.type_spec.ty;
                self#compile_lvalue e;
                self#write_instruction0 ASSIGN;
                self#write_instruction0 SP_INC;
                self#cleanup_condition_dummyrefs vb
            | Some e
              when match e.node with DummyRef _ -> false | _ -> true ->
                (* Scalar-ref init with non-DummyRef rhs: CHECKUDO +
                   R_ASSIGN pattern. The freshly-declared slot starts
                   empty, so no old-value release. *)
                let vb = vars_before () in
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
                self#cleanup_condition_dummyrefs vb
            | Some ({ node = DummyRef (dummy_idx, inner); _ } as e)
              when (match v.value_type with
                   | Ref (Struct _ | String | Array _ | HLLParam) -> true
                   | _ -> false)
                   && (match inner.node with New _ -> false | _ -> true) ->
                (* [ref X y = method()] decl. [compile_delete_ref]
                   balances the freshly-declared slot (empty) before
                   the inner method's result lvalue is assigned and
                   the dummy cleanup fires. Distinct from RefAssign
                   (DUP;SP_INC;ASSIGN;POP) because that pattern bumps
                   a refcount on the "previous" value, which doesn't
                   exist at decl time. *)
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
                    node =
                      Ident (decl.name, LocalVariable (v.index, decl.location));
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
        | Ref _ ->
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
              }
        | Int | Bool | LongInt | Float | FuncType _ | String ->
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
            self#compile_expr_and_pop
              {
                node = Assign (EqAssign, lhs, rhs);
                ty = rhs.ty;
                loc = decl.location;
              }
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
                self#write_instruction1 PUSH sno;
                self#write_instruction0 SR_ASSIGN;
                self#compile_pop decl.type_spec.ty (ASTVariable decl)
            | None -> ())
        | Array _ ->
            let has_dims = List.length decl.array_dim > 0 in
            self#compile_local_ref v.index;
            if has_dims then (
              List.iter decl.array_dim ~f:self#compile_expression;
              self#write_instruction1 PUSH (List.length decl.array_dim);
              self#write_instruction0 A_ALLOC)
            else self#write_instruction0 A_FREE
        | Delegate _ -> (
            self#compile_local_ref v.index;
            self#write_instruction0 REF;
            match decl.initval with
            | Some ({ ty = String; _ } as e) ->
                self#compile_expression e;
                self#write_instruction0 DG_SET
            | Some ({ ty = TyMethod _; _ } as e) ->
                self#compile_expression e;
                self#write_instruction0 DG_SET
            | Some ({ ty = Delegate _; _ } as e) ->
                self#compile_expression e;
                self#write_instruction0 DG_ASSIGN;
                self#write_instruction0 DG_POP
            | Some _ ->
                compiler_bug "invalid delegate initval"
                  (Some (ASTVariable decl))
            | None -> self#write_instruction0 DG_CLEAR)
        (* v11 foreach desugar produces [Wrap T] loop-var slots and
           sometimes [Void] placeholders; both are filled in by later
           statements emitted by the desugarer, so the declaration
           itself is a no-op. *)
        | Wrap _ when Ain.version ctx.ain > 8 -> ()
        | Void -> ()
        | IMainSystem | HLLFunc2 | HLLParam | Wrap _ | Option _
        | Unknown87 _ | IFace _ | Enum2 _ | Enum _ | HLLFunc | Unknown98
        | IFaceWrap _ | Function | Method | NullType ->
            compile_error
              (Printf.sprintf "Unimplemented variable type: %s for `%s`"
                 (jaf_type_to_string decl.type_spec.ty)
                 decl.name)
              (ASTVariable decl)

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
      (* ENDFUNC is not generated for the [NULL] function and methods
         except auto-generated array initializers. The global-init
         function ("0") and the per-class auto-array-initializer
         ("2") both need ENDFUNC so the VM knows where the function
         body ends. *)
      (match decl with
      | { name = "NULL"; _ } -> ()
      | { class_name = None; _ }
      | { name = "0"; _ }
      | { name = "2"; _ }
      | { is_lambda = true; _ } ->
          self#write_instruction1 ENDFUNC index
      | _ -> ());
      self#resolve_gotos;
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
              | PropertyDecl _ | EventDecl _ ->
                  (* [Declarations.expand_struct_decls] rewrites these
                     into [MemberDecl] + [Method] components before
                     codegen runs, so reaching this arm means the
                     expansion was skipped. *)
                  compiler_bug
                    "PropertyDecl/EventDecl not expanded before codegen" None
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
