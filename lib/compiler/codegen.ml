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

type cflow_type =
  | CFlowLoop of { continue_addr : int (* -1 if it is not yet known *) }
  | CFlowSwitch of Ain.Switch.t

type cflow_stmt = {
  kind : cflow_type;
  mutable break_addrs : int list;
  mutable continue_addrs : int list;
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
  mutable switch_break_deleted_dummies : int list;
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

    (* Enclosing functions for the current lambda body, parent-first.
       Populated when entering a lambda by parsing the lambda's name
       (the pattern is [Class@<lambda : ParentName(line, col)>]); used
       by [compile_dereference] for [CapturedVariable] to look up the
       parent slot's actual ain type, since the lambda-side [expr.ty]
       drops the [Wrap] wrapper that foreach iteration vars carry. *)
    val mutable enclosing_functions : Ain.Function.t list = []

    (* v12: true while compiling the expression of a [Return _] stmt.
       The [ArrayLiteral] DummyRef path consults this to decide whether
       the literal's backing slot escapes via the return value (drop
       from [scope.vars] so [end_scope] doesn't free what the caller is
       about to read) or stays local (keep in [scope.vars] so
       [end_scope] emits the [Array.Free <slot>] orig requires to keep
       the slot from leaking past its branch). *)
    val mutable is_in_return_expr = false

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

    val mutable last_condition_deleted_dummies : int list = []

    val mutable end_switch_deleted_dummies : int list = []

    val mutable v12_last_use_deleted_vars : int list = []

    val mutable suppress_inline_deleted_scope_cleanup = false

    val mutable block_depth : int = 0

    (* v11: lambda body indexes whose JUMP-over-body has already been
       written by [pre_emit_lambda_args] before the enclosing call
       evaluates its arguments. The [Lambda] expression case consults
       this to skip the inline JUMP+body path — re-emitting would
       register the body at a shifted address and corrupt the
       function table. *)
    val pre_emitted_lambdas : (int, unit) Hashtbl.t =
      Hashtbl.create (module Int)

    (* v12 delegate assignment emits inline lambda bodies before the
       destination lvalue, matching the original compiler. Keep this
       separate from [pre_emitted_lambdas], which is also used for
       argument-lambda queueing. *)
    val v12_assignment_lambdas : (int, unit) Hashtbl.t =
      Hashtbl.create (module Int)

    (* v12: track duplicate prototype slots we've already emitted a body
       for, so the recursive compile_function on the dup doesn't try to
       duplicate the dup. *)
    val body_dup_emitted : (int, unit) Hashtbl.t =
      Hashtbl.create (module Int)

    val mutable v12_current_body_dup_rank : int option = None

    val mutable v12_iface_local_init_owns_cast_guard = false

    val v12_dummy_slots_initialized : (int, unit) Hashtbl.t =
      Hashtbl.create (module Int)

    (* v12: iface locals whose next statement (after declaration)
       unconditionally assigns them — original Rance10 skips the
       NULL-init prefix for these since the assignment overwrites
       the slot before any read. Populated by [compile_block] before
       processing the Declarations statement. *)
    val v12_skip_iface_init : (int, unit) Hashtbl.t =
      Hashtbl.create (module Int)

    (* v12: lambda fundecls deferred for top-level emission. The v12
       original compiler emits each lambda as a separate function table
       entry placed AFTER its containing function — not inline via the
       v11 [JUMP-over-body] idiom. Queue lambdas as they're encountered
       during caller compilation; drain to top-level emission after the
       containing non-lambda function's ENDFUNC. Draining a lambda may
       queue further nested lambdas; the drain loop runs until empty. *)
    val v12_lambda_queue : Jaf.fundecl Queue.t = Queue.create ()

    (* v11 property-setter argument context. Set true while compiling
       arguments for a property setter call (the [DUP_X2 + CALLMETHOD
       + DELETE/POP] idiom). Suppresses [compile_argument]'s [A_REF]
       after the dummy ASSIGN for [Ref (Struct|Array)] args, since the
       setter idiom owns the page-ref via [DUP_X2] + the slot's
       [SH_LOCALDELETE] without an extra incref. *)
    val mutable in_prop_setter_arg : bool = false

    (* v12 Array-HLL store into a REF-element array ([array<ref T>],
       [CALLHLL Array PushBack 21]): the runtime stores the page-ref
       with its own incref, so the pushed value arg stays a bare
       borrowed read — orig [CASTask@JoinImp] / [CASTaskParts@Next] /
       [BattleLog@0] push [.LOCALREF v] / getter results straight into
       [PushBack 21] with no [A_REF]. VALUE-element arrays
       ([PushBack 13]) keep the bump (orig
       [PlayerSkillEffectCollection@Add] emits [A_REF]). Set while
       compiling non-receiver args of such calls. *)
    val mutable in_ref_elem_hll_store_arg : bool = false

    val mutable bare_new_receiver_uses_default_ctor : bool = false

    (* The currentl active scopes. *)
    val mutable scopes = Stack.create ()

    (* Labels/gotos record for the current function. *)
    val mutable labels = Hashtbl.create (module String)

    (* Running CRC-32 of the current function. *)
    val mutable crc_state : Crc32.t = Crc32.Inactive

    (** Begin a scope. Variables created within a scope are deleted when the
        scope ends. *)
    method start_scope = Stack.push scopes { vars = [] }

    (** End a scope. Deletes variable created within the scope. *)
    method end_scope =
      let scope = Stack.pop_exn scopes in
      (* delete scope-local variables *)
      let is_function_scope = Option.is_none (Stack.top scopes) in
      let vars =
        List.sort scope.vars ~compare:(fun a b ->
            Int.descending a.index b.index)
      in
      List.iter vars ~f:(fun v ->
          let already_inline_deleted =
            Ain.version_gte ctx.ain (12, 0)
            && (List.mem end_switch_deleted_dummies v.index ~equal:Int.equal
               || (suppress_inline_deleted_scope_cleanup
                  && List.mem inline_deleted_dummies v.index
                       ~equal:Int.equal))
          in
          let already_last_use_deleted =
            Ain.version_gte ctx.ain (12, 0)
            && List.mem v12_last_use_deleted_vars v.index ~equal:Int.equal
          in
          if is_function_scope then
            (* At function exit, emit no cleanup. Variables are
               released by the VM's RETURN opcode auto-free. The
               earlier experiment of emitting an end-of-scope IFace
               cleanup here (introduced in 51077c2 to address
               RunIScene's RETURN crash) regressed 10 property getter
               functions audit-wise and broke menu/survey runtime in
               c8889e7→HEAD comparison. Keep the function-exit a
               no-op until the RunIScene RETURN issue is fixed
               upstream (likely in IFace last-use tracking, not
               here). *)
            ()
          else if already_inline_deleted || already_last_use_deleted then ()
          else self#compile_delete_var v)

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
        without normalisation. No-op on pre-v11.

        v12: original Rance10 emits only 65 ITOB total across the
        entire .ain — vs ~15k from this path in ours. The v12 IFZ
        evidently tolerates non-bool values directly, so skip this
        condition-side normalisation entirely. *)
    method maybe_emit_condition_itob (test : expression) =
      if
        Ain.version_lt ctx.ain (12, 0)
        && Ain.version ctx.ain > 8
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
      | Call (_, _, DelegateCall no) ->
          Some (Ain.function_of_delegate_index ctx.ain no).return_type
      | Call (_, _, HLLCall (lib_no, fun_no)) ->
          let lib = Ain.get_library_by_index ctx.ain lib_no in
          Some lib.functions.(fun_no).return_type
      | _ -> None

    (** v12 ownership classification of a value expression — single
        source of truth for "does the stacked value carry an owning
        page-ref that the consumer is about to drop without incref?".
        Replaces the four ad-hoc DummyRef/Call walks scattered across
        compile_argument, ArrayLiteral, NullCoalesce, etc.

        - [`Owned]   : producer just created a fresh page (NEW/NEWCALL)
                      and the value lives only in a synthetic dummy
                      slot that scope-exit will release. Consumer must
                      A_REF before storing.
        - [`Borrowed]: producer is a call whose ain-level return type
                      is [Ref _] (Array.At, *.First, getter returning
                      [ref T], ...). Same A_REF need as [`Owned] — the
                      dummy holds the only stack-side reference.
        - [`Stable]  : already-incref'd source (member, ident slot,
                      direct lvalue). No A_REF needed.

        The classifier walks through transparent wrappers (Cast,
        RvalueRef, DummyRef) before inspecting the producer node, so
        callers don't have to repeat that boilerplate. *)
    method expression_ownership (expr : expression) =
      let is_optional_dispatch (call_expr : expression) =
        match call_expr.node with
        | Call ({ node = OptionalMember _; _ }, _, _) -> true
        | _ -> false
      in
      let rec walk (e : expression) =
        match e.node with
        | New _ | NewCall _ -> `Owned
        | DummyRef (_, ({ node = New _ | NewCall _; _ })) -> `Owned
        | DummyRef (_, ({ node = Call _; _ } as inner)) ->
            if is_optional_dispatch inner then `Stable
            else (
              match self#ain_call_return_type inner with
              | Some (Ain.Type.Ref _) -> `Borrowed
              | _ -> (
                  match inner.ty with
                  | Ref _ -> `Borrowed
                  | _ -> `Stable))
        | DummyRef (_, inner) -> walk inner
        | Cast (_, inner) | RvalueRef inner -> walk inner
        | Call _ ->
            if is_optional_dispatch e then `Stable
            else (
              match self#ain_call_return_type e with
              | Some (Ain.Type.Ref _) -> `Borrowed
              | _ -> `Stable)
        | _ -> `Stable
      in
      walk expr

    (** True iff the expression's stacked value needs an [A_REF] bump
        before a v12 consumer that takes ownership without incref-ing
        (CALLHLL store, ArrayLiteral PushBack, String arg to a
        ref-receiving HLL). Centralises the
        [dummy_inner_returns_ref || bare_new_arg] / per-element
        ArrayLiteral walks into one predicate. *)
    method needs_a_ref_for_consume (expr : expression) =
      Ain.version_gte ctx.ain (12, 0)
      &&
      match self#expression_ownership expr with
      | `Owned | `Borrowed -> true
      | `Stable -> false

    (** Push one array-literal element for [Array.PushBack].
        Per-element A_REF for borrowed-ref / new-T sources: when the
        element is [new T()] (DummyRef-wrapped) or an HLL
        ref-returning call, the pushed page-ref must be bumped before
        PushBack stores it (orig: CGroupInstance@AddBoxLine /
        CLineInstance@GetOBB / TextButton@Init emit [NEW; ASSIGN;
        A_REF; PushBack] per element). Struct-typed VARIABLE reads and
        [this] push BARE borrowed refs — orig's CASTask@Next/Join1-5
        emit plain [PUSHSTRUCTPAGE] / [REF] into [PushBack 21]; the
        deref/This wrappers' auto-A_REF leaked one ref per element and
        diverged from orig. Scalars and S_PUSH literals stay plain. *)
    method emit_array_literal_element (elem : expression) =
      let bare_struct_read =
        Ain.version_gte ctx.ain (12, 0)
        &&
        match (elem.node, elem.ty) with
        | This, _ -> true
        | (Ident _ | Member (_, _, ClassVariable _)),
          (Struct _ | Ref (Struct _)) ->
            is_variable_ref elem.node
        | _ -> false
      in
      if bare_struct_read then (
        match elem.node with
        | This -> self#write_instruction0 PUSHSTRUCTPAGE
        | _ ->
            self#compile_variable_ref elem;
            self#write_instruction0 REF)
      else (
        self#compile_expression elem;
        if self#needs_a_ref_for_consume elem then
          self#write_instruction0 A_REF)

    (** Destructure [base.G1()....Gk()?.H1()....] — a getter chain with
        exactly one optional hop: plain zero-arg getters up to the
        tested receiver, the optional getter, then more plain getters.
        Each call is DummyRef-backed (variableAlloc). Returns
        (base, inner plain hops before the test, the optional hop,
         outer plain hops after it) with hops as (getter fn, dummy)
        in execution order; None when the shape doesn't match. Used by
        the ??-deferred scalar-field arm for chain receivers. *)
    method private optional_getter_field_chain (e : expression) =
      let rec strip (e : expression) =
        match e.node with
        | Cast (_, i) | RvalueRef i -> strip i
        | _ -> e
      in
      let rec walk_outer (e : expression) outer =
        match (strip e).node with
        | DummyRef
            ( dno,
              { node =
                  Call
                    ( { node = Member (inner, _, ClassMethod (_, g)); _ },
                      [],
                      MethodCall _ );
                _ } ) ->
            walk_outer inner ((g, dno) :: outer)
        | DummyRef
            ( dno,
              { node =
                  Call
                    ( { node = OptionalMember (recv, _, ClassMethod (_, g)); _ },
                      [],
                      MethodCall _ );
                _ } ) ->
            let rec walk_inner (e : expression) inner =
              match (strip e).node with
              | DummyRef
                  ( ino,
                    { node =
                        Call
                          ( { node = Member (deeper, _, ClassMethod (_, ig)); _ },
                            [],
                            MethodCall _ );
                      _ } ) ->
                  walk_inner deeper ((ig, ino) :: inner)
              | _ when is_variable_ref (strip e).node -> Some (strip e, inner)
              | _ -> None
            in
            Option.map (walk_inner recv []) ~f:(fun (base, inner) ->
                (base, inner, (g, dno), outer))
        | _ -> None
      in
      walk_outer e []

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
      last_condition_deleted_dummies <- [];
      if Ain.version ctx.ain > 8 then
        match Stack.top scopes with
        | None -> ()
        | Some scope ->
            let n_new = List.length scope.vars - vars_before in
            if n_new > 0 then (
              let raw = List.take scope.vars n_new in
              let new_vars =
                let filtered =
                  if Ain.version_gte ctx.ain (12, 0) then
                    (* v12: skip Array-typed dummies here. They live to
                       [end_scope] and the [Array.Free <slot>] fires
                       there. Per-statement cleanup would double-free
                       the slot's populated array.
                       Keep ONLY page-holding dummies (the types
                       [compile_delete_var] actually releases) — the
                       recorded list replays as raw [SH_LOCALDELETE]s
                       in if-branch cleanup, and a scalar spill (e.g.
                       the TitleMenu 右辺値参照化用 enum in SceneTitle@0's
                       parts lambda) holds a plain value: the 8-op
                       expansion's [REF; DELETE] frees whatever PAGE ID
                       that value names (title screen: pages 0..7 →
                       DG_CALL argument-page death). Original treats
                       such conditions as cleanup-free and uses the
                       no-replay if layout. *)
                    List.filter raw ~f:(fun (v : Ain.Variable.t) ->
                        match v.value_type with
                        | Array _ -> false
                        | IFace _ | Ref _ | Struct _ -> true
                        | _ -> false)
                  else raw
                in
                if Ain.version_gte ctx.ain (12, 0) then
                  List.sort filtered ~compare:(fun a b ->
                      Int.descending a.index b.index)
                else filtered
              in
              List.iter new_vars ~f:self#compile_delete_var;
              let new_idxs = List.map new_vars ~f:(fun v -> v.index) in
              last_condition_deleted_dummies <- new_idxs;
              inline_deleted_dummies <- new_idxs @ inline_deleted_dummies;
              match Stack.top cflow_stmts with
              | None -> ()
              | Some s ->
                  s.inline_deleted_dummies <-
                    new_idxs @ s.inline_deleted_dummies)

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

    method emit_inline_deleted_dummy_cleanup =
      if Ain.version ctx.ain > 8 then
        List.iter inline_deleted_dummies ~f:(fun idx ->
            self#write_instruction1 SH_LOCALDELETE idx)

    method emit_last_condition_dummy_cleanup =
      if Ain.version ctx.ain > 8 then
        List.iter last_condition_deleted_dummies ~f:(fun idx ->
            self#write_instruction1 SH_LOCALDELETE idx)

    method record_switch_break_deleted_vars idxs =
      if Ain.version ctx.ain > 8 then
        match Stack.top cflow_stmts with
        | Some ({ kind = CFlowSwitch _; _ } as s) ->
            let idxs = List.rev idxs in
            let idxs =
              List.filter idxs ~f:(fun idx ->
                  let v : Ain.Variable.t = self#get_local idx in
                  String.is_prefix v.name ~prefix:"<dummy")
            in
            let idxs =
              List.filter idxs ~f:(fun idx ->
                  not
                    (List.mem s.inline_deleted_dummies idx
                       ~equal:Int.equal))
            in
            let idxs =
              List.filter idxs ~f:(fun idx ->
                  not
                    (List.mem s.switch_break_deleted_dummies idx
                       ~equal:Int.equal))
            in
            s.switch_break_deleted_dummies <-
              s.switch_break_deleted_dummies @ idxs
        | _ -> ()

    (** Begin a loop. *)
    method start_loop continue_addr =
      Stack.push cflow_stmts
        {
          kind = CFlowLoop { continue_addr };
          break_addrs = [];
          continue_addrs = [];
          scopes_at_start = Stack.length scopes;
          inline_deleted_dummies = [];
          switch_break_deleted_dummies = [];
        }

    (** Begin a switch statement. *)
    method start_switch ty node =
      let op, case_type =
        match ty with
        | Jaf.Bool | Int | LongInt | Enum _ -> (SWITCH, Ain.Switch.IntCase)
        | String -> (STRSWITCH, Ain.Switch.StringCase)
        | _ -> compiler_bug "invalid switch type" (Some node)
      in
      let switch = Ain.add_switch ctx.ain case_type in
      Stack.push cflow_stmts
        {
          kind = CFlowSwitch switch;
          break_addrs = [];
          continue_addrs = [];
          scopes_at_start = Stack.length scopes;
          inline_deleted_dummies = [];
          switch_break_deleted_dummies = [];
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
             let deleted_dummies =
               s.inline_deleted_dummies @ s.switch_break_deleted_dummies
             in
             List.iter deleted_dummies ~f:(fun idx ->
                 self#write_instruction1 SH_LOCALDELETE idx);
             end_switch_deleted_dummies <-
               deleted_dummies @ end_switch_deleted_dummies);
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

    (** Emit a 'continue' jump for the innermost enclosing loop. If the loop's
        continue target is not yet known (do-while), the jump operand location
        is recorded for later patching. *)
    method add_continue node =
      let nearest_loop =
        Stack.find cflow_stmts ~f:(function
          | { kind = CFlowLoop _; _ } -> true
          | _ -> false)
      in
      match nearest_loop with
      | Some { kind = CFlowLoop { continue_addr }; _ } when continue_addr >= 0
        ->
          self#write_instruction1 JUMP continue_addr
      | Some loop ->
          loop.continue_addrs <- (current_address + 2) :: loop.continue_addrs;
          self#write_instruction1 JUMP 0
      | None -> compile_error "'continue' statement outside of loop" node

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

    (* Feed a 32-bit word into the running CRC. *)
    method private crc_push_word n = crc_state <- Crc32.feed_word crc_state n

    (* Hash a label/goto's qualified name "FuncName::labelName" into the CRC. *)
    method private crc_push_label_name label =
      let name = (Option.value_exn current_function).name ^ "::" ^ label in
      crc_state <- Crc32.feed_string crc_state name

    (** Element-type code for the [Array] HLL's polymorphic-type
        operand. Used as the third operand of [CALLHLL Array.*] in
        v11; [-1] when the receiver isn't actually an array. *)
    method array_element_type_code (ty : Jaf.jaf_type) =
      match ty with
      | Array t | Ref (Array t) ->
          Ain.Type.int_of_data_type (Ain.version ctx.ain)
            (jaf_to_ain_type ~ctx t)
      | _ -> -1

    method array_element_type_code_for_expr (e : expression) =
      let from_ain_type = function
        | Ain.Type.Array Ain.Type.HLLParam | Ref (Array Ain.Type.HLLParam) ->
            self#array_element_type_code e.ty
        | Ain.Type.Array t | Ref (Array t) ->
            Ain.Type.int_of_data_type (Ain.version ctx.ain) t
        | _ -> self#array_element_type_code e.ty
      in
      let rec loop (e : expression) =
        match e.node with
        | Cast (_, inner) | RvalueRef inner | DummyRef (_, inner) -> loop inner
        | Call (_, Some receiver :: _, HLLCall _) -> (
            match self#array_element_type_code e.ty with
            | -1 | 74 -> loop receiver
            | t -> t)
        | Ident (_, LocalVariable (i, _)) ->
            let v : Ain.Variable.t = self#get_local i in
            from_ain_type v.value_type
        | Ident (_, GlobalVariable i) ->
            let v : Ain.Variable.t = Ain.get_global_by_index ctx.ain i in
            from_ain_type v.value_type
        | Member (_, _, ClassVariable _) -> from_ain_type (self#member_type e)
        | Member ({ node = This; _ }, member_name, _) -> (
            match current_function with
            | Some f -> (
                match String.lsplit2 f.name ~on:'@' with
                | Some (class_name, _) -> (
                    match Ain.get_struct ctx.ain class_name with
                    | Some s -> (
                        match
                          List.find s.members ~f:(fun (v : Ain.Variable.t) ->
                              String.equal v.name member_name
                              || String.equal v.name ("<" ^ member_name ^ ">"))
                        with
                        | Some v -> from_ain_type v.value_type
                        | None -> self#array_element_type_code e.ty)
                    | None -> self#array_element_type_code e.ty)
                | None -> self#array_element_type_code e.ty)
            | None -> self#array_element_type_code e.ty)
        | _ -> self#array_element_type_code e.ty
      in
      loop e

    method emit_interface_vtable_init class_index =
      if Ain.version_gte ctx.ain (12, 0) then
        let s = Ain.get_struct_by_index ctx.ain class_index in
        if not (List.is_empty s.interfaces) then (
          let vtable_slot =
            List.find_mapi s.members ~f:(fun i (v : Ain.Variable.t) ->
                if String.equal v.name "<vtable>" then Some i else None)
          in
          match vtable_slot with
          | None -> ()
          | Some vtable_slot ->
              let total_methods =
                List.fold s.interfaces ~init:0
                  ~f:(fun acc (iface : Ain.Struct.interface) ->
                    let iface_s =
                      Ain.get_struct_by_index ctx.ain iface.struct_type
                    in
                    acc + List.length iface_s.vmethods)
              in
              match
                ( Ain.get_library_index ctx.ain "Array",
                  Ain.get_library_index ctx.ain "Array"
                  |> Option.bind ~f:(fun lib_no ->
                         Ain.get_library_function_index ctx.ain lib_no
                           "Alloc") )
              with
              | Some array_lib, Some array_alloc ->
                  let vtable = Array.create ~len:total_methods 0 in
                  List.iter s.interfaces
                    ~f:(fun (iface : Ain.Struct.interface) ->
                      let iface_s =
                        Ain.get_struct_by_index ctx.ain iface.struct_type
                      in
                      List.iteri iface_s.vmethods
                        ~f:(fun i iface_fn_idx ->
                          let iface_fn =
                            Ain.get_function_by_index ctx.ain iface_fn_idx
                          in
                          let prefix = iface_s.name ^ "@" in
                          let short_name =
                            if String.is_prefix iface_fn.name ~prefix then
                              String.chop_prefix_exn iface_fn.name ~prefix
                            else iface_fn.name
                          in
                          let same_shape (owner : Ain.Struct.t)
                              (candidate : Ain.Function.t) =
                            let candidate_short =
                              let prefix = owner.name ^ "@" in
                              if String.is_prefix candidate.name ~prefix then
                                String.chop_prefix_exn candidate.name ~prefix
                              else candidate.name
                            in
                            String.equal candidate_short short_name
                            && Int.equal candidate.nr_args iface_fn.nr_args
                          in
                          let iface_rank =
                            List.take iface_s.vmethods i
                            |> List.count ~f:(fun prev_idx ->
                                   let prev =
                                     Ain.get_function_by_index ctx.ain prev_idx
                                   in
                                   same_shape iface_s prev)
                          in
                          let iface_group_count =
                            List.count iface_s.vmethods ~f:(fun idx ->
                                let fn =
                                  Ain.get_function_by_index ctx.ain idx
                                in
                                same_shape iface_s fn)
                          in
                          let reverse_duplicate_group =
                            String.is_suffix short_name ~suffix:"::get"
                            || String.is_suffix short_name ~suffix:"::set"
                          in
                          let impl_rank =
                            if reverse_duplicate_group then
                              Int.max 0 (iface_group_count - 1 - iface_rank)
                            else iface_rank
                          in
                          let impl_idx =
                            let rank = ref 0 in
                            let from_vmethods =
                              List.find_map s.vmethods ~f:(fun impl_idx ->
                                  let impl_fn =
                                    Ain.get_function_by_index ctx.ain impl_idx
                                  in
                                  if same_shape s impl_fn then
                                    if Int.equal !rank impl_rank then
                                      Some impl_idx
                                    else (
                                      Int.incr rank;
                                      None)
                                  else None)
                            in
                            match from_vmethods with
                            | Some _ -> from_vmethods
                            | None ->
                                let matches = ref [] in
                                Ain.function_iter ctx.ain ~f:(fun impl_fn ->
                                    if same_shape s impl_fn then
                                      matches := impl_fn.index :: !matches);
                                List.rev !matches |> Fn.flip List.nth impl_rank
                          in
                          match impl_idx with
                          | Some impl_idx ->
                              vtable.(iface.vtable_offset + i) <- impl_idx
                          | None -> ()));
                  self#write_instruction0 PUSHSTRUCTPAGE;
                  self#write_instruction1 PUSH vtable_slot;
                  self#write_instruction0 REF;
                  self#write_instruction0 DUP;
                  self#write_instruction1 PUSH total_methods;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction3 CALLHLL array_lib array_alloc 10;
                  Array.iteri vtable ~f:(fun i impl_idx ->
                      self#write_instruction0 DUP;
                      self#write_instruction1 PUSH i;
                      self#write_instruction1 PUSH impl_idx;
                      self#write_instruction0 ASSIGN;
                      self#write_instruction0 POP);
                  self#write_instruction0 POP
              | _ -> ())

    method private ensure_v12_dummy_slot_initialized var_no =
      (* EXPERIMENTAL: disabled. diff_opcodes showed sys4lang emits the
         5-opcode pattern [PUSHLOCALPAGE; PUSH var; PUSH -1; ASSIGN; POP]
         ~15,495 times more than the original Rance10.ain. The
         original doesn't emit this pre-init and works at runtime.
         Removing the pre-init brings the bytecode closer to orig.

         Earlier observation noted that disabling for Ref/Struct
         broke menu/survey at runtime, but that was caused by the
         IFace last-use cleanup landing as dead code after RETURN
         (now fixed in [emit_v12_last_use_cleanup]). With that fixed,
         the dummy-init disable should also be safe. *)
      ignore var_no;
      ()

    method write_instruction0 op =
      (* v12 dropped three delegate shorthand opcodes. Original v12 emits
         these expansions (verified by dasm comparison against original
         Rance10):

         - [DG_CLEAR] (0xF8): clear a delegate-typed slot.
             stack before: [dg_lvalue_pageref]
             v12 form: DG_NEW (push empty dg); DG_ASSIGN; DELETE

         - [DG_SET] (0xF2): assign single method to delegate.
             stack before: [dg_lvalue_pageref, page=-1, method_idx]
             v12 form: DG_NEW_FROM_METHOD; DG_ASSIGN; DELETE
             (the [-1, method_idx] pair already feeds DG_NEW_FROM_METHOD)

         - [DG_ERASE] (0xF7): erase single method from delegate.
             stack before: [dg_lvalue_pageref, method_idx]
             v12 form: PUSH -1; SWAP; DG_NEW_FROM_METHOD; DG_MINUSA; DELETE
             (need to inject the [-1] page argument under method_idx)

         Pre-v12 keeps emitting the shorthand for byte-stability. *)
      if Ain.version_gte ctx.ain (12, 0) then (
        match op with
        | DG_CLEAR ->
            self#write_instruction0 DG_NEW;
            self#write_instruction0 DG_ASSIGN;
            self#write_instruction0 DELETE
        | DG_SET ->
            self#write_instruction0 DG_NEW_FROM_METHOD;
            self#write_instruction0 DG_ASSIGN;
            self#write_instruction0 DELETE
        | DG_ERASE ->
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 SWAP;
            self#write_instruction0 DG_NEW_FROM_METHOD;
            self#write_instruction0 DG_MINUSA;
            self#write_instruction0 DELETE
        | _ ->
            CBuffer.write_int16 buffer (int_of_opcode op);
            self#crc_push_word (int_of_opcode op);
            current_address <- current_address + 2)
      else (
        CBuffer.write_int16 buffer (int_of_opcode op);
        self#crc_push_word (int_of_opcode op);
        current_address <- current_address + 2)

    (* v12 dropped [CHECKUDO] (opcode 0x78) — the VM rejects it at execute
       time with "undefined opcode 120". The original v12 compiler emits
       [DELETE] (0x77) in the same positions (slot release before reassign).
       Pre-v12 keeps emitting [CHECKUDO] for byte-stability. *)
    method emit_slot_release =
      if Ain.version_gte ctx.ain (12, 0) then self#write_instruction0 DELETE
      else self#write_instruction0 CHECKUDO

    method write_instruction1 op arg0 =
      match op with
      | SH_STRUCTREF when Ain.version_lt ctx.ain (1, 0) ->
          (* ain v0 encodes SH_STRUCTREF as 0x62 (which is EOF from v1 on). *)
          CBuffer.write_int16 buffer 0x62;
          self#crc_push_word 0x62;
          CBuffer.write_int32 buffer arg0;
          current_address <- current_address + 6
      | S_MOD when Ain.version_lt ctx.ain (11, 0) ->
          self#write_instruction1 PUSH arg0;
          self#write_instruction0 S_MOD
      | _ ->
          (* v12 dropped [SH_LOCALDELETE n] (opcode 0x82). Original v12
             uses an 8-instruction sequence that releases the held value
             AND nulls the slot, so the VM's auto-cleanup on function exit
             doesn't double-release:

               PUSHLOCALPAGE; PUSH n; DUP2; REF; DELETE;
               PUSH -1; ASSIGN; POP

             The DUP2 keeps a copy of the (page,slot) lvalue on the stack
             for the ASSIGN at the end. SH_LOCALDELETE call sites in our
             codegen are all for Ref / Struct slots, so PUSH -1 (NULL
             page-ref sentinel) is the right empty value. *)
          if Ain.version_gte ctx.ain (12, 0) && phys_equal op SH_LOCALDELETE
          then (
            self#write_instruction0 PUSHLOCALPAGE;
            self#write_instruction1 PUSH arg0;
            self#write_instruction0 DUP2;
            self#write_instruction0 REF;
            self#write_instruction0 DELETE;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 ASSIGN;
            self#write_instruction0 POP)
          else (
            CBuffer.write_int16 buffer (int_of_opcode op);
            self#crc_push_word (int_of_opcode op);
            CBuffer.write_int32 buffer arg0;
            current_address <- current_address + 6)

    method write_instruction1_float op arg0 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      self#crc_push_word (int_of_opcode op);
      CBuffer.write_float buffer arg0;
      current_address <- current_address + 6

    method write_instruction2 op arg0 arg1 =
      (* v12 dropped [SH_LOCALCREATE n sno] (opcode 0x81). Original v12
         emits [PUSHLOCALPAGE; PUSH n; NEW sno -1; ASSIGN; POP], using
         ctor=-1 even when a constructor exists — the v12 VM does default
         init for -1.

         The preceding [SH_LOCALDELETE] (which we already expand to the
         8-instr release-and-null sequence) leaves the slot at -1, so this
         expansion just creates the fresh struct and stores it. Original
         combines both into an 11-instr sequence; we emit them separately
         (~21 instr total) for simplicity — semantically equivalent. *)
      if Ain.version_gte ctx.ain (12, 0) && phys_equal op SH_LOCALCREATE
      then (
        self#write_instruction0 PUSHLOCALPAGE;
        self#write_instruction1 PUSH arg0;
        self#write_instruction0 DUP2;
        self#write_instruction0 REF;
        self#write_instruction0 DELETE;
        self#write_instruction0 DUP2;
        self#write_instruction2 NEW arg1 (-1);
        self#write_instruction0 ASSIGN;
        self#write_instruction0 POP;
        self#write_instruction0 POP;
        self#write_instruction0 POP)
      else (
        CBuffer.write_int16 buffer (int_of_opcode op);
        self#crc_push_word (int_of_opcode op);
        CBuffer.write_int32 buffer arg0;
        CBuffer.write_int32 buffer arg1;
        current_address <- current_address + 10)

    method write_instruction3 op arg0 arg1 arg2 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      self#crc_push_word (int_of_opcode op);
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
      | IFace _ when Ain.version_gte ctx.ain (12, 0) ->
          self#write_instruction0 PUSHLOCALPAGE;
          self#write_instruction1 PUSH v.index;
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction0 DELETE;
          self#write_instruction1 PUSH (-1);
          self#write_instruction0 ASSIGN;
          self#write_instruction0 POP
      | (Ref _ | Struct _) when Ain.version_gte ctx.ain (12, 0) ->
          (* v12 dropped [SH_LOCALDELETE] (per [v12-dropped-opcodes]).
             Emit the same 8-op expansion as the IFace arm so dummy
             Ref-Struct slots get the proper temp-slot cleanup orig
             emits after [this.X = new T()] property setter consumes
             the value. *)
          self#write_instruction0 PUSHLOCALPAGE;
          self#write_instruction1 PUSH v.index;
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction0 DELETE;
          self#write_instruction1 PUSH (-1);
          self#write_instruction0 ASSIGN;
          self#write_instruction0 POP
      | Ref _ | Struct _ -> self#write_instruction1 SH_LOCALDELETE v.index
      | Array _ when Ain.version ctx.ain > 8 -> (
          match Ain.get_library_index ctx.ain "Array" with
          | Some lib_no -> (
              match Ain.get_library_function_index ctx.ain lib_no "Free" with
              | Some fun_no ->
                  let elem_type =
                    ain_to_jaf_type ctx.ain v.value_type
                    |> self#array_element_type_code
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

    method private add_local_use uses i =
      if List.mem uses i ~equal:Int.equal then uses else i :: uses

    method private local_uses_expr uses (e : expression) =
      let opt_expr uses = function
        | Some e -> self#local_uses_expr uses e
        | None -> uses
      in
      let opt_exprs uses es = List.fold es ~init:uses ~f:opt_expr in
      match e.node with
      | Ident (_, LocalVariable (i, _)) -> self#add_local_use uses i
      | Ident _ | FuncAddr _ | MemberAddr _ | This | Null | ConstInt _
      | ConstFloat _ | ConstChar _ | ConstString _ | New _ ->
          uses
      | DummyRef (i, e) ->
          (* The DummyRef binds a hidden local slot [i] (the dummy) to
             hold the inner expression's value. Treat the slot itself
             as used here so [emit_v12_last_use_cleanup] can release
             IFace dummies at their last-use statement, matching orig's
             pattern of emitting [PUSHLOCALPAGE; PUSH i; DUP2; REF;
             DELETE; ...] immediately after the call that fills the
             dummy. Without this the dummy survives past RETURN and
             Rance10.exe's RETURN handler rejects the local-page free. *)
          self#local_uses_expr (self#add_local_use uses i) e
      | Unary (_, e) | Cast (_, e) | RvalueRef e
      | OptionalMember (e, _, _) | Member (e, _, _) ->
          self#local_uses_expr uses e
      | Binary (_, a, b) | Assign (_, a, b) | Seq (a, b)
      | NullCoalesce (a, b) | Subscript (a, b) ->
          self#local_uses_expr (self#local_uses_expr uses a) b
      | Ternary (a, b, c) ->
          self#local_uses_expr
            (self#local_uses_expr (self#local_uses_expr uses a) b)
            c
      | Call (callee, args, _) ->
          opt_exprs (self#local_uses_expr uses callee) args
      | NewCall (_, args) -> opt_exprs uses args
      | ArrayLiteral es -> List.fold es ~init:uses ~f:self#local_uses_expr
      | Lambda _ -> uses

    method private local_uses_stmt uses (stmt : statement) =
      let opt_expr uses = function
        | Some e -> self#local_uses_expr uses e
        | None -> uses
      in
      let stmt_uses uses s = self#local_uses_stmt uses s in
      match stmt.node with
      | EmptyStatement | Label _ | Goto _ | Continue | Break | Default
      | Jump _ | Message _ ->
          uses
      | Declarations decls ->
          List.fold decls.vars ~init:uses ~f:(fun uses v ->
              opt_expr
                (List.fold v.array_dim ~init:uses ~f:self#local_uses_expr)
                v.initval)
      | Expression e | Case e | Jumps e -> self#local_uses_expr uses e
      | Compound stmts | Switch (_, stmts) ->
          List.fold stmts ~init:uses ~f:stmt_uses
      | If (test, con, alt) ->
          stmt_uses (stmt_uses (self#local_uses_expr uses test) con) alt
      | While (test, body) | DoWhile (test, body) ->
          stmt_uses (self#local_uses_expr uses test) body
      | For (init, test, incr, body) ->
          stmt_uses (opt_expr (opt_expr (stmt_uses uses init) test) incr) body
      | ForEach (_, _, _, container, body) ->
          stmt_uses (self#local_uses_expr uses container) body
      | Return e -> opt_expr uses e
      | RefAssign (lhs, rhs) | ObjSwap (lhs, rhs) ->
          self#local_uses_expr (self#local_uses_expr uses lhs) rhs

    method private should_v12_last_use_cleanup i =
      Ain.version_gte ctx.ain (12, 0)
      && (not (List.mem inline_deleted_dummies i ~equal:Int.equal))
      && (not (List.mem v12_last_use_deleted_vars i ~equal:Int.equal))
      &&
      let f = Option.value_exn current_function in
      i >= f.nr_args
      &&
      let local = self#get_local i in
      (* IFace DUMMIES only — anonymous compile-time temps.

         Named IFace source-locals (e.g. [ILayoutBoxParts LayoutBox]
         in [CEnqueteView::InitLayout]) must NOT be last-use cleaned
         here: this method runs per-statement inside nested blocks
         and its [future_stmts] argument only covers the SIBLING
         remaining statements at the same block depth. A named local
         used inside an inner [if]-block but then used again AFTER
         the [if]-block looks "last-used" within the inner block, and
         we'd zero it just before the outer code tries to read it
         — observed runtime crash: survey's [LayoutBox.Core.Number]
         hits REF Page=-1 because [LayoutBox] was zeroed inside the
         preceding [if (LayoutBox.IsExistLayoutChild(...)) {...}]
         block.

         Dummy slots are safe because their lifetime is always the
         single expression that filled them — the source AST never
         references a dummy slot across statement boundaries. *)
      String.is_prefix local.name ~prefix:"<dummy"
      &&
      match local.value_type with
      | IFace _ -> true
      | _ -> false

    method private emit_v12_last_use_cleanup stmt future_stmts =
      if Ain.version_gte ctx.ain (12, 0)
         && not (self#statement_guaranteed_returns stmt)
      then
        (* Skip last-use cleanup when the statement guarantees its own
           RETURN — any cleanup emitted here lands after the RETURN as
           dead code that diverges from orig's bytecode and audit-
           regresses property getters like
           [CInfoText@GetPartsNumber]. The slots will be released by
           the VM's RETURN local-page free anyway. *)
        let current_uses = self#local_uses_stmt [] stmt in
        let future_uses =
          List.fold future_stmts ~init:[] ~f:self#local_uses_stmt
        in
        current_uses
        |> List.filter ~f:(fun i ->
               (not (List.mem future_uses i ~equal:Int.equal))
               && self#should_v12_last_use_cleanup i)
        |> List.iter ~f:(fun i ->
               self#compile_delete_var (self#get_local i);
               v12_last_use_deleted_vars <- i :: v12_last_use_deleted_vars)

    (** Walk lambda parent chain from [name]. The lambda-name pattern is
        [...<lambda : PARENT(line, col)>], possibly nested when a lambda
        is defined inside another lambda. Returns the list of enclosing
        ain functions, parent-first, so [List.nth result (level - 1)]
        gives the function whose local slot a CapturedVariable references. *)
    method find_lambda_parents (name : string) : Ain.Function.t list =
      let prefix = "<lambda : " in
      (* The function name in the ain table omits both the signature
         and the (line, col) suffix that the lambda-name embeds:
         [Class@Method(arg_types)(line, col)] → [Class@Method]. Strip
         trailing balanced [(...)] groups one at a time and look up at
         each step. When a strip reveals a signature like [(string)],
         use it to disambiguate overloads — looking up by bare name
         alone returns the FIRST matching overload, which for e.g.
         [Find(string)] vs [Find(int, int)] silently picks the wrong
         one. The wrong parent's [vars[0]] then has a different type
         than the captured variable, and [compile_dereference] emits
         the wrong dereference pattern (e.g. drops [A_REF] for String
         because the parent slot looked like [Int]). That manifests as
         a refcount leak in the captured string at lambda RETURN. *)
      let strip_one_paren_group body =
        let len = String.length body in
        if len > 0 && Char.equal body.[len - 1] ')' then
          let rec find_open i depth =
            if i < 0 then None
            else
              match body.[i] with
              | ')' -> find_open (i - 1) (depth + 1)
              | '(' when depth = 1 -> Some i
              | '(' -> find_open (i - 1) (depth - 1)
              | _ -> find_open (i - 1) depth
          in
          match find_open (len - 1) 0 with
          | Some i ->
              Some
                ( String.sub body ~pos:0 ~len:i,
                  String.sub body ~pos:(i + 1) ~len:(len - i - 2) )
          | None -> None
        else None
      in
      let parent_signature (f : Ain.Function.t) =
        List.take f.vars f.nr_args
        |> List.map ~f:(fun (v : Ain.Variable.t) ->
               Jaf.jaf_type_to_string (ain_to_jaf_type ctx.ain v.value_type))
        |> String.concat ~sep:", "
      in
      let lookup_by_name_and_sig bare_name sig_str =
        let result = ref None in
        Ain.function_iter ctx.ain ~f:(fun (f : Ain.Function.t) ->
            if Option.is_none !result
               && String.equal f.name bare_name
               && String.equal (parent_signature f) sig_str
            then result := Some f);
        !result
      in
      let rec lookup_parent body =
        match Ain.get_function ctx.ain body with
        | Some f -> Some f
        | None -> (
            match strip_one_paren_group body with
            | Some (shorter, sig_str) -> (
                (* Signature-disambiguated lookup; the [sig_str] only
                   resolves to a real overload after [(line, col)] has
                   already been stripped, so this short-circuits the
                   right level of the recursion. *)
                match lookup_by_name_and_sig shorter sig_str with
                | Some f -> Some f
                | None -> lookup_parent shorter)
            | None -> None)
      in
      let rec walk acc cur_name =
        match String.substr_index cur_name ~pattern:prefix with
        | None -> List.rev acc
        | Some start ->
            let body_start = start + String.length prefix in
            let len = String.length cur_name in
            let rec find_close i depth =
              if i >= len then None
              else
                match cur_name.[i] with
                | '<' -> find_close (i + 1) (depth + 1)
                | '>' when depth = 0 -> Some i
                | '>' -> find_close (i + 1) (depth - 1)
                | _ -> find_close (i + 1) depth
            in
            (match find_close body_start 0 with
            | None -> List.rev acc
            | Some close ->
                let body =
                  String.sub cur_name ~pos:body_start
                    ~len:(close - body_start)
                in
                match lookup_parent body with
                | None -> List.rev acc
                | Some parent -> walk (parent :: acc) body)
      in
      walk [] name

    (** Emit the code to put the value of a variable onto the stack (including
        member variables and array elements). Assumes a page + page-index is
        already on the stack. *)
    method compile_dereference (t : Ain.Type.t) =
      match t with
      (* v12 [Wrap (IFace _)] rvalue: emit a single [REFREF] so the
         unwrap leaves the 2-slot iface fat-ref [page, offset] on the
         stack. The consumer (dispatch, comparison) adds the right
         deref pattern. *)
      | Wrap (IFace _) when Ain.version_gte ctx.ain (12, 0) ->
          self#write_instruction0 REFREF
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
      | Ref (Int | Float | Bool | LongInt | Enum _ | FuncType _) ->
          self#write_instruction0 REFREF;
          self#write_instruction0 REF
      | Int | Float | Bool | LongInt | Enum _ | FuncType _ ->
          self#write_instruction0 REF
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
          (* ain v0/v1 has no A_REF; array rvalues are passed by reference
             without a deep copy. *)
          if ctx.version > 100 then self#write_instruction0 A_REF
      | IFace _ when Ain.version_gte ctx.ain (12, 0) ->
          self#write_instruction0 REFREF
      | (Struct _ | Ref (Struct _) | Ref (IFace _))
        when Ain.version ctx.ain > 8 ->
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
      | Unknown87 _ | IFace _ | Enum2 _ | HLLFunc | Unknown98
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
          let elem_is_v12_iface =
            match e.ty with
            | Struct (name, _) | Wrap (Struct (name, _)) ->
                Ain.version_gte ctx.ain (12, 0)
                && Hashtbl.mem ctx.interface_names name
            | _ -> false
          in
          (* v12 iface arrays are flat two-slot pairs: element [i] lives
             at slot [2i]. orig folds the doubling for constant indices
             ([PUSH 0] / [PUSH 2]), scaling at runtime only for computed
             ones. *)
          (match (elem_is_v12_iface, index.node) with
          | true, ConstInt n -> self#write_instruction1 PUSH (2 * n)
          | true, _ ->
              self#compile_expression index;
              self#write_instruction1 PUSH 2;
              self#write_instruction0 MUL
          | false, _ -> self#compile_expression index)
      (* v12 cast wrappers around a variable / member ref are no-ops at
         codegen — pass through to the inner expression's lvalue. *)
      | Cast (_, inner) -> self#compile_variable_ref inner
      | _ -> compiler_bug "Invalid variable ref" (Some (ASTExpression e))

    method compile_delete_ref _ty =
      self#write_instruction0 DUP2;
      self#write_instruction0 REF;
      self#write_instruction0 DELETE

    (** Emit the code to put a location (variable, struct member, or array
        element) onto the stack, e.g. to prepare for an assignment or to pass a
        variable by reference. *)
    method compile_lvalue (e : expression) =
      let compile_lvalue_after (t : Ain.Type.t) =
        match t with
        | Wrap (Int | Float | Bool | LongInt) -> self#write_instruction0 REFREF
        | Wrap String ->
            self#write_instruction0 REFREF;
            self#write_instruction0 REF
        | Wrap (IFace _) when Ain.version_gte ctx.ain (12, 0) ->
            (* v12 [Wrap (IFace _)] lvalue: emit a single [REFREF] so
               the unwrap leaves the 2-slot iface fat-ref [page, offset]
               on the stack. The consumer (method dispatch, comparison,
               etc.) then adds the right deref pattern. Previously this
               emitted [REFREF; REF] (or [REFREF; REFREF] for I-prefix
               names) which over- or under-derefs depending on the
               consumer. *)
            self#write_instruction0 REFREF
        | Ref (Int | Float | Bool | LongInt) -> self#write_instruction0 REFREF
        | Ref (String | Array _ | Struct _ | Delegate _) ->
            self#write_instruction0 REF
        | IFace _ when Ain.version_gte ctx.ain (12, 0) ->
            self#write_instruction0 REFREF
        | String | Array _ | Struct _ | Delegate _ ->
            self#write_instruction0 REF
        | _ -> ()
      in
      match e.node with
      | Ident (_, LocalVariable (i, _)) -> (
          match self#get_local i with
          | {
           value_type =
             ( String | Array _ | Struct _
             | Ref (String | Array _ | Struct _ | Delegate _) );
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
             ( String | Array _ | Struct _
             | Ref (String | Array _ | Struct _ | Delegate _) );
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
              ( Ref (String | Array _ | Struct _ | Delegate _)
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
          let elem_is_v12_iface =
            match e.ty with
            | Struct (name, _) | Wrap (Struct (name, _)) ->
                Ain.version_gte ctx.ain (12, 0)
                && Hashtbl.mem ctx.interface_names name
            | _ -> false
          in
          (* iface pair-slot indexing: fold [2i] for constant indices
             like orig (see compile_variable_ref). *)
          (match (elem_is_v12_iface, index.node) with
          | true, ConstInt n -> self#write_instruction1 PUSH (2 * n)
          | true, _ ->
              self#compile_expression index;
              self#write_instruction1 PUSH 2;
              self#write_instruction0 MUL
          | false, _ -> self#compile_expression index);
          if elem_is_v12_iface then
            (* An iface element VALUE is the two-slot fat-ref: orig
               reads it with [REFREF]. [compile_lvalue_after] can't
               know (the jaf type is a plain [Struct]; the iface-ness
               lives in [ctx.interface_names]) and emitted a one-slot
               [REF] — the dispatch dance then ran one slot short and
               the CALLMETHOD receiver was garbage
               ([BattleSkillSelector@ShowCardButton]'s
               [m_button[m_state].SetShowCardOne(...)]; first battle
               skill use died 【 REF 】要素数 = -1 inside the callee). *)
            self#write_instruction0 REFREF
          else compile_lvalue_after (jaf_to_ain_type e.ty)
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression e))
      | NewCall ({ ty = Struct (struct_name, s_no); _ }, args)
        when Ain.version ctx.ain > 8 ->
          (* v12 [new T(args)] as a method receiver / ref-assign
             target: emit constructor args before [NEW], leaving the
             new struct page-ref on the stack. *)
          self#compile_newcall struct_name s_no args
      | NewCall _ ->
          compiler_bug "NewCall as lvalue — needs dummy-ref lowering"
            (Some (ASTExpression e))
      | ArrayLiteral _ ->
          (* v12 [[…].Method(…)] — array literal as a method receiver.
             Push a [-1] sentinel. v12-wip stub. *)
          self#write_instruction1 PUSH (-1)
      | DummyRef (var_no, ref_expr) -> (
          self#scope_add_var (self#get_local var_no);
          let call_returns_ref =
            match self#ain_call_return_type ref_expr with
            | Some (Ain.Type.Ref _ | Ain.Type.IFace _) -> true
            | _ -> false
          in
          let dummy_is_iface =
            match (self#get_local var_no).value_type with
            | Ain.Type.IFace _ when Ain.version_gte ctx.ain (12, 0) -> true
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
              self#ensure_v12_dummy_slot_initialized var_no;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#emit_slot_release;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              let ctor = self#receiver_new_ctor s_no in
              self#write_instruction2 NEW s_no ctor;
              self#write_instruction0 ASSIGN;
              if Ain.version_lt ctx.ain (12, 0) then
                self#write_instruction0 A_REF
          (* v12 [new T(args)] in a DummyRef: prepare the dummy slot,
             release any previous value, then assign the constructed
             page-ref into the slot. *)
          | { node = NewCall ({ ty = Struct (struct_name, s_no); _ }, args); _ }
            when Ain.version ctx.ain > 8 ->
              self#ensure_v12_dummy_slot_initialized var_no;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#emit_slot_release;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#compile_newcall struct_name s_no args;
              self#write_instruction0 ASSIGN;
              if Ain.version_lt ctx.ain (12, 0) then
                self#write_instruction0 A_REF
          | { node = ArrayLiteral elems; ty = Array _; _ }
            when Ain.version ctx.ain > 8 ->
              (* v12: when the literal is the return value (e.g.
                 [return [];]), the slot's array escapes via [SP_INC]
                 and must NOT be cleaned at scope exit — drop the
                 dummy from [scope.vars] (matches historical behaviour).
                 Otherwise keep it so [end_scope] emits the
                 [Array.Free <slot>] orig requires to release the
                 populated array at branch exit. *)
              let drop_from_scope =
                Ain.version_lt ctx.ain (12, 0) || is_in_return_expr
              in
              if drop_from_scope then (
                match Stack.top scopes with
                | Some scope ->
                    scope.vars <-
                      List.filter scope.vars ~f:(fun v ->
                          not (Int.equal v.index var_no))
                | None -> ());
              let elem_ty = self#array_element_type_code ref_expr.ty in
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#write_instruction0 DUP;
              self#compile_CALLHLL "Array" "Free" elem_ty
                (ASTExpression ref_expr);
              List.iter elems ~f:(fun elem ->
                  self#write_instruction0 DUP;
                  self#emit_array_literal_element elem;
                  self#compile_CALLHLL "Array" "PushBack" elem_ty
                    (ASTExpression ref_expr));
              self#write_instruction0 A_REF
          | { node =
                NullCoalesce
                  (({ node = Call _; _ } as option_call), { node = Null; _ });
              _ }
            when Ain.version_gte ctx.ain (12, 0) -> (
              match self#ain_call_return_type option_call with
              | Some (Ain.Type.Option _) ->
                  self#compile_expression option_call;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let null_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction0 SWAP;
                  self#write_instruction1 PUSH var_no;
                  self#write_instruction0 SWAP;
                  self#write_instruction0 ASSIGN;
                  self#write_instruction0 POP;
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction1 PUSH var_no;
                  let end_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at null_addr current_address;
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH 0;
                  self#write_address_at end_addr current_address
              | _ ->
                  compiler_bug
                    "DummyRef NullCoalesce expected option-returning call"
                    (Some (ASTExpression ref_expr)))
          | { node = Call ({ node = OptionalMember (obj, _, _); _ }, args,
                            MethodCall (_, method_no)); _ }
            when Ain.version_gte ctx.ain (12, 0) && dummy_is_iface ->
              let receiver_is_iface =
                match obj.ty with
                | Struct (name, _) | Ref (Struct (name, _)) ->
                    Hashtbl.mem ctx.interface_names name
                | _ -> false
              in
              let receiver_is_casted_iface =
                match obj.node with
                | Cast (Struct (name, _), _) | Cast (Ref (Struct (name, _)), _) ->
                    Hashtbl.mem ctx.interface_names name
                | _ -> false
              in
              self#compile_lvalue obj;
              if not receiver_is_casted_iface then
                self#write_instruction0
                  (if receiver_is_iface then DUP_U2 else DUP);
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifnz_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#compile_method_call_for_receiver ~prefer_first_duplicate:true
                obj.ty args method_no;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#write_instruction0 DELETE;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 DUP_U2;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifnz2_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#write_instruction1 PUSH 0;
              let jump_end_inner = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifnz2_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at jump_end_inner current_address;
              let jump_end_outer = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifnz_addr current_address;
              if receiver_is_iface || receiver_is_casted_iface then (
                self#write_instruction0 POP;
                self#write_instruction0 POP)
              else self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at jump_end_outer current_address;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifz_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH 0;
              self#write_address_at ifz_addr current_address
          | _
            when Ain.version ctx.ain > 8
                 && not
                      (is_ref_scalar ref_expr.ty
                      || dummy_is_iface
                      || (call_returns_ref && dummy_is_ref_scalar))
                 &&
                 (match ref_expr.ty with
                 | String | Struct _ | Array _ | Delegate _ | HLLParam
                 | Ref (String | Struct _ | Array _ | Delegate _ | HLLParam) ->
                     true
                 | _ -> false) ->
              (* v11 rvalue-into-dummy (non-scalar): variableAlloc
                 wrapped a non-referenceable rvalue so it can serve as a
                 [ref T] argument. Evaluate the rvalue first, release
                 whatever the dummy currently holds via [REF; CHECKUDO],
                 then SWAP-dance an [ASSIGN] so the stored value is
                 left on the stack for the surrounding caller / null
                 check. Original SDK: [.LOCALREF dummy; CHECKUDO;
                 .LOCALASSIGN2 dummy]. *)
              let emit_checkudo_assign () =
                self#ensure_v12_dummy_slot_initialized var_no;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH var_no;
                self#write_instruction0 REF;
                self#emit_slot_release;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction0 SWAP;
                self#write_instruction1 PUSH var_no;
                self#write_instruction0 SWAP;
                self#write_instruction0 ASSIGN
                (* EXPERIMENTAL: the earlier A_REF here (commit d508efa)
                   was emitted for all [String | Ref String] DummyRef
                   targets to balance refcount when consumers like
                   S_ADD decrement. But it OVER-emits for null-coalesce
                   (??) contexts where the IFZ null-check consumes the
                   stack copy without decrementing the string heap
                   refcount. The extra A_REF in [MenuContext@Init]
                   pumps the local-page refcount to 2 at RETURN
                   (xsystem4 logs: "RETURN local page still referenced
                   fno=20505 page_slot=31792 ref=2"), causing
                   downstream PAGE_COPY -1 when menu opens. Disabling
                   the A_REF here may re-introduce the boot-lambda
                   double-free in [ResultArmyCountView@<lambda
                   InitParts>], but that lambda only runs during the
                   results screen (later than menu/start). *)
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
                  self#compile_method_call_for_receiver
                    ~prefer_first_duplicate:true obj.ty args method_no;
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
          | _
            when Ain.version ctx.ain > 8
                 && (dummy_is_ref_scalar || dummy_is_iface) ->
              (* v11 ref-scalar (2 VM stack slots per ref value):
                 same pattern but with [DUP_X2; POP] in place of [SWAP]
                 to rotate through 2-slot values, and [R_ASSIGN]
                 instead of [ASSIGN]. *)
              self#ensure_v12_dummy_slot_initialized var_no;
              self#compile_expression ref_expr;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#emit_slot_release;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction0 R_ASSIGN
          | _ when Ain.version ctx.ain > 8 ->
              (* v12 scalar RvalueRef dummies are ordinary local slots.
                 Store the value, pop the assignment result, then leave
                 the dummy lvalue for the by-ref call argument. *)
              self#compile_expression ref_expr;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction0 SWAP;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 SWAP;
              (match ref_expr.ty with
              | Float -> self#write_instruction0 F_ASSIGN
              | LongInt -> self#write_instruction0 LI_ASSIGN
              | String -> self#write_instruction0 S_ASSIGN
              | _ -> self#write_instruction0 ASSIGN);
              self#write_instruction0 POP;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH var_no
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
          (* v12 interface NULL as an lvalue (e.g. [obj.IFaceProp =
             NULL] flowing through the setter param, which
             [compile_argument] handles via [compile_lvalue] for
             [IFace _] callee types). Push the two-slot interface
             null pair. *)
          | Struct (name, _)
            when Ain.version_gte ctx.ain (12, 0)
                 && Hashtbl.mem ctx.interface_names name ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH 0
          (* v12 [obj.Prop = NULL] flows NULL through a [ref T] setter
             param without the type-check NULL→T coercion firing —
             property setter rewrite happens after check_assign. Push
             the v11 single-slot null sentinel. *)
          | Struct _ | Array _ | String | Delegate _ | HLLParam
            when Ain.version ctx.ain > 8 ->
              self#write_instruction1 PUSH (-1)
          | NullType -> self#write_instruction1 PUSH (-1)
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
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_lvalue b
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
      (* v12 cast wrapping an lvalue-shaped expression is a no-op at
         codegen — recurse into the inner so the page-ref ends up on
         the stack with the same encoding. *)
      | Cast (dst_t, inner) ->
          self#compile_lvalue inner;
          (match (inner.ty, dst_t) with
          | (Struct (src_name, src_sno) | Ref (Struct (src_name, src_sno))),
            (Struct (dst_name, dst_sno) | Ref (Struct (dst_name, dst_sno)))
            when Ain.version_gte ctx.ain (12, 0)
                 && not (Int.equal src_sno dst_sno) ->
              let src_is_iface = Hashtbl.mem ctx.interface_names src_name in
              let dst_is_iface = Hashtbl.mem ctx.interface_names dst_name in
              if src_is_iface then (
                (* X_ICAST already produces the receiver shape expected by
                   v12 optional-call null checks.  Emitting a second
                   cast-local NULL normalization here leaves only a
                   sentinel for the outer CALLMETHOD selector to deref. *)
                self#write_instruction0 POP;
                self#write_instruction1 X_ICAST dst_sno)
              else if dst_is_iface then self#write_instruction1 X_ICAST dst_sno
          | _ -> ())
      (* v12 [primary ?? fallback] used as an lvalue (e.g. ref-param
         argument): collapse to the primary's lvalue. The fallback is
         a sentinel (-1, [], etc.) that the runtime won't reach when
         the primary resolves. v12-wip — round-trip drops the
         fallback.

         EXCEPT when the fallback is a constructible [new T(...)]
         (dummy-backed): the original null-checks the primary and
         builds the fallback in the null path — e.g. a ref-returning
         getter [return find(...) ?? new T(...)]
         (SceneQuestMapGetCardDialog@CardInstance::get). Dropping it
         returned NULL to callers that immediately dereference. *)
      | NullCoalesce (a, b) -> (
          (* Lvalue-position [a ?? b] (e.g. [ref T x = call() ?? fallback]):
             test the primary's page-ref against the -1 null sentinel and
             fall back to [b]'s page-ref. Every fallback shape
             compile_lvalue understands takes this protocol — dropping it
             silently loses the [?? b] (EnemyActionCollection@Require's
             [At(i) ?? m_defaultAction] assigned NULL act on a miss). *)
          match b.node with
          | ( DummyRef (_, { node = New _ | NewCall _; _ })
            | Member (_, _, ClassVariable _)
            | Ident (_, (LocalVariable _ | GlobalVariable _)) )
            when Ain.version_gte ctx.ain (12, 0) ->
              self#compile_lvalue a;
              self#write_instruction0 DUP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifz_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              self#compile_lvalue b;
              self#write_address_at ifz_addr current_address
          | _ -> self#compile_lvalue a)
      (* v12 user-bodied event used as an lvalue (e.g. receiver for
         [this.Event.Clear()]). When the class still has an auto-event
         backing field, use it; otherwise fall back to the sentinel
         stub used for backing-less user-bodied events. *)
      | Member (obj, event_name, ClassEvent ev) -> (
          let backing_name = "<" ^ event_name ^ ">" in
          match
            Hashtbl.find ctx.structs ev.event_class
            |> Option.bind ~f:(fun s -> Hashtbl.find s.members backing_name)
          with
          | Some member ->
              self#compile_lvalue obj;
              self#write_instruction1 PUSH (Option.value_exn member.index);
              compile_lvalue_after (jaf_to_ain_type ~ctx member.type_spec.ty)
          | None -> self#write_instruction1 PUSH (-1))
      (* v12 generic-receiver member access used as an lvalue
         (assignment target, etc.). Same sentinel stub as the rvalue
         path. v12-wip — round-trip drops the assignment. *)
      | Member (_, _, UnresolvedMember) when Poly.equal e.ty HLLParam ->
          self#write_instruction1 PUSH (-1)
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
          self#write_instruction0 DELETE
      | Int | Float | Bool | LongInt | Enum _ | FuncType _ | Ref _ | TyFunction _
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
          (* v12: a bare [new T(...)] passed directly to an HLL/method
             arg needs an A_REF after the NEW; ASSIGN. The callee (e.g.
             Array.PushBack) stores the page-ref but doesn't incref it;
             the local dummy holding the NEW result then SH_LOCALDELETEs
             the only ref and the underlying struct is freed before the
             array's later read. *)
          let bare_new_arg =
            Ain.version_gte ctx.ain (12, 0)
            &&
            let check (e : expression) =
              match e.node with
              | New _ | NewCall _ -> true
              | _ -> false
            in
            check expr
            || (match dummy_ref_inner expr with
                | Some inner -> check inner
                | None -> false)
          in
          match t with
          | (Struct _ | Array _) when Ain.version ctx.ain > 8 ->
              (* v11 struct / array arg: the language-level [Ref] is
                 collapsed by typeAnalysis, but the call site still
                 needs the page-ref. v12 [CALLHLL] takes ownership of
                 the arg's refcount (orig emits [A_REF] before every
                 such call — e.g. [Array.PushBack(arr, val)]). Without
                 bumping the local's refcount, the local dummy's later
                 release drops refcount to 0 and frees the page the
                 HLL just stored → dangling page-id → next DELETE
                 fires [DeletePage Page=N] (the
                 PlayerCardSkill/PlayerSkillEffect crash chain).
                 `needs_a_ref_for_consume` classifies New/NewCall as
                 Owned and DummyRef-wrapped ref-returning calls as
                 Borrowed; the OptionalMember-dispatched case is
                 reported as Stable (the optional path emits its own
                 null sentinel). *)
              self#compile_expression expr;
              (* v11+ borrowed-ref pass-through: DummyRef wrapping a
                 Call whose ain-level return is [Ref _] needs A_REF
                 before the consuming call, so the dummy's later
                 SH_LOCALDELETE doesn't drop the only owning ref.
                 [needs_a_ref_for_consume] handles the v12 cases
                 (incl. New/NewCall and lvalue-source struct/array);
                 the OR below restores the v11 case the helper's
                 version gate would otherwise drop — caught when
                 Ixseal boot crashed with DeletePage Page=43 after
                 the v12 helper migration. *)
              let v11_dummy_call_returns_ref =
                Ain.version ctx.ain > 8
                && (not (Ain.version_gte ctx.ain (12, 0)))
                &&
                let rec walk (e : expression) =
                  match e.node with
                  | DummyRef (_, ({ node = Call _; _ } as inner)) -> (
                      match self#ain_call_return_type inner with
                      | Some (Ain.Type.Ref _) -> true
                      | _ -> (
                          match inner.ty with
                          | Ref _ -> true
                          | _ -> false))
                  | Cast (_, inner) | RvalueRef inner -> walk inner
                  | _ -> false
                in
                walk expr
              in
              if
                (self#needs_a_ref_for_consume expr
                && not in_ref_elem_hll_store_arg)
                || v11_dummy_call_returns_ref
              then self#write_instruction0 A_REF
          | IFace _ when Ain.version_gte ctx.ain (12, 0) ->
              (* v12 interface arg: callee declares 2 slots (IFace +
                 <void>). Interface-typed values already carry both
                 slots through [compile_lvalue]; concrete struct values
                 need the implemented interface vtable offset appended. *)
              self#compile_lvalue expr;
              (* Foreach loop-vars over iface arrays are stored as
                 [Wrap (IFace _)]: compile_lvalue leaves the
                 wrap-handle location, and orig adds a second [REFREF]
                 to materialize the 2-slot fat-ref before the call
                 consumes it. Without it the delegate/method argument
                 frame is misaligned — SkillEffectExecuter@
                 InnerProcess's [PostProcessEvent(p)] degraded the
                 frame pump after the first battle skill effect and
                 the attack-effect overlay never finished. *)
              (match expr.node with
              | Ident (_, LocalVariable (i, _)) -> (
                  match (self#get_local i).value_type with
                  | Ain.Type.Wrap (Ain.Type.IFace _) ->
                      self#write_instruction0 REFREF
                  | _ -> ())
              | _ -> ());
              (match (expr.ty, t) with
              | (Struct (_, actual_sno) | Ref (Struct (_, actual_sno))), IFace iface_sno ->
                  if not (Int.equal actual_sno iface_sno) then
                    Option.iter
                      (self#interface_vtable_offset actual_sno iface_sno)
                      ~f:(fun offset -> self#write_instruction1 PUSH offset)
              | _ -> ())
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
          | Wrap _ when Ain.version_gte ctx.ain (12, 0) ->
              (* v12 property event ref parameters are encoded as
                 Wrap<T> + <void>. The callee wants the raw source
                 location (page, index), not the value produced by
                 compile_lvalue's dereference tail. *)
              if is_variable_ref expr.node then self#compile_variable_ref expr
              else self#compile_lvalue expr
          | Method ->
              (* XXX: for delegate builtins *)
              self#compile_expression expr
          | Delegate _ -> (
              let is_null (e : expression) =
                match e.node with
                | Null -> true
                | Cast (_, inner) -> (match inner.node with Null -> true | _ -> false)
                | _ -> false
              in
              let emit_delegate_value (e : expression) =
                if is_null e then self#write_instruction0 DG_NEW
                else (
                  self#compile_expression e;
                  match e.ty with
                  | TyMethod _ | TyFunction _ ->
                      self#write_instruction0 DG_NEW_FROM_METHOD
                  | _ -> ())
              in
              (match expr.node with
              | Ternary (test, con, alt)
                when Ain.version_gte ctx.ain (12, 0)
                     && (is_null con || is_null alt) ->
                  self#compile_expression test;
                  (match test.node with
                  | Member (_, _, ClassVariable _) when Ain.version ctx.ain > 8 -> ()
                  | _ -> self#maybe_emit_condition_itob test);
                  let ifz_addr = current_address + 2 in
                  self#write_instruction1 IFZ 0;
                  emit_delegate_value con;
                  let jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at ifz_addr current_address;
                  emit_delegate_value alt;
                  self#write_address_at jump_addr current_address
              | _ -> emit_delegate_value expr))
          | Float when Ain.version ctx.ain > 8 ->
              self#compile_expression expr;
              (match expr.ty with
              | Int | LongInt | Enum _ | Bool -> self#write_instruction0 ITOF
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
                  | Ref (Array _ | String) ->
                      self#compile_lvalue expr;
                      self#write_instruction0 A_REF
                  | Ref (Struct _) ->
                      (* v12 [Ref Struct] arg passed to HLL [hll_param]:
                         needs [A_REF] just like Ref Array / Ref String.
                         Without it, [CALLHLL] takes ownership of the
                         page (stores it in the array) but the local
                         dummy's later release drops refcount to 0,
                         leaving a dangling page-id in the HLL-managed
                         data structure. Next access fires
                         [DeletePage Page=N]. Confirmed against orig
                         [PlayerSkillEffectCollection::Add] which
                         emits [A_REF] here — but only because that
                         array is VALUE-element ([PushBack 13]).
                         REF-element receivers push bare
                         ([in_ref_elem_hll_store_arg]). *)
                      self#compile_lvalue expr;
                      if
                        Ain.version_gte ctx.ain (12, 0)
                        && not in_ref_elem_hll_store_arg
                      then self#write_instruction0 A_REF
                  | Struct _ when in_ref_elem_hll_store_arg ->
                      (* Value-struct member/local read pushed into a
                         REF-element array store: bare borrowed page-ref
                         (orig [BattleLogCollection@Logs::get] pushes
                         [.STRUCTREF m_current] straight into
                         [PushBack 21]); the generic deref protocol's
                         [REF; A_REF] would leak one ref per store. *)
                      self#compile_variable_ref expr;
                      self#write_instruction0 REF
                  | _ -> self#compile_expression expr)
              | _ ->
                  self#compile_expression expr;
                  let inner_is_call =
                    match dummy_ref_inner expr with
                    | Some { node = Call _; _ } -> true
                    | _ -> false
                  in
                  (* Ref-returning-call results AND fresh [new T(...)]
                     push bare into REF-element array stores (orig
                     [BattleLog@0], [QuestMapObjectView@Load]'s
                     [m_marker.PushBack(new QuestMapObjectMarkerView(..))]).
                     A_REF is a PAGE COPY (xsystem4 vm.c: pop page id,
                     push deep-copied page) — with it, the array stored
                     a COPY while the original died with the dummy slot,
                     its [Parts] dtor deleting the engine part: every
                     quest-map marker/figure icon vanished same-frame.
                     VALUE-element stores ([PushBack 13]) still copy-in
                     via A_REF like orig. *)
                  if
                    ((dummy_inner_returns_ref && inner_is_call)
                    || bare_new_arg)
                    && not in_ref_elem_hll_store_arg
                  then self#write_instruction0 A_REF)
          | String when Ain.version ctx.ain > 8 ->
              (* Borrow analysis for `string` value-form args.
                 `needs_a_ref_for_consume` covers the
                 `Array.At / Array.First / Array.Last` shape
                 (DummyRef → ref-returning HLL call) while
                 [expression_ownership] reports `Stable` for the
                 OptionalMember-dispatched case (obj?.Method()) — that
                 path emits its own null sentinel and an extra A_REF
                 would re-deref an already-consumed value. Confirmed
                 against CEnqueteItemTextBox@SetInfo (positive) and
                 MenuContext@Init's d508efa regression (excluded). *)
              self#compile_expression expr;
              if self#needs_a_ref_for_consume expr then
                self#write_instruction0 A_REF
          | _ -> self#compile_expression expr)

    (** v11+: write [JUMP-over-body; body] for every [Lambda] argument
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
        let rec emit ?(body_only = false) (f : Jaf.fundecl) =
          let lambda_idx = Option.value_exn f.index in
          if not (Hashtbl.mem pre_emitted_lambdas lambda_idx)
             && not (Hashtbl.mem v12_assignment_lambdas lambda_idx)
          then (
            let nested =
              match f.body with
              | Some body -> collect_optional_call_lambdas_in_stmts body
              | None -> []
            in
            (* Original v12 pre-emits lambdas even when nested inside
               constructor/call arguments, before the surrounding call
               starts pushing receiver/value stack. *)
            let jump_addr =
              if body_only then None
              else (
                let addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                Some addr)
            in
            let nested_jump_addr =
              if List.is_empty nested then None
              else (
                let addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                Some addr)
            in
            List.iter nested ~f:(emit ~body_only:true);
            Option.iter nested_jump_addr ~f:(fun addr ->
                self#write_address_at addr current_address);
            self#compile_function f;
            Option.iter jump_addr ~f:(fun addr ->
                self#write_address_at addr current_address);
            Hashtbl.set pre_emitted_lambdas ~key:lambda_idx ~data:())
        and collect_lambdas (e : expression) =
          match e.node with
          | Lambda f -> [ f ]
          | Unary (_, e) | Cast (_, e) | DummyRef (_, e) | RvalueRef e
          | OptionalMember (e, _, _) | Member (e, _, _) ->
              collect_lambdas e
          | Binary (_, a, b) | Assign (_, a, b) | Seq (a, b)
          | NullCoalesce (a, b) | Subscript (a, b) ->
              collect_lambdas a @ collect_lambdas b
          | Ternary (a, b, c) ->
              collect_lambdas a @ collect_lambdas b @ collect_lambdas c
          | Call (f, args, _) ->
              collect_lambdas f
              @ List.concat_map args ~f:(function
                  | Some arg -> collect_lambdas arg
                  | None -> [])
          | NewCall (_, args) ->
              List.concat_map args ~f:(function
                | Some arg -> collect_lambdas arg
                | None -> [])
          | ArrayLiteral elems -> List.concat_map elems ~f:collect_lambdas
          | ConstInt _ | ConstFloat _ | ConstChar _ | ConstString _
          | Ident _ | FuncAddr _ | MemberAddr _ | New _ | This | Null ->
              []
        and callee_contains_optional_member (e : expression) =
          match e.node with
          | OptionalMember _ -> true
          | Member (e, _, _) | Cast (_, e) | DummyRef (_, e) | RvalueRef e ->
              callee_contains_optional_member e
          | Call (callee, _, _) -> callee_contains_optional_member callee
          | _ -> false
        and collect_optional_call_lambdas (e : expression) =
          match e.node with
          | Lambda _ -> []
          | Unary (_, e) | Cast (_, e) | DummyRef (_, e) | RvalueRef e
          | OptionalMember (e, _, _) | Member (e, _, _) ->
              collect_optional_call_lambdas e
          | Binary (_, a, b) | Assign (_, a, b) | Seq (a, b)
          | NullCoalesce (a, b) | Subscript (a, b) ->
              collect_optional_call_lambdas a @ collect_optional_call_lambdas b
          | Ternary (a, b, c) ->
              collect_optional_call_lambdas a
              @ collect_optional_call_lambdas b
              @ collect_optional_call_lambdas c
          | Call (callee, args, _) ->
              collect_optional_call_lambdas callee
              @ List.concat_map args ~f:(function
                  | Some arg ->
                      if callee_contains_optional_member callee then
                        collect_lambdas arg
                      else collect_optional_call_lambdas arg
                  | None -> [])
          | NewCall (_, args) ->
              List.concat_map args ~f:(function
                | Some arg -> collect_optional_call_lambdas arg
                | None -> [])
          | ArrayLiteral elems ->
              List.concat_map elems ~f:collect_optional_call_lambdas
          | ConstInt _ | ConstFloat _ | ConstChar _ | ConstString _
          | Ident _ | FuncAddr _ | MemberAddr _ | New _ | This | Null ->
              []
        and collect_optional_call_lambdas_in_stmt (s : statement) =
          match s.node with
          | EmptyStatement | Label _ | Goto _ | Continue | Break | Default
          | Jump _ ->
              []
          | Declarations ds ->
              List.concat_map ds.vars ~f:(fun v ->
                  Option.value_map v.initval ~default:[]
                    ~f:collect_optional_call_lambdas
                  @ List.concat_map v.array_dim
                      ~f:collect_optional_call_lambdas)
          | Expression e | Case e | Jumps e | Return (Some e) ->
              collect_optional_call_lambdas e
          | Return None | Message _ -> []
          | Compound stmts | Switch (_, stmts) ->
              collect_optional_call_lambdas_in_stmts stmts
          | If (c, t, e) ->
              collect_optional_call_lambdas c
              @ collect_optional_call_lambdas_in_stmt t
              @ collect_optional_call_lambdas_in_stmt e
          | While (c, body) | DoWhile (c, body) ->
              collect_optional_call_lambdas c
              @ collect_optional_call_lambdas_in_stmt body
          | For (init, test, step, body) ->
              collect_optional_call_lambdas_in_stmt init
              @ Option.value_map test ~default:[]
                  ~f:collect_optional_call_lambdas
              @ Option.value_map step ~default:[]
                  ~f:collect_optional_call_lambdas
              @ collect_optional_call_lambdas_in_stmt body
          | ForEach (_, _, _, container, body) ->
              collect_optional_call_lambdas container
              @ collect_optional_call_lambdas_in_stmt body
          | RefAssign (a, b) | ObjSwap (a, b) ->
              collect_optional_call_lambdas a @ collect_optional_call_lambdas b
        and collect_optional_call_lambdas_in_stmts stmts =
          List.concat_map stmts ~f:collect_optional_call_lambdas_in_stmt
        and scan (e : expression) =
          List.iter (collect_lambdas e) ~f:emit
        in
        let find_lambda (expr : expression) : Jaf.fundecl option =
          scan expr;
          None
        in
        List.iter args ~f:(function
          | Some expr -> (
              match find_lambda expr with
              | Some f ->
                  let lambda_idx = Option.value_exn f.index in
                  if not (Hashtbl.mem pre_emitted_lambdas lambda_idx)
                     && not (Hashtbl.mem v12_assignment_lambdas lambda_idx)
                  then (
                    (* Both v11 and v12: emit JUMP-over-body then inline
                       lambda body BEFORE any arg evaluation. Original
                       Rance10 pre-emits the lambda so the runtime
                       address sequence is contiguous — leaving stack
                       items pushed before the JUMP causes "file end
                       reached" because downstream code expects a clean
                       stack frame. *)
                    let jump_addr = current_address + 2 in
                    self#write_instruction1 JUMP 0;
                    self#compile_function f;
                    self#write_address_at jump_addr current_address;
                    Hashtbl.set pre_emitted_lambdas ~key:lambda_idx ~data:())
              | None -> ())
          | None -> ())

    method pre_emit_v12_rhs_lambdas expr =
      if Ain.version_gte ctx.ain (12, 0) then
        let emit (f : Jaf.fundecl) =
          let lambda_idx = Option.value_exn f.index in
          if not (Hashtbl.mem pre_emitted_lambdas lambda_idx)
             && not (Hashtbl.mem v12_assignment_lambdas lambda_idx)
          then (
            let jump_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#compile_function f;
            self#write_address_at jump_addr current_address;
            Hashtbl.set pre_emitted_lambdas ~key:lambda_idx ~data:())
        in
        let rec scan (e : expression) =
          match e.node with
          | Lambda f -> emit f
          | Unary (_, e) | Cast (_, e) | DummyRef (_, e) | RvalueRef e
          | OptionalMember (e, _, _) | Member (e, _, _) ->
              scan e
          | Binary (_, a, b) | Assign (_, a, b) | Seq (a, b)
          | NullCoalesce (a, b) | Subscript (a, b) ->
              scan a;
              scan b
          | Ternary (a, b, c) ->
              scan a;
              scan b;
              scan c
          | Call (f, args, _) ->
              scan f;
              List.iter args ~f:(Option.iter ~f:scan)
          | NewCall (_, args) -> List.iter args ~f:(Option.iter ~f:scan)
          | ArrayLiteral elems -> List.iter elems ~f:scan
          | ConstInt _ | ConstFloat _ | ConstChar _ | ConstString _
          | Ident _ | FuncAddr _ | MemberAddr _ | New _ | This | Null ->
              ()
        in
        scan expr

    method compile_function_arguments (args : expression option list) (f : Ain.Function.t) =
      let compile_arg arg (var : Ain.Variable.t) =
        self#compile_argument arg var.value_type
      in
      let params = Ain.Function.logical_parameters f in
      (* v12 tolerates arg/param count mismatch (overload resolution
         picked a stub that doesn't match real signature). Iterate
         the common prefix instead of erroring. *)
      let n = min (List.length args) (List.length params) in
      List.iter2_exn
        (List.take args n)
        (List.take params n)
        ~f:compile_arg

    method compile_hll_function_arguments lib args (f : Ain.Function.t) =
      let delegate_hint =
        match args with
        | Some { ty = Delegate (Some (_, dg_i)); _ } :: _ -> Some dg_i
        | Some { ty = Ref (Delegate (Some (_, dg_i))); _ } :: _ -> Some dg_i
        | Some { ty = Delegate None | Ref (Delegate None); _ } :: _ -> Some (-1)
        | _ -> None
      in
      (* v12 [Array.*(value)] where receiver is an iface-typed array and
         value is a struct (not an iface): the runtime expects a 2-slot
         IFace [page, vtable_offset] pair. [compile_dereference] for
         [Wrap (Struct _)] / [Struct _] emits only the page; we need a
         trailing [PUSH 0] to supply the vtable_offset. orig emits this
         pad for e.g. [array@ILoadableQuestMapObject.PushBack(qmoView)]
         where [qmoView] is [Wrap (Struct QuestMapObjectView)]. Without
         the pad the HLL sees garbage for the offset slot and crashes
         on the next iface dispatch / DELETE. *)
      let receiver_is_iface_array =
        Ain.version_gte ctx.ain (12, 0)
        && String.equal lib.Ain.Library.name "Array"
        &&
        let elem_is_iface : Jaf.jaf_type -> bool = function
          | Array t | Ref (Array t) -> (
              match t with
              | Struct (name, _) -> Hashtbl.mem ctx.interface_names name
              | _ -> false)
          | _ -> false
        in
        match args with
        | Some recv :: _ -> elem_is_iface recv.ty
        | _ -> false
      in
      let arg_is_bare_struct (arg : Jaf.expression option) =
        match arg with
        | Some { ty; _ } -> (
            let rec walk : Jaf.jaf_type -> bool = function
              | Wrap inner -> walk inner
              | Struct (name, _) ->
                  not (Hashtbl.mem ctx.interface_names name)
              | _ -> false
            in
            walk ty)
        | None -> false
      in
      let receiver_is_ref_elem_array =
        Ain.version_gte ctx.ain (12, 0)
        && String.equal lib.Ain.Library.name "Array"
        &&
        match args with
        | Some
            {
              ty =
                ( Array (Ref _ | Wrap (Ref _))
                | Ref (Array (Ref _ | Wrap (Ref _))) );
              _;
            }
          :: _ ->
            true
        | _ -> false
      in
      let compile_arg ~is_receiver arg (var : Ain.Variable.t) =
        (match (lib.Ain.Library.name, arg, var.value_type, delegate_hint) with
        | ( "Delegate",
            Some ({ ty = String; _ } as expr),
            (Ain.Type.HLLFunc | Ain.Type.HLLFunc2),
            Some dg_i ) ->
            self#compile_expression expr;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 SWAP;
            self#write_instruction1 DG_STR_TO_METHOD dg_i
        | _ when (not is_receiver) && receiver_is_ref_elem_array ->
            let prev = in_ref_elem_hll_store_arg in
            in_ref_elem_hll_store_arg <- true;
            Exn.protect
              ~f:(fun () -> self#compile_argument arg var.value_type)
              ~finally:(fun () -> in_ref_elem_hll_store_arg <- prev)
        | _ -> self#compile_argument arg var.value_type);
        (* IFace 2-slot pad for struct-value args to iface-array HLLs. *)
        if not is_receiver
           && receiver_is_iface_array
           && Poly.equal var.value_type Ain.Type.HLLParam
           && arg_is_bare_struct arg
        then self#write_instruction1 PUSH 0
      in
      let params = Ain.Function.logical_parameters f in
      let n = min (List.length args) (List.length params) in
      List.iteri (List.zip_exn (List.take args n) (List.take params n))
        ~f:(fun i (arg, var) -> compile_arg ~is_receiver:(i = 0) arg var)

    method interface_vtable_offset actual_sno iface_sno =
      let s = Ain.get_struct_by_index ctx.ain actual_sno in
      List.find_map s.interfaces ~f:(fun (iface : Ain.Struct.interface) ->
          if Int.equal iface.struct_type iface_sno then Some iface.vtable_offset
          else None)

    method v12_interface_receiver_method_slot ?(direct_getter_rank = false)
        ?(prefer_first_duplicate = false) (receiver_ty : Jaf.jaf_type)
        method_no =
      if not (Ain.version_gte ctx.ain (12, 0)) then None
      else
        match receiver_ty with
        | Jaf.Struct (name, sno)
        | Ref (Jaf.Struct (name, sno))
        | Wrap (Jaf.Struct (name, sno))
        | Wrap (Ref (Jaf.Struct (name, sno)))
          when Hashtbl.mem ctx.interface_names name ->
            let iface_s = Ain.get_struct_by_index ctx.ain sno in
            let method_fn = Ain.get_function_by_index ctx.ain method_no in
            let short_name (s : Ain.Struct.t) (f : Ain.Function.t) =
              let prefix = s.name ^ "@" in
              if String.is_prefix f.name ~prefix then
                String.chop_prefix_exn f.name ~prefix
              else f.name
            in
            let method_short = short_name iface_s method_fn in
            let same_shape (f : Ain.Function.t) =
              String.equal (short_name iface_s f) method_short
              && Int.equal f.nr_args method_fn.nr_args
            in
            let interface_slots =
              if List.is_empty iface_s.vmethods then
                let prefix = iface_s.name ^ "@" in
                let slots = ref [] in
                Ain.function_iter ctx.ain ~f:(fun f ->
                    if String.is_prefix f.name ~prefix && f.address < 0 then
                      slots := !slots @ [ f.index ]);
                !slots
              else iface_s.vmethods
            in
            let matches =
              List.filter_mapi interface_slots ~f:(fun i fn_idx ->
                  let fn = Ain.get_function_by_index ctx.ain fn_idx in
                  if same_shape fn then Some i else None)
            in
            let current_duplicate_rank () =
              match v12_current_body_dup_rank with
              | Some _ as rank -> rank
              | None -> self#current_body_duplicate_rank
            in
            if List.length matches > 1 then
              if
                String.is_suffix method_short ~suffix:"::get"
                || String.is_suffix method_short ~suffix:"::set"
              then
                match current_duplicate_rank () with
                | _ when direct_getter_rank -> List.hd matches
                | Some dup_rank ->
                    let wanted =
                      Int.max 0 (List.length matches - 1 - dup_rank)
                    in
                    (match List.nth matches wanted with
                    | Some slot -> Some slot
                    | None -> List.hd matches)
                | None ->
                    List.last matches
              else
                if prefer_first_duplicate then List.hd matches
                else
                  List.find_mapi interface_slots ~f:(fun i fn_idx ->
                      if Int.equal fn_idx method_no then Some i else None)
            else
            List.find_mapi interface_slots ~f:(fun i fn_idx ->
                if Int.equal fn_idx method_no then Some i else None)
        | _ -> None

    method v12_concrete_interface_method_slot ?(direct_getter_rank = false)
        ?(prefer_first_duplicate = false) (receiver_ty : Jaf.jaf_type)
        method_no =
      if not (Ain.version_gte ctx.ain (12, 0)) then None
      else
        let method_fn = Ain.get_function_by_index ctx.ain method_no in
        let receiver_ty_is_true_iface =
          match receiver_ty with
          | Jaf.Struct (name, _)
          | Ref (Jaf.Struct (name, _))
          | Wrap (Jaf.Struct (name, _))
          | Wrap (Ref (Jaf.Struct (name, _))) ->
              Hashtbl.mem ctx.interface_names name
          | _ -> false
        in
        let receiver_struct =
          match receiver_ty with
          | Jaf.Struct (_, sno)
          | Ref (Jaf.Struct (_, sno))
          | Wrap (Jaf.Struct (_, sno))
          | Wrap (Ref (Jaf.Struct (_, sno))) ->
              Some sno
          | _ -> method_fn.struct_type
        in
        match receiver_struct with
        | None -> None
        | Some sno ->
            let receiver = Ain.get_struct_by_index ctx.ain sno in
            if List.is_empty receiver.interfaces then None
            else
              let short_name (s : Ain.Struct.t) (f : Ain.Function.t) =
                let prefix = s.name ^ "@" in
                if String.is_prefix f.name ~prefix then
                  String.chop_prefix_exn f.name ~prefix
                else f.name
              in
              let method_short = short_name receiver method_fn in
              let same_method_shape (s : Ain.Struct.t) (f : Ain.Function.t) =
                String.equal (short_name s f) method_short
                && Int.equal f.nr_args method_fn.nr_args
              in
              let concrete_rank =
                let rank = ref 0 in
                let found = ref None in
                List.iter receiver.vmethods ~f:(fun fn_idx ->
                    if Option.is_none !found then
                      let f = Ain.get_function_by_index ctx.ain fn_idx in
                      if same_method_shape receiver f then (
                        if Int.equal fn_idx method_no then found := Some !rank;
                        Int.incr rank));
                !found
              in
              List.find_map receiver.interfaces
                ~f:(fun (iface : Ain.Struct.interface) ->
                  let iface_s =
                    Ain.get_struct_by_index ctx.ain iface.struct_type
                  in
                  let rank = ref 0 in
                  let group_count =
                    List.count iface_s.vmethods ~f:(fun iface_fn_idx ->
                        let iface_fn =
                          Ain.get_function_by_index ctx.ain iface_fn_idx
                        in
                        same_method_shape iface_s iface_fn)
                  in
                  let target_rank =
                    Option.map concrete_rank ~f:(fun r ->
                        if
                          String.is_suffix method_short ~suffix:"::get"
                          || String.is_suffix method_short ~suffix:"::set"
                        then
                          match self#current_body_duplicate_rank with
                          | Some dup_rank ->
                              Int.max 0 (group_count - 1 - dup_rank)
                          | None ->
                              if direct_getter_rank then r
                              else Int.max 0 (group_count - 1 - r)
                        else
                          if prefer_first_duplicate then 0
                          else
                          match (receiver_ty_is_true_iface, v12_current_body_dup_rank) with
                          | true, None -> 0
                          | _, Some dup_rank ->
                              Int.min (group_count - 1) (r + dup_rank)
                          | _ ->
                              r)
                  in
                  List.find_mapi iface_s.vmethods ~f:(fun i iface_fn_idx ->
                      let iface_fn =
                        Ain.get_function_by_index ctx.ain iface_fn_idx
                      in
                      if same_method_shape iface_s iface_fn then
                        match target_rank with
                        | Some wanted when Int.equal !rank wanted ->
                            Some (iface.vtable_offset + i)
                        | _ ->
                            Int.incr rank;
                            None
                      else None))

    method emit_vtable_method_selector slot =
      self#write_instruction0 DUP_U2;
      self#write_instruction1 PUSH 0;
      self#write_instruction0 REF;
      self#write_instruction0 SWAP;
      self#write_instruction1 PUSH slot;
      self#write_instruction0 ADD;
      self#write_instruction0 REF

    method private current_body_duplicate_rank =
      match current_function with
      | None -> None
      | Some cur ->
          if
            String.is_suffix cur.name ~suffix:"@0"
            || String.is_suffix cur.name ~suffix:"@2"
            || String.is_substring cur.name ~substring:"@0("
            || String.is_substring cur.name ~substring:"@2("
          then None
          else
          let same = ref [] in
          Ain.function_iter ctx.ain ~f:(fun f ->
              if String.equal f.name cur.name && Int.equal f.nr_args cur.nr_args
              then same := !same @ [ f.index ]);
          if List.length !same > 1 then
            List.findi !same ~f:(fun _ idx -> Int.equal idx cur.index)
            |> Option.map ~f:fst
          else None

    method private v12_concrete_receiver_has_interfaces receiver_ty =
      if not (Ain.version_gte ctx.ain (12, 0)) then false
      else
        let receiver_struct =
          match receiver_ty with
          | Jaf.Struct (_, sno)
          | Ref (Jaf.Struct (_, sno))
          | Wrap (Jaf.Struct (_, sno))
          | Wrap (Ref (Jaf.Struct (_, sno))) ->
              Some sno
          | _ -> None
        in
        match receiver_struct with
        | Some sno ->
            not (List.is_empty (Ain.get_struct_by_index ctx.ain sno).interfaces)
        | None -> false

    method compile_method_selector ?(concrete = false)
        ?(direct_getter_rank = false) ?(prefer_first_duplicate = false)
        receiver_ty method_no =
      match
        self#v12_interface_receiver_method_slot
          ~direct_getter_rank ~prefer_first_duplicate receiver_ty method_no
      with
      | Some slot -> self#emit_vtable_method_selector slot
      | None -> (
          match
            if concrete || self#v12_concrete_receiver_has_interfaces receiver_ty
            then
              self#v12_concrete_interface_method_slot ~direct_getter_rank
                ~prefer_first_duplicate receiver_ty method_no
            else None
          with
          | Some slot ->
              self#write_instruction1 PUSH 0;
              self#emit_vtable_method_selector slot
          | None -> self#write_instruction1 PUSH method_no)

    (** True iff [method_no] names a value property setter —
        [Prop::set] taking one non-ref value parameter and returning
        void. Optional-chain assignments through such setters yield
        the assigned value across the ?? merge (kept below the call
        via DUP_X2), so their statements pop once. *)
    method private is_value_prop_setter_method method_no args =
      let f = Ain.get_function_by_index ctx.ain method_no in
      String.is_suffix f.name ~suffix:"::set"
      && List.length args = 1
      && Poly.equal f.return_type Ain.Type.Void
      &&
      match List.hd (Ain.Function.logical_parameters f) with
      | Some { value_type = IFace _ | Ref _ | Wrap _; _ } -> false
      | _ -> true

    (** Match a discarded optional method chain —
        [DummyRef(dN, Call(Member(... DummyRef(d1, Call(OptionalMember
        (obj), a1, m1)) ...), aN, mN))] — returning the checked
        receiver and the links innermost-first as
        [(dummy_idx, receiver_ty, args, method_no)]. Only multi-link
        plain-struct chains: single links and interface receivers keep
        their existing paths. *)
    method private match_discarded_optional_chain (expr : expression) =
      let is_iface (ty : jaf_type) =
        match ty with
        | Struct (name, _) | Ref (Struct (name, _)) ->
            Hashtbl.mem ctx.interface_names name
        | _ -> false
      in
      let rec peel (e : expression) =
        match e.node with
        | DummyRef
            ( idx,
              {
                node =
                  Call
                    ( { node = OptionalMember (obj, _, _); _ },
                      args,
                      MethodCall (_, mno) );
                _;
              } ) ->
            Some (obj, [ (idx, obj.ty, args, mno) ])
        | DummyRef
            ( idx,
              {
                node =
                  Call
                    ( { node = Member (recv, _, ClassMethod _); _ },
                      args,
                      MethodCall (_, mno) );
                _;
              } ) ->
            Option.map (peel recv) ~f:(fun (obj, links) ->
                (obj, links @ [ (idx, recv.ty, args, mno) ]))
        | _ -> None
      in
      match expr.node with
      | DummyRef _ -> (
          match peel expr with
          | Some (obj, links)
            when List.length links >= 2
                 && (not (is_iface obj.ty))
                 && not
                      (List.exists links ~f:(fun (_, rty, _, _) ->
                           is_iface rty)) ->
              Some (obj, links)
          | _ -> None)
      | _ -> None

    method private same_lvalue_shape (a : expression) (b : expression) =
      match (a.node, b.node) with
      | This, This -> true
      | Ident (_, ia), Ident (_, ib) -> Poly.equal ia ib
      | Member (ao, _, ClassVariable ai), Member (bo, _, ClassVariable bi)
        ->
          Int.equal ai bi && self#same_lvalue_shape ao bo
      | Subscript (ao, ai), Subscript (bo, bi) ->
          self#same_lvalue_shape ao bo && Poly.equal ai.node bi.node
      | _ -> false

    method private emit_reused_receiver_binary_op (ty : jaf_type)
        (op : binary_op) =
      match (ty, op) with
      | (Int | Enum _), Plus ->
          self#write_instruction0 ADD;
          true
      | (Int | Enum _), Minus ->
          self#write_instruction0 SUB;
          true
      | LongInt, Plus ->
          self#write_instruction0 LI_ADD;
          true
      | LongInt, Minus ->
          self#write_instruction0 LI_SUB;
          true
      | Float, Plus ->
          self#write_instruction0 F_ADD;
          true
      | Float, Minus ->
          self#write_instruction0 F_SUB;
          true
      | (Int | Enum _), Times ->
          self#write_instruction0 MUL;
          true
      | (Int | Enum _), Divide ->
          self#write_instruction0 DIV;
          true
      | (Int | Enum _), Modulo ->
          self#write_instruction0 MOD;
          true
      | Float, Times ->
          self#write_instruction0 F_MUL;
          true
      | Float, Divide ->
          self#write_instruction0 F_DIV;
          true
      | _ -> false

    method constructor_match struct_name (args : expression option list) =
      let ctor_name = struct_name ^ "@0" in
      let primary = Hashtbl.find ctx.functions ctor_name in
      let overloads =
        Option.value (Hashtbl.find ctx.overloads ctor_name) ~default:[]
      in
      let all = match primary with Some f -> f :: overloads | None -> overloads in
      let nargs = List.length args in
      match
        List.filter all ~f:(fun (f : fundecl) -> List.length f.params = nargs)
      with
      | [] -> None
      | [ f ] -> Some f
      | candidates ->
          (* Arity alone is ambiguous — pick by argument types like
             [resolve_overload] (loose compatibility, then prefer exact
             matches). Arity-first-match called BattleLog's
             [(ref BattleRound)] constructor for [new BattleLog(text)]
             (SceneBattle@ShowLog): the string page went in as the
             BattleRound ref and the ctor's first member read fired
             【 REF 】範囲外 (要素数 = -1) on the first battle skill
             use. orig calls the [(string)] ctor. *)
          let loose (p : variable) (t : jaf_type) =
            match (p.type_spec.ty, t) with
            | Delegate _, (TyMethod _ | TyFunction _) -> true
            | FuncType _, (TyMethod _ | TyFunction _) -> true
            | pt, Ref at when TypeAnalysis.type_equal pt at -> true
            | ( (Delegate _ | FuncType _ | Struct _ | Array _ | Ref _ | String),
                NullType ) ->
                true
            | (Int | LongInt | Bool), (Int | LongInt | Bool | Float) -> true
            | Float, (Int | LongInt | Bool | Float) -> true
            | pt, at -> TypeAnalysis.type_equal pt at
          in
          let strict (p : variable) (t : jaf_type) =
            match (p.type_spec.ty, t) with
            | Enum (_, a), Enum (_, b) -> a = b
            | Enum _, _ | _, Enum _ -> false
            | ( (Int | LongInt | Bool | Float),
                (Int | LongInt | Bool | Float) ) ->
                Poly.equal p.type_spec.ty t
            | pt, at -> TypeAnalysis.type_equal pt at
          in
          let matches pred (f : fundecl) =
            List.for_all2_exn f.params args ~f:(fun p a ->
                match a with
                | None -> true
                | Some e -> pred p e.ty)
          in
          let compatible =
            match List.filter candidates ~f:(matches loose) with
            | [] -> candidates
            | rest -> rest
          in
          (match List.filter compatible ~f:(matches strict) with
          | exact :: _ -> Some exact
          | [] -> List.hd compatible)

    method private bare_new_ctor s_no =
      if Ain.version_gte ctx.ain (12, 0) then -1
      else (Ain.get_struct_by_index ctx.ain s_no).constructor

    method private receiver_new_ctor s_no =
      if
        Ain.version_gte ctx.ain (12, 0)
        && bare_new_receiver_uses_default_ctor
      then (Ain.get_struct_by_index ctx.ain s_no).constructor
      else self#bare_new_ctor s_no

    method private with_bare_new_receiver_default_ctor f =
      let prev = bare_new_receiver_uses_default_ctor in
      Exn.protect
        ~f:(fun () ->
          bare_new_receiver_uses_default_ctor <- true;
          f ())
        ~finally:(fun () -> bare_new_receiver_uses_default_ctor <- prev)

    method compile_newcall struct_name s_no args =
      let default_ctor = (Ain.get_struct_by_index ctx.ain s_no).constructor in
      let matching_ctor = self#constructor_match struct_name args in
      let ctor_idx =
        match matching_ctor with
        | Some f -> Option.value f.index ~default:default_ctor
        | None -> default_ctor
      in
      (match matching_ctor with
      | Some f -> (
          match f.index with
          | Some fno ->
              let ctor = Ain.get_function_by_index ctx.ain fno in
              let params = Ain.Function.logical_parameters ctor in
              let n = min (List.length args) (List.length params) in
              List.iter2_exn
                (List.take args n)
                (List.take params n)
                ~f:(fun arg (var : Ain.Variable.t) ->
                  match var.value_type with
                  | Ain.Type.Delegate _ | Ain.Type.Method | Ain.Type.IFace _ ->
                      self#compile_argument arg var.value_type
                  | Ain.Type.Ref _ | Ain.Type.Wrap _ -> (
                      match arg with
                      | Some expr when is_variable_ref expr.node ->
                          self#compile_argument arg var.value_type
                      | _ -> Option.iter arg ~f:self#compile_expression)
                  | _ -> self#compile_argument arg var.value_type)
          | None ->
              List.iter args ~f:(fun arg ->
                  Option.iter arg ~f:self#compile_expression))
      | None ->
          List.iter args ~f:(fun arg -> Option.iter arg ~f:self#compile_expression));
      self#write_instruction2 NEW s_no ctor_idx

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

    method compile_method_call_for_receiver ?(concrete = false)
        ?(direct_getter_rank = false) ?(prefer_first_duplicate = false)
        receiver_ty args method_no =
      let f = Ain.get_function_by_index ctx.ain method_no in
      let emitted_self_event_accessor_update =
        Ain.version_gte ctx.ain (12, 0)
        &&
        match (current_function, args) with
        | Some current, [ Some rhs ] when current.index = method_no -> (
            let event_name_and_op =
              match String.chop_suffix f.name ~suffix:"::add" with
              | Some prefix -> Some (prefix, DG_PLUSA)
              | None -> (
                  match String.chop_suffix f.name ~suffix:"::remove" with
                  | Some prefix -> Some (prefix, DG_MINUSA)
                  | None -> None)
            in
            let owner_struct =
              match f.struct_type with
              | Some sno -> Some (Ain.get_struct_by_index ctx.ain sno)
              | None -> (
                  match String.lsplit2 f.name ~on:'@' with
                  | Some (struct_name, _) -> Ain.get_struct ctx.ain struct_name
                  | None -> None)
            in
            match (owner_struct, event_name_and_op) with
            | Some s, Some (prefix, op) -> (
                let event_name =
                  match String.rsplit2 prefix ~on:'@' with
                  | Some (_, name) -> name
                  | None -> prefix
                in
                let backing_name = "<" ^ event_name ^ ">" in
                match
                  List.find s.members ~f:(fun (m : Ain.Variable.t) ->
                      String.equal m.name backing_name)
                with
                | Some member ->
                    self#write_instruction1 PUSH member.index;
                    self#write_instruction0 REF;
                    self#compile_lvalue rhs;
                    self#write_instruction0 op;
                    self#write_instruction0 POP;
                    true
                | None -> false)
            | _ -> false)
        | _ -> false
      in
      if emitted_self_event_accessor_update then ()
      else if Ain.version ctx.ain > 8 then (
        self#compile_method_selector ~concrete ~direct_getter_rank receiver_ty
          ~prefer_first_duplicate method_no;
        self#compile_function_arguments args f;
        self#write_instruction1 CALLMETHOD f.nr_args)
      else (
        self#compile_function_arguments args f;
        self#write_instruction1 CALLMETHOD method_no)

    method lvalue_storage_is_v12_iface (e : expression) =
      (* Recognize both bare [IFace _] storage (e.g. param/local) and
         [Wrap (IFace _)] storage (e.g. foreach-bound iface var). The
         comparison handler at line ~2880 emits an extra [POP] for
         iface-vs-NULL comparisons; without recognizing Wrap, the POP
         is skipped and stack discipline is off. *)
      let rec is_iface_ty = function
        | Ain.Type.IFace _ -> true
        | Ain.Type.Wrap inner -> is_iface_ty inner
        | _ -> false
      in
      Ain.version_gte ctx.ain (12, 0)
      &&
      match e.node with
      | Ident (_, LocalVariable (i, _)) ->
          is_iface_ty (self#get_local i).value_type
      | Ident (_, GlobalVariable i) ->
          is_iface_ty (Ain.get_global_by_index ctx.ain i).value_type
      | Member (_, _, ClassVariable _) ->
          is_iface_ty (self#member_type e)
      | DummyRef (var_no, _) ->
          is_iface_ty (self#get_local var_no).value_type
      | Cast (_, inner) -> self#lvalue_storage_is_v12_iface inner
      | _ -> false

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
          let no =
            if Ain.version_lt ctx.ain (1, 0) then Ain.add_message ctx.ain s
            else Ain.add_string ctx.ain s
          in
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
             read the var by index. Dereference using the PARENT slot's
             ain type (not [expr.ty]) — foreach iteration vars are
             stored as [Wrap String], which needs [REFREF; REF; A_REF],
             whereas [expr.ty] from the lambda body just sees [String]
             and would emit a plain [REF] that loads the ref-handle
             instead of the underlying string. *)
          self#write_instruction0 PUSHLOCALPAGE;
          for _ = 1 to level do
            self#write_instruction0 X_GETENV
          done;
          self#write_instruction1 PUSH i;
          let ty =
            match List.nth enclosing_functions (level - 1) with
            | Some parent ->
                (match List.nth parent.vars i with
                | Some (v : Ain.Variable.t) -> v.value_type
                | None -> jaf_to_ain_type expr.ty)
            | None -> jaf_to_ain_type expr.ty
          in
          self#compile_dereference ty
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
          self#write_instruction0 NOT;
          (* v11 NOT leaves non-bool input as-is; ITOB normalises to 0/1.
             v12: original never emits ITOB after NOT — NOT already
             produces 0/1 in v12 semantics. *)
          if Ain.version ctx.ain > 8 && Ain.version_lt ctx.ain (12, 0) then
            self#write_instruction0 ITOB
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
      | Binary
          ( ((RefEqual | RefNEqual) as op),
            ( { node =
                  DummyRef
                    ( _,
                      { node =
                          NullCoalesce
                            (({ node = Call _; _ } as option_call),
                             { node = Null; _ });
                        _ } );
                _ } as a ),
            { node = Null; _ } )
        when Ain.version_gte ctx.ain (12, 0) -> (
          match self#ain_call_return_type option_call with
          | Some (Ain.Type.Option _) ->
              self#compile_lvalue a;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH 0;
              let cmp =
                match op with
                | RefEqual -> R_EQUALE
                | RefNEqual -> R_NOTE
                | _ -> assert false
              in
              self#write_instruction0 cmp
          | _ ->
              compiler_bug
                "option-null DummyRef compare expected option-returning call"
                (Some (ASTExpression expr)))
      | Binary (op, a, b) -> (
          (match op with
          (* v11 ref/wrap === / !== handling. See the operator case
             below for the EQUALE-vs-R_EQUALE selection — together they
             match alice.exe's emission. *)
          | RefEqual | RefNEqual ->
              self#compile_lvalue a;
              (match (a.ty, b.node) with
              | (Struct (name, _) | Ref (Struct (name, _))), Null
                when Ain.version_gte ctx.ain (12, 0)
                     && Hashtbl.mem ctx.interface_names name ->
                  self#write_instruction0 POP
              | _ -> ());
              let lhs_is_call_or_dummy =
                match a.node with
                | Call _ | DummyRef _ -> true
                | _ -> false
              in
              (match a.ty with
              | Wrap (Struct (name, _) | Ref (Struct (name, _)))
                when Ain.version_gte ctx.ain (12, 0)
                     && Hashtbl.mem ctx.interface_names name ->
                  (* v12 [Wrap (IFace _)] storage: [compile_lvalue_after]
                     emitted a single [REFREF] leaving the 2-slot iface
                     fat-ref on the stack. For comparison vs NULL we
                     want just the page (1 slot) — add a [REF] to
                     collapse the fat-ref to the page value. *)
                  self#write_instruction0 REF
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
              (match (op, b.node) with
              | (Equal | NEqual), Null
                when Ain.version_gte ctx.ain (12, 0)
                     && self#lvalue_storage_is_v12_iface a ->
                  self#write_instruction0 POP;
                  (* iface→concrete X_ICAST leaves [page, vofs, validator]
                     on stack; the standard POP above drops the validator
                     (matching the Wrap<IFace>/IFace fat-ref case). For a
                     concrete-struct cast result we want only page for the
                     NULL compare, so drop vofs too. Match original's
                     `X_ICAST struct(N); POP; POP; PUSH -1; NOTE` pattern
                     used in boolean compare context (e.g. LoadActivity's
                     `T(field) != NULL`). Doing this here rather than
                     inside Cast preserves the stack shape for the
                     assignment path (R_ASSIGN with NULL guard at e.g.
                     SceneBattle@OnSkillEffectPostProcess). *)
                  (match a.node with
                  | Cast ((Struct (n, _) | Ref (Struct (n, _))), _)
                    when not (Hashtbl.mem ctx.interface_names n) ->
                      self#write_instruction0 POP
                  | _ -> ())
              | _ -> ());
              self#compile_expression b);
          match (a.ty, op) with
          | (Int | LongInt | Bool | Enum _), Equal ->
              self#write_instruction0 EQUALE
          | (Int | LongInt | Bool | Enum _), NEqual ->
              self#write_instruction0 NOTE
          | (Int | Enum _), Plus -> self#write_instruction0 ADD
          | (Int | Enum _), Minus -> self#write_instruction0 SUB
          | (Int | Enum _), Times -> self#write_instruction0 MUL
          | (Int | Enum _), Divide -> self#write_instruction0 DIV
          | (Int | Enum _), Modulo -> self#write_instruction0 MOD
          | (Int | LongInt | Enum _), LT -> self#write_instruction0 LT
          | (Int | LongInt | Enum _), GT -> self#write_instruction0 GT
          | (Int | LongInt | Enum _), LTE -> self#write_instruction0 LTE
          | (Int | LongInt | Enum _), GTE -> self#write_instruction0 GTE
          | (Int | Bool | Enum _), BitOr -> self#write_instruction0 OR
          | (Int | Bool | Enum _), BitXor -> self#write_instruction0 XOR
          | (Int | Bool | Enum _), BitAnd -> self#write_instruction0 AND
          | (Int | Bool | Enum _), LShift -> self#write_instruction0 LSHIFT
          | (Int | Bool | Enum _), RShift -> self#write_instruction0 RSHIFT
          | (Int | Enum _), (LogOr | LogAnd) ->
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
              let rec int_of_t (t : Ain.Type.t) =
                match t with
                | Int -> 2
                | Enum _ -> 2
                | Float -> 3
                | String -> 4
                | Bool -> 48
                | LongInt -> 56
                (* v12 [string % wrap_or_hll_param]: format-arg whose
                   compile-time type is unknown. Best guess [Int]. *)
                | HLLParam -> 2
                | Wrap inner -> int_of_t inner
                | _ ->
                    compiler_bug "invalid type for string formatting"
                      (Some (ASTExpression expr))
              in
              self#write_instruction1 S_MOD (int_of_t (jaf_to_ain_type b.ty))
          | ( String,
              ( Minus | Times | Divide | BitOr | BitXor | BitAnd | LShift
              | RShift | LogOr | LogAnd ) ) ->
              compiler_bug "invalid string operator" (Some (ASTExpression expr))
          (* v12 [p === NULL] / [p === q] where p is a plain Struct
             (interface or class slot, not [Ref Struct]). Both sides
             are page-ids on the stack — plain EQUALE / NOTE. Also
             cover scalar / enum cases where the lhs is an int / null
             sentinel (e.g. [Parse() ?? NULL] of an enum). *)
          | ( ( Struct _ | Array _ | String | Delegate _ | Int | Bool
              | Enum _ | LongInt | NullType | HLLParam ),
              RefEqual ) ->
              self#write_instruction0 EQUALE
          | ( ( Struct _ | Array _ | String | Delegate _ | Int | Bool
              | Enum _ | LongInt | NullType | HLLParam ),
              RefNEqual ) ->
              self#write_instruction0 NOTE
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
          (* v12 struct/array/delegate page-ref identity compare against
             NULL ([-1]) or another page-ref: both sides reduce to a
             single int (the page id), so plain EQUALE/NOTE works. *)
          | (Struct _ | Array _ | Delegate _ | HLLParam), Equal ->
              self#write_instruction0 EQUALE
          | (Struct _ | Array _ | Delegate _ | HLLParam), NEqual ->
              self#write_instruction0 NOTE
          | _ ->
              compiler_bug "invalid binary expression"
                (Some (ASTExpression expr)))
      | Assign (op, lhs, rhs) -> (
          (* v12 [receiver?.DelegateMember += method] / [-= method].
             The optional-member compound-assign to a delegate member
             is NOT the rvalue-member shape: the original keeps the
             member as a place (REF) in the non-null branch and builds
             the rhs delegate in BOTH null-check branches — the
             receiver-null path still constructs and DELETEs the
             delegate (balanced), only the fully-non-null path runs
             DG_PLUSA/DG_MINUSA. Compiling the OptionalMember as an
             rvalue (the previous behaviour) collapsed the null branch
             and ran DG_PLUSA on a -1 sentinel, mis-registering the
             handler; firing it (e.g. mouse wheel on a scroll view)
             then REF'd a -1 page. Handles the call-receiver, direct
             ClassVariable delegate-member shape (ScrollBase@Init
             getCurrentSceneStack()?.WheelEvent += this.OnWheel). *)
          let rhs_is_method_ref =
            match rhs.node with
            | Member (_, _, ClassMethod _)
            | Cast (_, { node = Member (_, _, ClassMethod _); _ })
            | Lambda _ | FuncAddr _
            | Cast (_, { node = FuncAddr _; _ })
            | Cast (_, { node = Lambda _; _ }) ->
                true
            | _ -> false
          in
          let optional_delegate_add =
            if
              Ain.version_gte ctx.ain (12, 0)
              && (match op with PlusAssign | MinusAssign -> true | _ -> false)
              && (match lhs.ty with Delegate _ -> true | _ -> false)
              && rhs_is_method_ref
            then
              match lhs.node with
              | OptionalMember
                  (({ node = DummyRef (_, { node = Call _; _ }); _ } as receiver),
                   _, ClassVariable midx) ->
                  Some (receiver, midx)
              | _ -> None
            else None
          in
          (match optional_delegate_add with
          | Some (receiver, midx) ->
              let dgop = match op with PlusAssign -> DG_PLUSA | _ -> DG_MINUSA in
              let emit_rhs_dg () =
                self#compile_expression rhs;
                self#write_instruction0 DG_NEW_FROM_METHOD
              in
              (* Evaluate the receiver call: CALLFUNC; store to its
                 dummy slot; leave the page-ref on the stack. The
                 DummyRef machinery registers the slot so its
                 SH_LOCALDELETE is emitted at statement cleanup. *)
              self#compile_expression receiver;
              self#write_instruction0 DUP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let a_recv_null = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              (* receiver non-null: push [member_index, valid-marker 0] *)
              self#write_instruction1 PUSH midx;
              self#write_instruction1 PUSH 0;
              let a_merge = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at a_recv_null current_address;
              (* receiver null: drop it, push three -1 sentinels *)
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at a_merge current_address;
              (* second level: was the marker valid (not -1)? *)
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let a_member_null = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              (* member present: REF to the delegate place, add rhs *)
              self#write_instruction0 REF;
              emit_rhs_dg ();
              self#write_instruction0 dgop;
              self#write_instruction0 DELETE;
              let a_end = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at a_member_null current_address;
              (* receiver was null: still build+discard the delegate *)
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              emit_rhs_dg ();
              self#write_instruction0 DELETE;
              self#write_address_at a_end current_address
          | None -> ());
          if Option.is_some optional_delegate_add then ()
          else (
          let lhs_is_v12_iface =
            Ain.version_gte ctx.ain (12, 0)
            && is_variable_ref lhs.node
            &&
            match lhs.node with
            | Ident (_, LocalVariable (i, _)) -> (
                match (self#get_local i).value_type with
                | Ain.Type.IFace _ -> true
                | Ain.Type.Struct s ->
                    let name =
                      (Ain.get_struct_by_index ctx.ain s).name
                    in
                    Hashtbl.mem ctx.interface_names name
                | Ain.Type.Ref (Ain.Type.Struct s) ->
                    let name =
                      (Ain.get_struct_by_index ctx.ain s).name
                    in
                    Hashtbl.mem ctx.interface_names name
                | _ -> false)
            | Ident (_, GlobalVariable i) -> (
                match (Ain.get_global_by_index ctx.ain i).value_type with
                | Ain.Type.IFace _ -> true
                | Ain.Type.Struct s ->
                    let name =
                      (Ain.get_struct_by_index ctx.ain s).name
                    in
                    Hashtbl.mem ctx.interface_names name
                | Ain.Type.Ref (Ain.Type.Struct s) ->
                    let name =
                      (Ain.get_struct_by_index ctx.ain s).name
                    in
                    Hashtbl.mem ctx.interface_names name
                | _ -> false)
            | Member (_, _, ClassVariable _) -> (
                match self#member_type lhs with
                | Ain.Type.IFace _ -> true
                | _ -> false)
            | _ -> (
                match lhs.ty with
                | Struct (name, _) | Ref (Struct (name, _)) | Unresolved name
                  ->
                    Hashtbl.mem ctx.interface_names name
                | _ -> false)
          in
          let pre_emit_v12_delegate_assignment_lambda () =
            if Ain.version_gte ctx.ain (12, 0) then
              let rec find_lambda (e : expression) =
                match e.node with
                | Lambda f -> Some f
                | Cast (_, inner) -> find_lambda inner
                | _ -> None
              in
              match (op, lhs.ty, find_lambda rhs) with
              | EqAssign, Delegate _, Some f
                when not (Hashtbl.mem v12_assignment_lambdas
                            (Option.value_exn f.index)) ->
                  let lambda_idx = Option.value_exn f.index in
                  let jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#compile_function f;
                  self#write_address_at jump_addr current_address;
                  Hashtbl.set v12_assignment_lambdas ~key:lambda_idx ~data:()
              | _ -> ()
          in
          pre_emit_v12_delegate_assignment_lambda ();
          self#pre_emit_v12_rhs_lambdas rhs;
          let emitted_v12_iface_cast_rhs_first_assign =
            match (op, lhs.node, rhs.node) with
            | ( EqAssign,
                Ident (_, LocalVariable (lhs_i, _)),
                Cast
                  ( (Struct (dst_name, dst_sno) | Ref (Struct (dst_name, dst_sno))),
                    ({ ty =
                         (Struct (src_name, _src_sno)
                         | Ref (Struct (src_name, _src_sno)));
                       _ } as inner) ) )
              when lhs_is_v12_iface
                   && Hashtbl.mem ctx.interface_names dst_name ->
                self#compile_expression inner;
                if Hashtbl.mem ctx.interface_names src_name then
                  self#write_instruction0 POP;
                self#write_instruction1 X_ICAST dst_sno;
                self#write_instruction0 POP;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction0 DUP_X2;
                self#write_instruction0 POP;
                self#write_instruction1 PUSH lhs_i;
                self#write_instruction0 DUP_X2;
                self#write_instruction0 POP;
                self#write_instruction0 R_ASSIGN;
                self#write_instruction0 POP;
                self#write_instruction0 DUP;
                self#write_instruction0 SP_INC;
                true
            | _ -> false
          in
          if not emitted_v12_iface_cast_rhs_first_assign then (
          let emitted_v12_iface_cast_assign =
            match (op, lhs.node, rhs.node) with
            | ( EqAssign,
                Ident (_, LocalVariable (lhs_i, _)),
                Cast
                  ( (Struct (_, dst_sno) | Ref (Struct (_, dst_sno))),
                    ({ ty =
                         (Struct (src_name, _) | Ref (Struct (src_name, _)));
                       _ } as inner) ) )
              when lhs_is_v12_iface
                   && is_variable_ref inner.node
                   && Hashtbl.mem ctx.interface_names src_name ->
                self#compile_variable_ref inner;
                self#write_instruction0 REF;
                self#write_instruction1 X_ICAST dst_sno;
                self#write_instruction0 POP;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction0 DUP_X2;
                self#write_instruction0 POP;
                self#write_instruction1 PUSH lhs_i;
                self#write_instruction0 DUP_X2;
                self#write_instruction0 POP;
                self#write_instruction0 R_ASSIGN;
                self#write_instruction0 POP;
                self#write_instruction0 DUP;
                self#write_instruction0 SP_INC;
                true
            | _ -> false
          in
          if not emitted_v12_iface_cast_assign then (
          let emitted_v12_ref_struct_direct_assign =
            let lhs_storage_is_ref_struct =
              match lhs.node with
              | Ident (_, LocalVariable (i, _)) -> (
                  match (self#get_local i).value_type with
                  | Ain.Type.Ref (Struct _) -> true
                  | _ -> false)
              | Ident (_, GlobalVariable i) -> (
                  match (Ain.get_global_by_index ctx.ain i).value_type with
                  | Ain.Type.Ref (Struct _) -> true
                  | _ -> false)
              | Member (_, _, ClassVariable _) -> (
                  match self#member_type lhs with
                  | Ain.Type.Ref (Struct _) -> true
                  | _ -> false)
              | _ -> false
            in
            Ain.version_gte ctx.ain (12, 0)
            && (not lhs_is_v12_iface)
            && lhs_storage_is_ref_struct
            &&
            match (op, rhs.node, rhs.ty, lhs.node) with
            | ( EqAssign,
                (Null | Cast ((Struct _ | Ref (Struct _)), _)),
                _,
                (Ident _ | Member (_, _, ClassVariable _)) )
            | ( EqAssign,
                _,
                (Struct _ | Ref (Struct _)),
                (Ident _ | Member (_, _, ClassVariable _)) ) ->
                self#compile_variable_ref lhs;
                self#compile_expression rhs;
                self#write_instruction0 ASSIGN;
                self#write_instruction0 SP_INC;
                true
            | _ -> false
          in
          if not emitted_v12_ref_struct_direct_assign then (
          if lhs_is_v12_iface then self#compile_variable_ref lhs
          else self#compile_lvalue lhs;
          self#compile_expression rhs;
          match (op, rhs.ty) with
          | EqAssign, NullType when lhs_is_v12_iface ->
              self#write_instruction1 PUSH 0;
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC
          | EqAssign, _ when lhs_is_v12_iface ->
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC
          | EqAssign, _ when Poly.(lhs.ty = Bool) ->
              (* v11 ASSIGN-to-bool normalises non-bool rhs via ITOB.
                 v12 ASSIGN tolerates any int value in a bool slot —
                 original Rance10 emits ITOB only after [PUSH N; REF]
                 (reading an int slot as bool), never after constants
                 or expressions. Skip ITOB for v12. *)
              (if Ain.version_gte ctx.ain (11, 0)
                  && Ain.version_lt ctx.ain (12, 0) then
                 match rhs.node with
                 | ConstInt _ -> self#write_instruction0 ITOB
                 | _
                   when (not (TypeAnalysis.is_bool_producing_expr rhs))
                        && (match rhs.ty with Bool -> false | _ -> true) ->
                     self#write_instruction0 ITOB
                 | _ -> ());
              self#write_instruction0 ASSIGN
          | EqAssign, (Int | Bool | Enum _ | TyFunction _ | FuncType _) ->
              self#write_instruction0 ASSIGN
          | PlusAssign, (Int | Bool | Enum _) -> self#write_instruction0 PLUSA
          | MinusAssign, (Int | Bool | Enum _) -> self#write_instruction0 MINUSA
          | TimesAssign, (Int | Bool | Enum _) -> self#write_instruction0 MULA
          | DivideAssign, (Int | Bool | Enum _) -> self#write_instruction0 DIVA
          | ModuloAssign, (Int | Bool | Enum _) -> self#write_instruction0 MODA
          | OrAssign, (Int | Bool | Enum _) -> self#write_instruction0 ORA
          | XorAssign, (Int | Bool | Enum _) -> self#write_instruction0 XORA
          | AndAssign, (Int | Bool | Enum _) -> self#write_instruction0 ANDA
          | LShiftAssign, (Int | Bool | Enum _) -> self#write_instruction0 LSHIFTA
          | RShiftAssign, (Int | Bool | Enum _) -> self#write_instruction0 RSHIFTA
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
              | Delegate dg ->
                  let dg_i =
                    match dg with Some (_, dg_i) -> dg_i | None -> -1
                  in
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
              | Delegate dg ->
                  let dg_i =
                    match dg with Some (_, dg_i) -> dg_i | None -> -1
                  in
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
              | String ->
                  self#write_instruction0
                    (if ctx.version <= 100 then S_PLUSA else S_PLUSA2)
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
          (* v12 [delegate += &Function]: the [&] operator types as
             [TyFunction], same dispatch shape as [TyMethod]. Wrap with
             [DG_NEW_FROM_METHOD] then [DG_PLUSA; DELETE]. *)
          | PlusAssign, TyFunction _ when Ain.version ctx.ain > 8 ->
              (match rhs.node with
              | FuncAddr _
              | Cast (_, { node = FuncAddr _; _ })
              | Cast (_, { node = Member (_, _, ClassMethod _); _ })
              | Cast (_, { node = Lambda _; _ })
              | Lambda _ ->
                  self#write_instruction0 DG_NEW_FROM_METHOD
              | _ -> ());
              self#write_instruction0 DG_PLUSA;
              self#write_instruction0 DELETE
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
          | MinusAssign, TyMethod _ ->
              if Ain.version ctx.ain > 8 then (
                (* v12 [event -= method]: the lhs already pushed
                   [pageref, method_idx]; wrap to a one-entry delegate
                   via [DG_NEW_FROM_METHOD], then subtract with
                   [DG_MINUSA; DELETE].  The pre-v12 [DG_ERASE]
                   shorthand expands with a spurious [PUSH -1; SWAP]
                   that overrides the receiver page. *)
                (match rhs.node with
                | Member (_, _, ClassMethod _)
                | Cast (_, { node = Member (_, _, ClassMethod _); _ })
                | Lambda _ | FuncAddr _
                | Cast (_, { node = FuncAddr _; _ })
                | Cast (_, { node = Lambda _; _ }) ->
                    self#write_instruction0 DG_NEW_FROM_METHOD
                | _ -> ());
                self#write_instruction0 DG_MINUSA;
                self#write_instruction0 DELETE)
              else self#write_instruction0 DG_ERASE
          | MinusAssign, Delegate _ -> self#write_instruction0 DG_MINUSA
          | EqAssign, (Struct _ | Ref (Struct _))
            when Ain.version_gte ctx.ain (12, 0)
                 &&
                 (match lhs.node with
                 | Ident (_, LocalVariable (i, _)) -> (
                     match (self#get_local i).value_type with
                     | Ain.Type.IFace _ -> true
                     | _ -> false)
                 | Ident (_, GlobalVariable i) -> (
                     match (Ain.get_global_by_index ctx.ain i).value_type with
                     | Ain.Type.IFace _ -> true
                     | _ -> false)
                 | Member (_, _, ClassVariable _) -> (
                     match self#member_type lhs with
                     | Ain.Type.IFace _ -> true
                     | _ -> false)
                 | _ -> (
                     match lhs.ty with
                     | Struct (name, _) | Ref (Struct (name, _)) ->
                         Hashtbl.mem ctx.interface_names name
                     | _ -> false)) ->
              (* v12 interface values are encoded as a two-slot ref-like
                 pair. Assigning a cast/concrete struct expression into an
                 interface local must transfer that pair with R_ASSIGN;
                 SR_ASSIGN treats the first slot as a struct page and asks
                 the VM to deep-copy it, which can fail as PAGE_COPY page 0
                 when the source is NULL. *)
              self#write_instruction0 R_ASSIGN
          | EqAssign, Struct (_, sno) | EqAssign, Ref (Struct (_, sno)) ->
              (* Pre-v11 [SR_ASSIGN] reads the struct type id from a
                 prior [PUSH]; ain v0/v1 and v11 have no such operand.
                 v11 also wants an explicit [A_REF] before [SR_ASSIGN]
                 when the rhs is a [DummyRef]'d call result — the call
                 leaves a single page-ref on the stack, the dummy's
                 [ASSIGN] stores it without an incref, and without an
                 [A_REF] the dummy's [SH_LOCALDELETE] frees the only
                 owner. Applies to plain function calls, HLL/array
                 calls, property getters, and chained method calls. *)
              if Ain.version ctx.ain <= 1 then ()
              else if Ain.version ctx.ain <= 8 then
                self#write_instruction1 PUSH sno
              else (
                ignore sno;
                match rhs.node with
                | DummyRef
                    ( _,
                      { node =
                          ( Call _ | New { ty = Struct _; _ }
                          | NewCall ({ ty = Struct _; _ }, _) );
                        _ } )
                | New { ty = Struct _; _ } ->
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
          (* v12 [delegate_var = NULL]: nullify by assigning the
             [-1]-pair already pushed by compile_expression on a
             NullType rhs. Dispatch on the lhs page-type. *)
          | EqAssign, NullType -> (
              match lhs.ty with
              | Delegate _ ->
                  if Ain.version ctx.ain > 8 then (
                    self#write_instruction0 DG_ASSIGN;
                    self#write_instruction0 DELETE)
                  else self#write_instruction0 DG_SET
              | Struct _ | Ref (Struct _) ->
                  self#write_instruction0 SR_ASSIGN
              | Array _ | Ref (Array _) ->
                  self#write_instruction0 X_SET
              | String -> self#write_instruction0 S_ASSIGN
              | _ ->
                  compiler_bug "NULL assignment to unsupported type"
                    (Some (ASTExpression expr)))
          | _, _ ->
              compiler_bug "invalid assignment" (Some (ASTExpression expr)))
          ))))
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_expression b
      | Ternary (test, con, alt) ->
          self#compile_expression test;
          (match test.node with
          | Member (_, _, ClassVariable _) when Ain.version ctx.ain > 8 -> ()
          | _ -> self#maybe_emit_condition_itob test);
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
          let emitted_v12_iface_var_cast =
            match (src_t, dst_t) with
            | (Struct (src_name, src_sno) | Ref (Struct (src_name, src_sno))),
              (Struct (dst_name, dst_sno) | Ref (Struct (dst_name, dst_sno)))
              when Ain.version_gte ctx.ain (12, 0)
                   && not (Int.equal src_sno dst_sno)
                   && is_variable_ref e.node
                   && Hashtbl.mem ctx.interface_names src_name ->
                self#compile_variable_ref e;
                self#write_instruction0 REF;
                self#write_instruction1 X_ICAST dst_sno;
                if Hashtbl.mem ctx.interface_names dst_name then (
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let ifnz_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  let jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at ifnz_addr current_address;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH 0;
                  self#write_address_at jump_addr current_address)
                else
                  (* iface→concrete X_ICAST leaves [page, vofs, validator]
                     on stack. We deliberately leave all three: the
                     parent context decides whether to drop down to just
                     [page] (boolean compare via the consumer-side POP at
                     the BinaryOp `!= NULL` site) or to consume all three
                     under a NULL guard for ref assignment (R_ASSIGN
                     pattern: `PUSH -1; EQUALE; IFZ skip; POP POP; PUSH
                     -1; PUSH 0; skip:; R_ASSIGN`). Emitting POP POP here
                     unconditionally was the 7dbcbaf approach and broke
                     the assignment path — the NULL guard then misfires
                     against [page] instead of [validator], the
                     subsequent R_ASSIGN reads stack garbage and crashes
                     with `Page=0,Index=<big>` (close-collection
                     teardown). *)
                  ();
                true
            | _ -> false
          in
          if not emitted_v12_iface_var_cast then (
          (* v12 [IfaceName(this)] cast: compile_expression This for a
             Struct-typed receiver emits [PUSHSTRUCTPAGE; A_REF]. The
             extra A_REF bumps the struct page's refcount, but X_ICAST
             below consumes the page without taking that ownership, so
             the leftover ref leaks and the runtime's DeletePage
             eventually fails (refcount never reaches 0). Original
             Rance10 emits a plain PUSHSTRUCTPAGE here. Bypass the
             auto-A_REF wrapper by emitting PUSHSTRUCTPAGE directly when
             the inner is bare This destined for a struct/iface X_ICAST. *)
          let is_v12_this_to_struct_cast =
            Ain.version_gte ctx.ain (12, 0)
            &&
            match (e.node, src_t, dst_t) with
            | This, Struct _, (Struct _ | Ref (Struct _)) -> true
            | _ -> false
          in
          if is_v12_this_to_struct_cast then
            self#write_instruction0 PUSHSTRUCTPAGE
          else
            self#compile_expression e;
          match (src_t, dst_t) with
          | Int, Int -> ()
          | Enum _, (Int | Enum _) -> ()
          | Int, Enum _ -> ()
          | LongInt, LongInt -> ()
          | (Int | LongInt | Enum _), Bool -> self#write_instruction0 ITOB
          | (Int | LongInt | Enum _), Float -> self#write_instruction0 ITOF
          | (Bool | Int | Enum _), LongInt -> self#write_instruction0 ITOLI
          | LongInt, (Int | Enum _) -> ()
          | (Bool | Int | LongInt | Enum _), String ->
              self#write_instruction0 I_STRING
          | Bool, (Bool | Int | Enum _) -> ()
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
          | String, Delegate dg ->
              let dg_i =
                match dg with Some (_, dg_i) -> dg_i | None -> -1
              in
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
          (* v12 originals emit X_ICAST for checked interface casts
             between distinct struct ids. *)
          | (Struct (src_name, src_sno) | Ref (Struct (src_name, src_sno))),
            (Struct (dst_name, dst_sno) | Ref (Struct (dst_name, dst_sno))) ->
              if
                Ain.version_gte ctx.ain (12, 0)
                && not (Int.equal src_sno dst_sno)
              then (
                let src_is_iface = Hashtbl.mem ctx.interface_names src_name in
                let dst_is_iface = Hashtbl.mem ctx.interface_names dst_name in
                if src_is_iface then
                  self#write_instruction0 POP;
                self#write_instruction1 X_ICAST dst_sno;
                if
                  src_is_iface && dst_is_iface
                  && not v12_iface_local_init_owns_cast_guard
                then (
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let ifnz_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  let jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at ifnz_addr current_address;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH 0;
                  self#write_address_at jump_addr current_address)
                else if
                  src_is_iface && not v12_iface_local_init_owns_cast_guard
                then (
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let ifnz_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  self#write_instruction0 POP;
                  let jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at ifnz_addr current_address;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_address_at jump_addr current_address)
                else if
                  dst_is_iface && not v12_iface_local_init_owns_cast_guard
                then (
                  (* Struct -> Iface cast (src not iface): X_ICAST pushes
                     3 items [validator (top); vofs_for_dst; original_page].
                     The downstream consumer (e.g. IFace RETURN) reads the
                     2-item pair [vofs (top); obj]. Without the null check
                     pattern, the trailing validator stays on top and the
                     consumer misreads (vofs=validator, obj=vofs). Emit the
                     same pattern as the iface->iface arm above so success
                     collapses to [vofs; original_page] and failure to
                     [-1; 0]. *)
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let ifnz_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  let jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at ifnz_addr current_address;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH 0;
                  self#write_address_at jump_addr current_address))
          (* v12 [Wrap T] is the v11 fat-ref encoding. Cast to a
             concrete struct discards the wrap — both representations
             share the underlying page-ref at the VM level. *)
          | Wrap (Struct _ | HLLParam), Struct _ -> ()
          | Struct _, Wrap (Struct _ | HLLParam) -> ()
          (* v12 wildcard sink/source: typed value flowing through an
             [hll_param] sentinel slot. No conversion needed. *)
          | HLLParam, _ | _, HLLParam -> ()
          | _ ->
              compiler_bug
                (Printf.sprintf "invalid cast from %s to %s"
                   (jaf_type_to_string src_t) (jaf_type_to_string dst_t))
                (Some (ASTExpression expr))))
      | Subscript (obj, index) -> (
          self#compile_lvalue obj;
          self#compile_expression index;
          (* v12: array of interface elements stores each entry as a
             (page, vtable_offset) pair occupying 2 slots. Scale the
             index by 2 and use REFREF to load the pair. The default
             path below uses [REF; A_REF] which reads a single slot. *)
          let element_is_v12_iface =
            Ain.version_gte ctx.ain (12, 0)
            &&
            match expr.ty with
            | Struct (name, _) | Wrap (Struct (name, _)) ->
                Hashtbl.mem ctx.interface_names name
            | _ -> false
          in
          if element_is_v12_iface then (
            self#write_instruction1 PUSH 2;
            self#write_instruction0 MUL;
            self#write_instruction0 REFREF)
          else
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
      | Member (_, _, UnresolvedMember) when Poly.equal expr.ty HLLParam ->
          (* v12 generic-receiver member access: type was widened to
             [HLLParam] because the receiver type couldn't be resolved
             (foreach loop var over a generic container, etc.). Push
             a [-1] sentinel as a stub — round-trip is intentionally
             broken on v12-wip. *)
          self#write_instruction1 PUSH (-1)
      | Member (_, _, UnresolvedMember) ->
          compiler_bug "member expression has no member_type"
            (Some (ASTExpression expr))
      | Member (_, _, ClassProperty _) ->
          (* Type analysis rewrites reads/writes on property members
             into explicit get/set method calls before codegen runs. *)
          compiler_bug "property member expression not rewritten"
            (Some (ASTExpression expr))
      | Member (_, _, ClassEvent _) ->
          (* v12 user-bodied event read as a value (e.g.
             [this.E.Empty()] or [bool b = e.IsBound]). The underlying
             delegate has no exposed slot; push a [-1] sentinel as a
             stub — v12-wip, round-trip intentionally broken. *)
          self#write_instruction1 PUSH (-1)
      (* regular function call *)
      | Call (_, args, FunctionCall function_no) ->
          let f = Ain.get_function_by_index ctx.ain function_no in
          self#pre_emit_lambda_args args;
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
          let rec is_dummyref_shape (e : expression) =
            match e.node with
            | DummyRef _ -> true
            (* v12 [Call(...)?.Method(...)] where the call returns a
               plain struct (not a ref). [variableAlloc] only wraps
               Calls whose ain-level return is [Ref]; plain-struct
               returns reach here as bare [Call]. [compile_lvalue]
               handles them like a single-slot page-ref, matching the
               [DummyRef] path. *)
            | Call (_, _, (HLLCall _ | FunctionCall _ | MethodCall _ | BuiltinCall _))
              -> true
            (* v12 cast-receiver: [(Iface)expr?.Method(...)]. The cast
               is a no-op at codegen (Struct↔Struct), so the receiver's
               shape is whatever's inside. *)
            | Cast (_, inner) -> is_dummyref_shape inner
            | _ -> false
          in
          let is_dummyref = is_dummyref_shape e in
          (* v12: walk through [Wrap T] to reach the underlying iface
             type. foreach over `ref array@IFace` or `ref array@ref T`
             binds the loop var as [Wrap (IFace _)] / [Wrap (Ref Struct)]
             — the receiver shape decisions (DUP_U2 vs DUP, REFREF vs
             REF) must look past the Wrap so dispatch sees the iface
             fat-ref instead of the Wrap handle. Mirrors v12_iface_type
             in the NullCoalesce path (codegen.ml:4932). Without this,
             `Item?.Release()` inside `foreach (Item : this.ItemList)`
             over an iface-array crashes at dispatch with garbage
             vtable offset → REF Page=N elem_count=-1 (observed at
             CEnqueteItemManager@Release during survey close). *)
          let rec v12_iface_walk (ty : jaf_type) =
            match ty with
            | Struct (name, _) | Ref (Struct (name, _)) ->
                Hashtbl.mem ctx.interface_names name
            | Wrap inner when Ain.version_gte ctx.ain (12, 0) ->
                v12_iface_walk inner
            | _ -> false
          in
          let receiver_is_iface =
            Ain.version_gte ctx.ain (12, 0) && v12_iface_walk e.ty
          in
          let receiver_is_casted_iface =
            match e.node with
            | Cast (Struct (name, _), _) | Cast (Ref (Struct (name, _)), _) ->
                Ain.version_gte ctx.ain (12, 0)
                && Hashtbl.mem ctx.interface_names name
            | _ -> false
          in
          if is_dummyref then (
            self#compile_lvalue e;
            if not receiver_is_casted_iface then
              self#write_instruction0
                (if receiver_is_iface then DUP_U2 else DUP);
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE;
            let ifnz_addr = current_address + 2 in
            self#write_instruction1 IFNZ 0;
            self#compile_method_call_for_receiver ~prefer_first_duplicate:true
              e.ty args method_no;
            self#write_instruction1 PUSH 0;
            let jump_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#write_address_at ifnz_addr current_address;
            if receiver_is_iface then (
              self#write_instruction0 POP;
              self#write_instruction0 POP)
            else self#write_instruction0 POP;
            push_null_sentinel ();
            self#write_address_at jump_addr current_address)
          else (
            self#compile_variable_ref e;
            (if Ain.version ctx.ain > 8 then
               match e.node with
               | Ident (_, LocalVariable (i, _)) -> (
                   match (self#get_local i).value_type with
                   | Ain.Type.Wrap (Ain.Type.Ref _) ->
                       self#write_instruction0 REFREF
                   (* v12 foreach-bound iface var has storage type
                      [Wrap (IFace _)]. Without [REFREF] before
                      [DUP2; REF], the null-check reads the Wrap
                      page-handle and the post-check dispatch uses
                      it as a fat-ref → vtable indexed at garbage
                      offset. Mirrors NullCoalesce path's
                      is_wrap_ref_local block (codegen.ml:5002). *)
                   | Ain.Type.Wrap (Ain.Type.IFace _)
                     when Ain.version_gte ctx.ain (12, 0) ->
                       self#write_instruction0 REFREF
                   | _ -> ())
               | _ -> ());
            self#write_instruction0 DUP2;
            self#write_instruction0 REF;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE;
            let ifnz_addr = current_address + 2 in
            self#write_instruction1 IFNZ 0;
            self#write_instruction0 (if receiver_is_iface then REFREF else REF);
            self#compile_method_call_for_receiver ~prefer_first_duplicate:true
              e.ty args method_no;
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
          let emitted_self_event_accessor_update =
            Ain.version_gte ctx.ain (12, 0)
            &&
            match (current_function, e.node, args) with
            | ( Some f,
                This,
                [ Some rhs ] )
              when f.index = method_no -> (
                let event_name_and_op =
                  match String.chop_suffix mname ~suffix:"::add" with
                  | Some event_name -> Some (event_name, DG_PLUSA)
                  | None -> (
                      match String.chop_suffix mname ~suffix:"::remove" with
                      | Some event_name -> Some (event_name, DG_MINUSA)
                      | None -> None)
                in
                let is_current_accessor =
                  String.equal f.name mname
                  ||
                  match f.struct_type with
                  | Some sno ->
                      let s = Ain.get_struct_by_index ctx.ain sno in
                      String.equal f.name (s.name ^ "@" ^ mname)
                  | None -> false
                in
                match (is_current_accessor, f.struct_type, event_name_and_op) with
                | true, Some sno, Some (event_name, op) -> (
                    let s = Ain.get_struct_by_index ctx.ain sno in
                    let short_event_name =
                      match String.rsplit2 event_name ~on:'@' with
                      | Some (_, name) -> name
                      | None -> event_name
                    in
                    let backing_name = "<" ^ short_event_name ^ ">" in
                    match
                      List.find s.members ~f:(fun (m : Ain.Variable.t) ->
                          String.equal m.name backing_name)
                    with
                    | Some member ->
                        self#write_instruction0 PUSHSTRUCTPAGE;
                        self#write_instruction1 PUSH member.index;
                        self#write_instruction0 REF;
                        self#compile_lvalue rhs;
                        self#write_instruction0 op;
                        self#write_instruction0 POP;
                        true
                    | None -> false)
                | _ -> false)
            | _ -> false
          in
          if not emitted_self_event_accessor_update then (
          self#pre_emit_lambda_args args;
          let bare_new_receiver_default_ctor =
            Ain.version_gte ctx.ain (12, 0)
            &&
            let f = Ain.get_function_by_index ctx.ain method_no in
            String.is_suffix f.name ~suffix:"@ToString"
          in
          if bare_new_receiver_default_ctor then
            self#with_bare_new_receiver_default_ctor (fun () ->
                self#compile_lvalue e)
          else self#compile_lvalue e;
          (* v11 Wrap receiver: unwrap the fat-ref before CALLMETHOD
             so the method dispatches on the wrapped struct, not the
             wrapper slot. *)
          (match e.ty with
          | Wrap (Struct (name, _) | Ref (Struct (name, _)))
            when Ain.version_gte ctx.ain (12, 0)
                 && Hashtbl.mem ctx.interface_names name ->
              (* v12 [Wrap (IFace _)] receiver: [compile_lvalue_after]
                 emitted a single [REFREF] giving the wrap target's
                 (page, idx) — where the iface fat-ref is stored. For
                 dispatch we need a second [REFREF] to read the actual
                 iface fat-ref's 2 slots (page, offset). *)
              self#write_instruction0 REFREF
          | Wrap (Struct (_, sno)) when Ain.version_gte ctx.ain (12, 0) ->
              let s = Ain.get_struct_by_index ctx.ain sno in
              if not (String.is_prefix s.name ~prefix:"I") then (
                self#write_instruction0 REFREF;
                self#write_instruction0 REF)
          | Wrap _ when Ain.version ctx.ain > 8 ->
              self#write_instruction0 REFREF;
              self#write_instruction0 REF
          | _ -> ());
          if self#lvalue_storage_is_v12_iface e
             && Option.is_none
                  (self#v12_interface_receiver_method_slot e.ty method_no)
          then self#write_instruction0 POP;
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
            &&
            let param_ty =
              match List.hd (Ain.Function.logical_parameters f) with
              | Some { value_type; _ } -> Some value_type
              | None -> None
            in
            (* v12 struct-property setters: whether the call uses the
               assignment-bookkeeping idiom ([A_REF; DUP_X2; CALLMETHOD;
               DELETE]) is decided by the property's BACKING STORAGE,
               not by the rhs shape:

               - VALUE-backed ([CASSize <GridSize>;]): the setter
                 SR_ASSIGN-copies the argument into the inline member.
                 The caller still owns the arg page, so orig increfs it
                 across the call and DELETEs it after — even when the
                 rhs is a fresh [new T(...)].
               - REF-backed ([ref T <LayoutBox>;]): the setter claims
                 the reference itself (SP_INC inside). The caller hands
                 over its page-ref with a plain [CALLMETHOD]; an extra
                 A_REF here would leak.

               Backing kinds are readable from our own struct table —
               declarations.ml's expand_property_decl collapses
               value-storable [ref T] properties to a value-typed
               [<Name>] member (the 595ffb9 rule), matching the
               original ain's member tables (verified: original
               Rance10 has [CASSize <GridSize>] vs
               [ref CEnqueteLayoutBox <LayoutBox>], and the idiom
               follows exactly that split across the 99+15 divergent
               setter sites, 2026-07-02).

               [= NULL] rhs stays a plain call regardless: A_REF on the
               [-1] NULL sentinel trips [PAGE_COPY]. Properties with no
               [<Name>] backing member (fully user-bodied accessors)
               default to the ref-backed plain call. *)
            let rhs_is_null =
              match args with
              | [ Some { node = Null; _ } ] -> true
              | _ -> false
            in
            let rhs_is_new =
              match args with
              | [ Some { node = New _ | NewCall _; _ } ] -> true
              | [ Some
                    { node = DummyRef (_, { node = New _ | NewCall _; _ }); _ }
                ] ->
                  true
              | _ -> false
            in
            (* Backing storage of the callee's property.
               [`Value]: value-typed [<Prop>] member — the setter
               copies. [`Ref]: ref-typed [<Prop>] member — the setter
               claims the reference. [`Elided]: no [<Prop>] member at
               all (every accessor is user-bodied); these behave like
               value properties at call sites (e.g.
               CPartsTimeLineItem@HeaderSize).
               [f.name] is the class-qualified callee
               ("ns::Class@Prop::set"); [mname] is only the short
               member name. *)
            let prop_backing_kind =
              match String.chop_suffix f.name ~suffix:"::set" with
              | None -> `Elided
              | Some qualified -> (
                  match String.rsplit2 qualified ~on:'@' with
                  | None -> `Elided
                  | Some (class_name, prop) -> (
                      match Ain.get_struct ctx.ain class_name with
                      | None -> `Elided
                      | Some s -> (
                          let backing = "<" ^ prop ^ ">" in
                          match
                            List.find s.members
                              ~f:(fun (m : Ain.Variable.t) ->
                                String.equal m.name backing)
                          with
                          | None -> `Elided
                          | Some m -> (
                              match m.value_type with
                              | Ain.Type.Ref _ -> `Ref
                              | _ -> `Value))))
            in
            match param_ty with
            | Some (IFace _ | Wrap _) -> false
            | Some (Ref (Struct _)) when Ain.version_gte ctx.ain (12, 0) ->
                (* NULL rhs: always a plain call (A_REF on the -1
                   sentinel trips PAGE_COPY).
                   Value/elided-backed property: idiom, even for a
                   fresh [new T(...)] — the setter copies, the caller
                   still owns and releases the arg page.
                   Ref-backed property: the setter claims the ref.
                   A fresh NEW hands over its only ref with a plain
                   call; a borrowed rhs (getter result, member read)
                   needs the idiom's A_REF so the setter's claim
                   doesn't steal the previous owner's ref. *)
                if rhs_is_null then false
                else (
                  match prop_backing_kind with
                  | `Value | `Elided -> true
                  | `Ref -> not rhs_is_new)
            | Some (Ref (Delegate _)) when Ain.version_gte ctx.ain (12, 0) ->
                (* Delegate-typed property setters take the arg as a
                   ref-delegate page. The setter stores it without its
                   own incref, so orig increfs across the call
                   ([A_REF; DUP_X2; CALLMETHOD; DELETE], e.g.
                   CEnqueteView@Prepare's [this.SendEnquete = dgFunc]).
                   Without it the stored delegate page dies with the
                   caller's arg slot — firing it later dispatches on a
                   freed page. *)
                not rhs_is_null
            | Some (Ref _) -> false
            | _ -> true
          in
          let concrete_receiver =
            Ain.version_gte ctx.ain (12, 0)
            &&
            match e.node with
            | This -> true
            | _ -> false
          in
          let direct_getter_rank =
            Ain.version_gte ctx.ain (12, 0)
            &&
            match (current_function, e.node) with
            | Some f, Ident (_, LocalVariable (i, _)) -> i < f.nr_args
            | _ -> false
          in
          if is_prop_setter then (
            let f = Ain.get_function_by_index ctx.ain method_no in
            let param_ty =
              match List.hd (Ain.Function.logical_parameters f) with
              | Some { value_type; _ } -> Some value_type
              | None -> None
            in
            (* Compound property assignment ([Prop += rhs], typeAnalysis
               marks it with an UNCALLED [Member _::get] as the Binary
               lhs). Original protocol evaluates the receiver once and
               juggles three copies: get, op, set, then RE-GETS the
               property as the expression value (statement discard POPs
               it). Exemplars: GameChapter1/2@Run [Turn += 1],
               BadCondition::GetDefaultRound [CurseTurn += 1],
               CFolder@IncrementItem/DecrementItem [NumofItem +-= 1]. *)
            let compound_prop_arg =
              match args with
              | [ Some
                    { node =
                        Binary
                          ( op,
                            { node = Member (_, _, ClassMethod (gname, getter_no));
                              ty = getter_ty;
                              _ },
                            rhs );
                      _ } ]
                when Ain.version_gte ctx.ain (12, 0)
                     && String.is_suffix gname ~suffix:"::get" ->
                  Some (op, getter_no, getter_ty, rhs)
              | _ -> None
            in
            match compound_prop_arg with
            | Some (op, getter_no, getter_ty, rhs) ->
                self#write_instruction1 PUSH 0;
                self#write_instruction0 DUP2;
                self#write_instruction0 DUP2;
                self#write_instruction0 POP;
                self#compile_method_selector ~concrete:concrete_receiver
                  ~direct_getter_rank e.ty method_no;
                self#write_instruction0 DUP_X2;
                self#write_instruction0 POP;
                self#write_instruction0 SWAP;
                self#write_instruction0 POP;
                self#write_instruction1 PUSH getter_no;
                self#write_instruction1 CALLMETHOD 0;
                self#compile_expression rhs;
                if not (self#emit_reused_receiver_binary_op getter_ty op)
                then
                  compiler_bug "unsupported compound property operator"
                    (Some (ASTExpression expr));
                self#write_instruction1 CALLMETHOD 1;
                self#write_instruction0 POP;
                self#write_instruction1 PUSH getter_no;
                self#write_instruction1 CALLMETHOD 0
            | None ->
            let reused_receiver_binary_arg =
              match (String.chop_suffix mname ~suffix:"::set", args) with
              | ( Some prop_base,
                  [ Some
                      { node =
                          Binary
                            ( op,
                              { node =
                                  Call
                                    ( { node =
                                          Member
                                            (getter_recv, getter_name, _);
                                        _ },
                                      [],
                                      MethodCall (_, getter_no) );
                                ty = getter_ty;
                                _ },
                              rhs );
                        _ } ] )
                when Ain.version_gte ctx.ain (12, 0)
                     && String.equal getter_name (prop_base ^ "::get")
                     && self#same_lvalue_shape e getter_recv
                     &&
                     (match (getter_ty, op) with
                     | (Int | Enum _ | LongInt | Float), (Plus | Minus) ->
                         true
                     | _ -> false)
                     &&
                     Option.value_map param_ty ~default:false ~f:(fun t ->
                         Poly.equal t (jaf_to_ain_type getter_ty)) ->
                  Some (op, getter_no, getter_ty, rhs)
              | _ -> None
            in
            let emitted_reused_receiver_arg =
              match reused_receiver_binary_arg with
              | Some (op, getter_no, getter_ty, rhs) ->
                  (* v12 original reuses the already-pushed setter receiver
                     as the getter receiver for [x.Prop = x.Prop + rhs].
                     This keeps the page-ref ownership pattern aligned with
                     the SDK output. *)
                  let interface_receiver =
                    Option.is_some
                      (self#v12_interface_receiver_method_slot
                         ~direct_getter_rank:false e.ty method_no)
                  in
                  if interface_receiver then self#write_instruction0 DUP2
                  else (
                    self#write_instruction1 PUSH 0;
                    self#write_instruction0 DUP2;
                    self#write_instruction0 POP);
                  self#compile_method_selector ~concrete:concrete_receiver
                    ~direct_getter_rank e.ty method_no;
                  self#write_instruction0 DUP_X2;
                  self#write_instruction0 POP;
                  self#write_instruction0 SWAP;
                  if not interface_receiver then self#write_instruction0 POP;
                  if interface_receiver then
                    self#compile_method_selector ~direct_getter_rank e.ty
                      getter_no
                  else self#write_instruction1 PUSH getter_no;
                  self#write_instruction1 CALLMETHOD 0;
                  self#compile_expression rhs;
                  self#emit_reused_receiver_binary_op getter_ty op
              | None -> false
            in
            if not emitted_reused_receiver_arg then (
              self#compile_method_selector ~concrete:concrete_receiver e.ty
                ~direct_getter_rank method_no;
              let prev = in_prop_setter_arg in
              Exn.protect
                ~f:(fun () ->
                  in_prop_setter_arg <- true;
                  self#compile_function_arguments args f)
                ~finally:(fun () -> in_prop_setter_arg <- prev));
            let is_ref_struct_new_setter =
              match param_ty with
              | Some (Ref (Struct _ | Delegate _)) -> true
              | _ -> false
            in
            if is_ref_struct_new_setter then self#write_instruction0 A_REF;
            self#write_instruction0 DUP_X2;
            (* String setters need an extra [A_REF] before [CALLMETHOD]
               so the trailing [DELETE] correctly releases the
               duplicated page-ref left on the stack. Other types
               (Bool/Int/Float/Struct) don't need this — scalars
               carry no refcount and Struct comes through a DummyRef
               whose [SH_LOCALDELETE] handles cleanup. *)
            let is_string_setter =
              match param_ty with Some String -> true | _ -> false
            in
            if is_string_setter then self#write_instruction0 A_REF;
            self#write_instruction1 CALLMETHOD f.nr_args;
            if is_string_setter || is_ref_struct_new_setter then
              self#write_instruction0 DELETE
            else self#write_instruction0 POP)
          else
            let rec prefer_first_duplicate_receiver (e : expression) =
              match e.node with
              | Call _ | DummyRef _ -> true
              | Cast (_, inner) -> prefer_first_duplicate_receiver inner
              | _ -> false
            in
            self#compile_method_call_for_receiver
              ~concrete:concrete_receiver ~direct_getter_rank
              ~prefer_first_duplicate:(prefer_first_duplicate_receiver e)
              e.ty args method_no)
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
              (* v12: the receiver may be a [Call] / [DummyRef] / [Cast]
                 (e.g. [this.GetItemList()?.Any(...)]) rather than a
                 plain variable ref. Use [compile_lvalue] for those —
                 it leaves a single-slot page-ref on the stack matching
                 what [compile_variable_ref + DUP2 + REF] would have
                 produced for a variable. *)
              let rec is_dummyref_shape (e : expression) =
                match e.node with
                | DummyRef _ -> true
                | Call (_, _, (HLLCall _ | FunctionCall _ | MethodCall _ | BuiltinCall _))
                  -> true
                | Cast (_, inner) -> is_dummyref_shape inner
                | _ -> false
              in
              let is_dummyref = is_dummyref_shape e in
              if is_dummyref then (
                self#compile_lvalue e;
                self#write_instruction0 DUP;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE;
                let ifnz_addr = current_address + 2 in
                self#write_instruction1 IFNZ 0;
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
                (match f.return_type with
                | Ain.Type.Void -> self#write_instruction1 PUSH (-1)
                | _ ->
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction1 PUSH (-1));
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
                self#write_address_at jump_addr current_address))
      (* HLL function call *)
      | Call (_, args, HLLCall (lib_no, fun_no)) ->
          self#pre_emit_lambda_args args;
          let f = Ain.function_of_hll_function_index ctx.ain lib_no fun_no in
          let lib = Ain.get_library_by_index ctx.ain lib_no in
          self#compile_hll_function_arguments lib args f;
          if Ain.version ctx.ain > 8 then
            (* v11 [CALLHLL] carries an extra type-id operand. For Array
               library methods it's the element type of the receiver;
               for everything else the runtime ignores it and -1 is
               fine. *)
            let type_id =
              if String.equal lib.name "Array" then
                match args with
                | Some receiver :: _ ->
                    self#array_element_type_code_for_expr receiver
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
          (* Same bare-push rule as [compile_hll_function_arguments]:
             stores into REF-element arrays don't bump the value arg. *)
          let ref_elem_store =
            Ain.version_gte ctx.ain (12, 0)
            && (match builtin with
               | ArrayPushBack | ArrayInsert | ArrayFill -> true
               | _ -> false)
            &&
            match e.ty with
            | Array (Ref _ | Wrap (Ref _))
            | Ref (Array (Ref _ | Wrap (Ref _))) ->
                true
            | _ -> false
          in
          if ref_elem_store then (
            let prev = in_ref_elem_hll_store_arg in
            in_ref_elem_hll_store_arg <- true;
            Exn.protect
              ~f:(fun () -> self#compile_function_arguments args f)
              ~finally:(fun () -> in_ref_elem_hll_store_arg <- prev))
          else self#compile_function_arguments args f;
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
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayAlloc ->
              self#write_instruction1 PUSH (List.length args);
              self#write_instruction0 A_ALLOC
          | ArrayRealloc when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Realloc"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayRealloc ->
              (* FIXME: this built-in should be variadic *)
              self#write_instruction1 PUSH 1;
              self#write_instruction0 A_REALLOC
          | ArrayFree when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Free"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayFree -> self#write_instruction0 A_FREE
          | ArrayNumof when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Numof"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayNumof -> self#write_instruction0 A_NUMOF
          | ArrayCopy when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Copy"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayCopy -> self#write_instruction0 A_COPY
          | ArrayFill when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Fill"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayFill -> self#write_instruction0 A_FILL
          | ArrayPushBack when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "PushBack"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayPushBack -> self#write_instruction0 A_PUSHBACK
          | ArrayPopBack when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "PopBack"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayPopBack -> self#write_instruction0 A_POPBACK
          | ArrayEmpty when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Empty"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayEmpty -> self#write_instruction0 A_EMPTY
          | ArrayErase when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Erase"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayErase -> self#write_instruction0 A_ERASE
          | ArrayInsert when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Insert"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayInsert -> self#write_instruction0 A_INSERT
          | ArraySort when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Sort"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArraySort -> self#write_instruction0 A_SORT
          | ArraySortBy when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "SortMem"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArraySortBy -> self#write_instruction0 A_SORT_MEM
          | ArrayReverse when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Reverse"
                (self#array_element_type_code_for_expr e)
                (ASTExpression expr)
          | ArrayReverse -> self#write_instruction0 A_REVERSE
          | ArrayFind when Ain.version ctx.ain > 8 ->
              self#compile_CALLHLL "Array" "Find"
                (self#array_element_type_code_for_expr e)
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
      | Call (e, _args, UnresolvedCall)
        when Poly.(e.ty = HLLParam) || Poly.(expr.ty = HLLParam) ->
          (* v11 [hll_param] call — the callee type stays unresolved
             through typeAnalysis because [hll_param] is a runtime-
             polymorphic slot. Compile the callee and push a zero
             placeholder so downstream stack shape is correct; the
             actual dispatch happens via the HLL bridge at runtime.
             v12 also reaches here through unknown_delegate / generic-
             property callees where only [expr.ty] (the call result)
             got widened to [HLLParam]. *)
          self#compile_expression e;
          self#write_instruction1 PUSH 0
      | Call (_, _, _) ->
          compiler_bug "invalid call expression" (Some (ASTExpression expr))
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression expr))
      | NewCall ({ ty = Struct (struct_name, s_no); _ }, args) ->
          (* v12 `new T(args)`: original Rance10 pushes args BEFORE the
             NEW opcode, then NEW with the ctor function index that
             matches the arg count.
             Example: new CASColor(0, 0, 0, 255) emits:
               PUSH 0; PUSH 0; PUSH 0; PUSH 255
               NEW struct(455), 18568:CASColor@0  (the 4-arg ctor)
             not the default-ctor index from struct.constructor. *)
          self#compile_newcall struct_name s_no args
      | NewCall _ ->
          compiler_bug "NewCall on non-struct type"
            (Some (ASTExpression expr))
      | ArrayLiteral _ ->
          compiler_bug "bare array literal expression"
            (Some (ASTExpression expr))
      | RvalueRef _ ->
          compiler_bug "RvalueRef in rvalue context" (Some (ASTExpression expr))
      | DummyRef _ ->
          self#compile_lvalue expr;
          (* In v11, [compile_lvalue]'s dummy-populate path already emits
             the appropriate deref for struct/array dummies, so the stack
             is already the shape [compile_expression] would have produced
             via [SR_REF2]. Pre-v11 still needs [SR_REF2]. Enums are
             scalars here like everywhere else ([compile_dereference],
             [is_ref_scalar]) — omitting them left the lvalue's 2-slot
             (page, index) pair where the consumer expected one value:
             [return list.At(...)] in the enum-returning
             [GameConfig::GetNextSpeedType] returned the INDEX and
             leaked the page id into the caller, whose setter
             CALLMETHOD then popped the page id as its method number —
             【CALLMETHOD】存在しない関数番号 on every game-speed
             button click. *)
          if Ain.version ctx.ain > 8 then
            (match expr.ty with
            | Int | Float | Bool | LongInt | Enum _ | FuncType _ ->
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
          (* v12 NULL flowing through a [ternary ? meth : NULL] where
             the other branch is a method ref. Push the v11 method-
             ref null-pair. *)
          | TyMethod _ | TyFunction _ when Ain.version ctx.ain > 8 ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH 0
          (* v12 interface NULL: interface values are two-slot
             [page, slot] pairs. [this.Activity = NULL] / passing
             [NULL] as an interface argument needs both slots pushed
             so the setter / function reads the right arity.
             Interfaces are represented in [jaf_type] as
             [Struct (name, _)] where [name] is in
             [ctx.interface_names]. *)
          | Struct (name, _)
            when Ain.version_gte ctx.ain (12, 0)
                 && Hashtbl.mem ctx.interface_names name ->
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH 0
          | ty ->
              compiler_bug
                ("unimplemented: NULL rvalue of type " ^ jaf_type_to_string ty)
                (Some (ASTExpression expr)))
      | Lambda f ->
          let lambda_idx = Option.value_exn f.index in
          let emit_lambda_receiver () =
            (* The delegate's bound page is the executing frame: struct
               page inside methods, and inside LAMBDA bodies too — a
               nested lambda must inherit the enclosing lambda's page or
               its env chain breaks and firing it CALLMETHODs a NULL
               object (Rance10 quest-map selection events: startEvent /
               endEvent lambdas built inside the RunMapQuest factory
               lambda). Lambdas hosted by static functions run with page
               -1, where PUSHSTRUCTPAGE degrades to -1 at runtime — same
               encoding the original emits. Our lambda names don't carry
               the original's [Class@] prefix, so the "@" check alone
               misses lambdas nested in static-function lambdas — also
               match the [<lambda] marker every generated name embeds. *)
            match current_function with
            | Some f
              when Option.is_some f.struct_type
                   || String.is_substring f.name ~substring:"@"
                   || String.is_substring f.name ~substring:"<lambda" ->
                self#write_instruction0 PUSHSTRUCTPAGE
            | _ -> self#write_instruction1 PUSH (-1)
          in
          if
            Hashtbl.mem v12_assignment_lambdas lambda_idx
            || Hashtbl.mem pre_emitted_lambdas lambda_idx
          then
            (* pre_emit_lambda_args writes the body; second encounter
               just pushes the receiver+index. *)
            emit_lambda_receiver ()
          else (
            (* Inline the lambda body inside the outer function, between
               a JUMP-over and the receiver push. Each lambda decl in
               source produces an inline FUNC...ENDFUNC block at that
               point in the outer's bytecode. v12 original Rance10 has
               ~21k inline FUNC opcodes vs our ~400 under dedup — letting
               each use re-emit a fresh body matches the original layout. *)
            let jump_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#compile_function f;
            self#write_address_at jump_addr current_address;
            Hashtbl.set pre_emitted_lambdas ~key:lambda_idx ~data:();
            emit_lambda_receiver ());
          self#write_instruction1 PUSH lambda_idx
      | OptionalMember (obj, name, mt) ->
          (* [a?.b] rvalue: evaluate [a]; if the result is the [-1]
             null sentinel, push the type-appropriate default; else
             access [.b] on [a]. *)
          let optional_iface_member =
            Ain.version_gte ctx.ain (12, 0)
            &&
            match (mt, expr.ty) with
            | ClassVariable _, (Struct (name, _) | Ref (Struct (name, _))) ->
                Hashtbl.mem ctx.interface_names name
            | _ -> false
          in
          if optional_iface_member then (
            match mt with
            | ClassVariable var_no ->
                self#compile_expression obj;
                self#write_instruction0 DUP;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE;
                let outer_null_addr = current_address + 2 in
                self#write_instruction1 IFNZ 0;
                self#write_instruction1 PUSH var_no;
                self#write_instruction0 DUP2;
                self#write_instruction0 REF;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE;
                let inner_null_addr = current_address + 2 in
                self#write_instruction1 IFNZ 0;
                self#write_instruction0 REFREF;
                self#write_instruction1 PUSH 0;
                let inner_end_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at inner_null_addr current_address;
                self#write_instruction0 POP;
                self#write_instruction0 POP;
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH (-1);
                self#write_address_at inner_end_addr current_address;
                let outer_end_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at outer_null_addr current_address;
                self#write_instruction0 POP;
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH (-1);
                self#write_address_at outer_end_addr current_address;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE;
                let final_null_addr = current_address + 2 in
                self#write_instruction1 IFNZ 0;
                let final_end_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at final_null_addr current_address;
                self#write_instruction0 POP;
                self#write_instruction0 POP;
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH 0;
                self#write_address_at final_end_addr current_address
            | _ -> compiler_bug "optional interface member expected field"
                     (Some (ASTExpression expr)))
          else (
            (* v11+: [compile_expression] on a [Ref T] obj emits
               [REF; A_REF] (the deref pattern). When [obj] is NULL
               (-1), the A_REF bump triggers a [PAGE_COPY page=-1]
               crash because the VM tries to incref a non-existent
               page. Use [compile_lvalue]+[REF] (no A_REF) for the
               null-check so we only attempt to bump after we've
               confirmed the value isn't NULL. The A_REF (if needed)
               is implicit in the subsequent member access path. *)
            let obj_needs_aref_skip =
              Ain.version ctx.ain > 8
              && match obj.ty with
                 | Ref (Struct _ | Array _ | String | Delegate _)
                 | Struct _ | Array _ | Delegate _ -> true
                 | _ -> false
            in
            if obj_needs_aref_skip && is_variable_ref obj.node then
              (* [compile_lvalue] for a [Ref Struct] global/local
                 emits [PUSHxPAGE; PUSH i; REF] — the REF already
                 reads the slot value (the ref/page-id). No A_REF
                 needed for the null check. *)
              self#compile_lvalue obj
            else self#compile_expression obj;
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
            self#write_address_at jump_addr current_address)
      | NullCoalesce (a, b) ->
          let a_inner =
            match a.node with DummyRef (_, inner) -> inner | _ -> a
          in
          let unwrap_dummy (e : expression) =
            match e.node with DummyRef (_, inner) -> inner | _ -> e
          in
          let v12_iface_type (ty : jaf_type) =
            let rec walk (t : jaf_type) =
              match t with
              | Struct (name, _) | Ref (Struct (name, _)) ->
                  Hashtbl.mem ctx.interface_names name
              (* v12 foreach-bound iface var: storage is [Wrap T] where
                 T is the iface. Treat as iface for receiver-shape
                 decisions so the not-null branch emits the second
                 REFREF to materialize the fat-ref before dispatch. *)
              | Wrap inner -> walk inner
              | _ -> false
            in
            Ain.version_gte ctx.ain (12, 0) && walk ty
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
          match a_inner.node with
          | Binary (((Equal | NEqual) as cmp_op), cmp_lhs, cmp_rhs)
            when Ain.version_gte ctx.ain (12, 0)
                 && (let rec strip (e : expression) =
                       match e.node with
                       | DummyRef (_, inner)
                       | Cast (_, inner)
                       | RvalueRef inner ->
                           strip inner
                       | _ -> e
                     in
                     match (strip cmp_lhs).node with
                    | OptionalMember (r, _, ClassMethod _) ->
                        is_variable_ref r.node
                    | Call
                        ( { node = OptionalMember (r, _, ClassMethod _); _ },
                          _,
                          MethodCall _ ) ->
                        is_variable_ref r.node
                    | _ -> false) ->
              (* v12 [(recv?.Prop == X) ?? fb] — the null test wraps the
                 WHOLE comparison: orig tests the receiver, jumps to the
                 fallback when null, and re-reads the receiver for a
                 plain getter + compare in the live arm. Routing the
                 inner optional through the generic (value, marker)
                 protocol instead EQUALEs the MARKER against X and
                 strands the value slot — a one-slot VM stack leak per
                 execution that detonates in the caller's next page
                 op. Exemplar (only site in Rance10):
                 [CardApView@Set]'s
                 [s?.Kind == SkillKind::Action ?? false] leaked during
                 BattleCardButton construction; the collection's
                 element store then died as 【 DeletePage 】 at battle
                 entry. *)
              let receiver, getter_no =
                let rec strip (e : expression) =
                  match e.node with
                  | DummyRef (_, inner) | Cast (_, inner) | RvalueRef inner ->
                      strip inner
                  | _ -> e
                in
                match (strip cmp_lhs).node with
                | OptionalMember (r, _, ClassMethod (_, g)) -> (r, g)
                | Call ({ node = OptionalMember (r, _, ClassMethod (_, g)); _ },
                        _, _ ) ->
                    (r, g)
                | _ ->
                    compiler_bug "optional-compare ?? arm: unexpected lhs"
                      (Some (ASTExpression expr))
              in
              let emit_recv_value () =
                self#compile_variable_ref receiver;
                (match receiver.node with
                | Ident (_, LocalVariable (i, _)) -> (
                    match (self#get_local i).value_type with
                    | Ain.Type.Wrap (Ain.Type.Ref _)
                    | Ain.Type.Wrap (Ain.Type.IFace _) ->
                        self#write_instruction0 REFREF
                    | _ -> ())
                | _ -> ());
                self#write_instruction0 REF
              in
              emit_recv_value ();
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let live_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#compile_expression b;
              let merge_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at live_addr current_address;
              emit_recv_value ();
              self#write_instruction1 PUSH getter_no;
              self#write_instruction1 CALLMETHOD 0;
              self#compile_expression cmp_rhs;
              self#write_instruction0
                (match cmp_op with Equal -> EQUALE | _ -> NOTE);
              self#write_address_at merge_jump current_address
          | Call ({ node = OptionalMember _; _ }, _, _)
            when Ain.version_gte ctx.ain (12, 0)
                 && (match expr.ty with Array _ -> true | _ -> false)
                 && (match b.node with
                    | DummyRef
                        (_, { node = DummyRef (_, { node = ArrayLiteral []; _ });
                              _ }) ->
                        true
                    | _ -> false) ->
              (* v12 [recv?.GetList() ?? []] value form. orig: run the
                 optional call's (value, marker) merge, then on null
                 DELETE the placeholder, CLEAR the [new array<T>] dummy
                 (Array.Free, keeping one ref via DUP) and release the
                 receiver-chain call dummy early; on live, store the
                 result into the [右辺値参照化用] spill (keeping the
                 value); ONE [A_REF] covers both arms. The old routing
                 compiled the fallback through the ArrayLiteral-lvalue
                 emission — its A_REF landed in the NULL arm only, so
                 the live arm returned a BORROWED array page and the
                 caller's cleanup freed the collection's real array
                 (PlayerCardCollection@GetOrganizationCards, fires when
                 an organization has no instances). *)
              let rv_no, arr_no =
                match b.node with
                | DummyRef (rv, { node = DummyRef (arr, _); _ }) -> (rv, arr)
                | _ ->
                    compiler_bug "array ?? [] arm: unexpected fallback"
                      (Some (ASTExpression expr))
              in
              let receiver_spine_dummies =
                let rec collect (e : expression) acc =
                  match e.node with
                  | DummyRef (no, inner) -> collect inner (no :: acc)
                  | OptionalMember (recv, _, _) | Member (recv, _, _) ->
                      collect recv acc
                  | Call ({ node = OptionalMember (recv, _, _); _ }, _, _) ->
                      collect recv acc
                  | _ -> acc
                in
                collect a_inner []
              in
              self#compile_expression a;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let live_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 DELETE;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH arr_no;
              self#write_instruction0 REF;
              self#write_instruction0 DUP;
              self#compile_CALLHLL "Array" "Free"
                (self#array_element_type_code expr.ty)
                (ASTExpression expr);
              List.iter receiver_spine_dummies ~f:(fun no ->
                  self#write_instruction1 SH_LOCALDELETE no;
                  match Stack.top scopes with
                  | Some scope ->
                      scope.vars <-
                        List.filter scope.vars ~f:(fun sv ->
                            not (Int.equal sv.index no))
                  | None -> ());
              let merge_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at live_addr current_address;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH rv_no;
              self#write_instruction0 REF;
              self#write_instruction0 DELETE;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction0 SWAP;
              self#write_instruction1 PUSH rv_no;
              self#write_instruction0 SWAP;
              self#write_instruction0 ASSIGN;
              self#write_address_at merge_jump current_address;
              self#write_instruction0 A_REF
          | Member (field_recv, _, ClassVariable var_no)
            when Ain.version_gte ctx.ain (12, 0)
                 && (match expr.ty with
                    | Int | Bool | Float | Enum _ -> true
                    | _ -> false)
                 && Option.is_some (self#optional_getter_field_chain field_recv)
            ->
              (* v12 [base.Opt?.Getter....field ?? fallback] — scalar
                 field at the end of an optional GETTER CHAIN. Same
                 deferred-pair protocol as the variable-receiver arm
                 below, but the pair's page comes from the chain's last
                 call result: call the optional getter (spilling each
                 hop into its 戻り値 dummy), null-test its result, run
                 the remaining plain getter hops in the live branch,
                 then juggle (result, field idx, marker) across the
                 merge; the null paths push (-1,-1,-1) and the fallback
                 repoints the pair at the 右辺値参照化用 spill. One
                 trailing [REF] serves both arms. Our generic path left
                 a bare -1 on the null side and dereferenced it
                 unconditionally: [act.Leader?.State.IsCritical ??
                 false] crashed every non-sure-hit ENEMY attack with
                 【REF】Page=-1 Index=4
                 (AvoidanceCalculator@IsAttackHitConstantlyBySkillAndState;
                 same family as the CMotionAlphaData@AddParam follow-up
                 recorded on c4e983c). *)
              let base, inner_hops, (opt_g, opt_d), outer_hops =
                Option.value_exn (self#optional_getter_field_chain field_recv)
              in
              let spill dummy_no =
                self#scope_add_var (self#get_local dummy_no);
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH dummy_no;
                self#write_instruction0 REF;
                self#emit_slot_release;
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction0 SWAP;
                self#write_instruction1 PUSH dummy_no;
                self#write_instruction0 SWAP;
                self#write_instruction0 ASSIGN
              in
              let hop (g, d) =
                self#write_instruction1 PUSH g;
                self#write_instruction1 CALLMETHOD 0;
                spill d
              in
              (match base.node with
              | This -> self#write_instruction0 PUSHSTRUCTPAGE
              | _ ->
                  self#compile_variable_ref base;
                  self#write_instruction0 REF);
              List.iter inner_hops ~f:hop;
              self#write_instruction0 DUP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let outer_null_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              hop (opt_g, opt_d);
              List.iter outer_hops ~f:hop;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 DUP_U2;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let inner_null_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#write_instruction1 PUSH 0;
              let inner_ok_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at inner_null_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at inner_ok_jump current_address;
              let merge_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at outer_null_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at merge_jump current_address;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let deref_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              (match b.node with
              | DummyRef (dummy_idx, inner) ->
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
              self#write_address_at deref_addr current_address;
              self#write_instruction0 REF
          | OptionalMember (receiver, _, ClassVariable var_no)
            when Ain.version_gte ctx.ain (12, 0)
                 && is_variable_ref receiver.node
                 && (match expr.ty with
                    | Int | Bool | Float | Enum _ -> true
                    | _ -> false) ->
              (* v12 [recv?.field ?? fallback], scalar field, value form.
                 The original defers the field READ past the merge as a
                 (page, index) pair + status marker (null = -1;-1;-1):
                 the null branch pops the pair, evaluates the fallback
                 and gives it a home — the [<dummy : 右辺値参照化用>]
                 local (or the fallback's own slot when it's an lvalue) —
                 so one trailing [REF] dereferences whichever pair
                 survived. The generic arm instead read the field
                 in-branch and pushed the scalar default [0] on null,
                 which the [??] merge's [-1] test never matched — the
                 fallback silently never applied. Exemplar:
                 [SceneQuestMap@Run]'s [m_restoreInfo?.IsNeedRunEvent ??
                 true] evaluated false on fresh quests, skipping the
                 quest-opening event. *)
              let is_wrap_ref_local =
                match receiver.node with
                | Ident (_, LocalVariable (i, _)) -> (
                    match (self#get_local i).value_type with
                    | Ain.Type.Wrap (Ain.Type.Ref _) -> true
                    | Ain.Type.Wrap (Ain.Type.IFace _) -> true
                    | _ -> false)
                | _ -> false
              in
              self#compile_variable_ref receiver;
              if is_wrap_ref_local then self#write_instruction0 REFREF;
              self#write_instruction0 DUP2;
              self#write_instruction0 REF;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let outer_null_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#write_instruction0 REF;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 DUP_U2;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let inner_null_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#write_instruction1 PUSH 0;
              let inner_ok_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at inner_null_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at inner_ok_jump current_address;
              let merge_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at outer_null_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at merge_jump current_address;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let deref_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              (match b.node with
              | DummyRef (dummy_idx, inner) ->
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
              self#write_address_at deref_addr current_address;
              self#write_instruction0 REF
          | OptionalMember (receiver, _, ClassVariable var_no)
            when Ain.version_gte ctx.ain (12, 0)
                 && is_variable_ref receiver.node
                 && (match expr.ty with String -> true | _ -> false) ->
              (* v12 [recv?.strfield ?? fallback], string field, value
                 form. Unlike the scalar deferral above, the original
                 reads the string page IN the not-null branch (with its
                 own null test on the string itself), merges a (value,
                 marker) pair, stores the fallback into the [<dummy :
                 右辺値参照化用>] spill (releasing the dummy's old value
                 first), and [A_REF]s the merged result — the read is a
                 borrowed page ref, and the consumer's trailing [DELETE]
                 (e.g. after [S_ASSIGN]) must not free the source
                 member's only reference. Our old in-branch shape
                 skipped the dummy and the bump: constructing
                 [SpecificBattleSkillConverter] freed [g_enemy.CreateId]
                 and the next construction crashed battle entry with
                 [ページの取得に失敗２：S_ASSIGN]. *)
              let is_wrap_ref_local =
                match receiver.node with
                | Ident (_, LocalVariable (i, _)) -> (
                    match (self#get_local i).value_type with
                    | Ain.Type.Wrap (Ain.Type.Ref _) -> true
                    | Ain.Type.Wrap (Ain.Type.IFace _) -> true
                    | _ -> false)
                | _ -> false
              in
              self#compile_variable_ref receiver;
              if is_wrap_ref_local then self#write_instruction0 REFREF;
              self#write_instruction0 DUP2;
              self#write_instruction0 REF;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let outer_null_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#write_instruction0 REF;
              self#write_instruction1 PUSH var_no;
              self#write_instruction0 REF;
              self#write_instruction0 DUP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let inner_null_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#write_instruction1 PUSH 0;
              let inner_ok_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at inner_null_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at inner_ok_jump current_address;
              let merge_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at outer_null_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at merge_jump current_address;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let live_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              (match b.node with
              | DummyRef (dummy_idx, inner) ->
                  self#compile_expression inner;
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction1 PUSH dummy_idx;
                  self#write_instruction0 REF;
                  self#write_instruction0 DELETE;
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction0 SWAP;
                  self#write_instruction1 PUSH dummy_idx;
                  self#write_instruction0 SWAP;
                  self#write_instruction0 ASSIGN
              | _ -> self#compile_expression b);
              self#write_address_at live_addr current_address;
              self#write_instruction0 A_REF
          | OptionalMember (receiver, _, ClassMethod (_, method_no))
            when Ain.version ctx.ain > 8 ->
              (* v12 [receiver?.Property ?? fallback].  Like optional
                 method calls, defer the getter until after the ?? null
                 check.  Foreach locals over arrays of refs are stored as
                 Wrap(Ref Struct); the original unwraps that wrapper with
                 REFREF before checking the referenced page. *)
              let receiver_is_iface = v12_iface_type receiver.ty in
              let rec is_dummyref_shape (e : expression) =
                match e.node with
                | DummyRef _ -> true
                | Call
                    ( _,
                      _,
                      ( HLLCall _ | FunctionCall _ | MethodCall _
                      | BuiltinCall _ ) ) ->
                    true
                | Cast (_, inner) -> is_dummyref_shape inner
                | _ -> false
              in
              let is_dummyref = is_dummyref_shape receiver in
              let receiver_is_casted_from_iface =
                match receiver.node with
                | Cast
                    ( _,
                      {
                        ty = Struct (name, _) | Ref (Struct (name, _));
                        _;
                      } ) ->
                    Hashtbl.mem ctx.interface_names name
                | _ -> false
              in
              let is_wrap_ref_local =
                match receiver.node with
                | Ident (_, LocalVariable (i, _)) -> (
                    match (self#get_local i).value_type with
                    | Ain.Type.Wrap (Ain.Type.Ref _) -> true
                    (* v12 foreach-bound iface var has storage type
                       [Wrap (IFace _)] (e.g. [Item] in
                       [foreach (Item : this.ItemList) Item?.SetInfo(...)]).
                       Same as [Wrap (Ref _)] it needs a [REFREF] unwrap
                       before [DUP2; REF] so the null check reads the
                       underlying iface fat-ref, not the Wrap handle.
                       Without this, dispatch sees a garbage offset and
                       [REF vtable[offset+method_no]] crashes OOB. *)
                    | Ain.Type.Wrap (Ain.Type.IFace _)
                      when Ain.version_gte ctx.ain (12, 0) ->
                        true
                    | _ -> false)
                | _ -> false
              in
              if is_dummyref then (
                self#compile_lvalue receiver;
                if not receiver_is_casted_from_iface then
                  self#write_instruction0
                    (if receiver_is_iface then DUP_U2 else DUP);
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE)
              else (
                self#compile_variable_ref receiver;
                if is_wrap_ref_local then self#write_instruction0 REFREF;
                self#write_instruction0 DUP2;
                self#write_instruction0 REF;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE);
              let ifnz_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              if not is_dummyref then
                self#write_instruction0
                  (if receiver_is_iface then REFREF else REF);
              self#write_instruction1 PUSH 0;
              let optional_jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifnz_addr current_address;
              if is_dummyref then (
                self#write_instruction0 POP;
                if receiver_is_iface || receiver_is_casted_from_iface then
                  self#write_instruction0 POP)
              else (
                self#write_instruction0 POP;
                self#write_instruction0 POP);
              self#write_instruction1 PUSH (-1);
              if receiver_is_iface then self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at optional_jump_addr current_address;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifz_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              if receiver_is_iface then self#write_instruction0 POP;
              self#compile_expression b;
              let jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifz_addr current_address;
              self#compile_method_call_for_receiver receiver.ty [] method_no;
              self#write_address_at jump_addr current_address
          | Call
              ( { node = OptionalMember (receiver, opt_mname, _); _ },
                args,
                MethodCall (_, method_no) )
            when Ain.version ctx.ain > 8 ->
              (* v12 [receiver?.Method() ?? fallback].  Keep the
                 receiver live across the optional-status check and
                 call the method only in the non-null branch.  Emitting
                 the call before the [??] check can vtable-deref a
                 [-1] receiver for chained property reads like
                 [this.Parts?.Parent ?? 0]. *)
              self#pre_emit_lambda_args args;
              let receiver_is_iface = v12_iface_type receiver.ty in
              let rec is_dummyref_shape (e : expression) =
                match e.node with
                | DummyRef _ -> true
                | Call
                    ( _,
                      _,
                      ( HLLCall _ | FunctionCall _ | MethodCall _
                      | BuiltinCall _ ) ) ->
                    true
                | Cast (_, inner) -> is_dummyref_shape inner
                | _ -> false
              in
              let is_dummyref = is_dummyref_shape receiver in
              let receiver_is_casted_from_iface =
                match receiver.node with
                | Cast
                    ( _,
                      {
                        ty = Struct (name, _) | Ref (Struct (name, _));
                        _;
                      } ) ->
                    Hashtbl.mem ctx.interface_names name
                | _ -> false
              in
              let is_wrap_ref_local =
                match receiver.node with
                | Ident (_, LocalVariable (i, _)) -> (
                    match (self#get_local i).value_type with
                    | Ain.Type.Wrap (Ain.Type.Ref _) -> true
                    (* v12 foreach-bound iface var has storage type
                       [Wrap (IFace _)] (e.g. [Item] in
                       [foreach (Item : this.ItemList) Item?.SetInfo(...)]).
                       Same as [Wrap (Ref _)] it needs a [REFREF] unwrap
                       before [DUP2; REF] so the null check reads the
                       underlying iface fat-ref, not the Wrap handle.
                       Without this, dispatch sees a garbage offset and
                       [REF vtable[offset+method_no]] crashes OOB. *)
                    | Ain.Type.Wrap (Ain.Type.IFace _)
                      when Ain.version_gte ctx.ain (12, 0) ->
                        true
                    | _ -> false)
                | _ -> false
              in
              let is_value_prop_setter =
                Ain.version ctx.ain > 8
                &&
                let f = Ain.get_function_by_index ctx.ain method_no in
                String.is_suffix f.name ~suffix:"::set"
                && List.length args = 1
                && Poly.equal f.return_type Ain.Type.Void
                &&
                match List.hd (Ain.Function.logical_parameters f) with
                | Some { value_type = IFace _ | Ref _ | Wrap _; _ } -> false
                | _ -> true
              in
              (* Property READS ([x?.Prop ?? b], the getter has no
                 source-level call syntax) are DEFERRED by the original
                 compiler like all optional-chain consumers — the
                 receiver crosses the merge as a padded 2-slot pair.
                 Only explicit method calls ([x?.M() ?? b]) evaluate
                 inside the non-null branch (exemplars: deferred
                 CommonMenu@IsQuestRetireEnable [findQuestFromId(..)?
                 .IsRetireEnable ?? false] vs in-branch CEnqueteView@
                 MouseWheelEvent [this.Item?.IsFocusTextBox() ?? false]). *)
              let is_property_getter =
                let f = Ain.get_function_by_index ctx.ain method_no in
                (String.is_suffix f.name ~suffix:"::get"
                || String.is_substring f.name ~substring:"::get#")
                && List.is_empty args
              in
              if
                is_dummyref
                && (not receiver_is_iface)
                && (not receiver_is_casted_from_iface)
                && (not is_value_prop_setter)
                && not (is_property_getter && Ain.version_gte ctx.ain (12, 0))
              then (
                (* v12 [dummy?.Method(args) ?? fallback] where the receiver
                   is a ref-returning call/getter (dummy slot),
                   non-interface. The original compiler CALLS the method
                   inside the non-null branch — where the null check just
                   proved the receiver valid — pushing a 0 marker below
                   the result; the null branch pushes [-1, -1]. The
                   generic path below instead DEFERS the CALLMETHOD past
                   the ?? marker check, by which point the receiver
                   page-ref is gone and CALLMETHOD dispatches on -1
                   (REF Page=-1, e.g. CEnqueteView@MouseWheelEvent's
                   this.Item?.IsFocusTextBox() ?? false on survey scroll). *)
                self#compile_lvalue receiver;
                self#write_instruction0 DUP;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE;
                let a_null = current_address + 2 in
                self#write_instruction1 IFNZ 0;
                self#compile_method_call_for_receiver receiver.ty args
                  method_no;
                self#write_instruction1 PUSH 0;
                let a_merge = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at a_null current_address;
                self#write_instruction0 POP;
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH (-1);
                self#write_address_at a_merge current_address;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE;
                let a_have = current_address + 2 in
                self#write_instruction1 IFZ 0;
                self#write_instruction0 POP;
                self#compile_expression b;
                self#write_address_at a_have current_address)
              else (
              if is_dummyref then (
                self#compile_lvalue receiver;
                if not receiver_is_casted_from_iface then
                  self#write_instruction0
                    (if receiver_is_iface then DUP_U2 else DUP);
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE)
              else (
                self#compile_variable_ref receiver;
                if is_wrap_ref_local then self#write_instruction0 REFREF;
                self#write_instruction0 DUP2;
                self#write_instruction0 REF;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE);
              (* v12: the original's optional-chain protocol always
                 carries the deferred receiver across the marker merge
                 as a 2-slot pair. Interface receivers are naturally
                 2-slot fat-refs; PLAIN receivers get padded with a
                 [PUSH 0] (and the null pair is [-1; -1]). Exemplars:
                 Scenes::RunISceneWithAssistant [assistant?.
                 ParentPartsNumber ?? 0] and CommonMenu@
                 IsQuestRetireEnable [findQuestFromId(..)?.IsRetireEnable
                 ?? false]. *)
              let pad_plain_receiver =
                Ain.version_gte ctx.ain (12, 0)
                && (not receiver_is_iface)
                && not receiver_is_casted_from_iface
              in
              let receiver_slots_2 =
                receiver_is_iface || receiver_is_casted_from_iface
                || pad_plain_receiver
              in
              let ifnz_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              if not is_dummyref then
                self#write_instruction0
                  (if receiver_is_iface then REFREF else REF);
              if pad_plain_receiver then self#write_instruction1 PUSH 0;
              self#write_instruction1 PUSH 0;
              let optional_jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifnz_addr current_address;
              if is_dummyref then (
                self#write_instruction0 POP;
                if receiver_is_iface || receiver_is_casted_from_iface then
                  self#write_instruction0 POP)
              else (
                self#write_instruction0 POP;
                self#write_instruction0 POP);
              self#write_instruction1 PUSH (-1);
              if receiver_slots_2 then self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at optional_jump_addr current_address;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              (* [(x?.Prop = x?.Prop + rhs) ?? rhs] — the decompiled
                 expansion of a compound assignment on an optional
                 receiver. The original checks the receiver ONCE and
                 runs the getter on a [DUP2] of the already-verified
                 pair inside the non-null branch; the inner [x?.Prop]
                 must NOT go through the generic optional-value
                 protocol (its unconsumed status marker corrupts the
                 stack under the setter CALLMETHOD — the survey-scroll
                 [構造体ページ N 取得失敗] crash at CEnqueteView@Scroll).
                 Mirrors the non-optional reused-receiver arm. *)
              let reused_optional_getter =
                match (String.chop_suffix opt_mname ~suffix:"::set", args) with
                | ( Some prop_base,
                    [ Some
                        { node =
                            Binary
                              ( op,
                                { node =
                                    Call
                                      ( { node =
                                            OptionalMember
                                              (getter_recv, getter_name, _);
                                          _ },
                                        [],
                                        MethodCall (_, getter_no) );
                                  ty = getter_ty;
                                  _ },
                                tail );
                          _ } ] )
                  when Ain.version_gte ctx.ain (12, 0)
                       && receiver_is_iface
                       && String.equal getter_name (prop_base ^ "::get")
                       && self#same_lvalue_shape receiver getter_recv
                       &&
                       (match (getter_ty, op) with
                       | (Int | Enum _ | LongInt | Float), (Plus | Minus) ->
                           true
                       | _ -> false) ->
                    Some (op, getter_no, getter_ty, tail)
                | _ -> None
              in
              let compile_setter_call () =
                let f = Ain.get_function_by_index ctx.ain method_no in
                match reused_optional_getter with
                | Some (op, getter_no, getter_ty, tail) ->
                    self#write_instruction0 DUP2;
                    self#compile_method_selector receiver.ty method_no;
                    self#write_instruction0 DUP_X2;
                    self#write_instruction0 POP;
                    self#write_instruction0 SWAP;
                    self#compile_method_selector receiver.ty getter_no;
                    self#write_instruction1 CALLMETHOD 0;
                    self#compile_expression tail;
                    ignore
                      (self#emit_reused_receiver_binary_op getter_ty op
                        : bool);
                    self#write_instruction0 DUP_X2;
                    self#write_instruction1 CALLMETHOD f.nr_args
                | None ->
                    self#compile_method_selector receiver.ty method_no;
                    let prev = in_prop_setter_arg in
                    Exn.protect
                      ~f:(fun () ->
                        in_prop_setter_arg <- true;
                        self#compile_function_arguments args f)
                      ~finally:(fun () -> in_prop_setter_arg <- prev);
                    self#write_instruction0 DUP_X2;
                    (match List.hd (Ain.Function.logical_parameters f) with
                    | Some { value_type = String; _ } ->
                        self#write_instruction0 A_REF
                    | _ -> ());
                    self#write_instruction1 CALLMETHOD f.nr_args
              in
              if is_value_prop_setter && Ain.version_gte ctx.ain (12, 0) then (
                (* Setter form: the original lays out the non-null
                   branch FIRST ([IFNZ] to the null/fallback branch),
                   the reverse of the value-form order below. Exemplar:
                   RunISceneWithAssistant [(assistant?.ParentPartsNumber
                   = ss.LayerPartsNumber) ?? ss.LayerPartsNumber]. *)
                let null_addr = current_address + 2 in
                self#write_instruction1 IFNZ 0;
                if pad_plain_receiver then self#write_instruction0 POP;
                compile_setter_call ();
                let end_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at null_addr current_address;
                self#write_instruction0 POP;
                if receiver_slots_2 then self#write_instruction0 POP;
                self#compile_expression b;
                self#write_address_at end_addr current_address)
              else (
                let ifz_addr = current_address + 2 in
                self#write_instruction1 IFZ 0;
                self#write_instruction0 POP;
                if receiver_slots_2 then self#write_instruction0 POP;
                self#compile_expression b;
                let jump_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at ifz_addr current_address;
                if pad_plain_receiver then self#write_instruction0 POP;
                if is_value_prop_setter then compile_setter_call ()
                else
                  self#compile_method_call_for_receiver receiver.ty args
                    method_no;
                self#write_address_at jump_addr current_address))
          | Call
              ( {
                  node =
                    Member
                      ( ({
                           node =
                             DummyRef
                               ( dummy_idx,
                                 {
                                   node =
                                     Call
                                       ( { node = OptionalMember (obj, _, _); _ },
                                         opt_args,
                                         MethodCall (_, opt_method_no) );
                                   _;
                                 } );
                           _;
                         } as receiver),
                        _,
                        _ );
                  _;
                },
                args,
                MethodCall (_, method_no) )
            when Ain.version_gte ctx.ain (12, 0)
                 && v12_iface_type receiver.ty ->
              (* v12 [obj?.IfaceProp.Value ?? fallback].  The optional
                 receiver must be checked before compiling [.Value];
                 otherwise the outer member access dereferences the
                 [-1] receiver that the optional branch produced. *)
              self#pre_emit_lambda_args args;
              let rec is_dummyref_shape (e : expression) =
                match e.node with
                | DummyRef _ -> true
                | Call
                    ( _,
                      _,
                      ( HLLCall _ | FunctionCall _ | MethodCall _
                      | BuiltinCall _ ) ) ->
                    true
                | Cast (_, inner) -> is_dummyref_shape inner
                | _ -> false
              in
              let obj_is_dummyref = is_dummyref_shape obj in
              let obj_is_iface = v12_iface_type obj.ty in
              if obj_is_dummyref then (
                self#compile_lvalue obj;
                self#write_instruction0 (if obj_is_iface then DUP_U2 else DUP);
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE)
              else (
                self#compile_variable_ref obj;
                self#write_instruction0 DUP2;
                self#write_instruction0 REF;
                self#write_instruction1 PUSH (-1);
                self#write_instruction0 EQUALE);
              let ifnz_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              if not obj_is_dummyref then
                self#write_instruction0 (if obj_is_iface then REFREF else REF);
              self#compile_method_call_for_receiver obj.ty opt_args
                opt_method_no;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH dummy_idx;
              self#write_instruction0 REF;
              self#write_instruction0 DELETE;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH dummy_idx;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction0 R_ASSIGN;
              self#write_instruction1 PUSH 0;
              let optional_jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifnz_addr current_address;
              if obj_is_dummyref then (
                self#write_instruction0 POP;
                if obj_is_iface then self#write_instruction0 POP)
              else (
                self#write_instruction0 POP;
                self#write_instruction0 POP);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at optional_jump_addr current_address;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              if self#is_value_prop_setter_method method_no args then (
                (* [(obj?.IfaceProp.Value = rhs) ?? rhs] — orig (FUNC 5655
                   infoview::detail::CInfoText@SetAlpha) lays the setter
                   arm FIRST (IFNZ to the fallback), keeps the assigned
                   value below the vtable CALLMETHOD via DUP_X2, and
                   yields it on BOTH arms; the statement pops once and
                   the dummy's LOCALDELETE (last-use tracking) follows.
                   The old in-branch shape left the fallback value with
                   no statement POP: one slot leaked per null receiver —
                   the save-crash class, on the per-frame infoview
                   fades. *)
                let f = Ain.get_function_by_index ctx.ain method_no in
                let fallback_addr = current_address + 2 in
                self#write_instruction1 IFNZ 0;
                self#compile_method_selector receiver.ty method_no;
                (let prev = in_prop_setter_arg in
                 Exn.protect
                   ~f:(fun () ->
                     in_prop_setter_arg <- true;
                     self#compile_function_arguments args f)
                   ~finally:(fun () -> in_prop_setter_arg <- prev));
                self#write_instruction0 DUP_X2;
                (match List.hd (Ain.Function.logical_parameters f) with
                | Some { value_type = String; _ } ->
                    self#write_instruction0 A_REF
                | _ -> ());
                self#write_instruction1 CALLMETHOD f.nr_args;
                let end_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at fallback_addr current_address;
                self#write_instruction0 POP;
                self#write_instruction0 POP;
                self#compile_expression b;
                self#write_address_at end_addr current_address)
              else (
                let ifz_addr = current_address + 2 in
                self#write_instruction1 IFZ 0;
                self#write_instruction0 POP;
                self#write_instruction0 POP;
                self#compile_expression b;
                let jump_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at ifz_addr current_address;
                self#compile_method_call_for_receiver receiver.ty args
                  method_no;
                self#write_address_at jump_addr current_address)
          | Call
              ( {
                  node =
                    Member
                      ( ({
                           node =
                             DummyRef
                               ( dummy_idx,
                                 {
                                   node =
                                     Call
                                       ( { node = OptionalMember (obj, _, _); _ },
                                         opt_args,
                                         MethodCall (_, opt_method_no) );
                                   _;
                                 } );
                           _;
                         } as receiver),
                        _,
                        _ );
                  _;
                },
                args,
                MethodCall (_, method_no) )
            when Ain.version_gte ctx.ain (12, 0)
                 && not (v12_iface_type receiver.ty) ->
              (* v12 [obj?.Property1.Property2 ?? fallback] for non-iface
                 receivers (e.g. [leader?.Status.Atk ?? 0]).  Matches
                 orig's pattern: store the inner getter result in the
                 dummy slot only on the non-null path, push a (0, 0)
                 marker pair vs a (-1, -1, -1) triple to discriminate,
                 then either call the outer getter on the dummy slot or
                 emit the fallback.  The existing
                 [Member.DummyRef.Call.OptionalMember] iface variant
                 above uses 2-slot ops (R_ASSIGN, DUP_X2); this case
                 uses 1-slot ops for plain struct dummies. *)
              self#pre_emit_lambda_args args;
              let outer_setter =
                (* [(obj?.Getter(..).Prop = rhs) ?? rhs] — optional
                   property ASSIGNMENT through a call receiver. The
                   getter-chain layout below leaves nothing on the
                   non-null arm (void setter) but the fallback on the
                   null arm, leaking one stack slot per null receiver
                   at statement level — consumed later as garbage
                   (page, index) by an unrelated ASSIGN (the Rance 10
                   save dialog's 変数代入エラー via SaveObjectView@
                   ParentPartsNumber::postset). The original yields
                   the assigned value on BOTH arms: non-null branch
                   FIRST (IFNZ to the fallback), setter deferred past
                   the merge with the value kept below the call via
                   DUP_X2, one statement POP, then the dummy's
                   LOCALDELETE. *)
                if
                  (match receiver.ty with
                  | Struct (name, _) | Ref (Struct (name, _)) ->
                      not (Hashtbl.mem ctx.interface_names name)
                  | _ -> false)
                  && self#is_value_prop_setter_method method_no args
                then Some (Ain.get_function_by_index ctx.ain method_no)
                else None
              in
              (match outer_setter with
              | Some f ->
                  (* Register the dummy so statement cleanup emits its
                     LOCALDELETE (after the statement POP, matching
                     orig). *)
                  self#scope_add_var (self#get_local dummy_idx);
                  let obj_is_variable = is_variable_ref obj.node in
                  if obj_is_variable then (
                    (* Original keeps the receiver as a (page, index)
                       pair across the null test and re-REFs it in the
                       non-null branch. *)
                    self#compile_variable_ref obj;
                    self#write_instruction0 DUP2;
                    self#write_instruction0 REF;
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction0 EQUALE)
                  else (
                    self#compile_lvalue obj;
                    self#write_instruction0 DUP;
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction0 EQUALE);
                  let recv_null_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  if obj_is_variable then self#write_instruction0 REF;
                  self#compile_method_call_for_receiver obj.ty opt_args
                    opt_method_no;
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction1 PUSH dummy_idx;
                  self#write_instruction0 REF;
                  self#emit_slot_release;
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction0 SWAP;
                  self#write_instruction1 PUSH dummy_idx;
                  self#write_instruction0 SWAP;
                  self#write_instruction0 ASSIGN;
                  self#write_instruction1 PUSH 0;
                  self#write_instruction1 PUSH 0;
                  let merge_jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at recv_null_addr current_address;
                  if obj_is_variable then (
                    self#write_instruction0 POP;
                    self#write_instruction0 POP)
                  else self#write_instruction0 POP;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1);
                  self#write_address_at merge_jump_addr current_address;
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 EQUALE;
                  let fallback_addr = current_address + 2 in
                  self#write_instruction1 IFNZ 0;
                  self#write_instruction0 POP;
                  self#compile_method_selector receiver.ty method_no;
                  (let prev = in_prop_setter_arg in
                   Exn.protect
                     ~f:(fun () ->
                       in_prop_setter_arg <- true;
                       self#compile_function_arguments args f)
                     ~finally:(fun () -> in_prop_setter_arg <- prev));
                  self#write_instruction0 DUP_X2;
                  (match List.hd (Ain.Function.logical_parameters f) with
                  | Some { value_type = String; _ } ->
                      self#write_instruction0 A_REF
                  | _ -> ());
                  self#write_instruction1 CALLMETHOD f.nr_args;
                  let end_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at fallback_addr current_address;
                  self#write_instruction0 POP;
                  self#write_instruction0 POP;
                  self#compile_expression b;
                  self#write_address_at end_addr current_address
              | None ->
              self#compile_lvalue obj;
              self#write_instruction0 DUP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifnz_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              (* non-null: call the inner getter (e.g. Status::get) on
                 [obj], store the result in [dummy_idx] via the
                 standard [SWAP; ASSIGN] dance, then push the (0, 0)
                 non-null marker pair. *)
              self#compile_method_call_for_receiver obj.ty opt_args opt_method_no;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH dummy_idx;
              self#write_instruction0 REF;
              self#emit_slot_release;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction0 SWAP;
              self#write_instruction1 PUSH dummy_idx;
              self#write_instruction0 SWAP;
              self#write_instruction0 ASSIGN;
              self#write_instruction1 PUSH 0;
              self#write_instruction1 PUSH 0;
              let optional_jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifnz_addr current_address;
              (* null branch: drop the dup'd [obj], push the
                 (-1, -1, -1) null-marker triple. *)
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at optional_jump_addr current_address;
              (* common: discriminate via [PUSH -1; EQUALE] on the top
                 marker.  IFZ jumps when the marker was [0] (non-null),
                 falls through when it was [-1] (null). *)
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifz_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              (* null finalize: drop the remaining two markers, emit
                 the fallback. *)
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#compile_expression b;
              let jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at ifz_addr current_address;
              (* non-null finalize: drop the discriminator, call the
                 outer getter (e.g. Atk::get) on the dummy-slot value
                 still on stack. *)
              self#write_instruction0 POP;
              self#compile_method_call_for_receiver receiver.ty args method_no;
              self#write_address_at jump_addr current_address)
          | _ ->
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
            (* v12 scalar fallback: when b is a literal (or any
               non-lvalue), evaluate it as a value and push a dummy
               slot pair so the surrounding REF works. *)
            | true, (ConstInt _ | ConstFloat _ | ConstChar _ | Null
                    | Unary _ | Binary _) ->
                self#compile_expression b
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
            else if
              match self#ain_call_return_type a_inner with
              | Some (Ain.Type.Option _) -> true
              | _ -> false
            then (
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let ifz_addr = current_address + 2 in
              self#write_instruction1 IFZ 0;
              self#write_instruction0 POP;
              self#compile_expression b;
              self#write_address_at ifz_addr current_address)
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

    (** v12 [call()?.Event += handler] statement, where the event lives
        on an interface receiver so the subscription dispatches the
        [::add]/[::remove] accessor through the vtable. The original
        compiler DEFERS the accessor call past the null-check merge — a
        marker recheck guards the dispatch — and builds the handler
        delegate in BOTH branches (the null branch constructs and
        DELETEs it, balanced, without the call). The generic optional-
        call arm instead calls inside the non-null branch and pushes a
        marker the statement then POPs — runtime-equivalent, but a
        LENGTH divergence at every subscription site (CADVEngine@
        OpenPanel's ten panel buttons, sealtool CCamera@0, ...).
        Emits the original shape and returns true when it applies. *)
    method private try_optional_event_subscription_stmt (expr : expression) =
      match expr.node with
      | Call
          ( { node = OptionalMember (e, _, _); _ },
            ([ Some rhs ] as args),
            MethodCall (_, method_no) )
        when Ain.version_gte ctx.ain (12, 0) -> (
          let f = Ain.get_function_by_index ctx.ain method_no in
          let is_accessor =
            String.is_suffix f.name ~suffix:"::add"
            || String.is_suffix f.name ~suffix:"::remove"
          in
          let rhs_builds_delegate =
            (* Both branches compile the rhs, so it must be a pure
               method reference / pre-emitted lambda (pushes only). *)
            match rhs.node with
            | Member (_, _, ClassMethod _) | Lambda _ -> true
            | _ -> false
          in
          let rec is_dummyref_shape (e : expression) =
            match e.node with
            | DummyRef _ -> true
            | Call
                (_, _, (HLLCall _ | FunctionCall _ | MethodCall _ | BuiltinCall _))
              ->
                true
            | Cast (_, inner) -> is_dummyref_shape inner
            | _ -> false
          in
          let rec v12_iface_walk (ty : jaf_type) =
            match ty with
            | Struct (name, _) | Ref (Struct (name, _)) ->
                Hashtbl.mem ctx.interface_names name
            | Wrap inner -> v12_iface_walk inner
            | _ -> false
          in
          let receiver_is_casted_iface =
            match e.node with
            | Cast (Struct (name, _), _) | Cast (Ref (Struct (name, _)), _) ->
                Hashtbl.mem ctx.interface_names name
            | _ -> false
          in
          if
            is_accessor
            && Poly.equal f.return_type Ain.Type.Void
            && rhs_builds_delegate && is_dummyref_shape e
            && v12_iface_walk e.ty
            && not receiver_is_casted_iface
          then (
            self#pre_emit_lambda_args args;
            self#compile_lvalue e;
            self#write_instruction0 DUP_U2;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE;
            let ifnz1_addr = current_address + 2 in
            self#write_instruction1 IFNZ 0;
            self#write_instruction1 PUSH 0;
            let jump_merge_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#write_address_at ifnz1_addr current_address;
            self#write_instruction0 POP;
            self#write_instruction0 POP;
            self#write_instruction1 PUSH (-1);
            self#write_instruction1 PUSH (-1);
            self#write_instruction1 PUSH (-1);
            self#write_address_at jump_merge_addr current_address;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE;
            let ifnz2_addr = current_address + 2 in
            self#write_instruction1 IFNZ 0;
            self#compile_method_call_for_receiver ~prefer_first_duplicate:true
              e.ty args method_no;
            let jump_end_addr = current_address + 2 in
            self#write_instruction1 JUMP 0;
            self#write_address_at ifnz2_addr current_address;
            self#write_instruction0 POP;
            self#write_instruction0 POP;
            self#compile_function_arguments args f;
            self#write_instruction0 DELETE;
            self#write_address_at jump_end_addr current_address;
            true)
          else false)
      | _ -> false

    method compile_expr_and_pop ?(before_pop = fun () -> ()) (expr : expression)
        =
      match expr.node with
      | Assign
          ( EqAssign,
            ( {
                node = Member (_, member_name, ClassVariable _);
                _;
              } as lhs ),
            { node = Null; _ } )
        when Ain.version_gte ctx.ain (12, 0)
             && String.is_prefix member_name ~prefix:"<"
             && String.is_suffix member_name ~suffix:">"
             && (match self#member_type lhs with
                | Ref (Struct _) -> true
                | _ -> false)
             && (match current_function with
                | Some f ->
                    String.is_suffix f.name ~suffix:"@0"
                    || String.is_suffix f.name ~suffix:"@2"
                | None -> false) ->
          self#compile_variable_ref lhs;
          self#write_instruction1 PUSH (-1);
          self#write_instruction0 ASSIGN;
          before_pop ();
          self#write_instruction0 POP
      | Assign
          ( EqAssign,
            ( {
                node = Member (_, member_name, ClassVariable _);
                _;
              } as lhs ),
            rhs )
        when Ain.version_gte ctx.ain (12, 0)
             && String.is_prefix member_name ~prefix:"<"
             && String.is_suffix member_name ~suffix:">"
             && (match self#member_type lhs with
                | Ref (Struct _) -> true
                | _ -> false)
             && (match current_function with
                | Some f ->
                    String.is_suffix f.name ~suffix:"@0"
                    || String.is_suffix f.name ~suffix:"@2"
                | None -> false)
             && (match rhs.node with
                | New _ | NewCall _ | DummyRef (_, { node = New _ | NewCall _; _ }) ->
                    true
                | _ -> false) ->
          self#compile_variable_ref lhs;
          (match rhs.node with
          | DummyRef (dummy_idx, { node = New { ty = Struct (_, s_no); _ }; _ }) ->
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH dummy_idx;
              self#write_instruction0 REF;
              self#write_instruction0 DELETE;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH dummy_idx;
              let ctor = self#receiver_new_ctor s_no in
              self#write_instruction2 NEW s_no ctor;
              self#write_instruction0 ASSIGN;
              self#write_instruction0 ASSIGN;
              before_pop ();
              self#write_instruction0 SP_INC;
              self#write_instruction1 SH_LOCALDELETE dummy_idx
          | DummyRef
              ( dummy_idx,
                {
                  node = NewCall ({ ty = Struct (struct_name, s_no); _ }, args);
                  _;
                } ) ->
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH dummy_idx;
              self#write_instruction0 REF;
              self#write_instruction0 DELETE;
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH dummy_idx;
              self#compile_newcall struct_name s_no args;
              self#write_instruction0 ASSIGN;
              self#write_instruction0 ASSIGN;
              before_pop ();
              self#write_instruction0 SP_INC;
              self#write_instruction1 SH_LOCALDELETE dummy_idx
          | New { ty = Struct (_, s_no); _ } ->
              let ctor = self#bare_new_ctor s_no in
              self#write_instruction2 NEW s_no ctor;
              self#write_instruction0 ASSIGN;
              before_pop ();
              self#write_instruction0 SP_INC
          | NewCall ({ ty = Struct (struct_name, s_no); _ }, args) ->
              self#compile_newcall struct_name s_no args;
              self#write_instruction0 ASSIGN;
              before_pop ();
              self#write_instruction0 SP_INC
          | _ -> compiler_bug "invalid ref-struct backing initializer"
                   (Some (ASTExpression rhs)))
      (* NOTE: a transplanted arm here used to REBIND [struct_var = new T]
         statements (compile_variable_ref; NEW; ASSIGN; POP). orig deep-
         copies through a [<dummy : new T>] slot ([A_REF; SR_ASSIGN]) so
         the destination page keeps its identity — see the matching note
         in variableAlloc's [visit_expression]. The generic Assign path
         below emits that shape once the dummy exists. *)
      | Assign (EqAssign, lhs, { node = Null; _ })
        when Ain.version_gte ctx.ain (12, 0)
             && (match lhs.ty with
                | Struct (name, _) | Ref (Struct (name, _)) | Unresolved name ->
                    Hashtbl.mem ctx.interface_names name
                | _ -> false)
             && (match current_function with
                | Some f ->
                    String.is_suffix f.name ~suffix:"@0"
                    || String.is_suffix f.name ~suffix:"@2"
                | None -> false)
             && is_variable_ref lhs.node
        ->
          (* Constructor/default member init starts from a zeroed slot.
             Original v12 writes the interface null pair directly; deleting
             the old value first feeds page 0 to DELETE. *)
          self#compile_variable_ref lhs;
          self#write_instruction1 PUSH (-1);
          self#write_instruction1 PUSH 0;
          self#write_instruction0 R_ASSIGN;
          before_pop ();
          self#write_instruction0 POP;
          self#write_instruction0 SP_INC
      | Assign (EqAssign, lhs, { node = Null; _ })
        when Ain.version_gte ctx.ain (12, 0)
             && (match lhs.ty with
                | Struct (name, _) | Ref (Struct (name, _)) | Unresolved name ->
                    Hashtbl.mem ctx.interface_names name
                | _ -> false)
        ->
          (* v12 interface refs are two-slot values. Nulling one uses
             R_ASSIGN after deleting the previous interface page-ref;
             SR_ASSIGN treats the first slot as a struct page and fails
             when that slot is 0. *)
          self#compile_variable_ref lhs;
          (* Foreach-bound iface var has slot storage [Wrap (IFace _)]
             — compile_variable_ref only pushes the wrap-handle location.
             Unwrap with REFREF so DUP2;REF;...;R_ASSIGN operates on
             the underlying iface fat-ref pair instead of corrupting
             the wrap-handle (which the foreach desugar reuses on the
             next iteration → REF-on-freed-page crash at survey close,
             unmasked after the OptionalMember REFREF fix in 3a64b94). *)
          (match lhs.node with
          | Ident (_, LocalVariable (i, _)) -> (
              match (self#get_local i).value_type with
              | Ain.Type.Wrap (Ain.Type.IFace _) ->
                  self#write_instruction0 REFREF
              | _ -> ())
          | _ -> ());
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction1 PUSH (-1);
          self#write_instruction1 PUSH 0;
          self#write_instruction0 DUP_X2;
          self#write_instruction0 POP;
          self#write_instruction0 DUP_X2;
          self#write_instruction0 POP;
          self#write_instruction0 DELETE;
          self#write_instruction0 R_ASSIGN;
          before_pop ();
          self#write_instruction0 POP;
          self#write_instruction0 SP_INC
      | Assign
          ( EqAssign,
            ( {
                node =
                  Member
                    ( _,
                      member_name,
                      ClassVariable _
                    );
                _;
              } as lhs ),
            ({ node = Ident ("value", LocalVariable _); _ } as rhs)
          )
        when Ain.version_gte ctx.ain (12, 0)
             && String.is_prefix member_name ~prefix:"<"
             && String.is_suffix member_name ~suffix:">"
             && (match current_function with
                | Some f -> String.is_suffix f.name ~suffix:"::set"
                | None -> false)
             && (match self#member_type lhs with IFace _ -> true | _ -> false)
        ->
          (* v12 auto interface-property setters transfer the backing
             two-slot interface ref directly. Treating it as a struct page
             ref stores only half of the pair and later dispatch can use the
             vtable offset as a page id. *)
          self#compile_variable_ref lhs;
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction0 DELETE;
          self#compile_lvalue rhs;
          self#write_instruction0 R_ASSIGN;
          before_pop ();
          self#write_instruction0 POP;
          self#write_instruction0 SP_INC
      | Assign
          ( EqAssign,
            ( {
                node =
                  Member
                    ( _,
                      member_name,
                      ClassVariable _
                    );
                ty = String;
                _;
              } as lhs ),
            ({ node = Ident ("value", LocalVariable _); ty = String; _ } as rhs)
          )
        when Ain.version ctx.ain > 8
             && String.is_prefix member_name ~prefix:"<"
             && String.is_suffix member_name ~suffix:">"
             && (match current_function with
                | Some f -> String.is_suffix f.name ~suffix:"::set"
                | None -> false) ->
          (* Auto string-property setters use the backing slot transfer
             shape directly; the generic string assignment path would
             add A_REF/DELETE and diverge from v11 output. *)
          self#compile_lvalue lhs;
          self#compile_lvalue rhs;
          self#write_instruction0 S_ASSIGN;
          before_pop ();
          self#write_instruction0 POP
      | Assign
          ( EqAssign,
            ( {
                node =
                  Member
                    ( _,
                      member_name,
                      ClassVariable _
                    );
                _; 
              } as lhs ),
            ({ node = Ident ("value", LocalVariable _); _ } as rhs)
          )
        when Ain.version_gte ctx.ain (12, 0)
             && String.is_prefix member_name ~prefix:"<"
             && String.is_suffix member_name ~suffix:">"
             && (match current_function with
                | Some f -> String.is_suffix f.name ~suffix:"::set"
                | None -> false)
             && (match self#member_type lhs with Struct _ -> true | _ -> false)
        ->
          (* v12 auto setters whose backing storage is a value struct
             copy the incoming ref-struct value directly into the backing
             page. The generic assignment path adds a DummyRef A_REF/DELETE
             pair that original setters do not emit. *)
          self#compile_lvalue lhs;
          self#compile_lvalue rhs;
          self#write_instruction0 SR_ASSIGN;
          before_pop ();
          self#write_instruction0 POP
      | Assign
          ( EqAssign,
            ( {
                node =
                  Member
                    ( _,
                      member_name,
                      ClassVariable _
                    );
                _;
              } as lhs ),
            ({ node = Ident ("value", LocalVariable _); _ } as rhs)
          )
        when Ain.version_gte ctx.ain (12, 0)
             && String.is_prefix member_name ~prefix:"<"
             && String.is_suffix member_name ~suffix:">"
             && (match current_function with
                | Some f -> String.is_suffix f.name ~suffix:"::set"
                | None -> false)
             && (match self#member_type lhs with Ref (Struct _) -> true | _ -> false)
        ->
          (* v12 auto setters for ref-struct backings (kept as ref when
             the target has no default constructor) assign the page-ref
             directly. Using SR_ASSIGN treats the slot as a struct page
             and can trip page-0 errors on uninitialized backings. *)
          self#compile_variable_ref lhs;
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction0 DELETE;
          self#compile_lvalue rhs;
          self#write_instruction0 ASSIGN;
          before_pop ();
          self#write_instruction0 SP_INC
      | Assign
          ( EqAssign,
            { node = Ident (_, LocalVariable (i, _)); _ },
            { node = ConstInt n; _ } )
        when ctx.version > 100 && ctx.version < 630
             && not (Ain.Type.is_ref (self#get_local i).value_type) ->
          self#write_instruction2 SH_LOCALASSIGN i n
      | Unary
          ( (( PreInc | PostInc | PreDec | PostDec | ForeachInc
             | ForeachDec ) as op),
            { node = Ident (_, LocalVariable (i, _)); _ } )
        when ctx.version > 100 && ctx.version < 630
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
      | Call
          ( {
              node =
                Member
                  ( ({
                       node =
                         DummyRef
                           ( dummy_idx,
                             ({
                                node =
                                  Call
                                    ( { node = OptionalMember (obj, _, _); _ },
                                      opt_args,
                                      MethodCall (_, opt_method_no) );
                                _;
                              } as opt_call) );
                       _;
                     } as receiver),
                    _,
                    _ );
              _;
            },
            args,
            MethodCall (_, method_no) )
        when Ain.version ctx.ain > 8 && Poly.equal expr.ty Void -> (
          (* v12 [obj?.Prop.Method()] used as a statement.  The
             optional receiver must guard the entire outer method call:
             if [obj] is NULL, alice skips [.Method()] and leaves only
             the optional-chain status sentinel for the statement POP.
             Letting [DummyRef] materialize [-1] first makes the outer
             CALLMETHOD dereference a null receiver (REF page=-1). *)
          self#pre_emit_lambda_args args;
          let receiver_is_iface =
            match receiver.ty with
            | Struct (name, _) | Ref (Struct (name, _)) ->
                Hashtbl.mem ctx.interface_names name
            | _ -> false
          in
          let rec is_dummyref_shape (e : expression) =
            match e.node with
            | DummyRef _ -> true
            | Call
                ( _,
                  _,
                  (HLLCall _ | FunctionCall _ | MethodCall _ | BuiltinCall _)
                  ) ->
                true
            | Cast (_, inner) -> is_dummyref_shape inner
            | _ -> false
          in
          let obj_is_dummyref = is_dummyref_shape obj in
          if obj_is_dummyref then (
            self#compile_lvalue obj;
            self#write_instruction0
              (if receiver_is_iface then DUP_U2 else DUP);
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE)
          else (
            self#compile_variable_ref obj;
            self#write_instruction0 DUP2;
            self#write_instruction0 REF;
            self#write_instruction1 PUSH (-1);
            self#write_instruction0 EQUALE);
          let ifnz_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          if not obj_is_dummyref then
            self#write_instruction0
              (if receiver_is_iface then REFREF else REF);
          self#compile_method_call_for_receiver obj.ty opt_args opt_method_no;
          let stored_two_slots =
            receiver_is_iface || is_ref_scalar opt_call.ty
          in
          if stored_two_slots then (
            (* 2-slot link result (iface / ref-scalar pair): rotate the
               pair under [page, index] with [DUP_X2; POP]. *)
            self#write_instruction0 PUSHLOCALPAGE;
            self#write_instruction1 PUSH dummy_idx;
            self#write_instruction0 REF;
            self#write_instruction0 DELETE;
            self#write_instruction0 PUSHLOCALPAGE;
            self#write_instruction0 DUP_X2;
            self#write_instruction0 POP;
            self#write_instruction1 PUSH dummy_idx;
            self#write_instruction0 DUP_X2;
            self#write_instruction0 POP;
            self#write_instruction0 R_ASSIGN)
          else (
            (* 1-slot link result: the [DUP_X2] rotation reaches one slot
               BELOW this statement's values, weaving the caller's pending
               stack slot into the ASSIGN triple — a wild write
               [page(dummy_idx)[caller_junk] = value] (the save-dialog
               【 ASSIGN 】 Page:1 crash, SaveObjectView@SetZ/SetIndex/
               SetShowNewFlat/SetPos). Original stores with the SWAP
               dance (.STACK_LOCALASSIGN) and releases the dummy after
               the statement POP. *)
            self#scope_add_var (self#get_local dummy_idx);
            self#write_instruction0 PUSHLOCALPAGE;
            self#write_instruction1 PUSH dummy_idx;
            self#write_instruction0 REF;
            self#emit_slot_release;
            self#write_instruction0 PUSHLOCALPAGE;
            self#write_instruction0 SWAP;
            self#write_instruction1 PUSH dummy_idx;
            self#write_instruction0 SWAP;
            self#write_instruction0 ASSIGN);
          self#compile_method_call_for_receiver receiver.ty args method_no;
          self#write_instruction1 PUSH 0;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifnz_addr current_address;
          if obj_is_dummyref then (
            self#write_instruction0 POP;
            if receiver_is_iface then self#write_instruction0 POP)
          else (
            self#write_instruction0 POP;
            self#write_instruction0 POP);
          self#write_instruction1 PUSH (-1);
          self#write_address_at jump_addr current_address;
          if stored_two_slots then (
            before_pop ();
            self#write_instruction0 POP)
          else (
            (* orig: statement POP first, then the dummy's LOCALDELETE *)
            self#write_instruction0 POP;
            before_pop ()))
      (* v12 [obj?.M1().M2()...Mn()] discarded statement where the final
         call returns a value (DummyRef-wrapped root). The original
         guards the ENTIRE chain on one receiver test: the non-null
         branch runs every link (each stored to its dummy, no
         intermediate tests) and null-tests only the FINAL result to
         build the (value, marker) discard pair; the null branch
         bypasses everything with a (-1, -1) pair; the merge pops both
         and the dummies' LOCALDELETEs follow. Compiling the inner
         [obj?.M1()] as its own optional unit instead normalizes NULL
         to -1 and runs [.M2()] on it — CALLMETHOD on a NULL page
         (SaveObjectView@SetSortedIndex [p?.Motion().SetPos(..)] with
         no activity attached, on the save dialog path). *)
      | DummyRef _
        when Ain.version_gte ctx.ain (12, 0)
             && Option.is_some (self#match_discarded_optional_chain expr) ->
          (match self#match_discarded_optional_chain expr with
          | None -> assert false
          | Some (obj, links) ->
              List.iter links ~f:(fun (_, _, args, _) ->
                  self#pre_emit_lambda_args args);
              let obj_is_variable = is_variable_ref obj.node in
              (if obj_is_variable then (
                 self#compile_variable_ref obj;
                 self#write_instruction0 DUP2;
                 self#write_instruction0 REF;
                 self#write_instruction1 PUSH (-1);
                 self#write_instruction0 EQUALE)
               else (
                 self#compile_lvalue obj;
                 self#write_instruction0 DUP;
                 self#write_instruction1 PUSH (-1);
                 self#write_instruction0 EQUALE));
              let null_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              if obj_is_variable then self#write_instruction0 REF;
              List.iter links ~f:(fun (idx, recv_ty, args, mno) ->
                  self#compile_method_call_for_receiver recv_ty args mno;
                  self#scope_add_var (self#get_local idx);
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction1 PUSH idx;
                  self#write_instruction0 REF;
                  self#emit_slot_release;
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction0 SWAP;
                  self#write_instruction1 PUSH idx;
                  self#write_instruction0 SWAP;
                  self#write_instruction0 ASSIGN);
              self#write_instruction0 DUP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction0 EQUALE;
              let tail_null_addr = current_address + 2 in
              self#write_instruction1 IFNZ 0;
              self#write_instruction1 PUSH 0;
              let tail_join = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at tail_null_addr current_address;
              self#write_instruction0 POP;
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at tail_join current_address;
              let merge_jump = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at null_addr current_address;
              (if obj_is_variable then (
                 self#write_instruction0 POP;
                 self#write_instruction0 POP)
               else self#write_instruction0 POP);
              self#write_instruction1 PUSH (-1);
              self#write_instruction1 PUSH (-1);
              self#write_address_at merge_jump current_address;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              before_pop ())
      (* v11 [obj?.Method()] / [obj?.HllCall()] used as a statement: the
         optional chain leaves a fat-null sentinel int on the stack
         (0 for success, -1 for null) that must be discarded. The
         expression's [ty] is [Void] (the called method returns void),
         and the default [compile_pop Void] is a no-op — emit an
         explicit [POP] so the stack stays balanced. *)
      | Call ({ node = OptionalMember _; _ }, _, (MethodCall _ | HLLCall _))
        when Ain.version ctx.ain > 8 && Poly.equal expr.ty Void ->
          if self#try_optional_event_subscription_stmt expr then before_pop ()
          else (
            self#compile_expression expr;
            before_pop ();
            self#write_instruction0 POP)
      (* v12 [obj?.Method(...)] / [obj?.Prop.Method(...)] discarded as a
         statement when the method returns a scalar: the optional
         protocol merges a (value, marker) pair — the Void arms above
         pop only the sentinel, but here the ignored return value sits
         under it and must be popped too. Leaving it leaks one stack
         slot per execution; the parts framework's DG_CALL loop then
         consumes the leaked [true] as a delegate page id (survey-open
         【 DG_CALL 】 ページ番号 = 1 via CEnqueteItemManager@SetEnable /
         CEnqueteItemCheckIcon@SetEnable). *)
      | Call ({ node = OptionalMember _; _ }, _, (MethodCall _ | HLLCall _))
      | Call
          ( {
              node =
                Member
                  ( {
                      node =
                        DummyRef
                          ( _,
                            {
                              node =
                                Call
                                  ( { node = OptionalMember _; _ },
                                    _,
                                    MethodCall _ );
                              _;
                            } );
                      _;
                    },
                    _,
                    _ );
              _;
            },
            _,
            MethodCall _ )
        when Ain.version_gte ctx.ain (12, 0)
             && (match expr.ty with
                | Int | Bool | Float | LongInt | Enum _ -> true
                | _ -> false) ->
          self#compile_expression expr;
          before_pop ();
          self#write_instruction0 POP;
          self#write_instruction0 POP
      | NullCoalesce
          ( {
              node =
                Call
                  ( { node = OptionalMember _; _ },
                    _,
                    (MethodCall _ | HLLCall _) );
              _;
            },
            _ )
        when Ain.version ctx.ain > 8 && Poly.equal expr.ty Void ->
          self#compile_expression expr;
          before_pop ();
          self#write_instruction0 POP
      (* v12 [(obj?.Getter(..).Prop = rhs) ?? rhs] as a statement: the
         optional-assignment arm yields the assigned value on both
         paths (DUP_X2 protocol), so the statement pops once. The
         dispatcher routes this shape through [cleanup_after_pop] so
         the dummy's LOCALDELETE lands after the POP, matching orig.
         Non-iface receivers only — the iface ?? arm still compiles
         its setter branch without the value yield, so popping there
         would underflow (CInfoText@SetAlpha, every fade frame). *)
      | NullCoalesce
          ( {
              node =
                Call
                  ( {
                      node =
                        Member
                          ( ({
                               node =
                                 DummyRef
                                   ( _,
                                     {
                                       node =
                                         Call
                                           ( { node = OptionalMember _; _ },
                                             _,
                                             _ );
                                       _;
                                     } );
                               _;
                             } as sprop_receiver),
                            _,
                            _ );
                      _;
                    },
                    args,
                    MethodCall (_, method_no) );
              _;
            },
            _ )
        when Ain.version_gte ctx.ain (12, 0)
             && Poly.equal expr.ty Void
             && (match sprop_receiver.ty with
                (* Both receiver shapes yield the assigned value across
                   the ?? merge now — non-iface via the SWAP-dance arm,
                   iface via the vtable-selector arm (CInfoText@
                   SetAlpha protocol) — so the statement pops for
                   either. This predicate, the two emission arms, and
                   cleanup_after_pop must stay in lockstep. *)
                | Struct _ | Ref (Struct _) -> true
                | _ -> false)
             && self#is_value_prop_setter_method method_no args ->
          self#compile_expression expr;
          before_pop ();
          self#write_instruction0 POP
      | DummyRef _ ->
          self#compile_lvalue expr;
          before_pop ();
          (match expr.ty with
          | Ref (String | Struct _ | Array _ | HLLParam)
            when Ain.version_gte ctx.ain (11, 0) ->
              self#write_instruction0 POP
          | _ -> self#compile_pop expr.ty (ASTExpression expr))
      | Assign (EqAssign, lhs, { node = Null; _ })
        when Ain.version_gte ctx.ain (12, 0)
             &&
             (match lhs.node with
             | Ident (_, LocalVariable (i, _)) -> (
                 match (self#get_local i).value_type with
                 | Ain.Type.Ref (Struct _) -> true
                 | _ -> false)
             | Ident (_, GlobalVariable i) -> (
                 match (Ain.get_global_by_index ctx.ain i).value_type with
                 | Ain.Type.Ref (Struct _) -> true
                 | _ -> false)
             | Member (_, _, ClassVariable _) -> (
                 match self#member_type lhs with
                 | Ain.Type.Ref (Struct _) -> true
                 | _ -> false)
             | _ -> false) ->
          self#compile_variable_ref lhs;
          self#write_instruction1 PUSH (-1);
          self#write_instruction0 ASSIGN;
          self#write_instruction0 SP_INC;
          before_pop ()
      | Assign (EqAssign, lhs, rhs)
        when Ain.version_gte ctx.ain (12, 0)
             && (match lhs.node with
                | Ident (_, LocalVariable (i, _)) -> (
                    match (self#get_local i).value_type with
                    | Ain.Type.IFace _ -> true
                    | _ -> false)
                | Ident (_, GlobalVariable i) -> (
                    match (Ain.get_global_by_index ctx.ain i).value_type with
                    | Ain.Type.IFace _ -> true
                    | _ -> false)
                | Member (_, _, ClassVariable _) -> (
                    match self#member_type lhs with
                    | Ain.Type.IFace _ -> true
                    | _ -> false)
                | _ -> (
                    match lhs.ty with
                    | Struct (name, _) | Ref (Struct (name, _)) ->
                        Hashtbl.mem ctx.interface_names name
                    | _ -> false))
             && (match rhs.node with
                | Null -> false  (* let the existing Null special-cases handle it *)
                | _ -> true) ->
          (* v12 IFace lhs assignment as expression statement.
             Two sub-cases based on rhs shape:

             1. DummyRef(Call): rhs's R_ASSIGN stores into dummy slot,
                then we need stack juggle + second R_ASSIGN to assign
                to lhs. Match alice's pattern with DUP2; REF prefix.

             2. Simple rhs (Ident, Member, etc.): rhs emits 2 stack
                items (src_p, src_i). R_ASSIGN consumes 4, leaves 2.
                POP; SP_INC drops idx + refcount-bumps page.

             Original Rance10's pattern (DummyRef case):
             Original Rance10's pattern:
               <lhs lvalue: PUSHSTRUCTPAGE; PUSH N>
               DUP2; REF                  ; push old lhs value for later DELETE
               <rhs DummyRef path: stores call result in dummy slot via R_ASSIGN>
               DUP_X2; POP; DUP_X2; POP   ; stack juggle to bring old to top
               DELETE                     ; release old lhs value
               R_ASSIGN                   ; assign new value to lhs
               POP; SP_INC                ; cleanup, refcount-bump

             Our default codegen emits the two R_ASSIGNs back-to-back
             with no juggling, leaving stack imbalanced; the trailing
             compile_pop's DELETE then hits page=0. *)
          (match rhs.node with
           | DummyRef (_, { node = Call _; _ }) ->
             self#compile_variable_ref lhs;
             self#write_instruction0 DUP2;
             self#write_instruction0 REF;
             self#compile_expression rhs;
             self#write_instruction0 DUP_X2;
             self#write_instruction0 POP;
             self#write_instruction0 DUP_X2;
             self#write_instruction0 POP;
             self#write_instruction0 DELETE;
             self#write_instruction0 R_ASSIGN;
             self#write_instruction0 POP;
             self#write_instruction0 SP_INC
           | DummyRef (_, { node = New _ | NewCall _; _ }) | New _ | NewCall _
             ->
             (* A [new T] rhs leaves ONE slot (the page — the dummy
                dance's ASSIGN keeps the value); the juggle below is
                written for a two-slot iface pair. orig completes the
                pair with [PUSH 0] (concrete-class vtable offset)
                before juggling. Without it every op lands one slot
                off — DELETE eats the INDEX and R_ASSIGN stores
                garbage into the element ([BattleSkillSelector@
                InitCardButton]'s [m_button[i] <- new ...Collection]
                corrupted the button array; battle entry died at
                [DeletePage] in the selector init). *)
             self#compile_variable_ref lhs;
             self#write_instruction0 DUP2;
             self#write_instruction0 REF;
             self#compile_expression rhs;
             self#write_instruction1 PUSH 0;
             self#write_instruction0 DUP_X2;
             self#write_instruction0 POP;
             self#write_instruction0 DUP_X2;
             self#write_instruction0 POP;
             self#write_instruction0 DELETE;
             self#write_instruction0 R_ASSIGN;
             self#write_instruction0 POP;
             self#write_instruction0 SP_INC
           | _ ->
             (* Simple rhs (Ident, Member, etc.): match alice's pattern
                that releases the OLD lhs value before R_ASSIGN.
                  lhs lvalue                  ; [page, slot]
                  DUP2; REF                   ; [page, slot, old]
                  rhs (REFREF leaves 2)       ; [page, slot, old, src_p, src_i]
                  DUP_X2; POP; DUP_X2; POP    ; rearrange to [page, slot, src_p, src_i, old]
                  DELETE                       ; release old
                  R_ASSIGN                     ; consume 4, leave 2
                  POP; SP_INC                  ; drop idx, ref page *)
             self#compile_variable_ref lhs;
             self#write_instruction0 DUP2;
             self#write_instruction0 REF;
             self#compile_expression rhs;
             self#write_instruction0 DUP_X2;
             self#write_instruction0 POP;
             self#write_instruction0 DUP_X2;
             self#write_instruction0 POP;
             self#write_instruction0 DELETE;
             self#write_instruction0 R_ASSIGN;
             self#write_instruction0 POP;
             self#write_instruction0 SP_INC);
          before_pop ()
      | _ ->
          self#compile_expression expr;
          before_pop ();
          self#compile_pop expr.ty (ASTExpression expr)

    method private compile_ref_assign ~is_init ~parent lhs (rhs : expression) =
      self#compile_lock_peek;
      self#compile_variable_ref lhs;
      self#compile_delete_ref lhs.ty;
      (match (is_init, rhs.node) with
      | _, Null -> ()
      | true, _ -> self#write_instruction0 DUP2
      | false, _ -> ());
      self#compile_lvalue rhs;
      (match lhs.ty with
      | _ when is_ref_scalar lhs.ty -> (
          match rhs.node with
          | Null ->
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 POP
          | _ when is_init ->
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 POP;
              self#write_instruction0 REF;
              self#write_instruction0 SP_INC
          | _ ->
              self#write_instruction0 DUP_U2;
              self#write_instruction0 SP_INC;
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              self#write_instruction0 POP)
      | Ref (String | Struct _ | Array _) -> (
          match rhs.node with
          | Null ->
              self#write_instruction0 ASSIGN;
              self#write_instruction0 POP
          | _ when is_init ->
              self#write_instruction0 ASSIGN;
              self#write_instruction0 DUP_X2;
              self#write_instruction0 POP;
              self#write_instruction0 REF;
              self#write_instruction0 SP_INC;
              self#write_instruction0 POP
          | _ ->
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC;
              self#write_instruction0 ASSIGN;
              self#write_instruction0 POP)
      | _ -> compiler_bug "Invalid LHS in reference assignment" (Some parent));
      self#compile_unlock_peek

    (** Emit the code for a statement. Statements are stack-neutral, i.e. the
        state of the stack is unchanged after executing a statement. *)
    method compile_statement (stmt : statement) =
      DebugInfo.add_loc debug_info current_address stmt.loc;
      (* delete locals that will be out-of-scope after this statement *)
      List.iter (List.rev stmt.delete_vars) ~f:(fun i ->
          if List.mem inline_deleted_dummies i ~equal:Int.equal then ()
          else self#compile_delete_var (self#get_local i));
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
             - Struct/ref-struct assignment temporaries are different:
               original v12 releases the DummyRef slot first, then the
               assignment expression result. Reversing those can drop
               the page backing the dummy before its local cleanup runs.
             - For everything else, [compile_pop] emits a plain [POP]
               which doesn't touch refcounts; alice releases the slot
               BEFORE the [POP] so the dummy is gone while the value
               is still on the stack. *)
          let cleanup_after_pop =
            Ain.version ctx.ain > 8
            &&
            match e.ty with
            | String | Delegate _ | HLLParam | Array _
            | Ref (String | Array _ | HLLParam) ->
                true
            | _ -> (
                match e.node with
                | Assign (EqAssign, { node = DummyRef _; _ }, _) -> true
                (* v12 [obj.OptMethod(...)] / [obj?.Method(...)] / chained
                   optional access producing a plain scalar result (Int /
                   Bool / Float / Enum) at statement level: orig pops the
                   call's return value BEFORE the optional-chain dummy
                   cleanup. The default [before_pop = cleanup] ordering
                   leaves the return value buried under the cleanup ops
                   and POPs the wrong slot. *)
                | Call (_, _, MethodCall _) when
                    Ain.version_gte ctx.ain (12, 0)
                    && (match e.ty with
                        | Int | Bool | Float | LongInt | Enum _ -> true
                        | _ -> false) ->
                    true
                (* v12 [(obj?.Getter(..).Prop = rhs) ?? rhs]: the
                   statement POPs the assigned value the ?? merge
                   yields; the receiver dummy's LOCALDELETE follows
                   the POP in orig. *)
                | NullCoalesce
                    ( {
                        node =
                          Call
                            ( {
                                node =
                                  Member
                                    ( ({
                                         node =
                                           DummyRef
                                             ( _,
                                               {
                                                 node =
                                                   Call
                                                     ( {
                                                         node =
                                                           OptionalMember _;
                                                         _;
                                                       },
                                                       _,
                                                       _ );
                                                 _;
                                               } );
                                         _;
                                       } as sprop_receiver),
                                      _,
                                      _ );
                                _;
                              },
                              args,
                              MethodCall (_, method_no) );
                        _;
                      },
                      _ )
                  when Ain.version_gte ctx.ain (12, 0)
                       && Poly.equal e.ty Void
                       && (match sprop_receiver.ty with
                          (* iface and non-iface setter-?? both yield
                             the value and pop after the merge; keep in
                             lockstep with the emission arms and the
                             statement-POP predicate. *)
                          | Struct _ | Ref (Struct _) -> true
                          | _ -> false)
                       && self#is_value_prop_setter_method method_no args ->
                    true
                | _ -> false)
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
      | Label name ->
          self#crc_push_word 0x406;
          self#crc_push_label_name name;
          self#add_label name stmt
      | If (test, con, alt) ->
          let vars_before =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          let empty_statement stmt =
            match stmt.node with EmptyStatement -> true | _ -> false
          in
          let branch_exit_statement stmt =
            match stmt.node with
            | Return _ | Continue | Break -> true
            | Compound [ { node = (Return _ | Continue | Break); _ } ] -> true
            | _ -> false
          in
          let inverted_null_test =
            match test.node with
            | Binary ((Equal | NEqual as op), a, ({ node = Null; _ } as b)) ->
                let op = match op with Equal -> NEqual | NEqual -> Equal | _ -> op in
                Some { test with node = Binary (op, a, b) }
            | Binary ((Equal | NEqual as op), ({ node = Null; _ } as a), b) ->
                let op = match op with Equal -> NEqual | NEqual -> Equal | _ -> op in
                Some { test with node = Binary (op, a, b) }
            | _ -> None
          in
          if
            Ain.version_gte ctx.ain (12, 0)
            && empty_statement alt
            && branch_exit_statement con
            && Option.is_some inverted_null_test
          then (
            (* v12 [if (x == null) return false] / [if (x != null) ...]
               fast-path. The [inverted_null_test] helper returns the
               inner expression with the comparison sense flipped so a
               single IFNZ skips the branch-exit body when condition is
               originally [== null]. Restored from pre-workflow state —
               dropping this broke delegate-typed null comparisons,
               which the general path lowers via DG_EQUAL or similar. *)
            let test = Option.value_exn inverted_null_test in
            self#compile_expression test;
            self#cleanup_condition_dummyrefs vars_before;
            self#maybe_emit_condition_itob test;
            let after_return_addr = current_address + 2 in
            self#write_instruction1 IFNZ 0;
            self#compile_statement con;
            self#write_address_at after_return_addr current_address)
          else (
          let _ = empty_statement in
          let _ = branch_exit_statement in
          (* The original v12 compiler peels [LogNot] from a branch
             condition ONLY when the negated operand is a bool-returning
             METHOD call: [if (!obj.Fn())] emits CALLMETHOD followed by
             the inverted branch, no NOT. Negated variables, members and
             notably HLL calls keep the NOT even when declared bool
             (canonical shape: cond; NOT; IFNZ then; JUMP else).
             Evidence (first-divergence histograms, 2026-07-02):
             peel-always diverged in 475+ Rance10 functions, peel-never
             in 339+, peel-any-bool-call in 408. Exemplars: kept-NOT for
             [!g_bRestrainScreensaverWhileAutoMode] (bool global) and
             [!system.IsDebugMode()] (bool CALLHLL, DebugLogTextToClipboard);
             peeled for [!this.IsEnd()] (bool CALLMETHOD, CASTask@IsEndTask). *)
          let test, peeled_lognot =
            if Ain.version_gte ctx.ain (12, 0) then
              match test.node with
              | Unary (LogNot, inner) -> (
                  match (inner.node, inner.ty) with
                  | Call (_, _, MethodCall _), Bool -> (inner, true)
                  | _ -> (test, false))
              | _ -> (test, false)
            else (test, false)
          in
          self#compile_expression test;
          (* v11: release condition-local dummies before the IFZ so
             both the taken and not-taken branch see them cleaned up. *)
          self#cleanup_condition_dummyrefs vars_before;
          self#maybe_emit_condition_itob test;
          if Ain.version_gte ctx.ain (12, 0) then (
            (* Capture the per-if cleanup slot list now; nested ifs in con
               will clobber [last_condition_deleted_dummies]. *)
            let saved_last = last_condition_deleted_dummies in
            if List.is_empty saved_last then (
              (* No condition-local dummies released. Original v12
                 if-without-cleanup layout:
                   cond
                   IFNZ body_label     (or IFZ if peeled LogNot)
                   JUMP alt_label
                   body_label: con
                   [if alt: JUMP end_label]
                   alt_label: alt
                   end_label: *)
              let branch_op = if peeled_lognot then IFZ else IFNZ in
              let if_addr = current_address + 2 in
              self#write_instruction1 branch_op 0;
              let alt_jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at if_addr current_address;
              self#compile_statement con;
              match alt.node with
              | EmptyStatement ->
                  self#write_address_at alt_jump_addr current_address
              | _ ->
                  let end_jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at alt_jump_addr current_address;
                  self#compile_statement alt;
                  self#write_address_at end_jump_addr current_address)
            else (
              (* Original v12 if-with-cleanup layout (per dasm of original
                 Rance10 — SceneQuestMap@ProcessNext / GetMoveType /
                 CheckNoLeader / RunCurrentObjectEvent):
                   cond
                   [pre-IF replay]    (already emitted above)
                   IFNZ con_label     (or IFZ if peeled LogNot)
                   [false-path replay]  (saved_last)
                   JUMP alt_label       (cont_label when alt is empty)
                   con_label: con
                   [post-con replay]    (saved_last — ALWAYS, even after
                                         a returning con, where it is
                                         dead code; the v12 8-op
                                         LOCALDELETE expansion is
                                         idempotent so the live case is
                                         safe too)
                   [JUMP end_label      only when alt is non-empty
                   alt_label: alt]
                   end/cont_label:
                 The previous version jumped the false path PAST the alt
                 and compiled alt as con's fallthrough: with a non-empty
                 else, true executed BOTH branches and false executed
                 NEITHER — SceneQuestMap@ProcessNext's else branch is
                 CreateSelection(), so quest-map route choices never
                 appeared. *)
              let branch_op = if peeled_lognot then IFZ else IFNZ in
              let if_addr = current_address + 2 in
              self#write_instruction1 branch_op 0;
              List.iter saved_last ~f:(fun idx ->
                  self#write_instruction1 SH_LOCALDELETE idx);
              let alt_jump_addr = current_address + 2 in
              self#write_instruction1 JUMP 0;
              self#write_address_at if_addr current_address;
              self#compile_statement con;
              (* Post-con replay covers Ref/Struct call-result dummies
                 only (orig exemplars SceneQuestMap@ProcessNext /
                 GetMoveType / CheckNoLeader / RunCurrentObjectEvent).
                 IFace dummies stay out: their release is deferred by
                 last-use tracking, and a fresh wrapper result (e.g.
                 AFL_Parts_Wrap) is kept alive ONLY by the dummy — the
                 raw replay freed the live wrapper and the next dispatch
                 read its vtable from a dead page:【 CALLMETHOD 】
                 存在しない関数番号 -1 at the intro scene transition. *)
              List.iter saved_last ~f:(fun idx ->
                  match (self#get_local idx).value_type with
                  | Ain.Type.IFace _ -> ()
                  | _ -> self#write_instruction1 SH_LOCALDELETE idx);
              (match alt.node with
              | EmptyStatement ->
                  self#write_address_at alt_jump_addr current_address
              | _ ->
                  let end_jump_addr = current_address + 2 in
                  self#write_instruction1 JUMP 0;
                  self#write_address_at alt_jump_addr current_address;
                  self#compile_statement alt;
                  self#write_address_at end_jump_addr current_address)))
          else (
            let ifz_addr = current_address + 2 in
            self#write_instruction1 IFZ 0;
            self#compile_statement con;
            match alt.node with
            | EmptyStatement when Ain.version ctx.ain > 8 ->
                (* v11 omits the trailing JUMP-over-alt when there's no
                   else branch. *)
                self#write_address_at ifz_addr current_address
            | _ ->
                let jump_addr = current_address + 2 in
                self#write_instruction1 JUMP 0;
                self#write_address_at ifz_addr current_address;
                self#compile_statement alt;
                self#write_address_at jump_addr current_address))
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
          (* start the loop with an unknown continue address *)
          let loop_addr = current_address in
          self#start_loop (-1);
          self#compile_statement body;
          (* loop test ('continue' jumps here) *)
          List.iter (Stack.top_exn cflow_stmts).continue_addrs ~f:(fun addr ->
              self#write_address_at addr current_address);
          let vars_before =
            match Stack.top scopes with
            | Some scope -> List.length scope.vars
            | None -> 0
          in
          self#compile_expression test;
          (* v11: release condition-local dummies before the branch so
             both the loop-again and the exit path see them cleaned up. *)
          self#cleanup_condition_dummyrefs vars_before;
          self#maybe_emit_condition_itob test;
          self#write_instruction1 IFNZ loop_addr;
          (* loop end *)
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
          if Ain.version ctx.ain > 8 then self#write_instruction1 JUMP test_addr;
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
          self#emit_inline_deleted_dummy_cleanup;
          self#crc_push_word 0x407;
          self#crc_push_label_name name;
          (* The 0x407 marker replaces the JUMP, so don't hash the JUMP. *)
          let saved = crc_state in
          crc_state <- Crc32.Inactive;
          self#add_goto name (current_address + 2) stmt;
          self#write_instruction1 JUMP 0;
          crc_state <- saved
      | Continue ->
          (* v11: replay [SH_LOCALDELETE] for dummies released inside
             the loop before jumping back to the test. *)
          self#emit_loop_exit_cleanup;
          self#add_continue (ASTStatement stmt)
      | Break ->
          self#emit_loop_exit_cleanup;
          self#record_switch_break_deleted_vars stmt.delete_vars;
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
          let prev_in_return = is_in_return_expr in
          is_in_return_expr <- true;
          Exn.protect ~finally:(fun () -> is_in_return_expr <- prev_in_return)
            ~f:(fun () ->
          (match ((Option.value_exn current_function).return_type, e.node) with
          | Ref _, Null -> self#compile_lvalue e
          | Ref (Int | Float | Bool | LongInt | FuncType _), _ ->
              self#compile_lvalue e;
              self#write_instruction0 DUP_U2;
              self#write_instruction0 SP_INC
          | Ref (String | Struct _ | Array _ | Delegate _), _ ->
              self#compile_lvalue e;
              (match e.ty with
              | Wrap _ when Ain.version ctx.ain > 8 ->
                  (* v11 [Wrap T] return: unwrap the fat-ref to the
                     underlying page-ref before [DUP; SP_INC]. *)
                  self#write_instruction0 REFREF;
                  self#write_instruction0 REF
              | Struct _ | Ref (Struct _)
                when Ain.version_gte ctx.ain (12, 0) -> (
                  match e.node with
                  | Cast
                      ( (Struct (_, dst_sno) | Ref (Struct (_, dst_sno))),
                        { ty =
                            (Struct (_, src_sno) | Ref (Struct (_, src_sno)));
                          _;
                        } )
                    when not (Int.equal src_sno dst_sno) ->
                      (* Original v12 normalizes failed X_ICAST returns to
                         NULL before the return-value SP_INC. *)
                      self#write_instruction1 PUSH (-1);
                      self#write_instruction0 EQUALE;
                      let ifnz_addr = current_address + 2 in
                      self#write_instruction1 IFNZ 0;
                      self#write_instruction0 POP;
                      let jump_addr = current_address + 2 in
                      self#write_instruction1 JUMP 0;
                      self#write_address_at ifnz_addr current_address;
                      self#write_instruction0 POP;
                      self#write_instruction0 POP;
                      self#write_instruction1 PUSH (-1);
                      self#write_address_at jump_addr current_address
                  | _ -> ())
              | _ -> ());
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC
          | Ref _, _ ->
              compile_error "return statement not implemented for ref type"
                (ASTStatement stmt)
          | IFace iface_sno, _
            when Ain.version_gte ctx.ain (12, 0) -> (
              let rec is_null_expr (e : expression) =
                match e.node with
                | Null -> true
                | Cast (_, inner) -> is_null_expr inner
                | _ -> false
              in
              if is_null_expr e then (
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH 0)
              else (
                (* v12 IFace return of [ref Struct] LOCAL: emit
                   PUSHLOCALPAGE; PUSH slot; REF (lvalue page-ref).
                   [compile_expression] appends [A_REF] via
                   [compile_dereference] for [Ref (Struct _)], one
                   deref too many — the returned fat-ref's page slot
                   then contains the struct's vtable slot 0 (a function
                   index) instead of the page-id, and the caller's
                   REFREF on the stored iface crashes with
                   Page=<func_idx>. Match original Rance10
                   [CreateRadioButton] tail. Restrict to
                   Ident+LocalVariable to avoid affecting member-
                   access / captured-var / call-result returns whose
                   A_REF emission is conditionally correct. *)
                let rec peel_cast (x : expression) =
                  match x.node with Cast (_, inner) -> peel_cast inner | _ -> x
                in
                let inner = peel_cast e in
                (match (inner.node, inner.ty) with
                | Ident (_, LocalVariable _), (Struct _ | Ref (Struct _)) ->
                    self#compile_lvalue inner
                | _ -> self#compile_expression e);
                match e.ty with
                | Struct (_, actual_sno) | Ref (Struct (_, actual_sno)) ->
                    if not (Int.equal actual_sno iface_sno) then
                      Option.iter
                        (self#interface_vtable_offset actual_sno iface_sno)
                        ~f:(fun offset -> self#write_instruction1 PUSH offset);
                    self#write_instruction0 DUP_U2;
                    self#write_instruction0 SP_INC
                | _ -> ()))
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
                (* v11+ borrowed-ref early-return: when returning a
                   DummyRef-wrapped Call whose ain-level return is
                   [Ref _] (or [New _] / [NewCall _] in v12), bump the
                   page's refcount before [RETURN] so the caller
                   receives an owning ref and the local dummy's
                   subsequent [SH_LOCALDELETE] doesn't free it. The
                   [needs_a_ref_for_consume] helper bakes in a v12
                   version gate, which would skip this for v11 — but
                   v11 [parts::detail::CalcPartsRect]-style code paths
                   rely on the A_REF too. Match the original pre-helper
                   behavior here: emit A_REF whenever the DummyRef
                   inner is a Call returning [Ref _] OR (v12 only) a
                   bare [New]/[NewCall]. *)
                let needs_a_ref =
                  match e.node with
                  | DummyRef (_, inner) -> (
                      match inner.node with
                      | New _ | NewCall _ ->
                          Ain.version_gte ctx.ain (12, 0)
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
          self#write_instruction0 RETURN)
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
          self#pre_emit_v12_rhs_lambdas rhs;
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
              | _
                when Ain.version_gte ctx.ain (12, 0)
                     &&
                     (match lhs.ty with
                     | Wrap (Ref (String | Struct _ | Array _ | HLLParam)) ->
                         true
                     | Wrap (String | Struct _ | Array _ | HLLParam) -> true
                     | _ -> false) ->
                  let vars_before =
                    match Stack.top scopes with
                    | Some scope -> List.length scope.vars
                    | None -> 0
                  in
                  self#write_instruction0 REFREF;
                  self#write_instruction0 DUP2;
                  self#write_instruction0 REF;
                  self#compile_lvalue rhs;
                  self#write_instruction0 SWAP;
                  self#write_instruction0 DELETE;
                  self#write_instruction0 ASSIGN;
                  self#write_instruction0 SP_INC;
                  (match Stack.top scopes with
                  | Some scope ->
                      let n_new = List.length scope.vars - vars_before in
                      if n_new > 0 then
                        List.iter
                          (List.rev (List.take scope.vars n_new))
                          ~f:self#compile_delete_var
                  | None -> ())
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
              | DummyRef (dummy_idx, { node = Call _; _ }) ->
                  self#write_instruction0 R_ASSIGN;
                  self#write_instruction0 POP;
                  self#write_instruction0 SP_INC;
                  self#write_instruction1 SH_LOCALDELETE dummy_idx
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
            when Ain.version_gte ctx.ain (12, 0) ->
              (* v12 ref-object rebinding matches the original order:
                 read the old page, push the new page, then delete old.
                 Deleting before the rhs is in place trips page-0 deletes
                 for freshly zeroed member slots during @0 initialization. *)
              let vars_before =
                match Stack.top scopes with
                | Some scope -> List.length scope.vars
                | None -> 0
              in
              self#write_instruction0 DUP2;
              self#write_instruction0 REF;
              (match rhs.node with
              | Null -> self#write_instruction1 PUSH (-1)
              | _ -> self#compile_lvalue rhs);
              self#write_instruction0 SWAP;
              self#write_instruction0 DELETE;
              self#write_instruction0 ASSIGN;
              self#write_instruction0 SP_INC;
              (match Stack.top scopes with
              | Some scope ->
                  let n_new = List.length scope.vars - vars_before in
                  if n_new > 0 then
                    List.iter
                      (List.rev (List.take scope.vars n_new))
                      ~f:self#compile_delete_var
              | None -> ())
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
        Ain.version ctx.ain <= 1
        && Option.is_none decl.initval
        && List.is_empty decl.array_dim
      then ()
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
            let emit_v12_ref_null_init () =
              if Ain.version_gte ctx.ain (12, 0) then (
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                match ain_to_jaf_type ctx.ain v.value_type with
                | Ref (Int | Bool | LongInt | FuncType _) ->
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction1 PUSH 0;
                    self#write_instruction0 R_ASSIGN;
                    self#write_instruction0 POP;
                    self#write_instruction0 POP
                | Ref Float ->
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction1_float F_PUSH 0.0;
                    self#write_instruction0 R_ASSIGN;
                    self#write_instruction0 POP;
                    self#write_instruction0 POP
                | Ref (String | Struct _ | Array _ | HLLParam | Delegate _) ->
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction0 ASSIGN;
                    self#write_instruction0 POP
                | _ -> ())
            in
            (* Foreach-desugar dummies (is_private=true) get their value
               from the foreach loop's source expression — original Rance10
               doesn't emit the null-init prefix for them. Across 526
               functions in Rance10 this saves 5 instructions each. *)
            if false && not decl.is_private then emit_v12_ref_null_init ();
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
                self#emit_slot_release;
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
                   into the freshly-declared slot using ASSIGN; SP_INC.
                   For foreach containers (v12), [compile_lvalue] descends
                   into a [DummyRef] wrapping the [::get()] call result
                   and registers the result-dummy slot in [scope.vars].
                   Without an inline cleanup here that dummy survives
                   until end_scope, leaving its slot pointing at the
                   container array while the loop body emits other
                   dummies and breaks/continues. Mirrors the sibling
                   [is_private] branch above.

                   Also skip [compile_delete_ref] (DUP2;REF;DELETE) for
                   is_private vars — their slots are freshly allocated
                   with uninitialized memory; the VM's page lookup
                   ([FUN_00622720]) rejects non-allocated page-ids →
                   [DeletePage Page=N] crash (confirmed via Ghidra:
                   the page-table flag at offset +4 must equal 1). *)
                let vb = vars_before () in
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                if not decl.is_private then
                  self#compile_delete_ref decl.type_spec.ty;
                self#compile_lvalue e;
                self#write_instruction0 ASSIGN;
                self#write_instruction0 SP_INC;
                self#cleanup_condition_dummyrefs vb
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
                self#emit_slot_release;
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
        | Int | Bool | LongInt | Float | Enum _ | FuncType _ | String ->
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
                    | Int | Bool | LongInt | Enum _ -> ConstInt 0
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
            self#compile_expr_and_pop
              ~before_pop:(fun () ->
                if Ain.version ctx.ain > 8 then
                    self#cleanup_condition_dummyrefs vars_before)
                {
                  node = Assign (EqAssign, lhs, rhs);
                  ty = rhs.ty;
                  loc = decl.location;
                }
        | Struct sno -> (
            (* FIXME: use verbose versions *)
            if not (Ain.version_gte ctx.ain (12, 0)) then
              self#write_instruction1 SH_LOCALDELETE v.index;
            self#write_instruction2 SH_LOCALCREATE v.index sno;
            match decl.initval with
            | Some { node = New { ty = Struct (_, init_sno); _ }; _ }
              when Ain.version_gte ctx.ain (12, 0) && Int.equal init_sno sno ->
                ()
            | Some { node = NewCall ({ ty = Struct (_, init_sno); _ }, []); _ }
              when Ain.version_gte ctx.ain (12, 0) && Int.equal init_sno sno ->
                ()
            | Some e ->
                self#compile_lvalue
                  {
                    node =
                      Ident (decl.name, LocalVariable (v.index, decl.location));
                    ty = decl.type_spec.ty;
                    loc = decl.location;
                  };
                self#compile_expression e;
                if Ain.version ctx.ain > 1 && Ain.version ctx.ain <= 8 then
                  self#write_instruction1 PUSH sno;
                self#write_instruction0 SR_ASSIGN;
                self#compile_pop decl.type_spec.ty (ASTVariable decl)
            | None -> ())
        | Array _ ->
            let has_dims = List.length decl.array_dim > 0 in
            let elem_ty =
              match v.value_type with
              | Array t ->
                  Ain.Type.int_of_data_type (Ain.version ctx.ain) t
              | _ -> self#array_element_type_code decl.type_spec.ty
            in
            self#compile_local_ref v.index;
            if Ain.version ctx.ain > 8 then (
              self#write_instruction0 REF;
              match decl.initval with
              | Some { node = ArrayLiteral elems; _ } ->
                  self#write_instruction0 DUP;
                  self#compile_CALLHLL "Array" "Free" elem_ty
                    (ASTVariable decl);
                  List.iter elems ~f:(fun elem ->
                      self#write_instruction0 DUP;
                      self#emit_array_literal_element elem;
                      self#compile_CALLHLL "Array" "PushBack" elem_ty
                        (ASTVariable decl));
                  self#write_instruction0 POP
              | Some e ->
                  self#compile_expression e;
                  (* v12 [array@T x = obj.GetList();] — the rhs is a
                     ref-returning call held in a dummy slot. [X_SET]
                     consumes the stacked page-ref without incref-ing,
                     so orig bumps it first ([A_REF]) and releases the
                     dummy immediately after the copy ([LOCALDELETE]
                     between X_SET and the trailing DELETE) instead of
                     at scope end. Without the bump, the dummy's later
                     release frees the array the copy source still
                     points at (A_ASSIGN page-acquisition faults:
                     CRadioButtonBoxParts@InsertCheckbox class,
                     byte-verified). *)
                  let borrow_dummy =
                    if Ain.version_gte ctx.ain (12, 0) then
                      match e.node with
                      | DummyRef (var_no, { node = Call _; _ })
                        when self#needs_a_ref_for_consume e ->
                          Some var_no
                      | _ -> None
                    else None
                  in
                  Option.iter borrow_dummy ~f:(fun _ ->
                      self#write_instruction0 A_REF);
                  self#write_instruction0 X_SET;
                  Option.iter borrow_dummy ~f:(fun var_no ->
                      self#write_instruction1 SH_LOCALDELETE var_no;
                      (* Released here; drop it from the scope tracker
                         so exit paths don't replay the release. *)
                      match Stack.top scopes with
                      | Some scope ->
                          scope.vars <-
                            List.filter scope.vars ~f:(fun sv ->
                                not (Int.equal sv.index var_no))
                      | None -> ());
                  self#write_instruction0 DELETE
              | None ->
                  if has_dims then (
                    List.iter decl.array_dim ~f:self#compile_expression;
                    for _ = 1 to 4 - List.length decl.array_dim do
                      self#write_instruction1 PUSH (-1)
                    done;
                    self#compile_CALLHLL "Array" "Alloc" elem_ty
                      (ASTVariable decl))
                  else
                    self#compile_CALLHLL "Array" "Free" elem_ty
                      (ASTVariable decl))
            else if has_dims then (
              List.iter decl.array_dim ~f:self#compile_expression;
              self#write_instruction1 PUSH (List.length decl.array_dim);
              self#write_instruction0 A_ALLOC)
            else self#write_instruction0 A_FREE
        | Delegate _ -> (
            (match decl.initval with
            | Some e when Ain.version_gte ctx.ain (12, 0) ->
                let rec find_lambda (e : expression) =
                  match e.node with
                  | Lambda f -> Some f
                  | Cast (_, inner) -> find_lambda inner
                  | _ -> None
                in
                (match find_lambda e with
                | Some f ->
                    let lambda_idx = Option.value_exn f.index in
                    if not (Hashtbl.mem v12_assignment_lambdas lambda_idx)
                    then (
                      let jump_addr = current_address + 2 in
                      self#write_instruction1 JUMP 0;
                      self#compile_function f;
                      self#write_address_at jump_addr current_address;
                      Hashtbl.set v12_assignment_lambdas ~key:lambda_idx
                        ~data:())
                | None -> ())
            | _ -> ());
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
                if Ain.version ctx.ain > 8 then self#write_instruction0 DELETE
                else self#write_instruction0 DG_POP
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
        | IFace _ when Ain.version_gte ctx.ain (12, 0) ->
            let lhs =
              {
                node = Ident (decl.name, LocalVariable (v.index, decl.location));
                ty = decl.type_spec.ty;
                loc = decl.location;
              }
            in
            (match decl.initval with
            | None when not (Hashtbl.mem v12_skip_iface_init v.index) ->
                (* v12 IFace local without initval (e.g. [IEnqueteItem
                   Item;] in CEnqueteItemManager@Add): emit NULL init
                   for the 2-slot fat-ref so subsequent partial stores
                   leave the offset slot at 0 (not stale function-index
                   data). Skip when the next stmt unconditionally
                   assigns this var (e.g. [Type v; if ((v = ...) ==
                   NULL)]) — original Rance10 omits the init there too.
                   *)
                self#write_instruction0 PUSHLOCALPAGE;
                self#write_instruction1 PUSH v.index;
                self#write_instruction0 DUP2;
                self#write_instruction0 REF;
                self#write_instruction0 DELETE;
                self#write_instruction1 PUSH (-1);
                self#write_instruction1 PUSH 0;
                self#write_instruction0 R_ASSIGN;
                self#write_instruction0 POP;
                self#write_instruction0 SP_INC
            | None -> ()
            | Some rhs ->
                let vars_before =
                  match Stack.top scopes with
                  | Some scope -> List.length scope.vars
                  | None -> 0
                in
                self#compile_variable_ref lhs;
                self#compile_delete_ref decl.type_spec.ty;
                (match rhs.node with
                | New { ty = Struct (_, s_no); _ } ->
                    self#write_instruction2 NEW s_no (self#bare_new_ctor s_no)
                | _ ->
                    let prev = v12_iface_local_init_owns_cast_guard in
                    v12_iface_local_init_owns_cast_guard <- true;
                    Exn.protect
                      ~f:(fun () -> self#compile_expression rhs)
                      ~finally:(fun () ->
                        v12_iface_local_init_owns_cast_guard <- prev));
                (match rhs.node with
                | Cast
                    ( (Struct (_, dst_sno) | Ref (Struct (_, dst_sno))),
                      { ty =
                          (Struct (_, src_sno) | Ref (Struct (_, src_sno)));
                        _;
                      } )
                  when not (Int.equal src_sno dst_sno) ->
                    (* Original v12 guards X_ICAST immediately before
                       storing into an interface local: a failed cast is
                       normalized to the IFace null pair before R_ASSIGN. *)
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction0 EQUALE;
                    let ifz_addr = current_address + 2 in
                    self#write_instruction1 IFZ 0;
                    self#write_instruction0 POP;
                    self#write_instruction0 POP;
                    self#write_instruction1 PUSH (-1);
                    self#write_instruction1 PUSH 0;
                    self#write_address_at ifz_addr current_address
                | _ -> ());
                self#write_instruction0 R_ASSIGN;
                self#write_instruction0 POP;
                self#write_instruction0 SP_INC;
                self#cleanup_condition_dummyrefs vars_before)
        (* v11+ IFace locals/params don't need explicit init — the
           value is provided by the caller (params) or is a NULL ref
           (locals). *)
        | IFace _ when Ain.version ctx.ain > 8 -> ()
        | IMainSystem | HLLFunc2 | HLLParam | Wrap _ | Option _
        | Unknown87 _ | IFace _ | Enum2 _ | HLLFunc | Unknown98
        | IFaceWrap _ | Function | Method | NullType ->
            compile_error
              (Printf.sprintf "Unimplemented variable type: %s for `%s`"
                 (jaf_type_to_string decl.type_spec.ty)
                 decl.name)
              (ASTVariable decl)

    (** Emit the code for a block of statements. *)
    method compile_block (stmts : statement list) =
      let top_level = Int.equal block_depth 0 in
      block_depth <- block_depth + 1;
      self#start_scope;
      (* v12 iface-init suppression: for [Type var; <next stmt that
         unconditionally assigns var>;] patterns, original Rance10
         skips the NULL-init prefix. Detect via a rec walker on the
         next stmt's expression tree. *)
      let rec expr_assigns_var (e : expression) var_no =
        match e.node with
        | Assign (EqAssign, lhs, _) -> (
            match lhs.node with
            | Ident (_, LocalVariable (i, _)) -> Int.equal i var_no
            | _ -> false)
        | Binary (_, a, b) ->
            expr_assigns_var a var_no || expr_assigns_var b var_no
        | Ternary (a, b, c) ->
            expr_assigns_var a var_no || expr_assigns_var b var_no
            || expr_assigns_var c var_no
        | Cast (_, inner) | Unary (_, inner) -> expr_assigns_var inner var_no
        | _ -> false
      in
      let stmt_assigns_var (stmt : statement) var_no =
        match stmt.node with
        | Expression e -> expr_assigns_var e var_no
        | If (cond, _, _) -> expr_assigns_var cond var_no
        | While (cond, _) -> expr_assigns_var cond var_no
        | _ -> false
      in
      let rec loop = function
        | [] -> ()
        | stmt :: rest ->
            (* Populate skip-set for Declarations whose next stmt
               unconditionally assigns the var. *)
            (if Ain.version_gte ctx.ain (12, 0) then
               match (stmt.node, rest) with
               | Declarations decls, next :: _ ->
                   List.iter decls.vars ~f:(fun (v : variable) ->
                       match v.index with
                       | Some i when stmt_assigns_var next i ->
                           Hashtbl.set v12_skip_iface_init ~key:i ~data:()
                       | _ -> ())
               | _ -> ());
            self#compile_statement stmt;
            if Ain.version_gte ctx.ain (12, 0) then
              self#emit_v12_last_use_cleanup stmt rest;
            ignore top_level;
            loop rest
      in
      loop stmts;
      self#end_scope;
      block_depth <- block_depth - 1

    method private statement_guaranteed_returns (stmt : statement) =
      match stmt.node with
      | Return _ | Jump _ | Jumps _ -> true
      | Compound stmts -> self#statements_guaranteed_return stmts
      | If (_, con, alt) ->
          self#statement_guaranteed_returns con
          && self#statement_guaranteed_returns alt
      | _ -> false

    method private statements_guaranteed_return stmts =
      match List.last stmts with
      | Some stmt -> self#statement_guaranteed_returns stmt
      | None -> false

    (** Emit the code for a default return value. *)
    method compile_default_return (t : Ain.Type.t) decl =
      match t with
      | Ref (String | Struct _ | Array _ | Delegate _ | IFace _) ->
          self#write_instruction1 PUSH (-1)
      | Ref (Int | Float | Bool | LongInt) ->
          self#write_instruction1 PUSH (-1);
          self#write_instruction1 PUSH 0
      | Void -> ()
      | Int | Bool | LongInt | Enum _ | FuncType _ ->
          self#write_instruction1 PUSH 0
      | Float -> self#write_instruction1 F_PUSH 0
      | String -> self#write_instruction1 S_PUSH 0
      | IFace _ when Ain.version_gte ctx.ain (12, 0) ->
          self#write_instruction1 PUSH (-1);
          self#write_instruction1 PUSH 0
      | Struct _ | Array _ | Delegate _ | IFace _ ->
          self#write_instruction1 PUSH (-1)
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
      let prev_enclosing_functions = enclosing_functions in
      (if func.is_lambda then
         match self#find_lambda_parents func.name with
         | parents -> enclosing_functions <- parents);
      let prev_inline_deleted_dummies = inline_deleted_dummies in
      let prev_last_condition_deleted_dummies = last_condition_deleted_dummies in
      let prev_end_switch_deleted_dummies = end_switch_deleted_dummies in
      let prev_last_use_deleted_vars = v12_last_use_deleted_vars in
      let prev_block_depth = block_depth in
      let prev_v12_dummy_slots_initialized =
        Hashtbl.copy v12_dummy_slots_initialized
      in
      inline_deleted_dummies <- [];
      last_condition_deleted_dummies <- [];
      end_switch_deleted_dummies <- [];
      v12_last_use_deleted_vars <- [];
      Hashtbl.clear v12_dummy_slots_initialized;
      block_depth <- 0;
      let prev_cflow_stmts = cflow_stmts in
      cflow_stmts <- Stack.create ();
      let prev_scopes = scopes in
      scopes <- Stack.create ();
      let prev_labels = labels in
      labels <- Hashtbl.create (module String);
      (* Freeze the parent's CRC: it stops at this nested FUNC (lambda). *)
      let prev_crc_state = Crc32.freeze crc_state in
      self#write_instruction1 FUNC index;
      (* Accumulate the function CRC over the return/argument type codes and the
         body opcodes. FUNC and ENDFUNC are excluded. *)
      crc_state <- Crc32.start;
      let int_of_data_type t =
        Ain.Type.int_of_data_type (Ain.version ctx.ain) t
      in
      self#crc_push_word (int_of_data_type func.return_type);
      List.iter (Ain.Function.logical_parameters func) ~f:(fun v ->
          self#crc_push_word (int_of_data_type v.value_type));
      (match decl.class_index with
      | Some class_index
        when Ain.version_gte ctx.ain (12, 0)
             && (String.equal decl.name "0" || String.equal decl.name "2") ->
          self#emit_interface_vtable_init class_index
      | _ -> ());
      self#compile_block (Option.value_exn decl.body);
      let v12 = Ain.version_gte ctx.ain (12, 0) in
      let emits_v12_accessor_endfunc decl =
        v12 && Declarations.is_property_stub decl
      in
      let rec stmt_has_early_return (s : statement) =
        match s.node with
        | Return _ -> true
        | Compound stmts -> List.exists stmts ~f:stmt_has_early_return
        | If (_, con, alt) ->
            stmt_has_early_return con || stmt_has_early_return alt
        | While (_, body) | DoWhile (_, body) -> stmt_has_early_return body
        | For (_, _, _, body) | ForEach (_, _, _, _, body) ->
            stmt_has_early_return body
        | Switch (_, stmts) -> List.exists stmts ~f:stmt_has_early_return
        | _ -> false
      in
      let body_has_only_trailing_return =
        match decl.body with
        | None -> false
        | Some stmts ->
            (match List.last stmts with
             | Some last when (match last.node with Return _ -> true | _ -> false) ->
                 (* Check that no statement BEFORE the last has a return. *)
                 let earlier = List.drop_last_exn stmts in
                 not (List.exists earlier ~f:stmt_has_early_return)
             | _ -> false)
      in
      let skip_default_return =
        (decl.is_lambda
         && v12
         && self#statements_guaranteed_return (Option.value_exn decl.body)
         && (
           (* Orig skips the fallthrough default-return for v12 lambdas
              under two conditions:
              - IFace-returning (always, even with early returns)
              - body is a single trailing return (no early returns
                anywhere). Lambdas with early-return + final-return
                paths still get the orig fallthrough — observed in
                [activity::detail::AddUserComponent]'s inline
                [(string name) => bool { if (...) return false;
                ...; return ...; }] lambdas. *)
           (match func.return_type with
            | IFace _ -> true
            | _ -> false)
           || body_has_only_trailing_return))
        || (emits_v12_accessor_endfunc decl
           && String.is_suffix decl.name ~suffix:"::get")
      in
      if
        (not func.is_label)
        && (not (String.equal func.name "NULL"))
        && not skip_default_return
      then (
        self#compile_default_return func.return_type
          (ASTDeclaration (Function decl));
        self#write_instruction0 RETURN);
      let crc = Crc32.finalize crc_state in
      crc_state <- prev_crc_state;
      let func = { func with crc } in
      (* ENDFUNC is not generated for the [NULL] function and methods
         except auto-generated array initializers — the global-init
         function ("0") and the per-class auto-array-initializer ("2")
         both need ENDFUNC so the VM knows where the function body
         ends. ain v0/v1 does not have ENDFUNC.

         v12: original Rance10 does not emit ENDFUNC after most class
         methods/constructors. It does always terminate lambda bodies and
         the synthetic class "2" bodies, and free functions commonly carry
         ENDFUNC at source-file boundaries. Emitting ENDFUNC for every v12
         method changes the startup constructor/lambda layout. *)
      (match decl with
      | _ when ctx.version <= 100 -> ()
      | { name = "NULL"; _ } -> ()
      | { is_lambda = true; _ } when v12 -> self#write_instruction1 ENDFUNC index
      | { name = "2"; _ } when v12 -> self#write_instruction1 ENDFUNC index
      | _ when emits_v12_accessor_endfunc decl ->
          self#write_instruction1 ENDFUNC index
      | { class_name = None; _ } when v12 -> self#write_instruction1 ENDFUNC index
      | { class_name = None; _ }
      | { name = "0"; _ }
      | { name = "2"; _ }
      | { is_lambda = true; _ } ->
          self#write_instruction1 ENDFUNC index
      | _ -> ());
      self#resolve_gotos;
      Ain.write_function ctx.ain func;
      current_function <- prev_function;
      enclosing_functions <- prev_enclosing_functions;
      inline_deleted_dummies <- prev_inline_deleted_dummies;
      last_condition_deleted_dummies <- prev_last_condition_deleted_dummies;
      end_switch_deleted_dummies <- prev_end_switch_deleted_dummies;
      v12_last_use_deleted_vars <- prev_last_use_deleted_vars;
      Hashtbl.clear v12_dummy_slots_initialized;
      Hashtbl.iteri prev_v12_dummy_slots_initialized ~f:(fun ~key ~data ->
          Hashtbl.set v12_dummy_slots_initialized ~key ~data);
      block_depth <- prev_block_depth;
      cflow_stmts <- prev_cflow_stmts;
      scopes <- prev_scopes;
      labels <- prev_labels;
      (* v12 duplicate prototype body emission: Rance10 source contains
         repeated method/property/event prototypes, and the original
         compiler keeps separate FUNC rows for those repeats. Declaration
         analysis allocates the extra slots in [ctx.overloads]; when a
         real body for the same signature is compiled, emit that body into
         each duplicate slot instead of allocating speculative duplicates
         here. *)
      if v12
         && Option.is_some decl.body
         && not (Hashtbl.mem body_dup_emitted (Option.value_exn decl.index))
      then (
        let same_signature (other : fundecl) =
          List.length decl.params = List.length other.params
          && List.for_all2_exn decl.params other.params ~f:(fun a b ->
                 jaf_type_equal a.type_spec.ty b.type_spec.ty)
          && jaf_type_equal decl.return.ty other.return.ty
        in
        let source_obj = Ain.get_function_by_index ctx.ain index in
        let duplicates =
          Hashtbl.find ctx.overloads (Jaf.mangled_name decl)
          |> Option.value ~default:[]
          |> List.filter ~f:(fun dup ->
                 Option.is_none dup.body
                 && same_signature dup
                 &&
                 match dup.index with
                 | Some dup_idx ->
                     dup_idx <> index
                     && not (Hashtbl.mem body_dup_emitted dup_idx)
                 | None -> false)
        in
        List.iteri duplicates ~f:(fun dup_rank dup ->
            let dup_idx = Option.value_exn dup.index in
            Hashtbl.set body_dup_emitted ~key:dup_idx ~data:();
            let dup_obj = Ain.get_function_by_index ctx.ain dup_idx in
            Ain.write_function ctx.ain
              { dup_obj with
                return_type = source_obj.return_type;
                nr_args = source_obj.nr_args;
                vars = source_obj.vars;
                is_label = source_obj.is_label;
                is_lambda = source_obj.is_lambda };
            let prev_dup_rank = v12_current_body_dup_rank in
            Exn.protect
              ~f:(fun () ->
                v12_current_body_dup_rank <- Some (dup_rank + 1);
                self#compile_function
                  { decl with index = Some dup_idx; params = decl.params })
              ~finally:(fun () ->
                v12_current_body_dup_rank <- prev_dup_rank)));
      (* v12 interface-backed concrete duplicate emission: some interfaces
         contain duplicate exact prototypes, while their implementing class
         only declares one concrete prototype. Original Rance10 still emits
         one concrete FUNC body per duplicate interface slot (notably
         CActivityWrap/IActivity). Only synthesize the deficit between the
         repeated interface signature count and the class's own declaration
         count; classes that already repeat their prototypes are handled by
         the ctx.overloads path above. *)
      if v12
         && Option.is_some decl.body
         && not decl.is_lambda
         && not (String.is_suffix decl.name ~suffix:"::get")
         && not (String.is_suffix decl.name ~suffix:"::set")
         && not (String.is_suffix decl.name ~suffix:"::add")
         && not (String.is_suffix decl.name ~suffix:"::remove")
         && not (Hashtbl.mem body_dup_emitted (Option.value_exn decl.index))
      then (
        let same_signature (other : fundecl) =
          String.equal decl.name other.name
          && List.length decl.params = List.length other.params
          && List.for_all2_exn decl.params other.params ~f:(fun a b ->
                 jaf_type_equal a.type_spec.ty b.type_spec.ty)
          && jaf_type_equal decl.return.ty other.return.ty
        in
        let interface_signature_count class_name =
          match Hashtbl.find ctx.structs class_name with
          | None -> 0
          | Some jaf_s ->
              let ain_s = Ain.get_struct_by_index ctx.ain jaf_s.index in
              List.fold ain_s.interfaces ~init:0
                ~f:(fun acc (iface : Ain.Struct.interface) ->
                  let iface_s =
                    Ain.get_struct_by_index ctx.ain iface.struct_type
                  in
                  acc
                  + (Hashtbl.find ctx.v12_struct_methods iface_s.name
                    |> Option.value ~default:[]
                    |> List.count ~f:same_signature))
        in
        match decl.class_name with
        | None -> ()
        | Some class_name ->
            let class_count =
              Hashtbl.find ctx.v12_struct_methods class_name
              |> Option.value ~default:[]
              |> List.count ~f:same_signature
            in
            let needed =
              Int.max 0 (interface_signature_count class_name - class_count)
            in
            let dup_indices =
              Hashtbl.find ctx.v12_body_dup_indices
                (Option.value_exn decl.index)
              |> Option.value ~default:[]
            in
            let missing = needed - List.length dup_indices in
            let dup_indices =
              if missing > 0 then
                dup_indices
                @ List.init missing ~f:(fun _ ->
                    (Ain.add_function ~nr_args:(List.length decl.params)
                       ctx.ain (Jaf.mangled_name decl))
                      .index)
              else dup_indices
            in
            List.iteri dup_indices ~f:(fun dup_i dup_idx ->
              let source_obj = Ain.get_function_by_index ctx.ain index in
              let new_f = Ain.get_function_by_index ctx.ain dup_idx in
              Hashtbl.set body_dup_emitted ~key:new_f.index ~data:();
              Ain.write_function ctx.ain
                { new_f with
                  return_type = source_obj.return_type;
                  nr_args = source_obj.nr_args;
                  vars = source_obj.vars;
                  is_label = source_obj.is_label;
                  is_lambda = source_obj.is_lambda };
              let prev_dup_rank = v12_current_body_dup_rank in
              Exn.protect
                ~f:(fun () ->
                  v12_current_body_dup_rank <- Some (class_count + dup_i);
                  self#compile_function { decl with index = Some new_f.index })
                ~finally:(fun () ->
                  v12_current_body_dup_rank <- prev_dup_rank)
            ));
      (* v12 object-return helper duplication: original Rance10 emits
         repeated concrete FUNC bodies for a small family of ref/iface/array
         returning helpers even though the decompiled class declaration only
         contains one prototype. These duplicate rows are byte-identical and
         appear before later functions, so leaving them out shifts table shape
         around heavily-used battle/activity helpers. *)
      let object_return_dup_count () =
        if
          (not v12)
          || Option.is_none decl.body
          || decl.is_lambda
          || String.is_suffix decl.name ~suffix:"::get"
          || String.is_suffix decl.name ~suffix:"::set"
          || String.is_suffix decl.name ~suffix:"::add"
          || String.is_suffix decl.name ~suffix:"::remove"
          || Hashtbl.mem body_dup_emitted (Option.value_exn decl.index)
        then 0
        else
          let is_object_return =
            match func.return_type with
            | Ain.Type.Ref _ | Ain.Type.IFace _ | Ain.Type.Array _ -> true
            | _ -> false
          in
          if not is_object_return then 0
          else
            let qname = Jaf.mangled_name decl in
            let one_dup_names =
              Set.of_list
                (module String)
                [
                  "Activity@GetButton";
                  "Activity@GetCg";
                  "Activity@GetCheckBox";
                  "Activity@GetComboBox";
                  "Activity@GetForm";
                  "Activity@GetFromName";
                  "Activity@GetLabel";
                  "Activity@GetListBox";
                  "Activity@GetMLTextBox";
                  "Activity@GetParts";
                  "Activity@GetSpinBox";
                  "Activity@GetTextBox";
                  "Activity@GetVScrollBar";
                  "BattleContext@GetPlayer";
                  "CAS3DStage@GetBrushInstance";
                  "CAS3DStage@GetGroupInstance";
                  "CAS3DStage@GetInstance";
                  "PlayerAttackDamageCalculator@BadConditions";
                  "QuestMapObjectCollection@Get";
                  "enquate::detail::CEnqueteAnswerBox@Get";
                  "enquate::detail::CEnqueteAnswerIcon@GetCheckBox";
                  "enquate::detail::CEnqueteAnswerIcon@GetIcon";
                  "enquate::detail::CEnqueteDataManager@Get";
                  "stageeditor::detail::CSealEngine@GetSelectableInstanceList";
                  "stageeditor::detail::CSealEngine@GetSelectedInstanceList";
                  "stageeditor::detail::CStage@GetElement";
                  "stageeditor::detail::CStage@GetElementFromName";
                ]
            in
            if Set.mem one_dup_names qname then 1
            else if
              String.is_prefix qname ~prefix:"KeyValueMap<"
              &&
              (String.is_suffix qname ~suffix:"@Get"
              || String.is_suffix qname ~suffix:"@GetFromIndex")
            then 2
            else 0
      in
      let object_return_dups = object_return_dup_count () in
      if object_return_dups > 0 then
        for _ = 1 to object_return_dups do
          let mangled = Jaf.mangled_name decl in
          let source_obj = Ain.get_function_by_index ctx.ain index in
          let new_f = Ain.add_function ctx.ain mangled in
          Hashtbl.set body_dup_emitted ~key:new_f.index ~data:();
          Ain.write_function ctx.ain
            { new_f with
              return_type = source_obj.return_type;
              nr_args = source_obj.nr_args;
              vars = source_obj.vars;
              is_label = source_obj.is_label;
              is_lambda = source_obj.is_lambda };
          let readonly_lambda_name name =
            match String.substr_index name ~pattern:")(" with
            | Some pos ->
                String.prefix name (pos + 1)
                ^ " readonly"
                ^ String.drop_prefix name (pos + 1)
            | None -> name ^ " readonly"
          in
          let readonly_hll_overload lib_no fun_no =
            let lib = Ain.get_library_by_index ctx.ain lib_no in
            if
              fun_no >= 0
              && fun_no < Array.length lib.functions
              && String.equal lib.name "Array"
            then
              let base = lib.functions.(fun_no) in
              Array.find_mapi lib.functions ~f:(fun i f ->
                  if
                    i > fun_no
                    && String.equal f.name base.name
                    && Int.equal (List.length f.arguments)
                         (List.length base.arguments)
                  then Some i
                  else None)
              |> Option.value ~default:fun_no
            else fun_no
          in
          let clone_variable (v : Jaf.variable) =
            {
              v with
              type_spec = { v.type_spec with ty = v.type_spec.ty };
              array_dim = [];
              initval = None;
            }
          in
          let rec clone_expr (e : Jaf.expression) =
            { e with node = clone_expr_node e.node }
          and clone_expr_opt = function
            | None -> None
            | Some e -> Some (clone_expr e)
          and clone_expr_node = function
            | ConstInt _ as n -> n
            | ConstFloat _ as n -> n
            | ConstChar _ as n -> n
            | ConstString _ as n -> n
            | Ident _ as n -> n
            | FuncAddr _ as n -> n
            | MemberAddr _ as n -> n
            | This -> This
            | Null -> Null
            | New ts -> New { ts with ty = ts.ty }
            | Unary (op, e) -> Unary (op, clone_expr e)
            | Binary (op, a, b) -> Binary (op, clone_expr a, clone_expr b)
            | Assign (op, a, b) -> Assign (op, clone_expr a, clone_expr b)
            | Seq (a, b) -> Seq (clone_expr a, clone_expr b)
            | Ternary (a, b, c) ->
                Ternary (clone_expr a, clone_expr b, clone_expr c)
            | OptionalMember (e, name, mt) ->
                OptionalMember (clone_expr e, name, mt)
            | NullCoalesce (a, b) -> NullCoalesce (clone_expr a, clone_expr b)
            | Cast (ty, e) -> Cast (ty, clone_expr e)
            | Subscript (a, b) -> Subscript (clone_expr a, clone_expr b)
            | Member (e, name, mt) -> Member (clone_expr e, name, mt)
            | Call (e, args, HLLCall (lib_no, fun_no)) ->
                Call
                  ( clone_expr e,
                    List.map args ~f:clone_expr_opt,
                    HLLCall (lib_no, readonly_hll_overload lib_no fun_no) )
            | Call (e, args, ct) ->
                Call (clone_expr e, List.map args ~f:clone_expr_opt, ct)
            | NewCall (ts, args) ->
                NewCall ({ ts with ty = ts.ty }, List.map args ~f:clone_expr_opt)
            | ArrayLiteral elems -> ArrayLiteral (List.map elems ~f:clone_expr)
            | DummyRef (i, e) -> DummyRef (i, clone_expr e)
            | RvalueRef e -> RvalueRef (clone_expr e)
            | Lambda f -> Lambda (clone_lambda f)
          and clone_stmt (s : Jaf.statement) =
            { s with node = clone_stmt_node s.node; delete_vars = s.delete_vars }
          and clone_stmt_node = function
            | EmptyStatement -> EmptyStatement
            | Declarations ds ->
                Declarations
                  {
                    ds with
                    typespec = { ds.typespec with ty = ds.typespec.ty };
                    vars = List.map ds.vars ~f:clone_variable;
                  }
            | Expression e -> Expression (clone_expr e)
            | Compound ss -> Compound (List.map ss ~f:clone_stmt)
            | Label _ as n -> n
            | If (c, t, f) -> If (clone_expr c, clone_stmt t, clone_stmt f)
            | While (c, b) -> While (clone_expr c, clone_stmt b)
            | DoWhile (c, b) -> DoWhile (clone_expr c, clone_stmt b)
            | For (a, b, c, d) ->
                For
                  ( clone_stmt a,
                    Option.map b ~f:clone_expr,
                    Option.map c ~f:clone_expr,
                    clone_stmt d )
            | ForEach (rev, name, idx, e, b) ->
                ForEach (rev, name, idx, clone_expr e, clone_stmt b)
            | Goto _ as n -> n
            | Continue -> Continue
            | Break -> Break
            | Switch (e, ss) -> Switch (clone_expr e, List.map ss ~f:clone_stmt)
            | Case e -> Case (clone_expr e)
            | Default -> Default
            | Return e -> Return (Option.map e ~f:clone_expr)
            | Jump _ as n -> n
            | Jumps e -> Jumps (clone_expr e)
            | Message _ as n -> n
            | RefAssign (a, b) -> RefAssign (clone_expr a, clone_expr b)
            | ObjSwap (a, b) -> ObjSwap (clone_expr a, clone_expr b)
          and clone_lambda (f : Jaf.fundecl) =
            let old_idx = Option.value_exn f.index in
            let old_obj = Ain.get_function_by_index ctx.ain old_idx in
            let cloned =
              {
                f with
                name = readonly_lambda_name f.name;
                params = List.map f.params ~f:clone_variable;
                body = Option.map f.body ~f:(List.map ~f:clone_stmt);
                index = None;
              }
            in
            let new_idx =
              (Ain.add_function ~nr_args:(List.length cloned.params) ctx.ain
                 (Jaf.mangled_name cloned))
                .index
            in
            let new_obj = Ain.get_function_by_index ctx.ain new_idx in
            Ain.write_function ctx.ain
              {
                new_obj with
                return_type = old_obj.return_type;
                nr_args = old_obj.nr_args;
                vars = old_obj.vars;
                is_label = old_obj.is_label;
                is_lambda = old_obj.is_lambda;
              };
            { cloned with index = Some new_idx }
          in
          let dup_decl =
            {
              decl with
              index = Some new_f.index;
              params = List.map decl.params ~f:clone_variable;
              body = Option.map decl.body ~f:(List.map ~f:clone_stmt);
            }
          in
          self#compile_function dup_decl
        done;
      (* v12 property getter duplication: original Rance10 emits declared
         property getters twice (byte-identical bodies, separate
         FUNC indices). After the first emission, allocate a second
         slot and recurse — only when this is a class-method property
         getter found in the struct property table. *)
      let is_auto_property_getter (decl : fundecl) =
        let qname = Jaf.mangled_name decl in
        let skip_getter_dup =
          Set.mem
            (Set.of_list
               (module String)
               [
                 "ActivityLabel@Text::get";
                 "BattleLog@IndentText::get";
                 "BattleLog@Text::get";
                 "BattleLogCollection@Logs::get";
                 "BattleLogLine@LineText::get";
                 "LeaderCard@Skills::get";
                 "MenuContext@IsCheck::get";
                 "MenuContext@IsShow::get";
                 "Party@Leaders::get";
                 "PlayerAttackDamageCalculator@CardAtk::get";
                 "PlayerAttackDamageCalculator@SourceAtk::get";
                 "PlayerCard@Skills::get";
                 "PlayerCardCollection@Cards::get";
                 "PlayerCardSkill@Instance::get";
                 "Quest@QuestMap::get";
                 "SceneCharacterSetting@IsMan::get";
                 "SceneCharacterSetting@Type::get";
               ])
            qname
        in
        let declared_property =
          match decl.class_name with
          | Some class_name when String.is_suffix decl.name ~suffix:"::get" -> (
              let prop_name =
                String.drop_suffix decl.name (String.length "::get")
              in
              match Hashtbl.find ctx.structs class_name with
              | Some s -> Hashtbl.mem s.properties prop_name
              | None -> false)
          | _ -> false
        in
        v12
        && declared_property
        && not skip_getter_dup
        && String.is_suffix decl.name ~suffix:"::get"
        && (* Single-statement Return body (after type analysis the
              expression may be Cast/Member/etc., so don't restrict
              shape — just count stmts). User-bodied getters typically
              have multiple statements. *)
        (match decl.body with
         | Some _ -> true
         | _ -> false)
      in
      (* The dup_decl recursion needs to know it's already a dup so it
         doesn't dup itself. Mark the NEW index in the hashtable BEFORE
         the recursive call so the recursive [is_auto_property_getter]
         check skips it (via the second condition). *)
      if is_auto_property_getter decl
         && not (Hashtbl.mem body_dup_emitted (Option.value_exn decl.index))
      then (
        let mangled = Jaf.mangled_name decl in
        let dup_indices =
          Hashtbl.find ctx.v12_property_getter_dup_indices
            (Option.value_exn decl.index)
          |> Option.value ~default:[]
        in
        let dup_indices =
          if List.is_empty dup_indices then
            [ (Ain.add_function ctx.ain mangled).index ]
          else dup_indices
        in
        List.iter dup_indices ~f:(fun dup_idx ->
            Hashtbl.set body_dup_emitted ~key:dup_idx ~data:();
            let dup_f = Ain.get_function_by_index ctx.ain dup_idx in
            (* Copy vars/params/return_type from the original function so
               compile_lvalue can find them when re-emitting the body. *)
            Ain.write_function ctx.ain
              { dup_f with
                return_type = func.return_type;
                nr_args = func.nr_args;
                vars = func.vars;
                is_label = func.is_label };
            let dup_decl = { decl with index = Some dup_idx } in
            self#compile_function dup_decl));
      (* v12 lambda drain: after the outer (non-lambda) function's
         ENDFUNC is written, emit any lambdas queued during its body
         compilation as separate top-level FUNC entries. Each
         drained lambda may queue further nested lambdas; loop until
         the queue is empty. Lambdas themselves don't drain — only
         outer functions do, so we naturally process all nesting in
         the outer's drain phase. *)
      if not decl.is_lambda && Ain.version_gte ctx.ain (12, 0) then
        let rec drain () =
          match Queue.dequeue v12_lambda_queue with
          | Some f ->
              self#compile_function f;
              drain ()
          | None -> ()
        in
        drain ()

    (** Emit the code for an ain v1 scenario label. *)
    method compile_scenario_label (decl : fundecl) =
      Ain.add_scenario_label ctx.ain decl.name current_address;
      let body = Option.value_exn decl.body in
      match body with
      | [ { node = Expression { node = Call (_, [], FunctionCall _); _ }; _ } ]
        ->
          self#compile_block body
      | _ ->
          compile_error
            "ain v1 scenario label body must be a single argument-less \
             function call"
            (ASTDeclaration (Function decl))

    (** Compile a list of declarations. *)
    method compile jaf_name (decls : declaration list) =
      start_address <- Ain.code_size ctx.ain;
      current_address <- start_address;
      let compile_decl = function
        | Jaf.Function f
          when Ain.version_gte ctx.ain (12, 0)
               && f.is_lambda
               &&
               (let idx = Option.value_exn f.index in
                Hashtbl.mem pre_emitted_lambdas idx
                || Hashtbl.mem v12_assignment_lambdas idx) ->
            ()
        | Jaf.Function f ->
            if f.is_label && Ain.version ctx.ain = 1 then
              self#compile_scenario_label f
            else self#compile_function f
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
        | Enum e when Ain.version_gte ctx.ain (12, 0) ->
            (match e.name with
            | None -> ()
            | Some enum_name ->
                let rec eval_const_int (expr : expression) =
                  match expr.node with
                  | ConstInt i -> Some i
                  | Unary (UMinus, inner) ->
                      Option.map (eval_const_int inner) ~f:(fun i -> -i)
                  | Unary (UPlus, inner) -> eval_const_int inner
                  | Unary (BitNot, inner) ->
                      Option.map (eval_const_int inner) ~f:lnot
                  | Binary (Plus, a, b) ->
                      Option.both (eval_const_int a) (eval_const_int b)
                      |> Option.map ~f:(fun (a, b) -> a + b)
                  | Binary (Minus, a, b) ->
                      Option.both (eval_const_int a) (eval_const_int b)
                      |> Option.map ~f:(fun (a, b) -> a - b)
                  | _ -> None
                in
                let next = ref 0 in
                let enum_items =
                  List.map e.values ~f:(fun (name, opt_expr) ->
                      let value =
                        match opt_expr with
                        | Some expr -> Option.value_exn (eval_const_int expr)
                        | None -> !next
                      in
                      next := value + 1;
                      (name, value))
                in
                let enum_type : jaf_type =
                  Enum (enum_name, Ain.add_enum ctx.ain enum_name)
                in
                let emit_function ?vars (fdecl : fundecl) emit_body =
                  match fdecl.index with
                  | None -> ()
                  | Some index ->
                      let base = Ain.get_function_by_index ctx.ain index in
                      if base.address >= 0 then ()
                      else
                        let vars = Option.value vars ~default:base.vars in
                        let func =
                          { base with address = current_address + 6; vars }
                        in
                        let prev_function = current_function in
                        current_function <- Some func;
                        Ain.write_function ctx.ain func;
                        self#write_instruction1 FUNC index;
                        emit_body ();
                        self#write_instruction1 ENDFUNC index;
                        current_function <- prev_function
                in
                let local_ref slot =
                  self#write_instruction0 PUSHLOCALPAGE;
                  self#write_instruction1 PUSH slot;
                  self#write_instruction0 REF
                in
                let emit_int_return n =
                  self#write_instruction1 PUSH n;
                  self#write_instruction0 RETURN
                in
                let emit_option_enum_return n =
                  self#write_instruction1 PUSH n;
                  self#write_instruction1 PUSH 0;
                  self#write_instruction0 RETURN
                in
                let emit_option_enum_null_return () =
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction1 PUSH (-1);
                  self#write_instruction0 RETURN
                in
                let emit_string_return s =
                  self#write_instruction1 S_PUSH (Ain.add_string ctx.ain s);
                  self#write_instruction0 RETURN
                in
                let emit_chain ~string_input ~on_match ~on_default =
                  local_ref 0;
                  List.iter enum_items ~f:(fun (name, value) ->
                      self#write_instruction0 DUP;
                      if string_input then (
                        self#write_instruction0 A_REF;
                        self#write_instruction1 S_PUSH
                          (Ain.add_string ctx.ain name);
                        self#write_instruction0 S_EQUALE)
                      else (
                        self#write_instruction1 PUSH value;
                        self#write_instruction0 EQUALE);
                      let ifz_addr = current_address + 2 in
                      self#write_instruction1 IFZ 0;
                      self#write_instruction0 POP;
                      on_match name value;
                      self#write_address_at ifz_addr current_address);
                  self#write_instruction0 POP;
                  on_default ()
                in
                let emit_get_list fdecl =
                  let result_var =
                    Ain.Variable.make ~index:0 "result"
                      (jaf_to_ain_type ~ctx fdecl.return.ty)
                  in
                  emit_function ~vars:[ result_var ] fdecl (fun () ->
                      local_ref 0;
                      self#write_instruction0 DUP;
                      self#write_instruction1 PUSH (List.length enum_items);
                      self#write_instruction1 PUSH (-1);
                      self#write_instruction1 PUSH (-1);
                      self#write_instruction1 PUSH (-1);
                      let elem_code =
                        Ain.Type.int_of_data_type (Ain.version ctx.ain)
                          (jaf_to_ain_type enum_type)
                      in
                      self#compile_CALLHLL "Array" "Alloc" elem_code
                        (ASTDeclaration (Enum e));
                      List.iteri enum_items ~f:(fun i (_, value) ->
                          self#write_instruction0 DUP;
                          self#write_instruction1 PUSH i;
                          self#write_instruction1 PUSH value;
                          self#write_instruction0 ASSIGN;
                          self#write_instruction0 POP);
                      self#write_instruction0 DUP;
                      self#write_instruction0 SP_INC;
                      self#write_instruction0 RETURN)
                in
                Option.iter
                  (Hashtbl.find ctx.functions (enum_name ^ "::GetList"))
                  ~f:emit_get_list;
                Option.iter
                  (Hashtbl.find ctx.functions (enum_name ^ "::IsExist"))
                  ~f:(fun fdecl ->
                    emit_function fdecl (fun () ->
                        emit_chain ~string_input:false
                          ~on_match:(fun _ _ -> emit_int_return 1)
                          ~on_default:(fun () -> emit_int_return 0)));
                Option.iter
                  (Hashtbl.find ctx.functions (enum_name ^ "::Parse"))
                  ~f:(fun fdecl ->
                    emit_function fdecl (fun () ->
                        emit_chain ~string_input:true
                          ~on_match:(fun _ value ->
                            emit_option_enum_return value)
                          ~on_default:emit_option_enum_null_return));
                Hashtbl.find ctx.overloads (enum_name ^ "::Parse")
                |> Option.value ~default:[]
                |> List.iter ~f:(fun fdecl ->
                       match fdecl.params with
                       | [ { type_spec = { ty = Int; _ }; _ } ] ->
                           emit_function fdecl (fun () ->
                               emit_chain ~string_input:false
                                 ~on_match:(fun _ value ->
                                   emit_option_enum_return value)
                                 ~on_default:emit_option_enum_null_return)
                       | _ -> ());
                Option.iter
                  (Hashtbl.find ctx.functions (enum_name ^ "@String"))
                  ~f:(fun fdecl ->
                    emit_function fdecl (fun () ->
                        emit_chain ~string_input:false
                          ~on_match:(fun name _ -> emit_string_return name)
                          ~on_default:(fun () -> emit_string_return ""))))
        | Enum _ ->
            (* v12 enum codegen TODO: the auto-generated methods
               (Numof/GetList/IsExist/Parse/String) need real bodies.
               For now skip — the synthetic stubs we registered earlier
               will get default empty bodies via emit_undefined_function_stubs. *)
            ()
      in
      List.iter decls ~f:compile_decl;
      (if Ain.version_gte ctx.ain (1, 0) then
         let jaf_name = String.tr ~target:'/' ~replacement:'\\' jaf_name in
         self#write_instruction1 EOF (Ain.add_file ctx.ain jaf_name));
      self#write_buffer
  end

let compile ctx jaf_name decls debug_info =
  (new jaf_compiler ctx debug_info)#compile jaf_name decls
