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
open Compiler

let sprintf = Printf.sprintf

let arg_to_string dasm ain (argtype : Bytecode.argtype) arg =
  match argtype with
  | Int -> Int32.to_string arg
  | Float -> Int32.float_of_bits arg |> Float.to_string
  | Address -> Int32.to_string arg
  | Function -> (Ain.get_function_by_index ain (Int32.to_int_exn arg)).name
  | String ->
      sprintf "\"%s\""
        (Ain.get_string ain (Int32.to_int_exn arg) |> Option.value_exn)
  | Message ->
      sprintf "\'%s\'"
        (Ain.get_message ain (Int32.to_int_exn arg) |> Option.value_exn)
  | Local ->
      let f =
        Ain.get_function_by_index ain
          (Option.value_exn (Dasm.current_func dasm))
      in
      (List.nth_exn f.vars (Int32.to_int_exn arg)).name
  | Global -> sprintf "global(%ld)" arg
  | Struct -> sprintf "struct(%ld)" arg
  | Syscall ->
      Bytecode.string_of_syscall
        (Bytecode.syscall_of_int (Int32.to_int_exn arg))
  | Library -> sprintf "library(%ld)" arg
  | LibraryFunction -> sprintf "library_function(%ld)" arg
  | File -> Ain.get_file ain (Int32.to_int_exn arg) |> Option.value_exn
  | Delegate -> sprintf "delegate(%ld)" arg
  | Switch -> sprintf "switch(%ld)" arg

let print_disassemble ain =
  let dasm = Dasm.create ain in
  while not (Dasm.eof dasm) do
    let opcode = Bytecode.opcode_of_int (Dasm.opcode dasm) in
    let argtypes = Dasm.argument_types dasm in
    let args = Dasm.arguments dasm in
    Stdio.printf "%03d: %s %s\n" (Dasm.addr dasm)
      (Bytecode.string_of_opcode opcode)
      (String.concat ~sep:", "
         (List.map2_exn ~f:(arg_to_string dasm ain) argtypes args));
    Dasm.next dasm
  done

let compile_test ?(ain_version = 4) ?(hlls = []) input =
  let ctx = Jaf.context_from_ain (Ain.create ain_version 0) in
  let debug_info = DebugInfo.create () in
  try
    let srcs =
      List.(
        append
          (map hlls ~f:(fun (name, _) ->
               Pje.Hll (name, Stdlib.Filename.chop_extension name)))
          [ Pje.Jaf "test.jaf" ])
    in
    Compile.compile ctx srcs debug_info (fun name ->
        List.Assoc.find hlls ~equal:String.equal name
        |> Option.value ~default:input);
    print_disassemble ctx.ain
  with
  | CompileError.Compile_error e ->
      CompileError.print_error e (fun _ -> Some input)
  | Failure msg ->
      (* Print compiler crashes without the backtrace — recorded
         backtraces embed source line numbers and churn on every
         codegen.ml edit. *)
      Stdio.printf "(Failure %S)\n" msg

let%expect_test "empty function" =
  compile_test {|
    void f() {}
  |};
  [%expect
    {|
      000: FUNC f
      006: RETURN
      008: ENDFUNC f
      014: EOF test.jaf
      020: FUNC NULL
      026: EOF
    |}]

let%expect_test "return" =
  compile_test {|
    int f() {
      return 42;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: PUSH 42
      012: RETURN
      014: PUSH 0
      020: RETURN
      022: ENDFUNC f
      028: EOF test.jaf
      034: FUNC NULL
      040: EOF
    |}]

let%expect_test "lint inc" =
  compile_test {|
    void f() {
      lint i;
      i++;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 0
      016: PUSHLOCALPAGE
      018: PUSH 0
      024: DUP2
      026: REF
      028: DUP_X2
      030: POP
      032: LI_INC
      034: POP
      036: RETURN
      038: ENDFUNC f
      044: EOF test.jaf
      050: FUNC NULL
      056: EOF |}]

let%expect_test "compare lint and int" =
  compile_test {|
    void f(lint a) {
      a == 0;
      1 < a;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALREF a
      012: PUSH 0
      018: EQUALE
      020: POP
      022: PUSH 1
      028: SH_LOCALREF a
      034: LT
      036: POP
      038: RETURN
      040: ENDFUNC f
      046: EOF test.jaf
      052: FUNC NULL
      058: EOF
    |}]

let%expect_test "local ref int" =
  compile_test {|
    void f() {
      ref int r;
    }
  |};
  [%expect
    {|
    000: FUNC f
    006: CALLSYS LockPeek
    012: POP
    014: PUSHLOCALPAGE
    016: PUSH 0
    022: DUP2
    024: REF
    026: DELETE
    028: PUSH -1
    034: PUSH 0
    040: R_ASSIGN
    042: POP
    044: POP
    046: CALLSYS UnlockPeek
    052: POP
    054: RETURN
    056: ENDFUNC f
    062: EOF test.jaf
    068: FUNC NULL
    074: EOF
    |}]

let%expect_test "local ref string" =
  compile_test {|
    void f() {
      ref string r;
    }
  |};
  [%expect
    {|
      000: FUNC f
      006: CALLSYS LockPeek
      012: POP
      014: PUSHLOCALPAGE
      016: PUSH 0
      022: DUP2
      024: REF
      026: DELETE
      028: PUSH -1
      034: ASSIGN
      036: POP
      038: CALLSYS UnlockPeek
      044: POP
      046: RETURN
      048: ENDFUNC f
      054: EOF test.jaf
      060: FUNC NULL
      066: EOF
  |}]

let%expect_test "jump statement" =
  compile_test
    {|
    #sfunc(void) {
      jumps "foo";
      jump sfunc;
    }
  |};
  [%expect
    {|
      000: FUNC sfunc
      006: S_PUSH "foo"
      012: CALLONJUMP
      014: SJUMP
      016: S_PUSH "sfunc"
      022: CALLONJUMP
      024: SJUMP
      026: ENDFUNC sfunc
      032: EOF test.jaf
      038: FUNC NULL
      044: EOF
  |}]

let%expect_test "new" =
  compile_test {|
      struct S {};
      ref S f(int i) { return new S; }
  |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 1
    014: PUSH 0
    020: CALLSYS LockPeek
    026: POP
    028: NEW
    030: ASSIGN
    032: CALLSYS UnlockPeek
    038: POP
    040: SR_REF2 struct(0)
    046: RETURN
    048: PUSH -1
    054: RETURN
    056: ENDFUNC f
    062: EOF test.jaf
    068: FUNC NULL
    074: EOF
    |}]

let%expect_test "function returning ref" =
  compile_test {|
      struct S {};
      ref S f() { return f(); }
  |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: CALLFUNC f
    020: ASSIGN
    022: SR_REF2 struct(0)
    028: RETURN
    030: PUSH -1
    036: RETURN
    038: ENDFUNC f
    044: EOF test.jaf
    050: FUNC NULL
    056: EOF
    |}]

let%expect_test "ref_return_null" =
  compile_test
    {|
      struct S {};
      ref S f() {
        return NULL;
      }
      ref int g() {
        return NULL;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSH -1
    012: PUSH 0
    018: RETURN
    020: PUSH -1
    026: RETURN
    028: ENDFUNC f
    034: FUNC g
    040: PUSH -1
    046: PUSH 0
    052: RETURN
    054: PUSH -1
    060: PUSH 0
    066: RETURN
    068: ENDFUNC g
    074: EOF test.jaf
    080: FUNC NULL
    086: EOF
    |}]

let%expect_test "return_struct_from_ref" =
  compile_test
    {|
      struct S {};
      ref S rs;
      ref S f() {
        return NULL;
      }
      S g() {
        return rs;
        return f();
      }
    |};
  [%expect
    {| :0:0-0: dereference not supported for type (This is a compiler bug!) |}]

let%expect_test "local ref int" =
  compile_test
    {|
      struct S {
        void f(int a) {
          this.f(this.r);
        }
        ref int r;
      };
    |};
  [%expect
    {|
    000: FUNC S@f
    006: PUSHSTRUCTPAGE
    008: PUSHSTRUCTPAGE
    010: PUSH 0
    016: REFREF
    018: REF
    020: CALLMETHOD S@f
    026: RETURN
    028: EOF test.jaf
    034: FUNC NULL
    040: EOF
    |}]

let%expect_test "bool ? ref int : int" =
  compile_test
    {|
      int f(int a, ref int ra) {
        return a == 0 ? ra : a;
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALREF a
      012: PUSH 0
      018: EQUALE
      020: IFZ 44
      026: PUSHLOCALPAGE
      028: PUSH 1
      034: REFREF
      036: REF
      038: JUMP 50
      044: SH_LOCALREF a
      050: RETURN
      052: PUSH 0
      058: RETURN
      060: ENDFUNC f
      066: EOF test.jaf
      072: FUNC NULL
      078: EOF
    |}]

let%expect_test "bool ? ref : ref" =
  compile_test
    {|
      ref int f(bool b) {
        return b ? f(b) : NULL;
      }
  |};
  [%expect
    {|
    test.jaf:3:27-31: Type error: expected int; got null
        3 |         return b ? f(b) : NULL;
                                      ^^^^
    |}]

let%expect_test "assign this" =
  compile_test
    {|
      struct S {
        void f();
      };

      void S::f() {
        S s2;
        s2 = this;
      }
    |};
  [%expect
    {|
    test.jaf:7:11-13: Unimplemented variable type: S for `s2`
        7 |         S s2;
                      ^^
    |}]

let%expect_test "deref struct assign" =
  compile_test
    {|
      struct S {};
      ref S ref_s(ref S rs) {
        S s;
        s = ref_s(rs);
        return rs;
      }
    |};
  [%expect
    {|
    test.jaf:4:11-12: Unimplemented variable type: S for `s`
        4 |         S s;
                      ^
    |}]

let%expect_test "ref struct assign" =
  compile_test
    {|
      struct S {};
      ref S f() {
        ref S r = f();
        return r;
      }
    |};
  [%expect
    {|
    test.jaf:4:15-22: Unimplemented variable type: ref S for `r`
        4 |         ref S r = f();
                          ^^^^^^^
    |}]

let%expect_test "local ref int assign" =
  compile_test
    {|
      ref int f() {
        ref int r = f();
        return r;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: CALLSYS LockPeek
    012: POP
    014: PUSHLOCALPAGE
    016: PUSH 0
    022: DUP2
    024: REF
    026: DELETE
    028: DUP2
    030: CALLFUNC f
    036: R_ASSIGN
    038: POP
    040: POP
    042: REF
    044: SP_INC
    046: CALLSYS UnlockPeek
    052: POP
    054: PUSHLOCALPAGE
    056: PUSH 0
    062: REFREF
    064: DUP_U2
    066: SP_INC
    068: RETURN
    070: PUSH -1
    076: PUSH 0
    082: RETURN
    084: ENDFUNC f
    090: EOF test.jaf
    096: FUNC NULL
    102: EOF
    |}]

(* The `<-` reassignment operator derives the SP_INC page from the source
   lvalue. This matches the SDK compiler. *)
let%expect_test "local ref int reassign" =
  compile_test
    {|
      int f(ref int a, ref int b) {
        a <- b;
        return a;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: CALLSYS LockPeek
    012: POP
    014: PUSHLOCALPAGE
    016: PUSH 0
    022: DUP2
    024: REF
    026: DELETE
    028: DUP2
    030: PUSHLOCALPAGE
    032: PUSH 2
    038: REFREF
    040: R_ASSIGN
    042: POP
    044: POP
    046: REF
    048: SP_INC
    050: CALLSYS UnlockPeek
    056: POP
    058: PUSHLOCALPAGE
    060: PUSH 0
    066: REFREF
    068: REF
    070: RETURN
    072: PUSH 0
    078: RETURN
    080: ENDFUNC f
    086: EOF test.jaf
    092: FUNC NULL
    098: EOF
    |}]

let%expect_test "ref struct reassign" =
  compile_test
    {|
      struct S {};
      void f(ref S a, ref S b) {
        a <- b;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: CALLSYS LockPeek
    012: POP
    014: PUSHLOCALPAGE
    016: PUSH 0
    022: DUP2
    024: REF
    026: DELETE
    028: DUP2
    030: PUSHLOCALPAGE
    032: PUSH 1
    038: ASSIGN
    040: DUP_X2
    042: POP
    044: REF
    046: SP_INC
    048: POP
    050: CALLSYS UnlockPeek
    056: POP
    058: RETURN
    060: ENDFUNC f
    066: EOF test.jaf
    072: FUNC NULL
    078: EOF
    |}]

let%expect_test "struct ref int assign" =
  compile_test
    {|
    struct S { ref int r; };
    S g_s;
    void f() {
      g_s.r = 42;
    }
  |};
  [%expect
    {|
    000: FUNC f
    006: PUSHGLOBALPAGE
    008: PUSH 0
    014: PUSH 0
    020: REFREF
    022: PUSH 42
    028: ASSIGN
    030: POP
    032: RETURN
    034: ENDFUNC f
    040: EOF test.jaf
    046: FUNC NULL
    052: EOF
    |}]

let%expect_test "syscall" =
  compile_test {|
      void f() { system.Exit(42); }
  |};
  [%expect
    {|
      000: FUNC f
      006: PUSH 42
      012: CALLSYS Exit
      018: RETURN
      020: ENDFUNC f
      026: EOF test.jaf
      032: FUNC NULL
      038: EOF
  |}]

let%expect_test "global array initializer" =
  compile_test {|
      array@int a[10];
      void f() {}
  |};
  [%expect
    {|
      000: FUNC f
      006: RETURN
      008: ENDFUNC f
      014: EOF test.jaf
      020: FUNC 0
      026: PUSHGLOBALPAGE
      028: PUSH 0
      034: PUSH 10
      040: PUSH 1
      046: A_ALLOC
      048: RETURN
      050: ENDFUNC 0
      056: FUNC NULL
      062: EOF
    |}]

let%expect_test "if" =
  compile_test
    {|
      void f() {
        int i = 1;
        if (i) {
          i = 2;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 1
      016: SH_LOCALREF i
      022: IFZ 44
      028: SH_LOCALASSIGN i, 2
      038: JUMP 44
      044: RETURN
      046: ENDFUNC f
      052: EOF test.jaf
      058: FUNC NULL
      064: EOF
    |}]

let%expect_test "if-else" =
  compile_test
    {|
      void f() {
        int i = 1;
        if (i) {
          i = 2;
        } else {
          i = 3;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 1
      016: SH_LOCALREF i
      022: IFZ 44
      028: SH_LOCALASSIGN i, 2
      038: JUMP 54
      044: SH_LOCALASSIGN i, 3
      054: RETURN
      056: ENDFUNC f
      062: EOF test.jaf
      068: FUNC NULL
      074: EOF
    |}]

let%expect_test "for-loop" =
  compile_test
    {|
      void f() {
        int i;
        for (i = 0; i < 10; i++) {
          continue;
          break;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 0
      016: SH_LOCALASSIGN i, 0
      026: SH_LOCALREF i
      032: PUSH 10
      038: LT
      040: IFZ 82
      046: JUMP 64
      052: SH_LOCALINC i
      058: JUMP 26
      064: JUMP 52
      070: JUMP 82
      076: JUMP 52
      082: RETURN
      084: ENDFUNC f
      090: EOF test.jaf
      096: FUNC NULL
      102: EOF
    |}]

let%expect_test "for-inconly" =
  compile_test
    {|
      void f() {
        int i;
        for (;; i++) {
          continue;
          break;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN i, 0
      016: JUMP 34
      022: SH_LOCALINC i
      028: JUMP 16
      034: JUMP 22
      040: JUMP 52
      046: JUMP 22
      052: RETURN
      054: ENDFUNC f
      060: EOF test.jaf
      066: FUNC NULL
      072: EOF
    |}]

let%expect_test "forever" =
  compile_test
    {|
      void f() {
        for (;;) {
          continue;
          break;
        }
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: JUMP 6
      012: JUMP 24
      018: JUMP 6
      024: RETURN
      026: ENDFUNC f
      032: EOF test.jaf
      038: FUNC NULL
      044: EOF
    |}]

let%expect_test "logical-not" =
  compile_test {|
      void f() {
        bool b;
        b = !b;
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALASSIGN b, 0
      016: PUSHLOCALPAGE
      018: PUSH 0
      024: SH_LOCALREF b
      030: NOT
      032: ITOB
      034: ASSIGN
      036: POP
      038: RETURN
      040: ENDFUNC f
      046: EOF test.jaf
      052: FUNC NULL
      058: EOF
    |}]

let%expect_test "self reference in initval" =
  compile_test {|
      void f() {
        string s = s = "a";
      }
  |};
  [%expect
    {|
      000: FUNC f
      006: SH_LOCALREF s
      012: SH_LOCALREF s
      018: S_PUSH "a"
      024: S_ASSIGN
      026: S_ASSIGN
      028: S_POP
      030: RETURN
      032: ENDFUNC f
      038: EOF test.jaf
      044: FUNC NULL
      050: EOF
    |}]

let%expect_test "functype with string initval" =
  compile_test
    {|
        functype void funcptr(void);
        void f() {
          funcptr fp = "f";
        }
    |};
  [%expect
    {|
      000: FUNC f
      006: PUSHLOCALPAGE
      008: PUSH 0
      014: S_PUSH "f"
      020: PUSH 0
      026: FT_ASSIGNS
      028: S_POP
      030: RETURN
      032: ENDFUNC f
      038: EOF test.jaf
      044: FUNC NULL
      050: EOF |}]

let%expect_test "local delete" =
  compile_test
    {|
        struct S {};
        void f() {
          for (;;) {
            ref int r;
            array@int a;
            S s;
          }
        }
    |};
  [%expect
    {|
    test.jaf:7:15-16: Unimplemented variable type: S for `s`
        7 |             S s;
                          ^
    |}]

let%expect_test "local delete with goto" =
  compile_test
    {|
      struct S {};
      void f() {
        S s1;
        for (;;) {
          S s2;
          goto skip;
        }
        skip:
      }
    |};
  [%expect
    {|
    test.jaf:4:11-13: Unimplemented variable type: S for `s1`
        4 |         S s1;
                      ^^
    |}]

let%expect_test "member pointer" =
  compile_test
    {|
      struct S {
        int a;
        int b;
      };
      void f(array@S as) {
        as.SortBy(&S::b);
      }
    |};
  [%expect {| (Failure "tried to create array<interface>") |}]


let%expect_test "dg_return_null" =
  compile_test
    {|
      delegate void dg();
      dg f() {
        return NULL;
      }
      unknown_delegate g() {
        return NULL;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: DG_NEW
    008: RETURN
    010: PUSH -1
    016: RETURN
    018: ENDFUNC f
    024: FUNC g
    030: DG_NEW
    032: RETURN
    034: PUSH -1
    040: RETURN
    042: ENDFUNC g
    048: EOF test.jaf
    054: FUNC NULL
    060: EOF
    |}]

let%expect_test "dg_set" =
  compile_test
    {|
      delegate void dg();
      void f() {
        dg d = &f;
      }
    |};
  [%expect
    {|
      000: FUNC f
      006: PUSHLOCALPAGE
      008: PUSH 0
      014: REF
      016: PUSH 1
      022: PUSH -1
      028: SWAP
      030: DG_SET
      032: RETURN
      034: ENDFUNC f
      040: EOF test.jaf
      046: FUNC NULL
      052: EOF
    |}]

let%expect_test "dg_copy" =
  compile_test
    {|
      delegate void dg();
      void f(dg d) {
        dg dd = d;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 1
    014: REF
    016: PUSHLOCALPAGE
    018: PUSH 0
    024: REF
    026: DG_COPY
    028: DG_ASSIGN
    030: DG_POP
    032: RETURN
    034: ENDFUNC f
    040: EOF test.jaf
    046: FUNC NULL
    052: EOF
    |}]

let%expect_test "dg_set_string" =
  compile_test
    {|
      delegate void dg();
      void f() {
        dg d = "f";
        d = "f";
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: REF
    016: S_PUSH "f"
    022: PUSH -1
    028: SWAP
    030: PUSH 0
    036: DG_STR_TO_METHOD
    038: DG_SET
    040: PUSHLOCALPAGE
    042: PUSH 0
    048: REF
    050: S_PUSH "f"
    056: PUSH -1
    062: SWAP
    064: PUSH 0
    070: DG_STR_TO_METHOD
    072: DG_SET
    074: RETURN
    076: ENDFUNC f
    082: EOF test.jaf
    088: FUNC NULL
    094: EOF
    |}]

let%expect_test "ref delegate string assign" =
  compile_test
    {|
      delegate void dg();
      void f(ref dg d) {
        d = "f";
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: SH_LOCALREF d
    012: S_PUSH "f"
    018: PUSH -1
    024: SWAP
    026: PUSH 0
    032: DG_STR_TO_METHOD
    034: DG_SET
    036: RETURN
    038: ENDFUNC f
    044: EOF test.jaf
    050: FUNC NULL
    056: EOF
    |}]

let%expect_test "dg_add_string" =
  compile_test
    {|
      delegate void dg();
      void f() {
        dg d;
        d += "f";
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: REF
    016: DG_CLEAR
    018: PUSHLOCALPAGE
    020: PUSH 0
    026: REF
    028: S_PUSH "f"
    034: PUSH -1
    040: SWAP
    042: PUSH 0
    048: DG_STR_TO_METHOD
    050: DG_ADD
    052: RETURN
    054: ENDFUNC f
    060: EOF test.jaf
    066: FUNC NULL
    072: EOF
    |}]

let%expect_test "dg_from_string" =
  compile_test
    {|
      delegate void dg();
      void f(dg d) {}
      void g() {
        f("g");
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: RETURN
    008: ENDFUNC f
    014: FUNC g
    020: S_PUSH "g"
    026: PUSH -1
    032: SWAP
    034: PUSH 0
    040: DG_STR_TO_METHOD
    042: DG_NEW_FROM_METHOD
    044: CALLFUNC f
    050: RETURN
    052: ENDFUNC g
    058: EOF test.jaf
    064: FUNC NULL
    070: EOF
    |}]

let%expect_test "dg_erase" =
  compile_test
    {|
      delegate void dg();
      void f() {
        dg d;
        d.Erase(&f);
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: REF
    016: DG_CLEAR
    018: PUSHLOCALPAGE
    020: PUSH 0
    026: REF
    028: PUSH 1
    034: PUSH -1
    040: SWAP
    042: DG_ERASE
    044: RETURN
    046: ENDFUNC f
    052: EOF test.jaf
    058: FUNC NULL
    064: EOF
    |}]

let%expect_test "dg_argument" =
  compile_test
    {|
      delegate void dg();
      class C {
        void f() {
          g(this.f);
        }
        void g(dg d) {
          g(d);
        }
      };
    |};
  [%expect
    {|
    000: FUNC C@f
    006: PUSHSTRUCTPAGE
    008: PUSHSTRUCTPAGE
    010: PUSH 1
    016: DG_NEW_FROM_METHOD
    018: CALLMETHOD C@g
    024: RETURN
    026: FUNC C@g
    032: PUSHSTRUCTPAGE
    034: PUSHLOCALPAGE
    036: PUSH 0
    042: REF
    044: DG_COPY
    046: CALLMETHOD C@g
    052: RETURN
    054: EOF test.jaf
    060: FUNC NULL
    066: EOF
    |}]

let%expect_test "HLL-implemented builtin methods" =
  compile_test ~ain_version:8
    ~hlls:
      [
        ("String.hll", "void foo(ref string self);");
        ("Int.hll", "void bar(ref int self);");
      ]
    {|
      void f(string s, int i) {
        s.foo();
        "a".foo();
        i.bar();
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: REF
    016: CALLHLL library(0), library_function(0)
    026: S_PUSH "a"
    032: CALLHLL library(0), library_function(0)
    042: PUSHLOCALPAGE
    044: PUSH 1
    050: CALLHLL library(1), library_function(0)
    060: RETURN
    062: ENDFUNC f
    068: EOF test.jaf
    074: FUNC NULL
    080: EOF
    |}]

let%expect_test "comma operator in reference context" =
  compile_test
    {|
      void g(ref int x) {}
      void f() {
        int i;
        ref int ri;
        g((i, ri));     // left operand evaluated and discarded, ri passed by reference
        ri <- (i, ri);  // same, in a reference assignment
      }
    |};
  [%expect
    {|
    000: FUNC g
    006: RETURN
    008: ENDFUNC g
    014: FUNC f
    020: SH_LOCALASSIGN i, 0
    030: CALLSYS LockPeek
    036: POP
    038: PUSHLOCALPAGE
    040: PUSH 1
    046: DUP2
    048: REF
    050: DELETE
    052: PUSH -1
    058: PUSH 0
    064: R_ASSIGN
    066: POP
    068: POP
    070: CALLSYS UnlockPeek
    076: POP
    078: SH_LOCALREF i
    084: POP
    086: PUSHLOCALPAGE
    088: PUSH 1
    094: REFREF
    096: CALLFUNC g
    102: CALLSYS LockPeek
    108: POP
    110: PUSHLOCALPAGE
    112: PUSH 1
    118: DUP2
    120: REF
    122: DELETE
    124: DUP2
    126: SH_LOCALREF i
    132: POP
    134: PUSHLOCALPAGE
    136: PUSH 1
    142: REFREF
    144: R_ASSIGN
    146: POP
    148: POP
    150: REF
    152: SP_INC
    154: CALLSYS UnlockPeek
    160: POP
    162: RETURN
    164: ENDFUNC f
    170: EOF test.jaf
    176: FUNC NULL
    182: EOF
    |}]

(* v11 omits the trailing JUMP-over-alt when there's no else branch.
   Pre-v11 always emits one (legacy layout). *)
let%expect_test "v11 if without else skips trailing JUMP" =
  compile_test ~ain_version:11
    {|
      void f() {
        int i = 1;
        if (i) {
          i = 2;
        }
      }
  |};
  [%expect {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: PUSH 1
    020: ASSIGN
    022: POP
    024: PUSHLOCALPAGE
    026: PUSH 0
    032: REF
    034: ITOB
    036: IFZ 60
    042: PUSHLOCALPAGE
    044: PUSH 0
    050: PUSH 2
    056: ASSIGN
    058: POP
    060: RETURN
    062: ENDFUNC f
    068: EOF test.jaf
    074: FUNC NULL
    080: EOF
    |}]

(* v11 ref-decl: 'ref array@T List = globalArray;' uses the original
   compiler's DUP2+REF+DELETE declaration pattern instead of the older
   generic RefAssign lowering. *)
let%expect_test "v11 ref array decl from global" =
  compile_test ~ain_version:11 {|
    array@int g_List;
    void f() {
      ref array@int List = g_List;
    }
  |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: DUP2
    016: REF
    018: DELETE
    020: PUSHGLOBALPAGE
    022: PUSH 0
    028: REF
    030: ASSIGN
    032: SP_INC
    034: RETURN
    036: ENDFUNC f
    042: EOF test.jaf
    048: FUNC NULL
    054: EOF
    |}]

(* v11 emits NOT, then normalizes through ITOB before assignment. *)
let%expect_test "v11 NOT assign emits ITOB" =
  compile_test ~ain_version:11
    {|
      class C {
        int m_flag;
        void Toggle() {
          this.m_flag = !this.m_flag;
        }
      };
    |};
  [%expect
    {|
    000: FUNC C@Toggle
    006: PUSHSTRUCTPAGE
    008: PUSH 0
    014: PUSHSTRUCTPAGE
    016: PUSH 0
    022: REF
    024: NOT
    026: ITOB
    028: ASSIGN
    030: POP
    032: RETURN
    034: EOF test.jaf
    040: FUNC NULL
    046: EOF
    |}]

(* v11 SR_ASSIGN drops its struct-type-id operand. Pre-v11 needs
   PUSH sno; SR_ASSIGN — leaving the PUSH in v11 leaves a stale int on
   the stack and shifts every following instruction. *)
let%expect_test "v11 struct copy-assign omits SR_ASSIGN's type operand" =
  compile_test ~ain_version:11
    {|
      class S { int x; };
      void f(S a, S b) {
        a = b;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: REF
    016: PUSHLOCALPAGE
    018: PUSH 1
    024: REF
    026: A_REF
    028: SR_ASSIGN
    030: DELETE
    032: RETURN
    034: ENDFUNC f
    040: EOF test.jaf
    046: FUNC NULL
    052: EOF
    |}]

(* v11 OBJSWAP carries its type-id as a direct operand instead of
   reading it off the stack. Pre-v11 was [PUSH type; OBJSWAP]; v11 is
   [OBJSWAP type]. Without this, two opcode worth of bytes downstream
   get swallowed as the operand and the disassembler misaligns. *)
let%expect_test "v11 OBJSWAP encodes type as direct operand" =
  compile_test ~ain_version:11
    {|
      void f(string a, string b) {
        a <=> b;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: PUSHLOCALPAGE
    016: PUSH 1
    022: OBJSWAP 12
    028: RETURN
    030: ENDFUNC f
    036: EOF test.jaf
    042: FUNC NULL
    048: EOF
    |}]

(* v12 user-bodied event invocation: when the accessor bodies reference
   the event's own backing field (so [<E>] is kept), [this.E(args)]
   fires the backing delegate via the DG_CALLBEGIN/DG_CALL loop, same
   as a plain delegate member call. Regression: this used to fall
   through to the UnresolvedCall placeholder path (callee value +
   PUSH 0), silently dropping the dispatch — Rance10's parts-layer
   mouse-wheel events (CPartsFunctionSet@CallFunctionMouseWheel) never
   fired. *)
let%expect_test "v12 user-bodied event invocation is a delegate call" =
  compile_test ~ain_version:12
    {|
      delegate void dg(int n);
      class C {
        event dg E;
        void CallE(int n);
      };
      event dg C::E {
        add { this.E += value; }
        remove { this.E -= value; }
      }
      void C::CallE(int n) { this.E(n); }
    |};
  [%expect
    {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC C@E::add
    036: PUSHSTRUCTPAGE
    038: PUSH 0
    044: REF
    046: PUSHLOCALPAGE
    048: PUSH 0
    054: REF
    056: DG_PLUSA
    058: POP
    060: RETURN
    062: FUNC C@E::remove
    068: PUSHSTRUCTPAGE
    070: PUSH 0
    076: REF
    078: PUSHLOCALPAGE
    080: PUSH 0
    086: REF
    088: DG_MINUSA
    090: POP
    092: RETURN
    094: FUNC C@CallE
    100: PUSHSTRUCTPAGE
    102: PUSH 0
    108: REF
    110: PUSHLOCALPAGE
    112: PUSH 0
    118: REF
    120: DG_CALLBEGIN delegate(0)
    126: DG_CALL delegate(0), 142
    136: JUMP 126
    142: RETURN
    144: EOF test.jaf
    150: FUNC NULL
    156: EOF
    |}]

(* [f(...).String()] — a plain function-call receiver of an
   HLL-implemented primitive method. The Int/Float HLL takes the
   receiver as a (page, index) pair, so the rvalue must spill into a
   [<dummy : 右辺値参照化用>] local first. Regression: [FunctionCall]
   receivers skipped the RvalueRef wrap and pushed the bare value —
   the VM popped the value as the index and whatever lay beneath as
   the page (Rance10 in-game-menu hard fault at 多田情報ログ確認's
   [Ｐ味方カード個別名有無("Lv42 ランス").String()]). *)
let%expect_test "v12 function-call receiver of Int.String spills to a dummy local" =
  compile_test ~ain_version:12
    ~hlls:[ ("Int.hll", "string String(ref int self);") ]
    {|
      int f() { return 42; }
      string test() { return f().String(); }
    |};
  [%expect {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC f
    036: PUSH 42
    042: RETURN
    044: PUSH 0
    050: RETURN
    052: ENDFUNC f
    058: FUNC test
    064: CALLFUNC f
    070: PUSHLOCALPAGE
    072: SWAP
    074: PUSH 0
    080: SWAP
    082: ASSIGN
    084: POP
    086: PUSHLOCALPAGE
    088: PUSH 0
    094: CALLHLL library(0), library_function(0), -1
    108: RETURN
    110: S_PUSH ""
    116: RETURN
    118: ENDFUNC test
    124: EOF test.jaf
    130: FUNC NULL
    136: EOF
    |}]

(* v12 [(v?.P = v?.P + n) ?? n] — the decompiled expansion of a
   compound assignment on an optional interface receiver. The receiver
   is null-checked ONCE; the getter runs on a DUP2 of the verified
   fat-ref pair inside the non-null branch. Regression: the inner
   [v?.P] used to compile through the generic optional-value protocol,
   leaving its status marker on the stack under the setter CALLMETHOD —
   the VM then read an int as a struct page id (Rance10 survey-scroll
   構造体ページ取得失敗 crash at enquate CEnqueteView@Scroll). *)
let%expect_test "v12 optional compound assignment fuses getter onto checked receiver" =
  compile_test ~ain_version:12
    {|
      interface I {
        int P::get();
        void P::set(int value);
      };
      class C implements I {
        int P { get; set; }
      };
      void f(I v, int n) {
        (v?.P = v?.P + n) ?? n;
      }
    |};
  [%expect
    {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC C@P::get
    036: PUSHSTRUCTPAGE
    038: PUSH 1
    044: REF
    046: RETURN
    048: PUSH 0
    054: RETURN
    056: FUNC C@P::get
    062: PUSHSTRUCTPAGE
    064: PUSH 1
    070: REF
    072: RETURN
    074: PUSH 0
    080: RETURN
    082: FUNC C@P::set
    088: PUSHSTRUCTPAGE
    090: PUSH 1
    096: PUSHLOCALPAGE
    098: PUSH 0
    104: REF
    106: ASSIGN
    108: POP
    110: RETURN
    112: ENDFUNC C@P::set
    118: FUNC f
    124: PUSHLOCALPAGE
    126: PUSH 0
    132: DUP2
    134: REF
    136: PUSH -1
    142: EQUALE
    144: IFNZ 164
    150: REFREF
    152: PUSH 0
    158: JUMP 186
    164: POP
    166: POP
    168: PUSH -1
    174: PUSH -1
    180: PUSH -1
    186: PUSH -1
    192: EQUALE
    194: IFNZ 284
    200: DUP2
    202: DUP_U2
    204: PUSH 0
    210: REF
    212: SWAP
    214: PUSH 1
    220: ADD
    222: REF
    224: DUP_X2
    226: POP
    228: SWAP
    230: DUP_U2
    232: PUSH 0
    238: REF
    240: SWAP
    242: PUSH 0
    248: ADD
    250: REF
    252: CALLMETHOD NULL
    258: PUSHLOCALPAGE
    260: PUSH 2
    266: REF
    268: ADD
    270: DUP_X2
    272: CALLMETHOD I@P::get
    278: JUMP 298
    284: POP
    286: POP
    288: PUSHLOCALPAGE
    290: PUSH 2
    296: REF
    298: POP
    300: RETURN
    302: ENDFUNC f
    308: EOF test.jaf
    314: FUNC C@0
    320: RETURN
    322: ENDFUNC C@0
    328: FUNC NULL
    334: EOF
    |}]

(* v12 [recv?.field ?? fallback] on a scalar class field defers the
   field READ past the ?? merge: the non-null branch pushes the
   (page, index) pair plus a status marker instead of reading in-branch,
   the fallback branch spills its value into a [右辺値参照化用] dummy and
   pushes the dummy's pair, and a single trailing REF performs the read.
   Regression: the read happened in-branch and null pushed a plain 0
   while ?? tests the marker against -1 — the fallback never applied
   (Rance10 [m_restoreInfo?.IsNeedRunEvent ?? true] evaluated false on
   fresh quests, silently skipping the intro event). *)
let%expect_test "v12 scalar optional field ?? defers the read past the merge" =
  compile_test ~ain_version:12
    {|
      class R {
      public:
        int f;
      };
      class C {
        ref R m_r;
        int test();
      };
      int C::test() { return this.m_r?.f ?? 7; }
    |};
  [%expect {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC C@test
    036: PUSHSTRUCTPAGE
    038: PUSH 0
    044: DUP2
    046: REF
    048: PUSH -1
    054: EQUALE
    056: IFNZ 126
    062: REF
    064: PUSH 0
    070: DUP_U2
    072: PUSH -1
    078: EQUALE
    080: IFNZ 98
    086: PUSH 0
    092: JUMP 120
    098: POP
    100: POP
    102: PUSH -1
    108: PUSH -1
    114: PUSH -1
    120: JUMP 148
    126: POP
    128: POP
    130: PUSH -1
    136: PUSH -1
    142: PUSH -1
    148: PUSH -1
    154: EQUALE
    156: IFZ 196
    162: POP
    164: POP
    166: PUSH 7
    172: PUSHLOCALPAGE
    174: SWAP
    176: PUSH 0
    182: SWAP
    184: ASSIGN
    186: POP
    188: PUSHLOCALPAGE
    190: PUSH 0
    196: REF
    198: RETURN
    200: PUSH 0
    206: RETURN
    208: EOF test.jaf
    214: FUNC NULL
    220: EOF
    |}]

(* v12 delegate builds for lambdas created INSIDE another lambda bind
   the executing frame's struct page (degrades to -1 at runtime when
   unbound); only top-level lambdas in plain functions bind -1.
   Regression: the "@" name heuristic missed our lambda names, so inner
   builds pushed -1 and the delegate fired on a NULL page from the
   engine pump (Rance10 RunMapQuest event factories). *)
let%expect_test "v12 nested lambda delegate binds the executing struct page" =
  compile_test ~ain_version:12
    {|
      delegate void dg();
      void test() {
        dg a = () => void {
          dg b = () => void {
          };
          b();
        };
        a();
      }
    |};
  [%expect {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC test
    036: JUMP 132
    042: FUNC <lambda : test()(4, 16)>
    048: JUMP 68
    054: FUNC <lambda : <lambda : test()(4, 16)>()(5, 18)>
    060: RETURN
    062: ENDFUNC <lambda : <lambda : test()(4, 16)>()(5, 18)>
    068: PUSHLOCALPAGE
    070: PUSH 0
    076: REF
    078: PUSHSTRUCTPAGE
    080: PUSH 3
    086: DG_NEW_FROM_METHOD
    088: DG_ASSIGN
    090: DELETE
    092: PUSHLOCALPAGE
    094: PUSH 0
    100: REF
    102: DG_CALLBEGIN delegate(0)
    108: DG_CALL delegate(0), 124
    118: JUMP 108
    124: RETURN
    126: ENDFUNC <lambda : test()(4, 16)>
    132: PUSHLOCALPAGE
    134: PUSH 0
    140: REF
    142: PUSH -1
    148: PUSH 2
    154: DG_NEW_FROM_METHOD
    156: DG_ASSIGN
    158: DELETE
    160: PUSHLOCALPAGE
    162: PUSH 0
    168: REF
    170: DG_CALLBEGIN delegate(0)
    176: DG_CALL delegate(0), 192
    186: JUMP 176
    192: RETURN
    194: ENDFUNC test
    200: EOF test.jaf
    206: FUNC NULL
    212: EOF
    |}]

(* v12 optional property assignment under ??, receiver is a call result
   (DummyRef). The original defers the SETTER past the marker merge with
   the non-null branch laid out first (IFNZ to the fallback), keeps the
   assigned value below the CALLMETHOD via DUP_X2 so the ?? expression
   yields it on both arms, and the statement POPs it. Regression: the
   null arm evaluated the fallback and RETURNed without popping —
   leaking one stack slot per call with a null receiver
   (SaveObjectView@ParentPartsNumber::postset; the save dialog's ASSIGN
   crash with garbage page/index). *)
let%expect_test "v12 optional setter ?? statement balances both arms" =
  compile_test ~ain_version:12
    {|
      class R {
      public:
        int P { get; set; }
      };
      class A2 {
      public:
        ref R GetR(string key);
      };
      class C {
        ref A2 m_act;
        int m_q;
        void test();
      };
      int R::P { get { return this.<P>; } set { this.<P> = value; } }
      ref R A2::GetR(string key) { return NULL; }
      void C::test()
      {
        (this.m_act?.GetR("").P = this.m_q) ?? this.m_q;
      }
    |};
  [%expect {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC R@P::get
    036: PUSHSTRUCTPAGE
    038: PUSH 0
    044: REF
    046: RETURN
    048: PUSH 0
    054: RETURN
    056: FUNC R@P::get
    062: PUSHSTRUCTPAGE
    064: PUSH 0
    070: REF
    072: RETURN
    074: PUSH 0
    080: RETURN
    082: FUNC R@P::set
    088: PUSHSTRUCTPAGE
    090: PUSH 0
    096: PUSHLOCALPAGE
    098: PUSH 0
    104: REF
    106: ASSIGN
    108: POP
    110: RETURN
    112: ENDFUNC R@P::set
    118: FUNC A2@GetR
    124: PUSH -1
    130: RETURN
    132: PUSH -1
    138: RETURN
    140: FUNC C@test
    146: PUSHSTRUCTPAGE
    148: PUSH 0
    154: DUP2
    156: REF
    158: PUSH -1
    164: EQUALE
    166: IFNZ 236
    172: REF
    174: PUSH 4
    180: S_PUSH ""
    186: CALLMETHOD R@P::get
    192: PUSHLOCALPAGE
    194: PUSH 0
    200: REF
    202: DELETE
    204: PUSHLOCALPAGE
    206: SWAP
    208: PUSH 0
    214: SWAP
    216: ASSIGN
    218: PUSH 0
    224: PUSH 0
    230: JUMP 258
    236: POP
    238: POP
    240: PUSH -1
    246: PUSH -1
    252: PUSH -1
    258: PUSH -1
    264: EQUALE
    266: IFNZ 304
    272: POP
    274: PUSH 3
    280: PUSHSTRUCTPAGE
    282: PUSH 1
    288: REF
    290: DUP_X2
    292: CALLMETHOD R@P::get
    298: JUMP 318
    304: POP
    306: POP
    308: PUSHSTRUCTPAGE
    310: PUSH 1
    316: REF
    318: POP
    320: PUSHLOCALPAGE
    322: PUSH 0
    328: DUP2
    330: REF
    332: DELETE
    334: PUSH -1
    340: ASSIGN
    342: POP
    344: RETURN
    346: EOF test.jaf
    352: FUNC NULL
    358: EOF
    |}]

(* v12 [obj?.M1().M2()] discarded statement, non-void tail: ONE receiver
   test guards the whole chain (links run in-branch, stored to their
   dummies, only the FINAL result is null-tested into the discard pair;
   the null arm bypasses everything). Regression: the inner optional
   call normalized NULL to -1 and ran .M2() on it — CALLMETHOD on a
   NULL page (SaveObjectView@SetSortedIndex p?.Motion().SetPos on the
   save dialog path). *)
let%expect_test "v12 discarded optional chain guards every link" =
  compile_test ~ain_version:12
    {|
      class PMT {
      public:
        ref PMT SetPos(int a, int b);
      };
      class P2 {
      public:
        ref PMT Motion();
      };
      class C {
        ref P2 m_p;
        void test();
      };
      ref PMT PMT::SetPos(int a, int b) { return NULL; }
      ref PMT P2::Motion() { return NULL; }
      void C::test()
      {
        this.m_p?.Motion().SetPos(1, 2);
      }
    |};
  [%expect {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC PMT@SetPos
    036: PUSH -1
    042: RETURN
    044: PUSH -1
    050: RETURN
    052: FUNC P2@Motion
    058: PUSH -1
    064: RETURN
    066: PUSH -1
    072: RETURN
    074: FUNC C@test
    080: PUSHSTRUCTPAGE
    082: PUSH 0
    088: DUP2
    090: REF
    092: PUSH -1
    098: EQUALE
    100: IFNZ 244
    106: REF
    108: PUSH 2
    114: CALLMETHOD NULL
    120: PUSHLOCALPAGE
    122: PUSH 0
    128: REF
    130: DELETE
    132: PUSHLOCALPAGE
    134: SWAP
    136: PUSH 0
    142: SWAP
    144: ASSIGN
    146: PUSH 1
    152: PUSH 1
    158: PUSH 2
    164: CALLMETHOD P2@Motion
    170: PUSHLOCALPAGE
    172: PUSH 1
    178: REF
    180: DELETE
    182: PUSHLOCALPAGE
    184: SWAP
    186: PUSH 1
    192: SWAP
    194: ASSIGN
    196: DUP
    198: PUSH -1
    204: EQUALE
    206: IFNZ 224
    212: PUSH 0
    218: JUMP 238
    224: POP
    226: PUSH -1
    232: PUSH -1
    238: JUMP 260
    244: POP
    246: POP
    248: PUSH -1
    254: PUSH -1
    260: POP
    262: POP
    264: PUSHLOCALPAGE
    266: PUSH 1
    272: DUP2
    274: REF
    276: DELETE
    278: PUSH -1
    284: ASSIGN
    286: POP
    288: PUSHLOCALPAGE
    290: PUSH 0
    296: DUP2
    298: REF
    300: DELETE
    302: PUSH -1
    308: ASSIGN
    310: POP
    312: RETURN
    314: EOF test.jaf
    320: FUNC NULL
    326: EOF
    |}]

(* The final call returning void leaves the chain root un-wrapped (no
   DummyRef for a void result), so this takes the [obj?.Prop.Method()]
   statement arm. Its 1-slot dummy store must use the SWAP dance — the
   2-slot [DUP_X2; POP] rotation reaches below the statement's stack
   and turns the ASSIGN into a wild write (save-dialog 【 ASSIGN 】
   Page:1 crash, SaveObjectView@SetZ/SetIndex/SetShowNewFlat/SetPos) —
   and the dummy's LOCALDELETE follows the statement POP. *)
let%expect_test "v12 void-final optional chain stores its dummy 1-slot" =
  compile_test ~ain_version:12
    {|
      class PMT {
      public:
        void SetNum(int a);
      };
      class P2 {
      public:
        ref PMT GetParts(int k);
      };
      class C {
        ref P2 m_p;
        void test();
      };
      void PMT::SetNum(int a) {}
      ref PMT P2::GetParts(int k) { return NULL; }
      void C::test()
      {
        this.m_p?.GetParts(0).SetNum(3);
      }
    |};
  [%expect {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC PMT@SetNum
    036: RETURN
    038: FUNC P2@GetParts
    044: PUSH -1
    050: RETURN
    052: PUSH -1
    058: RETURN
    060: FUNC C@test
    066: PUSHSTRUCTPAGE
    068: PUSH 0
    074: DUP2
    076: REF
    078: PUSH -1
    084: EQUALE
    086: IFNZ 168
    092: REF
    094: PUSH 2
    100: PUSH 0
    106: CALLMETHOD PMT@SetNum
    112: PUSHLOCALPAGE
    114: PUSH 0
    120: REF
    122: DELETE
    124: PUSHLOCALPAGE
    126: SWAP
    128: PUSH 0
    134: SWAP
    136: ASSIGN
    138: PUSH 1
    144: PUSH 3
    150: CALLMETHOD PMT@SetNum
    156: PUSH 0
    162: JUMP 178
    168: POP
    170: POP
    172: PUSH -1
    178: POP
    180: PUSHLOCALPAGE
    182: PUSH 0
    188: DUP2
    190: REF
    192: DELETE
    194: PUSH -1
    200: ASSIGN
    202: POP
    204: RETURN
    206: EOF test.jaf
    212: FUNC NULL
    218: EOF
    |}]

(* When the condition allocates dummies, the false path must jump TO the
   else block and the then branch must replay the condition deletes and
   jump OVER it. The old layout jumped the false path past the else and
   let the then branch fall through into it: with a non-empty else, true
   ran BOTH branches and false ran NEITHER (SceneQuestMap@ProcessNext's
   else is CreateSelection(), so quest-map route choices never appeared). *)
let%expect_test "v12 if/else with condition dummies routes both branches" =
  compile_test ~ain_version:12
    {|
      class R {
      public:
        int P { get; set; }
      };
      class C {
        ref R GetR();
        void a();
        void b();
        void test();
      };
      ref R C::GetR() { return NULL; }
      void C::a() {}
      void C::b() {}
      void C::test()
      {
        if (this.GetR().P == 1) {
          this.a();
        } else {
          this.b();
        }
      }
    |};
  [%expect {|
    000: EOF 0
    006: EOF 1
    012: EOF 2
    018: EOF 3
    024: EOF 4
    030: FUNC R@P::get
    036: PUSHSTRUCTPAGE
    038: PUSH 0
    044: REF
    046: RETURN
    048: PUSH 0
    054: RETURN
    056: FUNC R@P::get
    062: PUSHSTRUCTPAGE
    064: PUSH 0
    070: REF
    072: RETURN
    074: PUSH 0
    080: RETURN
    082: FUNC R@P::set
    088: PUSHSTRUCTPAGE
    090: PUSH 0
    096: PUSHLOCALPAGE
    098: PUSH 0
    104: REF
    106: ASSIGN
    108: POP
    110: RETURN
    112: ENDFUNC R@P::set
    118: FUNC C@GetR
    124: PUSH -1
    130: RETURN
    132: PUSH -1
    138: RETURN
    140: FUNC C@a
    146: RETURN
    148: FUNC C@b
    154: RETURN
    156: FUNC C@test
    162: PUSHSTRUCTPAGE
    164: PUSH 1
    170: CALLMETHOD NULL
    176: PUSHLOCALPAGE
    178: PUSH 0
    184: REF
    186: DELETE
    188: PUSHLOCALPAGE
    190: SWAP
    192: PUSH 0
    198: SWAP
    200: ASSIGN
    202: PUSH 5
    208: CALLMETHOD NULL
    214: PUSH 1
    220: EQUALE
    222: PUSHLOCALPAGE
    224: PUSH 0
    230: DUP2
    232: REF
    234: DELETE
    236: PUSH -1
    242: ASSIGN
    244: POP
    246: IFNZ 282
    252: PUSHLOCALPAGE
    254: PUSH 0
    260: DUP2
    262: REF
    264: DELETE
    266: PUSH -1
    272: ASSIGN
    274: POP
    276: JUMP 326
    282: PUSHSTRUCTPAGE
    284: PUSH 2
    290: CALLMETHOD NULL
    296: PUSHLOCALPAGE
    298: PUSH 0
    304: DUP2
    306: REF
    308: DELETE
    310: PUSH -1
    316: ASSIGN
    318: POP
    320: JUMP 340
    326: PUSHSTRUCTPAGE
    328: PUSH 3
    334: CALLMETHOD NULL
    340: RETURN
    342: EOF test.jaf
    348: FUNC NULL
    354: EOF
    |}]

(* v11 reads strings via REF; A_REF instead of the pre-v11 S_REF — the
   pre-v11 form doesn't incref and the VM panics freeing the returned
   string. *)
let%expect_test "v11 string local deref uses REF + A_REF" =
  compile_test ~ain_version:11
    {|
      void f() {
        string s;
        string t = s;
      }
    |};
  [%expect
    {|
    000: FUNC f
    006: PUSHLOCALPAGE
    008: PUSH 0
    014: REF
    016: S_PUSH ""
    022: S_ASSIGN
    024: DELETE
    026: PUSHLOCALPAGE
    028: PUSH 1
    034: REF
    036: PUSHLOCALPAGE
    038: PUSH 0
    044: REF
    046: A_REF
    048: S_ASSIGN
    050: DELETE
    052: RETURN
    054: ENDFUNC f
    060: EOF test.jaf
    066: FUNC NULL
    072: EOF
    |}]

