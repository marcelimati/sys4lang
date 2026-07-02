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
  with CompileError.Compile_error e ->
    CompileError.print_error e (fun _ -> Some input)

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
  [%expect.unreachable]
[@@expect.uncaught_exn {|
  (* CR expect_test_collector: This test expectation appears to contain a backtrace.
     This is strongly discouraged as backtraces are fragile.
     Please change this test to not include a backtrace. *)
  (Failure "tried to create array<interface>")
  Raised at Stdlib.failwith in file "stdlib.ml", line 29, characters 17-33
  Called from Compiler__Codegen.jaf_compiler#compile_function.(fun) in file "lib/compiler/codegen.ml", line 7636, characters 29-60
  Called from Base__List0.iter in file "src/list0.ml", line 66, characters 4-7
  Called from Compiler__Codegen.jaf_compiler#compile_function in file "lib/compiler/codegen.ml", lines 7635-7636, characters 6-61
  Called from Base__List0.iter in file "src/list0.ml", line 66, characters 4-7
  Called from Compiler__Codegen.jaf_compiler#compile in file "lib/compiler/codegen.ml", line 8429, characters 6-37
  Called from Base__List0.iter in file "src/list0.ml", line 66, characters 4-7
  Called from Compiler__Compile.compile in file "lib/compiler/compile.ml", line 463, characters 2-37
  Called from Compiler_test__CompileTest.compile_test in file "lib/compiler/test/compileTest.ml", lines 76-78, characters 4-39
  Called from Compiler_test__CompileTest.(fun) in file "lib/compiler/test/compileTest.ml", lines 899-908, characters 2-6
  Called from Ppx_expect_runtime__Test_block.Configured.dump_backtrace in file "runtime/test_block.ml", line 142, characters 10-28
  |}]

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

