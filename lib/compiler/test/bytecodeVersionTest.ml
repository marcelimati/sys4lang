open Base
open Common
open Compiler

let string_of_argtype = function
  | Bytecode.Int -> "Int"
  | Float -> "Float"
  | Address -> "Address"
  | Function -> "Function"
  | String -> "String"
  | Message -> "Message"
  | Local -> "Local"
  | Global -> "Global"
  | Struct -> "Struct"
  | Syscall -> "Syscall"
  | Library -> "Library"
  | LibraryFunction -> "LibraryFunction"
  | File -> "File"
  | Delegate -> "Delegate"
  | Switch -> "Switch"

let print_argtypes version opcode =
  let ain = Ain.create version 0 in
  let buf = CBuffer.create 32 in
  CBuffer.write_int16 buf (Bytecode.int_of_opcode opcode);
  List.iter (Bytecode.args_of_opcode ~version opcode) ~f:(fun _ ->
      CBuffer.write_int32 buf 0);
  Ain.append_bytecode ain buf;
  let dasm = Dasm.create ain in
  Dasm.argument_types dasm
  |> List.map ~f:string_of_argtype
  |> String.concat ~sep:", "
  |> Stdio.print_endline

let%expect_test "versioned bytecode operands for v8 and v11" =
  List.iter
    [
      Bytecode.CALLHLL;
      NEW;
      S_MOD;
      OBJSWAP;
      DG_STR_TO_METHOD;
    ]
    ~f:(fun opcode ->
      Stdio.printf "%s\n" (Bytecode.string_of_opcode opcode);
      Stdio.printf "v8: %s\n"
        (String.concat ~sep:", "
           (List.map (Bytecode.args_of_opcode opcode) ~f:string_of_argtype));
      Stdio.printf "v11: ";
      print_argtypes 11 opcode);
  [%expect
    {|
    CALLHLL
    v8: Library, LibraryFunction
    v11: Library, LibraryFunction, Int
    NEW
    v8:
    v11: Struct, Function
    S_MOD
    v8:
    v11: Int
    OBJSWAP
    v8:
    v11: Int
    DG_STR_TO_METHOD
    v8:
    v11: Delegate
    |}]
