open Common
open Compiler

let hll_type_test ?(ain_version = 11) hll_input =
  let ctx = Jaf.context_from_ain (Ain.create ain_version 0) in
  let debug_info = DebugInfo.create () in
  try
    Compile.compile ctx [ Pje.Hll ("system.hll", "system"); Pje.Jaf "test.jaf" ]
      debug_info (function
        | "system.hll" -> hll_input
        | _ -> "");
    Stdio.print_endline "ok"
  with CompileError.Compile_error e ->
    CompileError.print_error e (function
      | "system.hll" -> Some hll_input
      | _ -> Some "")

let%expect_test "v11 hll ref array parameter syntax" =
  hll_type_test
    {| bool ResumeWriteComment(string szKeyName, string szFileName, ref array aszComment); |};
  [%expect {| ok |}]
