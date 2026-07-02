(* Lexer-side symbol table for v12 templated identifier disambiguation.
   When the parser sees `IDENT <`, that's normally a comparison expression.
   For v12 we also need to parse `Foo<X, Y>` as a templated type name.
   To keep the lexer hazard-free (see feedback memory: a lexer-level
   `<ident>` consumer would silently break `if (a<b>0)`), the lexer
   instead asks this table: is this IDENT a known templated type? If
   yes, emit a distinct TEMPLATE_IDENTIFIER token so the grammar can
   commit to parsing template args without conflicting with comparison. *)

open Base

let templated : (string, unit) Hashtbl.t = Hashtbl.create (module String)

let is_templated s = Hashtbl.mem templated s
let add_templated s = Hashtbl.set templated ~key:s ~data:()
let clear () = Hashtbl.clear templated

(* Pre-scan a source string to register any identifier immediately followed
   by `<` (no whitespace between) as templated. The decompiler emits
   comparisons with spaces (`a < b`) and template instantiations without
   (`Foo<X, Y>`), so the no-whitespace gate distinguishes them reliably.
   Skips string literals and comments to avoid false positives from
   message text. *)
let scan_source (source : string) =
  let len = String.length source in
  let is_ident_start c =
    Char.is_alpha c || Char.equal c '_'
  in
  let is_ident_continue c =
    Char.is_alphanum c || Char.equal c '_'
  in
  let pos = ref 0 in
  while !pos < len do
    let c = source.[!pos] in
    match c with
    | '/' when !pos + 1 < len && Char.equal source.[!pos + 1] '/' ->
        (* line comment *)
        while !pos < len && not (Char.equal source.[!pos] '\n') do
          Int.incr pos
        done
    | '/' when !pos + 1 < len && Char.equal source.[!pos + 1] '*' ->
        (* block comment *)
        pos := !pos + 2;
        let closed = ref false in
        while (not !closed) && !pos + 1 < len do
          if Char.equal source.[!pos] '*' && Char.equal source.[!pos + 1] '/' then begin
            pos := !pos + 2;
            closed := true
          end else Int.incr pos
        done
    | '"' ->
        (* string literal — skip to closing quote, honoring backslash escapes *)
        Int.incr pos;
        while !pos < len && not (Char.equal source.[!pos] '"') do
          if Char.equal source.[!pos] '\\' && !pos + 1 < len then pos := !pos + 2
          else Int.incr pos
        done;
        if !pos < len then Int.incr pos
    | '\'' ->
        (* message literal — skip similarly *)
        Int.incr pos;
        while !pos < len && not (Char.equal source.[!pos] '\'') do
          if Char.equal source.[!pos] '\\' && !pos + 1 < len then pos := !pos + 2
          else Int.incr pos
        done;
        if !pos < len then Int.incr pos
    | _ when is_ident_start c ->
        let start = !pos in
        Int.incr pos;
        while !pos < len && is_ident_continue source.[!pos] do
          Int.incr pos
        done;
        if !pos < len && Char.equal source.[!pos] '<' then begin
          let name = String.sub source ~pos:start ~len:(!pos - start) in
          add_templated name
        end
    | _ -> Int.incr pos
  done
