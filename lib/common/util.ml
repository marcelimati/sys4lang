open Base

(* Find the index of the last `::` separator at angle-bracket depth 0
   so v12 templated names like `Class::Method<Ns::Type>` split at
   `Class::Method`, not at the `::` inside the template args. *)
let last_toplevel_double_colon (name : string) =
  let n = String.length name in
  let depth = ref 0 in
  let result = ref None in
  let i = ref 0 in
  while !i < n do
    let c = name.[!i] in
    (if Char.equal c '<' then Int.incr depth
     else if Char.equal c '>' then depth := !depth - 1
     else if !depth = 0
             && Char.equal c ':'
             && !i + 1 < n
             && Char.equal name.[!i + 1] ':'
     then (
       result := Some !i;
       Int.incr i));
    Int.incr i
  done;
  !result

let parse_qualified_name name =
  match last_toplevel_double_colon name with
  | Some i ->
      let left = String.sub name ~pos:0 ~len:i in
      let right =
        String.sub name ~pos:(i + 2) ~len:(String.length name - i - 2)
      in
      (Some left, right)
  | None -> (None, name)
