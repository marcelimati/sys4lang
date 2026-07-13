(* Compare delegate-typed variable/member records between two ains.
   Reports, per matched function (by name), variables whose type contains
   Delegate i where the i differs (esp. -1 vs real index). Also scans
   struct members and delegate table sizes.

   Usage: scan_dgvars ORIG.ain OURS.ain *)
open Base
open Common
open Stdio

let rec dg_index (t : Ain.Type.t) =
  match t with
  | Delegate i -> Some i
  | Array t | Ref t | Wrap t | Option t | Unknown87 t -> dg_index t
  | _ -> None

let () =
  let orig = Ain.load (Sys.get_argv ()).(1) in
  let ours = Ain.load (Sys.get_argv ()).(2) in
  let ours_fns = Hashtbl.create (module String) in
  for i = 0 to Ain.nr_functions ours - 1 do
    let f = Ain.get_function_by_index ours i in
    Hashtbl.set ours_fns ~key:f.name ~data:f
  done;
  let total = ref 0 in
  let mismatch = ref 0 in
  let shown = ref 0 in
  for i = 0 to Ain.nr_functions orig - 1 do
    let fo = Ain.get_function_by_index orig i in
    match Hashtbl.find ours_fns fo.name with
    | None -> ()
    | Some fc ->
        let vo = Array.of_list fo.vars and vc = Array.of_list fc.vars in
        let n = min (Array.length vo) (Array.length vc) in
        for k = 0 to n - 1 do
          match (dg_index vo.(k).value_type, dg_index vc.(k).value_type) with
          | Some a, Some b ->
              Int.incr total;
              if a <> b then begin
                Int.incr mismatch;
                if !mismatch <= 20 then begin
                  Int.incr shown;
                  printf "VAR %s [%d] %s: orig dg=%d ours dg=%d\n" fo.name k
                    vo.(k).name a b
                end
              end
          | Some a, None ->
              Int.incr total;
              Int.incr mismatch;
              if !mismatch <= 20 then
                printf "VAR %s [%d] %s: orig dg=%d ours NOT-DG (%s)\n" fo.name k
                  vo.(k).name a
                  (Ain.Type.to_string vc.(k).value_type)
          | None, Some b ->
              Int.incr total;
              Int.incr mismatch;
              if !mismatch <= 20 then
                printf "VAR %s [%d] %s: orig NOT-DG (%s) ours dg=%d\n" fo.name k
                  vo.(k).name
                  (Ain.Type.to_string vo.(k).value_type)
                  b
          | None, None -> ()
        done
  done;
  printf "function vars: %d delegate-typed compared, %d mismatched\n" !total
    !mismatch;
  (* struct members *)
  let ours_structs = Hashtbl.create (module String) in
  for i = 0 to Ain.nr_structs ours - 1 do
    let s = Ain.get_struct_by_index ours i in
    Hashtbl.set ours_structs ~key:s.name ~data:s
  done;
  let mtotal = ref 0 and mmis = ref 0 in
  for i = 0 to Ain.nr_structs orig - 1 do
    let so = Ain.get_struct_by_index orig i in
    match Hashtbl.find ours_structs so.name with
    | None -> ()
    | Some sc ->
        let mo = Array.of_list so.members and mc = Array.of_list sc.members in
        let n = min (Array.length mo) (Array.length mc) in
        for k = 0 to n - 1 do
          match (dg_index mo.(k).value_type, dg_index mc.(k).value_type) with
          | Some a, Some b ->
              Int.incr mtotal;
              if a <> b then begin
                Int.incr mmis;
                if !mmis <= 20 then
                  printf "MEMBER %s.%s: orig dg=%d ours dg=%d\n" so.name
                    mo.(k).name a b
              end
          | Some _, None | None, Some _ ->
              Int.incr mtotal;
              Int.incr mmis;
              if !mmis <= 20 then
                printf "MEMBER %s.%s: type-shape mismatch (%s vs %s)\n" so.name
                  mo.(k).name
                  (Ain.Type.to_string mo.(k).value_type)
                  (Ain.Type.to_string mc.(k).value_type)
          | None, None -> ()
        done
  done;
  printf "struct members: %d delegate-typed compared, %d mismatched\n" !mtotal
    !mmis
