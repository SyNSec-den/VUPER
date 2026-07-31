open Formats
open Bigarray

(* Counters *)
let total = ref 0
let reject = ref 0
let samever = ref 0
let diffver = ref 0

(* Separate counters for 2025-01 files and for other files *)
let total_2025 = ref 0
let reject_2025 = ref 0
let samever_2025 = ref 0
let diffver_2025 = ref 0

let total_other = ref 0
let reject_other = ref 0
let samever_other = ref 0
let diffver_other = ref 0

let bigarray_of_file filename =
  let ic = open_in_bin filename in
  let len = in_channel_length ic in
  let ba = BigArrayExtr.make len '\x00' in
  let buffer = Bytes.create len in
  really_input ic buffer 0 len;
  close_in ic;
  for i = 0 to len - 1 do
    Array1.set ba.buffer i (Bytes.get buffer i)
  done;
  ba

let pos1 = { FormatTest.byte_pos = 0 ; FormatTest.byte_off = I0 ; }

let f bf =
  let a0 = (Formats.FormatTest.dL_DCCH_MessageType__Format.t_Parse) bf pos1 in
  match a0 with
  | Some (_v, flg) ->
      (* match the flag to DiffVer / SameVer; return a string flag *)
      (match flg with
       | FormatTest.DiffVer -> Some "DiffVer"
       | FormatTest.SameVer -> Some "SameVer"
       )
  | None -> None

let process_file filename =
  try
    let ba = bigarray_of_file filename in
    (* decide group by basename starting with "2025-01" *)
    let base = Filename.basename filename in
    let starts_with prefix s =
      let plen = String.length prefix in
      String.length s >= plen && String.sub s 0 plen = prefix
    in
    let is_2025 = starts_with "2025-01" base in
    if is_2025 then incr total_2025 else incr total_other;
    incr total;
    (match f ba with
   | Some "DiffVer" ->
     incr diffver;
     if is_2025 then incr diffver_2025 else incr diffver_other
   | Some "SameVer" ->
     incr samever;
     if is_2025 then incr samever_2025 else incr samever_other
   | Some _ ->
     (* parsed but flag not DiffVer/SameVer; count as accepted but not in the two accept buckets *)
     ()
   | None ->
     incr reject;
     if is_2025 then (incr reject_2025; Printf.printf "%s\n" filename)
     else (incr reject_other; Printf.printf "%s\n" filename))
  with _ ->
    (* on error count as reject in the appropriate bucket *)
    let base = Filename.basename filename in
    let starts_with prefix s =
      let plen = String.length prefix in
      String.length s >= plen && String.sub s 0 plen = prefix
    in
    let is_2025 = starts_with "2025-01" base in
    if is_2025 then incr reject_2025 else incr reject_other;
    incr reject; Printf.printf "%s\n" filename

let process_all_files_in_dir dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.iter
    (fun file ->
       let full_path = Filename.concat dir file in
       if not (Sys.is_directory full_path) then
         process_file full_path)

let () =
  process_all_files_in_dir "/home/zhouxt/Documents/parse/ASN1Parser/test_messages/rrc_msg/exported_rrc_messages/DL-DCCH/"
  ;
  Printf.printf "\nSummary:\n" ;
  (* Table for 2025-01 files *)
  Printf.printf "\n2025-01 files:\n" ;
  Printf.printf "%20s: %d\n" "Total" !total_2025 ;
  Printf.printf "%20s: %d\n" "Rejected" !reject_2025 ;
  Printf.printf "%20s: %d\n" "Accepted (SameVer)" !samever_2025 ;
  Printf.printf "%20s: %d\n" "Accepted (DiffVer)" !diffver_2025 ;

  (* Table for other files *)
  Printf.printf "\nOther files:\n" ;
  Printf.printf "%20s: %d\n" "Total" !total_other ;
  Printf.printf "%20s: %d\n" "Rejected" !reject_other ;
  Printf.printf "%20s: %d\n" "Accepted (SameVer)" !samever_other ;
  Printf.printf "%20s: %d\n" "Accepted (DiffVer)" !diffver_other ;

  (* Overall totals *)
  Printf.printf "\nOverall totals:\n" ;
  Printf.printf "%20s: %d\n" "Total" !total ;
  Printf.printf "%20s: %d\n" "Rejected" !reject ;
  Printf.printf "%20s: %d\n" "Accepted (SameVer)" !samever ;
  Printf.printf "%20s: %d\n" "Accepted (DiffVer)" !diffver