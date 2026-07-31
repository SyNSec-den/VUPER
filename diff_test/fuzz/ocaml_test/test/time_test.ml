
(** val a1 : BigArrayExtr.byte_buf **)
open Formats
open Bigarray
(* open Unix *)

(*let stdin_to_buffer () =
  let buf = Buffer.create 4096 in
  (try
    while true do
      Buffer.add_channel buf stdin 4096
    done
  with End_of_file -> ());
  Buffer.contents buf

let buffer_to_bigarray buf =
  (*  let str = Buffer.contents buffer in *)
  let ba = BigArrayExtr.make (String.length buf) '\x00' in
  for i = 0 to String.length buf - 1 do
    Array1.set ba.buffer i buf.[i]
  done;
  ba *)
  
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

(*let write_file msg filename =
  let oc = open_out filename in
  Printf.fprintf oc "%s" msg;
  close_out oc  *)


let pos1 = { FormatTest.byte_pos = 0 ; FormatTest.byte_off = I0 ; }

(** 0000 0100 1000  **)

(** 
    Here, we are testing the type of 
    (int <=10, bool option, bool, int (dft=1) <=10)
 **)
(*type a_type = FormatTest.bCCH_BCH_Message__type *)

let f bf : unit =
  ignore ((Formats.FormatTest.dL_DCCH_MessageType__Format.t_Parse) bf pos1)

      

let process_file filename =
  let ba = bigarray_of_file filename in

  (* OCaml Example using Mtime *)
  let start = Mtime_clock.elapsed_ns () in
  ignore (f ba);  (* Call parser *)
  
  let span = Int64.sub (Mtime_clock.elapsed_ns ()) start in
  span

let process_all_files_in_dir dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.fold_left
    (fun s file ->
       Int64.add s (let full_path = Filename.concat dir file in
            if Sys.is_directory full_path then
              0L
            else 
              (process_file full_path)))
    0L

(*Printf.printf "Caught with %s\n" msg) *)


(* Now I need to run the C code, as well as the python script
   (that santize the output).  
let run_program binary input_data =
  (* Open process with both input and output channels *)
  let (ic, oc) = Unix.open_process binary in
  (* Send input to the binary *)
  output_string oc input_data;
  flush oc;
  close_out oc;  (* Close stdin to signal EOF *)
  (* Read the output *)
  let rec read_output acc =
    try
      let line = input_line ic in
      read_output (acc ^ "\n" ^ line)
    with End_of_file -> acc
  in
  let output = read_output "" in
  (* Close the input channel *)
  ignore (Unix.close_process (ic, oc));
  output
 *)

(* Problem: stdin is too large? *)

let () =
  let time_total_ns = process_all_files_in_dir "/home/zhouxt/Documents/parse/ASN1Parser/test_messages/rrc_msg/exported_rrc_messages/DL-DCCH/" in
  let time_total_sec = (Int64.to_float time_total_ns) /. 1_000_000_000.0 in
  Printf.printf "Total Time for executing the file is %f\n" time_total_sec
