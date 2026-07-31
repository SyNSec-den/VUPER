(** val a1 : BigArrayExtr.byte_buf **)
open Formats
open Bigarray
(* open Unix *)

(*let bf1 =
  BigArrayExtr.make 10 '\x00' *)

(** val a3 : (int * ByteParser.B.coq_Pos) option **)

(*let () =
  Array1.set bf1.buffer 0 '\x01';
  Array1.set bf1.buffer 1 '\x05';
  Array1.set bf1.buffer 2 '\xc0';
  Array1.set bf1.buffer 3 '\x40';
  Array1.set bf1.buffer 4 '\x00';
  Array1.set bf1.buffer 5 '\x60';
  Array1.set bf1.buffer 6 '\x00';
  Array1.set bf1.buffer 7 '\x60';
  Array1.set bf1.buffer 8 '\x00';
  Array1.set bf1.buffer 9 '\x00'
  (** val a4 : unit **) *)

let stdin_to_buffer () =
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
  ba
  
(*let bigarray_of_file filename =
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
 *)

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

let f bf : string option  =
  let a0 = (Formats.FormatTest.uL_DCCH_MessageType__Format.t_Parse) bf pos1 in
  match a0 with
  | Some ((Exist a, _), _) -> 
    (*(Printf.sprintf "%d\n" (FormatTest.BA.to_nat p))
      ^ (DebugPrint.sprint_flg fg) *)
   (* Printf.printf "good"; *)
    Some (let j = FormatJson.uL_DCCH_MessageType__Type_to_jer a in 
          Yojson.Safe.to_string j) 
  (* "\nSucc in Decoding %d\n" *)

  | None -> None


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
  let bf = stdin_to_buffer () (*bigarray_of_file "../../message/test.bin" *) in
  (* First run the OCaml code *)
  let ba = buffer_to_bigarray bf in

  match f ba with
  | Some s ->
    (*write_file s "../../message/vp.json" *)
    Printf.printf "%s" s
  | None ->
    Printf.printf "\"Error\""


