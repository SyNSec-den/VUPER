(** val a1 : BigArrayExtr.byte_buf **)
open Formats
open Bigarray


let bf1 =
  BigArrayExtr.make 10 '\x00'

(** val a3 : (int * ByteParser.B.coq_Pos) option **)

let () =
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
(** val a4 : unit **)

let read_stdin_to_bigarray () =
  let buffer = Buffer.create 4096 in
  (try
     while true do
       Buffer.add_char buffer (input_char stdin)
     done
   with End_of_file -> ());
  let str = Buffer.contents buffer in
  let ba = BigArrayExtr.make (String.length str) '\x00' in
  for i = 0 to String.length str - 1 do
    Array1.set ba.buffer i str.[i]
  done;
  ba

(*

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

let f bf : string  =
  let a0 = (Formats.FormatTest.cAM__Format.t_Parse) bf pos1 in
  match a0 with
  | Some ((Exist a, _), _) -> 
    let j = FormatJson.cAM__Type_to_jer a in
    Yojson.Safe.to_string j
  | None -> "Error"

let () =
  let ba =  read_stdin_to_bigarray () in 
            (* bigarray_of_file "../../message/test.bin" in  *)
              (*Printf.printf "Read %d bytes from stdin\n" (ba.buf_len);*) 
    (*write_file s "../../message/vp.json" *)
  Printf.printf "%s" (f ba)



(*
open Formats.FormatTest

let print_bigarray_char_hex (ba : BigArrayExtr.byte_buf) =
  let len = ba.buf_len in 
  for i = 0 to len - 1 do
    Printf.printf "%02X " (Char.code (Bigarray.Array1.get ba.buffer i))
  done;
  print_newline ()



(*Printf.printf "%s" (f bf1) *)

(*  match (Formats.FormatTest.unit_format.t_to_len ()) with
    | Some p -> Printf.printf "%d" p
  | None -> Printf.printf "Nothing" *)
             (*  *)

(* Here, I would encode the input message and then print the encoding  *)
let () =
  let ba = BigArrayExtr.make 100 '\x00' in
  let ba' = (Formats.FormatTest.dL_DCCH_MessageType__Format.t_Serial) ba pos1 input_msg in
  match ba' with
  | Some ((bf', _), _) ->
     print_bigarray_char_hex bf';
     Printf.printf "%s" (f bf');
     
  | None ->
     Printf.printf "Fail to encode"
*)
