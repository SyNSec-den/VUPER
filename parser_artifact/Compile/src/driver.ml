open ASN1Format

let read_string (s : string) : asn1_obj =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let read_file filename = 
  let inf = open_in filename in
  let lexbuf = Lexing.from_channel inf in
  let ast = Parser.prog Lexer.read lexbuf in
  close_in inf;
  ast

let write_file msg filename =
  let oc = open_out filename in
  Printf.fprintf oc "%s" msg;
  close_out oc

(* let asn1_compile input_file output_file =
  let ast = read_file input_file in
  let code = Compiler.gen_asn1_list_def ast in
  write_file code output_file *)
