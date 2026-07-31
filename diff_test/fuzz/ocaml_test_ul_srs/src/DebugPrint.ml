
let print_opt p c =
  match c with
    Some c0 -> p c0
  | None -> Printf.printf "Value is None\n"

let print_bool b = Printf.printf "value of bool is : %s\n" (string_of_bool b)

let print_nat n = Printf.printf "value of nat is : %d\n" n

let print_pos pos = Printf.printf "Current position is : %d.\n" pos

let print_flg fg = match fg with
  | FormatTest.SameVer -> Printf.printf "Same version extension.\n"
  | FormatTest.DiffVer -> Printf.printf "Different version extension.\n"

let sprint_flg fg =
  match fg with
  | FormatTest.SameVer -> "Same version extension.\n"
  | FormatTest.DiffVer -> "Different version extension.\n"

(* Convert a byte (char) to hex string *)
let hex_of_byte (b : char) : string =
  Printf.sprintf "%02x" (Char.code b)

(* Convert a byte list to a JSON array of hex strings *)
let hex_of_byte_list (bl : char list) : string =
  (String.concat "" (List.map (fun b -> (hex_of_byte b)) bl))
       

let shift_to_8_bits (k : int) (n : int) : int =
  let r = 8 - (k mod 8) in 
  (n lsl r)  (* Shift left until >= 0x80 *)


(* So here, we turn byte list into bit list *)
let int_to_bit_string x n =
  let rec aux i acc =
    if i < 0 then acc
    else
      let bit = (x lsr i) land 1 in
      aux (i - 1) (acc ^ string_of_int bit)
  in
  aux (n - 1) ""
    
let bits_of_byte_list (bl : char list) : string =
  (String.concat "" (List.map (fun b -> int_to_bit_string (Char.code b) 8) bl))

let hex_of_bit_string bs = 
  let (k, (bl, n)) = bs in
  let bl_str = bits_of_byte_list bl in
  let bits_str =
    (if (k mod 8 = 0)
     then
       `String bl_str
     else
       (let r = (k mod 8) in 
        `String (bl_str ^ (int_to_bit_string n r)))) in 
  `Assoc ["value", bits_str;
          "length", `Int k]

let hex_of_bit_string_fixed bs =
  let (k, (bl, n)) = bs in
  let bl_str =  bits_of_byte_list bl in
  if (k mod 8 = 0)
  then
    `String bl_str
  else
    let r = (k mod 8) in 
    `String (bl_str ^ (int_to_bit_string n r))

(* Helper function to parse hex string into an integer *)
let int_of_hex_string (s : string) : int =
  int_of_string s

(* Parse a single byte hex string into a byte (char) *)
let byte_of_hex_string (s : string) : char =
  Char.chr (int_of_hex_string s)

let byte_list_of_yojson (json : Yojson.Safe.t) : char list =
  match json with
  | `List l -> List.map (function
      | `String s -> byte_of_hex_string s
      | _ -> failwith "Invalid byte hex string") l
  | _ -> failwith "Expected a JSON array for byte list"


