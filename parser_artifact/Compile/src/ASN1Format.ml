(* However, length constraint might also be
   a reference. 
 *)
type asn1_int =
  | INT_LIT of int
  | INT_REF of string

type length_constraint =
  | FIXED_LEN of asn1_int
  | RANGED_LEN of asn1_int * asn1_int
  | RANGED_LEN_Ext of asn1_int * asn1_int
  | NO_CONS_LEN

type int_constraint =
  | FIXED_INT of asn1_int
  | RANGED_INT of asn1_int * asn1_int
  | RANGED_INT_Ext of asn1_int * asn1_int
  | NO_CONS_INT

type known_string_type =
  | NumericString
  | IA5String

type unknown_string_type =
  | UTF8String

(**
   Object Identifier
   Universial OID and relative OID
 **)
type oid_type =
  | OID_uni
  | OID_relative

(** For now, we simply add a couple different terminal
   types
    we need to distinguish between known-multiplier string type
    vs UTF8String

   Not that ENUM might also have extensions.
 **)
type terminal =
  | NULL
  | INTEGER of int_constraint
  | BOOLEAN
  | ENUM of string list
  | ENUM_Ext of string list * string list
  | BIT_STRING of length_constraint
  | OCTET_STRING of length_constraint
  | KnownMultiString of known_string_type * length_constraint
  | UnknownMultiString of unknown_string_type
  | OID_TYPES of oid_type
  | Ref of string
  | PARAM_Ref of string * string

(** Here about the default type. There are much less
    available types here.
    
    We know from the RRC layer that default types are
    always a simple type. Mostly are ENUMERATED.

    But we will have to account for that these default
    types could be

    Here string default could be a enumerated, or a
    reference. We only know its an ID. Also we could
    read a bit-string
 **)
type default_val =
  | INTEGER_DFT of int
  | STR_DFT of string
  | BITS_DFT of string

(* Currently, we only support 'WITH CONSTRAINT' with the ABSENT.
   It would be easy to add support for PRESENT

   Here, this will indicate the absent field.
   One other thing we do not support is multiple constraints on the
   same target
*)
type with_components_constraint =
  | ABSENT of string 

(* Here, we must distinguish two different name.
   1. Names for reference.
   2. Names in a Field.

   Another thing we do not care too much is extension
   groups. Since they behave exactly like a SEQUENCE
   during enc/decoding. We simply will parse them into
   a Sequence.

   Now for extension groups, both extension groups in Choice
   and in Sequence are simply viewed as a Sequence.

   There are extension elements and extension groups.

   We need to make sure the asn1_typ in Default is a terminal
   type

   Another issue, SEQUENCE might have constraints.

   Another issue, we have parameterized type.

   Another issue with extension, they might have OPTIONAL or DEFAULT
 *)
type asn1_typ =
  | TERM of terminal
  | SEQUENCE of (seq_mrk list)
  | SEQUENCE_Ext of
      (seq_mrk list) * (ext_mrk list)
  | CHOICE of ((string * asn1_typ) list)
  | CHOICE_Ext of
       ((string * asn1_typ) list) * ((string * asn1_typ) list)
  | SEQUENCE_OF of (length_constraint * asn1_typ)

and seq_mrk =
  | NORMAL of string * asn1_typ
  | OPTIONAL of string * asn1_typ
  | DEFAULT of string * asn1_typ * default_val
  | CONSTRAINT of string * asn1_typ * with_components_constraint

and ext_mrk =
  | EXT_ELEM of string * asn1_typ
  | EXT_GRP of seq_mrk list

(* Assign the asn1_typ to some string reference value
   Certain notes for the name:
   It cannot contain underscore `_`;
   If there is a hyphen `-`, it shall be turned into an
   underscore `_`.
 *)
type asn1_type_def = (string * asn1_typ)

type asn1_value_def =
  | INT_value of string * int

type asn1_param_type_def = (string * string * asn1_typ)

type asn1_def =
  | ASN_Val of asn1_value_def
  | ASN_Type of asn1_type_def
  | ASN_PARAM_Type of asn1_param_type_def

(* A list of ASN.1 definitions *)
type asn1_list = asn1_def list

type import_def =
  | Val_Import of string
  | Type_Import of string

(* Import list is module name + definitions imported *)
type asn1_import_list = string * import_def list

(* A module is a imported list + all the asn1 definitions in the
   module
 *)
type asn1_module = string * asn1_import_list list * asn1_list

(* An asn1 object is simply a list of ASN.1 modules,
   in a good order
 *)
type asn1_obj = asn1_module list

(* It turns hyphen to underscore *)
let hp_to_us (s : string) =
  String.map (fun c -> if c = '-' then '_' else c) s

let str_to_bits (s : string) : bool list =
  s |> String.to_seq |> Seq.map (function
                            | '0' -> false
                            | '1' -> true
                            | _ -> false)
  |> List.of_seq
                          

let str_asn1_int a = 
  match a with
  | INT_LIT n -> Printf.sprintf "%d" n
  | INT_REF s -> s

let print_len_cons l =
  match l with
  | FIXED_LEN n -> Printf.printf "SIZE (%s)" (str_asn1_int n)
  | RANGED_LEN (lb, ub) -> Printf.printf "SIZE (%s..%s) " (str_asn1_int lb) (str_asn1_int ub)
  | _ -> () 

let rec iter_last f lst g = 
  match lst with
  | [] -> ()
  | [h] -> f h
  | h :: t ->
     f h; g ();   
     iter_last f t g

let print_comma_only () =
  Printf.printf ", "

let print_comma () =
  Printf.printf ",\n"

let print_vline () =
  Printf.printf "\n"

let print_string s =
  Printf.printf "%s" s

let print_enum e =
  Printf.printf "ENUMERATED {";
  iter_last print_string e print_comma_only;
  Printf.printf "}"

let print_term t =
  match t with
  | NULL -> Printf.printf "NULL"
  | INTEGER _  -> Printf.printf "INTEGER"
  (*Printf.printf "INTEGER (%s..%s)" (str_asn1_int lb) (str_asn1_int ub) *)
  | BOOLEAN -> Printf.printf "BOOLEAN"
  | ENUM e -> print_enum e
  | ENUM_Ext (_, _) -> ()
  | BIT_STRING c -> Printf.printf "BIT STRING "; print_len_cons c
  | OCTET_STRING c -> Printf.printf "OCTET STRING "; print_len_cons c
  | Ref r -> Printf.printf "%s" r
  |  _ -> ()

let print_bool b =
  if b then "TRUE" else "TRUE"

let print_dft t =
  match t with
  | INTEGER_DFT n ->
     Printf.printf "INTEGER\tDEFAULT %d" n
  | _ -> ()

(* Here is the iter function where the last term
   is treated differently.
 *)


(* Print f and g *)
let print_zip f g tup =
  let (t1, t2) = tup in
  Printf.printf "\t";
  f t1;
  Printf.printf "\t";
  g t2

(* Here, can I write a function that will print the
   ASN.1 Definition faithfully. 
 *)

and print_mrk_typ_ext tp_m =
  match tp_m with
  | NORMAL (name, _) ->
     Printf.printf "\t%s\t NORMAL" name;
  (*print_typ t; *)
  | DEFAULT (name, _, _) ->
     Printf.printf "\t%s\t DEFAULT" name;
  (*  print_dft t; *)
  | OPTIONAL (name, _) ->
     Printf.printf "\t%s\t" name;
     (* print_typ t; *)
     Printf.printf "\tOPTIONAL"
  | CONSTRAINT (name, _, _) ->
    Printf.printf "%s" name


let rec print_typ tp =
  match tp with
  | TERM _ -> ()
  (* print_term t *)
  | SEQUENCE t -> 
     (*Printf.printf "SEQUENCE {\n"; *)
     iter_last (print_mrk_typ) t print_comma
     (* Printf.printf "\n}" *)

  | SEQUENCE_Ext (t, ext) ->
     Printf.printf "SEQUENCE {\n";
     iter_last (print_mrk_typ) t print_comma;
     Printf.printf ",\n\t...,\n"; 
     iter_last (print_ext_typ) ext print_comma;
     Printf.printf "\n}"

  | CHOICE l -> 
     (*Printf.printf "CHOICE {\n"; *)
     iter_last (print_zip print_string print_typ) l print_comma;
  (*Printf.printf "\n}"  *)

  | CHOICE_Ext (_, _) ->
     Printf.printf "CHOICE {\n";
     (*iter_last (print_zip print_string print_typ) l print_comma; *)
     (*Printf.printf ",\n\t...,\n";*)
     (*iter_last (print_ext_typ) ext print_comma; *)
     Printf.printf "\n}"

  | SEQUENCE_OF (_, t)  -> 
     (*Printf.printf "SEQUENCE ";
     print_len_cons c;
     Printf.printf " OF "; *)
     print_typ t
     (*Printf.printf "\n" *)
     
and print_mrk_typ tp_m =
  match tp_m with
  | NORMAL (_, t) ->
     (*Printf.printf "\t%s\t NORMAL" name; *)
     print_typ t
  | DEFAULT (_, _, _) -> ()
  (*Printf.printf "\t%s\t DEFAULT" name; *)
  (*print_dft t*)
  | OPTIONAL (_, t) ->
     (*Printf.printf "\t%s\t" name; *)
    print_typ t
  | CONSTRAINT (_, _, _) -> ()
(*Printf.printf "\tOPTIONAL" *)

and print_ext_typ ext_m =
  match ext_m with
  | EXT_ELEM (_, _) -> ()
     (*(Printf.printf "\t%s\t" name;
      print_typ t*)
  | EXT_GRP t -> 
     iter_last (print_mrk_typ_ext) t print_comma

let print_typ_def (s : asn1_def) =
  match s with
  | ASN_Val _ -> ()
    (* (match vd with
     | INT_value (name, v) -> 
        Printf.printf "Print value of %s of %d\n" name v) *)
     
  | ASN_Type t' ->
     let (_, t) = t' in
     (* Printf.printf "%s\t::=\t" name; *)
     print_typ t;
  (* Printf.printf "\n" *)
  | ASN_PARAM_Type _ -> ()

let print_module_import_list (mi : asn1_import_list) =
  let (_, _) = mi in ()
  (*iter_last (Printf.printf "%s") al print_comma;
  Printf.printf "FROM %s\n" name *)

let print_module (m : asn1_module) =
  let (name, ail, al) = m in 
  (* string * asn1_import_list list * asn1_list *)
  Printf.printf "%s DEFINITIONS AUTOMATIC TAGS ::=\nBEGIN\n" name;
  (match ail with
  | [] -> ()
  | _ ->
     (Printf.printf "IMPORTS\n";
      iter_last print_module_import_list ail print_vline;
      Printf.printf ";\n"
     ));
  iter_last print_typ_def al print_vline;
  Printf.printf "ENDS\n"

let print_obj (a : asn1_obj) =
  iter_last print_module a print_vline

let print_import () =
  Printf.printf "import some files"

(* We can break it down into several steps
   1. For Terminal Types. For some cases we can
   directly use previously defined types, namely
   boolean.

   But for most other cases, like INTEGER (a..b),
   we have to define this new object. But when there
   are two of the same INTEGER sizes, we can re-use its
   format and parsers.

   And for Enumerated, we need to manually add the
   new type definition.

   We probably need to scan through the list of
   definitions first. (flatten it?)

   2. Another problem is ASN.1 file definitions
   might be out of order. So we need to have a
   in-order definition when we are doing it ourselves.

   3. The input shall be a list of ASN.1 type and value
   definitions.

   4. For each combinator format, we need to generate
   the 

 *)

(* One practical problem is the need to reorder the
   asn.1 definitions such that referenced definitions
   appear first.

   Or we don't need to do this, if we separately define
   each Definition in a new file? In this way, we save
   the effort of defining everything 

   Note that we are not expecting a name conflict in the
   definitions.

   Or we don't actually need to reorder, but we can generate a
   new file for evey new definition, similar to ASN1c. This
   might be better to organize, because we don't need to have
   a 10k loc Coq file. And we can have a clearer view of
   the correctness proofs. 
 *)

