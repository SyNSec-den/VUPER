(* In this file, we compile the basic types.  *)

open ASN1Format

let proj_name = "NR17"

(* This term is for enum where I need to generate
   nat
 *)

let rec print_n (n : int) (c : char) =
  if (n > 0) then
    (Printf.sprintf "%c" c) 
    ^ (print_n (n - 1) c)
  else
    ""

let rec print_n_str (n : int) (s : string) =
  if (n > 0) then
    (Printf.sprintf "%s" s) 
    ^ (print_n_str (n - 1) s)
  else
    ""

let gen_n_S (n : int) (x : string) : string =
  (print_n_str n "(S ")
  ^ x
  ^ (print_n n ')')


let make_op_opaque name = 
  (Printf.sprintf "Opaque %s__cond %s__Format.\n\n" name name)
  
let gen_term_nat (name : string) (ub : int) =
  (Printf.sprintf
     "Lemma %s__helper : to_bit_sz %d <= INT_MAX_LEN.\n  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.\nQed.\n"
     name ub)
  ^ (Printf.sprintf
       "Definition %s__Format : T_Format nat (fun z => (z <= %d)) :=\n  nat_enum_format %d %s__helper.\n\n"
       name ub ub name)

(* Turn a ASN.1 int into a string *)
let read_a_int (a : asn1_int) =
  match a with
  | INT_LIT n -> Printf.sprintf "%d" n
  | INT_REF s -> s

let gen_term_int_fixed (name : string) (n : asn1_int) = 
  (* Here are two helper lemmas generated,
     they are used for the format
   *)
  let n1 = read_a_int n in
  (Printf.sprintf "Definition %s__Type := Z.\n" name)
  ^ (Printf.sprintf "Definition %s__cond := (fun z : Z => z = %s)%%Z.\n" name n1)

let print_to_bit_sz_helper name lb ub =
  (Printf.sprintf
     "Lemma %s__helper2 : to_bit_sz (Z.to_nat (%s - %s)) <= INT_MAX_LEN.\n"
     name ub lb)
  ^ (Printf.sprintf
       "unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (%s - %s))%%Z). { apply Zorder.Zle_minus_le_0. apply %s__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.\n"
       ub lb name
    )

let print_unfold_int (a : asn1_int) : string =
  match a with
  | INT_LIT _ -> ""
  | INT_REF s -> Printf.sprintf "unfold %s.\n" s

let gen_term_int_ranged (name : string) (lb : asn1_int) (ub : asn1_int) = 
  (* Here are two helper lemmas generated,
     they are used for the format
   *)
  let lb1 = read_a_int lb in
  let ub1 = read_a_int ub in
  (* Here I need to unfold lb or ub if they are strings *)
  (Printf.sprintf
     "Lemma %s__helper1 : (%s <= %s)%%Z. %s%s lia. Qed.\n" name lb1 ub1
     (print_unfold_int lb) (print_unfold_int ub))
  ^ (print_to_bit_sz_helper name lb1 ub1)
  ^ (Printf.sprintf "Definition %s__Type := Z.\n" name)
  ^ (Printf.sprintf "Definition %s__cond := (fun z => (%s <= z <= %s)%%Z).\n"
       name lb1 ub1) 

let gen_term_int_ranged_ext (name : string) (lb : asn1_int) (ub : asn1_int) = 
  (* Here are two helper lemmas generated,
     they are used for the format
   *)
  let lb1 = read_a_int lb in
  let ub1 = read_a_int ub in
  (* Here I need to unfold lb or ub if they are strings *)
  (Printf.sprintf
     "Lemma %s__helper1 : (%s <= %s)%%Z. %s%s lia. Qed.\n" name lb1 ub1
     (print_unfold_int lb) (print_unfold_int ub))
  ^ (print_to_bit_sz_helper name lb1 ub1)
  ^ (Printf.sprintf "Definition %s__Type := Z.\n" name)
  ^ (Printf.sprintf "Definition %s__cond := (fun z => (%s <= z <= %s)%%Z \\/ (~((%s <= z <= %s)%%Z) /\\ (- 2 ^ 47 <= z <= 2 ^ 47 - 1)%%Z)).\n"
       name lb1 ub1 lb1 ub1) 


let gen_term_int (name : string) c =
  match c with
  | FIXED_INT n -> gen_term_int_fixed name n 
  | RANGED_INT (lb, ub) -> gen_term_int_ranged name lb ub
  | RANGED_INT_Ext (lb, ub) -> gen_term_int_ranged_ext name lb ub 
  | NO_CONS_INT ->
     (* Simply print its Type and  *)
     (Printf.sprintf "Definition %s__Type := Z.\n" name)
     ^  (Printf.sprintf "Definition %s__cond := (fun z => (- Z.pow 2 47 <= z <= Z.pow 2 47 - 1)%%Z).\n"
           name)


(* For ENUMERATED *)
let gen_term_enum (name : string) (l : string list) = 
  (* First we added the Type as a Inductive definition.
     Then, we would add the bijection between them and the
     a constrained number [0, length l - 1].

     Here we use the Proj2 format that is previously defined
     in test.v. Here Proj2 means that these two are strictly
     bijection
   *)
  let n = List.length l in 
  (Printf.sprintf "Inductive %s__Type : Set :=\n" name)
  ^ (String.concat "" (List.map (fun na -> Printf.sprintf " | %s__%s\n" name na) l))
  ^ (Printf.sprintf ".\nDefinition %s__cond := (fun (_ : %s__Type) => True).\n" name name)
  ^ (gen_term_nat (name ^ "__nat") (n - 1))

  (* Need to have this format of integer first *)
  ^ (Printf.sprintf "Definition %s__F1 t :=\n  match t with\n" name) 
  ^ (String.concat "" (List.mapi (fun i na ->
                           Printf.sprintf "  | %s__%s => %d\n" name na i) l)) 
  ^ (Printf.sprintf "  end.\nDefinition %s__F2 n :=\n  match n with\n" name)
  ^ (String.concat "" (List.mapi (fun i na ->
                           Printf.sprintf "  | %d => %s__%s\n" i name na) l))

  (* The rest could be mapped to any item in the definition *)
  ^ (Printf.sprintf "  | _ => %s__%s\n  end.\n" name (List.nth l 0))

  (* A helper function that would prove the inverse of f1 and f2 *)
  ^ (Printf.sprintf
       "Lemma %s__F1F2 : forall x : %s__Type, (%s__F1 x <= %d) /\\ %s__F2 (%s__F1 x) = x. imp_solve. Qed.\n"
       name name name (n - 1) name name) 
  ^ (Printf.sprintf
       "Lemma %s__F2F1 : forall (y : nat) (H : y <= %d), %s__F1 (%s__F2 y) = y. enum_solve H y. Qed.\n\n"
       name (n - 1) name name)

  (* End of definition of helpers  *)


let gen_term_enum_ext (name : string) (l : string list) (ext : string list) =
  let ne = List.length ext in
  let ext_name = name ^ "__ext" in
  (* like before, generate enum first *)
  (gen_term_enum (name ^ "__root") l)
  ^ (
    if ne = 0
    then
      ((Printf.sprintf "Definition %s__Type : Set := Empty_set.\n" ext_name)

       ^ (Printf.sprintf
            "Definition %s__cond := (fun (_ : %s__Type) => True).\n"
            ext_name ext_name))
    else
      (gen_term_enum ext_name ext)
      ^ (Printf.sprintf
           "Lemma %s__helper1 : forall a, a <= %d -> a <= 63. lia. Qed.\n"
        ext_name (ne - 1))
      ^ (Printf.sprintf
           "Definition %s__helper_format : T_Format nat (fun n => n <= %d) :=
            restrict_format (fun n : nat => n <= %d)
                  small_integer_format
                  %s__helper1
                  (fun a => Compare_dec.le_dec a %d).\n"
           ext_name (ne - 1) (ne - 1) ext_name (ne - 1))
  )


  (* Then, genearte the extensions. Note similar to choice, there is *)
  (*^ (Printf.sprintf "Inductive %s__Type : Set :=\n" ext_name)
  ^ (String.concat "" (List.map (fun na -> Printf.sprintf " | %s__%s" ext_name na) ext))
  (* ^ (Printf.sprintf " | %s__unknown (n : nat) (pf : %d <= n)" ext_name ne) *)
  ^ ".\n"

  ^ (Printf.sprintf
       "Definition %s__cond (z : %s__Type) := True.\n"
       ext_name ext_name)

  ^ (Printf.sprintf "Definition %s__F1 (t : %s__Type) : nat :=\n  match t with\n" ext_name ext_name) 
  ^ (String.concat "" (List.mapi (fun i na ->
                           Printf.sprintf "  | %s__%s => %d\n" ext_name na i) ext))
  ^ "end.\n"

(*  ^ (Printf.sprintf
       "  | %s__unknown n _ => n \n end.\n"
       ext_name) *)

  ^ (Printf.sprintf "Definition %s__helper n : %d <= %s := ltac:(prove_n_le_S).\n "
       ext_name ne (gen_n_S ne "n"))

  ^ (Printf.sprintf "Definition %s__F2 (n : nat) : %s__Type :=\n  match n with\n" ext_name ext_name)
  ^ (String.concat "" (List.mapi (fun i na ->
                           Printf.sprintf "  | %d => %s__%s\n" i ext_name na) ext))
  ^ "end.\n"
(*  ^ (Printf.sprintf
       "  | %s =>  %s__unknown _ (%s__helper n0) \n end.\n"
       (gen_n_S ne "n0") ext_name ext_name ) *)

  ^ (Printf.sprintf
       "Lemma %s__F1F2 :  (forall a : %s__Type, %s__cond a -> (fun n : nat => n <= 63) (%s__F1 a) /\\ %s__F2 (%s__F1 a) = a).\n"
       ext_name ext_name ext_name ext_name ext_name ext_name )
  ^ (Printf.sprintf "imp_solve.  unfold %s__F2.  enum_ext_solve1 n.  Qed.\n"
       ext_name)

  ^ (Printf.sprintf
       "Lemma %s__F2F1 : (forall b : nat, (fun n : nat => n <= 63) b -> %s__cond (%s__F2 b) /\\ %s__F1 (%s__F2 b) = b).\n"
       ext_name ext_name ext_name ext_name ext_name)
  ^ "intros. split; enum_ext_solve2 b. Qed.\n"
    
  ^ (Printf.sprintf "Definition %s__dec : dec_P %s__cond.\n" ext_name ext_name)
  ^ (Printf.sprintf
       "unfold dec_P, %s__cond. intro a. destruct a; auto. apply Compare_dec.le_dec. Defined.\n\n"
       ext_name) *)


  ^ (Printf.sprintf "Definition %s__Type : Set := %s__root__Type + %s__ext__Type.\n" name name name)
  ^ (Printf.sprintf "Definition %s__cond := sum_cond %s__root__cond %s__ext__cond.\n\n" name name name)
  

(* Next section for OCTET STRING *)
let gen_term_octets_fixed (name : string) (n : asn1_int) =
  let n1 = read_a_int n in
  (Printf.sprintf "Definition %s__Type := octet_string.\n" name)
  ^ (Printf.sprintf
       "Definition %s__cond := (fun bs : octet_string => (Z.of_nat (length bs) = %s)%%Z).\n"
       name n1)
(*  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond := octet_string_fixed_format %s.\n"
       name name name n1) *)

let gen_length_cons_helper name lb ub : string =
  let lb1 = read_a_int lb in
  let ub1 = read_a_int ub in
  (Printf.sprintf
     "Lemma %s__helper1 : (0 <= %s <= %s)%%Z. %s%s lia. Qed.\n"
     name lb1 ub1
     (print_unfold_int lb) (print_unfold_int ub))
  ^ (print_to_bit_sz_helper name lb1 ub1)

let gen_term_octets_ranged (name : string) lb ub =
  let lb1 = read_a_int lb in
  let ub1 = read_a_int ub in
  (gen_length_cons_helper name lb ub)
  ^ (Printf.sprintf "Definition %s__Type := octet_string.\n" name)
  ^ (Printf.sprintf
       "Definition %s__cond := (fun bs : octet_string => (%s <= Z.of_nat (length bs) <= %s)%%Z).\n"
       name lb1 ub1)
 (* ^ (Printf.sprintf
       "Definition %s__Format := octet_string_ranged_format %s %s %s__helper1 %s__helper2.\n" 
       name lb1 ub1 name name) *)

let gen_term_octets_no_cons (name : string) =
  (Printf.sprintf "Definition %s__Type := octet_string.\n" name)
  ^ (Printf.sprintf
       "Definition %s__cond := (fun bs : octet_string => length bs < Nat.pow 2 14).\n"
       name)
(*  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond := octet_string_no_cons_format.\n"
       name name name) *)

(* For octet string, also we have 3 cases. *)
let gen_term_octets (name : string) (c : length_constraint) =
  match c with
  | FIXED_LEN c -> gen_term_octets_fixed name c
  | RANGED_LEN (lb, ub) -> gen_term_octets_ranged name lb ub 
  | NO_CONS_LEN -> gen_term_octets_no_cons name
  | _ -> "" 


(* For BIT STRING *)
let gen_term_bits_fixed (name : string) (n : asn1_int) =
  let n1 = read_a_int n in
  (Printf.sprintf "Definition %s__Type := bit_string_fixed.\n" name)
  ^ (Printf.sprintf
       "Definition %s__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat %s /\\ bit_string_len_prop (fst z) (snd z)).\n"
       name n1)
 
let gen_term_bits_ranged (name : string) lb ub =
  let lb1 = read_a_int lb in
  let ub1 = read_a_int ub in
  (gen_length_cons_helper name lb ub)
  ^ (Printf.sprintf "Definition %s__Type := bit_string.\n" name)
  ^ (Printf.sprintf
       "Definition %s__cond := (fun z : bit_string => (%s <= Z.of_nat (fst z) <= %s)%%Z /\\ bit_string_len_prop (fst z) (snd z)).\n"
       name lb1 ub1)
(*  ^ *)

let gen_term_bits_no_cons (name : string) =
  (Printf.sprintf "Definition %s__Type := bit_string.\n" name)
  ^ (Printf.sprintf
       "Definition %s__cond := (fun z : bit_string => (fst z) < Nat.pow 2 14 /\\ bit_string_len_prop (fst z) (snd z)).\n"
       name)
(*  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond :=  bit_string_no_cons_format.\n"
       name name name) *)

let gen_term_bits (name : string) (c : length_constraint) =
  match c with
  | FIXED_LEN c -> gen_term_bits_fixed name c
  | RANGED_LEN (lb, ub) -> gen_term_bits_ranged name lb ub 
  | NO_CONS_LEN -> gen_term_bits_no_cons name
  | _ -> ""

(* Note that this only works for top-level definitions, otherwise,
   we do not need to define bool or null or formats without constraints. 
 *)
(* BOOLEAN *)
let gen_term_bool (name : string) =
  (Printf.sprintf "Definition %s__Type := bool.\n" name)
  ^ (Printf.sprintf
       "Definition %s__cond := (fun _ : bool => True).\n"
       name)
 (* ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond := bool_format.\n"
       name name name) *)

(* NULL *)
let gen_term_null (name : string) =
  (Printf.sprintf "Definition %s__Type := unit.\n" name)
  ^ (Printf.sprintf
       "Definition %s__cond := (fun _ : unit => True).\n"
       name)
 (* ^ (Printf.sprintf
       "Definition %s__Format : Format %s__Type %s__cond := Unit.\n"
       name name name) *)

let gen_term_ref (name : string) (ref_name : string) =
  (Printf.sprintf "Require Import %s.%s.\n" proj_name ref_name)
  ^ (Printf.sprintf "Definition %s__Type := %s__Type.\n" name ref_name)
  ^ (Printf.sprintf
       "Definition %s__cond := %s__cond.\n"
       name ref_name)
  ^ (make_op_opaque ref_name)

let gen_term_ref_filename ref_name =
  (Printf.sprintf "Require Import %s.%s.\n\n" proj_name ref_name)
  ^ (make_op_opaque ref_name)

let gen_term_param_ref name ref_name param_name =
  (Printf.sprintf "Require Import %s.%s.\n" proj_name ref_name)
  ^ (Printf.sprintf "Require Import %s.%s.\n" proj_name param_name)
  (* Need to prepare a Param_T *)

  (* Here, I need to have a list of param_name. Then if
     the module is already defined, I simply 
   *)
(*  ^ (Printf.sprintf "Module %s__mod.\n" name)
  ^ (Printf.sprintf "Module %s__MT <: Param_MT.\n" param_name)

  ^ (Printf.sprintf "Definition P_Type := %s__Type.\n" param_name)
  ^ (Printf.sprintf "Definition P_Cond := %s__cond.\n" param_name)
  ^ (Printf.sprintf "Definition P_Format := %s__Format.\n" param_name)

  ^ (Printf.sprintf "End %s__MT.\n" param_name)
  ^ (Printf.sprintf "Module format_mod := %s__module %s__MT.\n\n" ref_name param_name)
  ^ (Printf.sprintf "End %s__mod.\n" name) *)
     
  ^ (Printf.sprintf "Definition %s__Type := %s__Type %s__Type.\n" name ref_name param_name)
  ^ (Printf.sprintf
       "Definition %s__cond := %s__cond _ %s__cond.\n"
       name ref_name param_name)
  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond := %s__Format _ _ %s__Format.\n"
       name name name ref_name param_name)

  ^ (make_op_opaque name)
  
(* Here, consider the top level definitions, for example,
   T1 ::= BOOLEAN
   T2 ::= INTEGER (1..10)
   In this case, we need to define a new file for T1
   and T2. This is refered to as top-level definitions
 *)
let gen_term_type_top_level (tt : terminal) (name : string) = 
  match tt with
  | NULL -> gen_term_null name
  | INTEGER c -> gen_term_int name c
  | BOOLEAN -> gen_term_bool name
  | ENUM l -> gen_term_enum name l
  | ENUM_Ext (l, ext) -> gen_term_enum_ext name l ext
  | OCTET_STRING c -> gen_term_octets name c
  | BIT_STRING c -> gen_term_bits name c
  | Ref ref_name -> gen_term_ref name ref_name
  | PARAM_Ref (ref_name, param_name) ->
    gen_term_param_ref name ref_name param_name
  | _ -> ""

(* If some type does not have a predefined format,
   we need to define it one more time. 
 *)
let gen_term_type  (tt : terminal) (name : string) = 
  match tt with
  | INTEGER c ->
     (match c with
      | FIXED_INT n -> gen_term_int_fixed name n 
      | RANGED_INT (lb, ub) -> gen_term_int_ranged name lb ub
      | RANGED_INT_Ext (lb, ub) -> gen_term_int_ranged_ext name lb ub 
      | NO_CONS_INT -> "")
  | ENUM l  ->  gen_term_enum name l
  | ENUM_Ext (l, ext) -> gen_term_enum_ext name l ext
  | OCTET_STRING c ->
    (match c with
     (* ignore the case of extensions for now *)
      | FIXED_LEN c -> gen_term_octets_fixed name c
      | RANGED_LEN (lb, ub) -> gen_term_octets_ranged name lb ub
      | NO_CONS_LEN -> ""
      | _ -> "")
  | BIT_STRING c ->
    (match c with
     (* ignore the case of extensions for now *)
      | FIXED_LEN c -> gen_term_bits_fixed name c
      | RANGED_LEN (lb, ub) -> gen_term_bits_ranged name lb ub 
      | NO_CONS_LEN -> ""
      | _ -> "")
  | UnknownMultiString UTF8String -> ""
  | Ref ref_name -> gen_term_ref_filename ref_name
  | PARAM_Ref (ref_name, param_name) ->
     gen_term_param_ref name ref_name param_name
  | _ -> ""

(* We assume that l is not nil, but ext might be nil
  l might be nil *)
let gen_term_enum_ext_op name ne  =
  (* Case where there is no visiable extension.

     There is a slight problem here, if encode -> None when we
     are encoding a None in extension, then, this breaks the
     security property we want. So we simply encode it into a
     unknown thing. which is not a perfect approach but should work.
     Same for choice, we encode it to out-of-bound item. 
   *)
  let root_name = name ^ "__root" in
  let ext_name = name ^ "__ext" in
  (Printf.sprintf
     "Definition %s__Format : T_Format %s__Type (fun _ => True) :=\n" root_name root_name)
  ^ (Printf.sprintf "(* Eval compute in *)proj3_format %s__nat__Format %s__F1 %s__F2 %s__F1F2 %s__F2F1.\n\n"
       root_name root_name root_name root_name root_name) 
  ^ (make_op_opaque root_name)

  ^ (if ne = 0 then
       (Printf.sprintf
          "Definition %s__Format : T_Format %s__Type %s__cond := empty_format.\n\n"
          ext_name ext_name ext_name)
     else
       (Printf.sprintf
          "Definition %s__Format : T_Format %s__Type %s__cond :=\n"
          ext_name ext_name ext_name)
       ^ (Printf.sprintf
            "proj3_format %s__helper_format %s__F1 %s__F2 %s__F1F2 %s__F2F1.\n\n"
            ext_name ext_name ext_name ext_name ext_name) 
    )

  ^ (make_op_opaque ext_name)

  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond := sum_format %s__Format %s__Format.\n"
       name name name root_name ext_name)
  ^ (make_op_opaque name)

let gen_term_op_eval tt name =
  (match tt with
   | NULL -> ""
   | INTEGER c ->
      (match c with
       | FIXED_INT n ->
          let n1 = read_a_int n in
          (Printf.sprintf
             "Definition %s__Format : T_Format Z %s__cond := fixed_int_format %s. "
             name name n1)
       | RANGED_INT (lb, ub) ->
          let lb1 = read_a_int lb in
          let ub1 = read_a_int ub in
          (Printf.sprintf
             "Definition %s__Format : T_Format Z %s__cond :=\n ranged_int_format (%s) (%s) %s__helper1 %s__helper2.\n\n"
             name name lb1 ub1 name name)
       | RANGED_INT_Ext (lb, ub) ->
         let lb1 = read_a_int lb in
         let ub1 = read_a_int ub in
         (Printf.sprintf
            "Definition %s__Format : T_Format Z %s__cond :=\n int_format_ranged_ext (%s) (%s) %s__helper1 %s__helper2.\n\n"
            name name lb1 ub1 name name)
         | NO_CONS_INT -> "")
       | BOOLEAN -> ""
   | BIT_STRING c ->
      (match c with
       | FIXED_LEN n ->
           let n1 = read_a_int n in
           (Printf.sprintf
              "Definition %s__Format : T_Format %s__Type %s__cond := (* Eval compute in *) bit_string_fixed_format %s.\n"
              name name name n1)
       | RANGED_LEN (lb, ub) ->
          let lb1 = read_a_int lb in
          let ub1 = read_a_int ub in
          (Printf.sprintf
             "Definition %s__Format : T_Format %s__Type %s__cond := (* Eval compute in *) bit_string_ranged_format %s %s %s__helper1 %s__helper2.\n" 
             name name name lb1 ub1 name name)
       | NO_CONS_LEN -> ""
       | _ -> "")
   | ENUM _ ->
        (Printf.sprintf
           "Definition %s__Format : T_Format %s__Type (fun _ => True) :=\n" name name)
        ^ (Printf.sprintf "(* Eval compute in *) proj3_format %s__nat__Format %s__F1 %s__F2 %s__F1F2 %s__F2F1.\n\n"
             name name name name name)
   | ENUM_Ext (_, ext) ->
      gen_term_enum_ext_op name (List.length ext)
   
   | OCTET_STRING  c ->
      (match c with
       | FIXED_LEN n ->
          let n1 = read_a_int n in
          (Printf.sprintf
             "Definition %s__Format : T_Format %s__Type %s__cond := (* Eval compute in *) octet_string_fixed_format %s.\n"
             name name name n1)
       | RANGED_LEN (lb, ub) ->
          let lb1 = read_a_int lb in
          let ub1 = read_a_int ub in
          (Printf.sprintf
             "Definition %s__Format : T_Format %s__Type %s__cond := (* Eval compute in *) octet_string_ranged_format %s %s %s__helper1 %s__helper2.\n" 
             name name name lb1 ub1 name name)
       | NO_CONS_LEN -> ""
       | _ -> "")
   | Ref _ -> ""
   | PARAM_Ref _ -> ""
   | _ -> ""
  )
  ^ (make_op_opaque name)

let defined_term_type (tt : terminal) =
  match tt with
  | NULL -> true
  | INTEGER NO_CONS_INT -> true
  | BOOLEAN -> true
  | BIT_STRING NO_CONS_LEN -> true
  | OCTET_STRING NO_CONS_LEN -> true
  | UnknownMultiString UTF8String -> true
  | Ref _ -> true
  | _ -> false

let gen_term_op (tt : terminal) (name : string) =
  if (defined_term_type tt) then
    ""
  else
    gen_term_op_eval tt name

let get_op_term_name tt name =
  match tt with
  | NULL -> "unit"
  | BOOLEAN -> "bool"
  | INTEGER NO_CONS_INT -> "int"
  | BIT_STRING NO_CONS_LEN -> "bit_string_nc"
  | OCTET_STRING NO_CONS_LEN -> "octet_string_nc"
  | UnknownMultiString UTF8String -> "utf8_string"
  | Ref rf -> rf
  | _ -> name

let gen_term_op_top_level (tt : terminal) (name : string) =
  if (defined_term_type tt)
  then 
    let op_name = (get_op_term_name tt name) in 
    (Printf.sprintf "Definition %s__Format := %s__Format.\n"
       name op_name)
    ^ (Printf.sprintf "Opaque %s__Format.\n" name) 
  else
    gen_term_op_eval tt name   


