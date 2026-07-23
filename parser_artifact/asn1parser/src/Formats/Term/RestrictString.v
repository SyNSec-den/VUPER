Require Import 
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Comb.SeqOf
  ASN1Parser.Formats.Term.NonNeg.

Require Import Coq.Strings.Ascii
  Lia. 
(* First, consider the numeric string *)
Definition char_list := list ascii. 

Lemma zero_le10 : 0 <= 10. lia. Qed.

Lemma zero_le10_bit : to_bit_sz (10 - 0) <= Comb.INT_MAX_LEN.
  simpl. unfold to_bit_sz. simpl. unfold Comb.INT_MAX_LEN.
  lia. Qed.


Definition num_to_ascii :=
  (fun n : nat =>
     match n with
     | 0 => " "%char
     | 1 => "0"%char
     | 2 => "1"%char
     | 3 => "2"%char
     | 4 => "3"%char
     | 5 => "4"%char
     | 6 => "5"%char
     | 7 => "6"%char
     | 8 => "7"%char
     | 9 => "8"%char
     | 10 => "9"%char
     | _ => " "%char
     end). 

Definition ascii_to_num :=  (fun a : ascii =>
       match a with
       | " "%char => 0
       | "0"%char => 1
       | "1"%char => 2
       | "2"%char => 3
       | "3"%char => 4
       | "4"%char => 5
       | "5"%char => 6
       | "6"%char => 7
       | "7"%char => 8
       | "8"%char => 9
       | "9"%char => 10
       | _  => 0
       end).

Definition numeric_constraint :=  (fun a : ascii =>
       a = " "%char 
       \/ a = "0"%char
       \/ a = "1"%char
       \/ a = "2"%char
       \/ a = "3"%char
       \/ a = "4"%char
       \/ a = "5"%char
       \/ a = "6"%char
       \/ a = "7"%char
       \/ a = "8"%char
       \/ a = "9"%char) .

From Coq Require Import ssreflect ssrfun ssrbool.

Lemma numeric_string_helper1 : (forall a : ascii,
        numeric_constraint a ->
        (fun z : nat => 0 <= z <= 10) (ascii_to_num a) /\
          num_to_ascii (ascii_to_num a) = a).
Proof.
  move=> a H.
  case: H => [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]] /=;  split; try lia; by [].  
Qed.

Lemma b_cases (b : nat) :
  0 <= b <= 10 -> 
  b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ 
  b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10.
Proof.
  (* lia instantly solves finite integer boundaries like this *)
  move; lia. 
Qed.

Lemma numeric_string_helper2 : (forall b : nat,
        (fun z : nat => 0 <= z <= 10) b ->
        numeric_constraint (num_to_ascii b) /\
          ascii_to_num (num_to_ascii b) = b).
Proof. 
  move => b /b_cases H. unfold numeric_constraint. 
  case: H => [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]] /=;  split; try reflexivity; auto 15. 
Qed. 

Require Import ASN1Parser.Formats.Term.NormExtFormat. 
Definition numeric_string_dec : Comb.dec_P numeric_constraint.
  unfold Comb.dec_P, numeric_constraint.
  intros.
  repeat (apply sumbool_or1; try apply ascii_dec).
Defined.

Definition numeric_string__Format :=
  proj_format
    numeric_constraint
    (nat_range_format 0 10 zero_le10 zero_le10_bit)
    ascii_to_num
    num_to_ascii
    numeric_string_helper1 
    numeric_string_helper2
    numeric_string_dec. 

Lemma zero_le127 : 0 <= 127. lia. Qed.

Lemma zero_le127_bit : to_bit_sz (127 - 0) <= Comb.INT_MAX_LEN.
  simpl. unfold to_bit_sz. simpl. unfold Comb.INT_MAX_LEN.
  lia. Qed.

Lemma ia5_string_helper1 : (forall a : ascii,
        (fun a0 : ascii => nat_of_ascii a0 < Nat.pow 2 7) a ->
        (fun z : nat => 0 <= z <= 127) (nat_of_ascii a) /\
        ascii_of_nat (nat_of_ascii a) = a). 
Proof.
  intros.  simpl in *. split; try lia.
  apply ascii_nat_embedding.
Qed.

Lemma ia5_string_helper2 : (forall b : nat,
        (fun z : nat => 0 <= z <= 127) b ->
        (fun a : ascii => nat_of_ascii a < 128)
          (ascii_of_nat b) /\
          nat_of_ascii (ascii_of_nat b) = b).
Proof.
  intros. simpl in *.
  rewrite nat_ascii_embedding; try lia.
Qed.

(* Strict ASCII format, only has 128 terms, 
   ia5 string is simply a sequence of ia5 string format
 *)
Definition ia5_constraint :=
  (fun a : ascii => nat_of_ascii a < Nat.pow 2 7).

Definition ia5_string__Format :=
  proj_format
    ia5_constraint
    (nat_range_format 0 (Nat.pow 2 7 - 1) zero_le127 zero_le127_bit)
    nat_of_ascii
    ascii_of_nat
    ia5_string_helper1
    ia5_string_helper2
    (fun a => Compare_dec.lt_dec (nat_of_ascii a) (Nat.pow 2 7)). 

(* This is more complex, first we need to consider
   for each term. Then we need to 
 *)
(* playground *)
Require Import
  Coq.Strings.String
  ASN1Parser.Formats.Term.OctetString.

Delimit Scope string_scope with string.
Local Open Scope string_scope.

Definition s := "Hello, 世界". 

(* The basic format of a utf8-string is the same as 
   an octet string, length + bytes. 

   However, we do have to note that some of the strings
   might be illegal utf8. We ignore that for now at least
 *)
Opaque Nat.pow.
Lemma string_len a :
  Datatypes.length (list_byte_of_string a) = length a.
  induction a.
  - simpl. auto.
  - unfold list_byte_of_string in *. rewrite List.length_map in IHa.
    rewrite List.length_map.
    simpl. f_equal. auto.
Qed.

Lemma string_len2 a :
  length (string_of_list_byte a) = Datatypes.length a.
  induction a.
  - simpl. auto.
  - unfold string_of_list_byte in *. simpl. 
    f_equal. auto.
Qed.

Lemma string_format_helper1 :
  (forall a : string,
      (fun s : string => length s < Nat.pow 2 14) a ->
      (fun bs : list Byte.byte => Datatypes.length bs < Nat.pow 2 14)
        (list_byte_of_string a) /\ string_of_list_byte (list_byte_of_string a) = a).
Proof.
  intros.
  simpl in *.
  rewrite string_of_list_byte_of_string. rewrite string_len. split; auto. 
Qed.

Lemma string_format_helper2 : (forall b : list Byte.byte,
        (fun bs : list Byte.byte => Datatypes.length bs < Nat.pow 2 14) b ->
        (fun s : string => length s < Nat.pow 2 14) (string_of_list_byte b) /\
          list_byte_of_string (string_of_list_byte b) = b).
Proof.
  intros. simpl in *. rewrite list_byte_of_string_of_list_byte.
  rewrite string_len2. split; auto. Qed.

(* This is a dummy function in Coq, but it will be mapped to a 
   actual function in OCaml that will be more 
 *)
Definition check_utf8_string (s : string) : Prop := True.

Definition check_utf8_string_dec  : Comb.dec_P (check_utf8_string).
  unfold Comb.dec_P, check_utf8_string. intros; left; auto.
Defined.
             
Definition utf8_string_cond := (fun s => check_utf8_string s /\ length s < Nat.pow 2 14). 

Definition utf8_string__Format :=
  restrict_format
    utf8_string_cond
    (proj_format
       (fun s : string => length s < Nat.pow 2 14)
       octet_string_no_cons_format
       list_byte_of_string
       string_of_list_byte
       string_format_helper1
       string_format_helper2
       (fun s => Compare_dec.lt_dec (length s) (Nat.pow 2 14)))
    (fun s H => proj2 H)
    (fun s => Comb.sumbool_and1  (check_utf8_string_dec s)
                (Compare_dec.lt_dec (length s) (Nat.pow 2 14))).

(*Definition utf8_char_format :=
  restrict_format
    (fun a : string =>
       
    ). *)
