Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Comb.ListFormatProp
  Coq.Strings.Byte.

(* Here, it encodes a list of bytes
   This is not the most efficient, but pretty
   practical
 *)

(* First we define a byte format *)
Lemma eight_le_max_len : (8 <= INT_MAX_LEN).
  unfold INT_MAX_LEN. Lia.lia.
Qed.

(* No option version of of_nat *)
Definition of_nat_non_opt (a : nat) : byte :=
  match (of_nat a) with
  | Some b => b
  | None => x00
  end.

Lemma byte_format_helper1 : (forall a : byte,
        (fun _ : byte => True) a ->
        (fun z : nat => z < Nat.pow 2 8) (to_nat a) /\
          of_nat_non_opt (to_nat a) = a).
Proof.
  intros. simpl. split.
  - assert (G := to_nat_bounded a).  Lia.lia.
  - unfold of_nat_non_opt. rewrite of_to_nat. auto.
Qed.

Lemma byte_format_helper2 : (forall a' : nat,
        (fun z : nat => z < Nat.pow 2 8) a' ->
        (fun _ : byte => True) (of_nat_non_opt a') /\
          to_nat (of_nat_non_opt a') = a').
Proof.
  intros. simpl. simpl in *. split; auto.
  unfold of_nat_non_opt.
  destruct  (of_nat a') eqn:E.
  - erewrite to_of_nat. eauto. auto.
  - rewrite of_nat_None_iff in E. Lia.lia.
Qed.
    
Definition byte_format : T_Format Byte.byte (fun _ => True) :=
  proj_format
    (fun b : byte => True)
    (basic_n_bit_format 8 eight_le_max_len)
    to_nat
    of_nat_non_opt
    byte_format_helper1
    byte_format_helper2
    (fun _ => left I). 
    

Definition byte_list_format (n : nat)
  := list_format byte_format n.
