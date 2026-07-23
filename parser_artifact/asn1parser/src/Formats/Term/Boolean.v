
Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  Lia.

(* Here, in Format definitions, we will add some small example using 
   the BitBuffer. 

   Here, le means lemma in the names of the definitions.
 *)

Definition bl_le_1 : forall a : bool,
  True ->
  (if a then 1 else 0) < Nat.pow 2 1 /\
  match (if a then 1 else 0) with
  | 0 => false
  | S _ => true
  end = a.
Proof.
  intros. destruct a; simpl; auto.
Qed.

Definition bl_le_2 : (forall a' : nat,
        (fun z : nat => z < Nat.pow 2 1) a' ->
        (fun _ : bool => True)
          ((fun n : nat => match n with
                           | 0 => false
                           | S _ => true
                           end) a') /\
        (fun b : bool => if b then 1 else 0)
          ((fun n : nat => match n with
                           | 0 => false
                           | S _ => true
                           end) a') = a').
Proof. intros.  simpl. split; auto.
       simpl in H. destruct a'; lia. 
Qed.

Lemma one_le_len : 1 <= INT_MAX_LEN.
Proof.  eapply le_n_S.  apply PeanoNat.Nat.le_0_l. Qed.

Definition zero_le_len : 0 <= INT_MAX_LEN := PeanoNat.Nat.le_0_l INT_MAX_LEN. 

(* Here, I should simply define the parser/serializer using the 
   definitions. We evaluate the formats. 
 *)

Opaque ByteBuffer.put_n_nat ByteBuffer.read_n_nat.
Opaque proj_serialize proj_parse.

Definition bool_format : T_Format bool (fun _ : bool => True) :=
  Eval compute in
    proj_format (fun _ : bool => True)
      (basic_n_bit_format 1 one_le_len)
      (fun b => if b then 1 else 0)
      (fun n : nat => match n with
                      | 0 => false
                      | S _ => true
                      end)
      bl_le_1
      bl_le_2
      (fun _ => left I).

Transparent proj_parse.

Require Import ASN1Parser.tact
  ASN1Parser.Formats.SameVerProp.

Lemma bool_parse_SameVer :
  parse_to_SameVer (T_Parse bool (fun _ : bool => True) bool_format).
Proof.
  apply proj_SameVer. apply (basic_bit_SameVer 1).
Qed.

Lemma bool_format_SameVer : forall a bf pos pos' flg,
  T_Parse bool (fun _ : bool => True) bool_format bf pos = Some (a, pos', flg) -> flg = SameVer.
Proof.
  intros [b pf_b] bf pos pos' flg H.
  exact (bool_parse_SameVer bf pos pos' b pf_b flg H).
Qed.

(* Examples using BitBuffer, we use a module to encapsulate it *)

(*
Require Import ASN1Parser.BitBuffer.

Module bool_example.
  Import Coq.Lists.List.

  Example bool_enc := PT.Serialize_T bool_format.
  Example bool_dec := PT.Parse_T bool_format.

  Example b_test := Eval compute in
      bool_enc (true :: false :: false :: nil) 2 false.
 
  Example b_test_val := Eval compute in
      match b_test with
      | Some (b, p0, _) => bool_dec b 2
      | None => None
      end.

End bool_example.
*)
