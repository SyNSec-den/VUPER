Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Term.Unit
  ASN1Parser.Array.BitRep
  ASN1Parser.tact
  Lia.

Definition valid_enc_if {A : Set} {P : A -> Prop} (ser : Serialize A P) :=
  exists min_len,
  forall pos bf a pf_a,
    BA.to_nat pos + min_len <= BA.len bf ->
    (exists bf' pos',  ser bf pos a = Some (bf', pos', pf_a) /\
       BA.to_nat pos' <= BA.to_nat pos + min_len).

Lemma put_n_nat_valid n (pf_n : n <= 48):
  valid_enc_if (ByteBuffer.put_n_nat n).
Proof.
  unfold valid_enc_if. intros. 
  exists (n + 7). intros.
  unfold ByteBuffer.put_n_nat.
  rewrite <- PeanoNat.Nat.leb_le in pf_n.
  rewrite pf_n.
  rewrite PeanoNat.Nat.add_assoc in H. 
  eassert (G := ByteBufferProp.BPP.put_n_bits_valid_if
                  n _ _ _ pf_a H ).
  apply G.   
Qed.

Lemma proj_valid_enc
   {A B : Set} {P2 : B -> Prop} {P1 : A -> Prop}
   (b_ser : Serialize B P2) (f : A -> B)
   (imp : forall a : A, P1 a -> P2 (f a))
   (dec_a : dec_P P1):
  valid_enc_if b_ser -> 
  valid_enc_if (proj_serialize b_ser f dec_a).
Proof.
  intros. unfold valid_enc_if in *.  destruct_ex. 
  exists x. intros. eassert (G := H _ _ (f a) (imp a pf_a) H0).
  destruct_ex. split_and.
  exists x0. exists x1.
  unfold proj_serialize.
  destruct (dec_a a).
  - rewrite H2.  split.
    + encode_eq.
    + lia.
  - destruct (n pf_a). 
Qed.

Lemma restrict_valid_enc
  {A : Set} {P R : A -> Prop}
  (ser : Serialize A P)  (r_dec : dec_P R)
  (imp : forall a : A, R a -> P a) : 
  valid_enc_if ser -> 
  valid_enc_if (restrict_serialize r_dec ser).
Proof.
  intros. unfold valid_enc_if, restrict_serialize in *.
  destruct_ex. exists x. intros. 
  eassert (G := H _ _ a (imp a pf_a) H0). destruct_ex. split_and. 
  destruct (r_dec a).
  - rewrite H2.  exists x0. exists x1.
    split.
    +  encode_eq. 
    + lia.
  - destruct (n pf_a). 
Qed.

Lemma unit_valid_enc_if : valid_enc_if put_unit.
  unfold valid_enc_if.
  exists 0. intros.
  exists bf, pos.

  unfold put_unit.
  destruct_if_goal; try lia.
  split.
  - encode_eq.
  - lia. 
Qed.

Require Import ASN1Parser.Formats.Term.LengthDet.
(* The first term of sigma needs to be boolean *)
Lemma bool_valid_enc : valid_enc_if (T_Serial _ _ Boolean.bool_format).
Proof.
  simpl.  apply proj_valid_enc.
  - intros. destruct a; lia.
  - apply (put_n_nat_valid 1).
    lia.
Qed.

Lemma sigma_valid_enc
  {B : Set} 
  (P2 : bool -> B -> Prop)
  (pser2 : forall a : bool, True ->  Serialize B (P2 a)) :
  (forall a, valid_enc_if (pser2 a I)) -> 
  valid_enc_if (sigma_serialize (T_Serial _ _ Boolean.bool_format) P2 pser2).
Proof. 
  unfold valid_enc_if. intros.
  assert (G1 := H true). 
  assert (G2 := H false).  destruct_ex.

  (* Also we need to consider the bool encoding itself *)
  destruct (bool_valid_enc). 
  exists (x0 + x + x1). intros. 
  
  unfold sigma_serialize. destruct a.
  assert (BA.to_nat pos + x1 <= BA.len bf). { lia. } 
  eassert (K1 := H2 _ _ b I H4). destruct_ex. split_and.
  unfold fst, snd in *. 
  rewrite H6.
   eassert (V1 := CombProp.same_len_after_enc _
                     (CombProp.fmt_enc_ni (T_Correct _ _ Boolean.bool_format))
                     H6). 
  destruct b eqn:Eb.
  - assert (BA.to_nat x3 + x0 <= BA.len x2). { lia. } 
    eassert (K2 := H1 _ _ b0 H8 H9).
    destruct_ex. split_and. rewrite H11.
    exists x4. exists x5. split; try encode_eq. lia.
  - assert (BA.to_nat x3 + x <= BA.len x2). { lia. }
    eassert (K1 := H0 _ _ b0 H8 H9).
    destruct_ex. split_and. rewrite H11.
    exists x4. exists x5. split; try encode_eq. lia.
Qed.

Lemma choose_len_valid_enc :   (forall a : bool,
     valid_enc_if
       ((fun (a0 : bool) (_ : True) =>
           T_Serial _ _ (choose_len_det_format a0))  a I)).
Proof.
  intros. destruct a eqn:Ea; 
    unfold choose_len_det_format;
    unfold restrict_format, T_Serial;
    apply restrict_valid_enc.
  - apply (choose_len_det_helper2 true).
  -  apply  put_n_nat_valid. lia.
  - apply (choose_len_det_helper2 false).
  -  apply  put_n_nat_valid. lia.
Qed.

Lemma uncons_len_valid_enc : valid_enc_if (T_Serial _ _ uncons_len_det_format).
  unfold uncons_len_det_format.
  apply proj_valid_enc.
  - intros. apply det_le_helper. auto.
  - unfold bit_len_format. unfold sigma_format.
    unfold T_Serial.

    eassert (G :=  sigma_valid_enc
                     (fun (b : bool) (n : nat) =>
                        if b then Nat.pow 2 7 <= n < Nat.pow 2 14 else n < Nat.pow 2 7)
                     (fun (a : bool) (_ : True) =>
                        (T_Serial _ _ (choose_len_det_format a)))
                     choose_len_valid_enc).
    apply G.
Qed.


Lemma choose_norm_valid_enc :
  (forall a : bool, valid_enc_if
                      ((fun (a0 : bool) (_ : True) =>
                          let (T_Serial, T_Parse, T_to_len, _) :=
                            choose_norm_small_det a0 in
                          T_Serial) a I)).
  unfold choose_norm_small_det.
  destruct a; unfold restrict_format.
  - apply restrict_valid_enc.
    + intros. lia.
    + apply uncons_len_valid_enc.
  - unfold NonNeg.nat_range_format.
    apply proj_valid_enc.
    + apply   (NonNeg.nat_range_helper1 1 64).
    + unfold NonNeg.nat_format.
      apply restrict_valid_enc.
      * apply  (NonNeg.nat_le (64 - 1)).
      * apply put_n_nat_valid.
        simpl. unfold NonNeg.to_bit_sz.  simpl. lia.
Qed.
    
Lemma bit_norm_valid_enc : valid_enc_if (T_Serial _ _ bit_norm_small_len_format).
  unfold bit_norm_small_len_format. 
  (* Here, sigma works because there are only two options for boolean *)
  unfold sigma_format, T_Serial.
  eassert (G :=  sigma_valid_enc
                   (fun (b : bool) (n : nat) =>
                      if b then 65 <= n < Nat.pow 2 14 else 1 <= n <= 64)
                   (fun (a : bool) (_ : True) =>
                      let (T_Serial, T_Parse, T_to_len, _) :=
                        choose_norm_small_det a in
                      T_Serial)
                   choose_norm_valid_enc).
  apply G.
Qed.

Lemma small_det_valid_enc : valid_enc_if small_enc.
  unfold small_enc.

  unfold normally_small_len_det_format.
  apply proj_valid_enc. intros. split; auto.
  - apply norm_small_helper1. auto. 
  - apply bit_norm_valid_enc.
Qed.

(* Now we prove have proved it, test it in OpenType.
   After this, we prove it for bit list. 
 *)

Require Import ASN1Parser.Formats.Term.BoolList. 

Lemma list_and_true (a : list bool) : ListFormat.list_and (fun _ : bool => True) a.
  induction a; simpl; auto. 
Qed.    

Require Import ASN1Parser.Formats.CombProp.

Lemma bool_list_valid_enc n : valid_enc_if (bool_list_serialize n).
  induction n.
  - unfold bool_list_serialize. simpl.
    apply restrict_valid_enc; intros. 
    + destruct a.
      * simpl.  auto.
      * simpl in H. lia.
    + unfold valid_enc_if. exists 0. intros.
      exists bf, pos.
      destruct a.
      * unfold ListFormat.put_fixed_item.
        unfold put_unit.
        destruct (Compare_dec.le_dec (BA.to_nat pos) (BA.len bf)).
        { split.
          - encode_eq.
          - lia. }
        { lia. }
      * simpl in pf_a.  lia.
  - unfold bool_list_serialize.  simpl.
    apply restrict_valid_enc; intros.
    + split; auto. apply list_and_true.
    + unfold valid_enc_if in *.
      assert (1 <= 48). { lia. } 
      assert (K := put_n_nat_valid 1 H).
      destruct K. 
      
      destruct IHn. exists (x + x0). 

      intros. destruct a.
      * simpl in pf_a. lia.
      * unfold proj_serialize.
        assert (BA.to_nat pos + x <= BA.len bf). { lia. }

        assert ((if b then 1 else 0) < Nat.pow 2 1).
        { simpl. destruct b; auto. } 
        eassert (G := H0 _ _ (if b then 1 else 0) H4 H3).
        destruct_ex.  split_and.
        rewrite H6.

        unfold bool_list_serialize in H1.

        eassert (K' := same_len_after_enc _
                         (fmt_enc_ni (ByteBufferProp.BPP.basic_n_bit_format_correct 1 H))
                         H6).

        assert (BA.to_nat x2 + x0 <= BA.len x1).  { lia. }

        simpl in H8. inversion H8. 
        eassert (G' := H1 _ _ a H11 H9).
        destruct_ex. split_and.
        simpl in H12.

        unfold restrict_serialize in H12.
        destruct_match_dec_new. destruct_enc.
        unfold proj_serialize in E0.
        rewrite E0.

        exists b0, p.
        split.
        { encode_eq. }
        { inversion H12. subst.  lia. } 
Qed.

    
