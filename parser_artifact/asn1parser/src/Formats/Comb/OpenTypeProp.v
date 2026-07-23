Require Import
          ASN1Parser.Array.ByteBuffer
          ASN1Parser.Array.ByteBufferProp.

Require Import
  ASN1Parser.Formats.Comb.SeqProd
  ASN1Parser.Formats.Comb.Seq
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombProp
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Comb.OpenType
  ASN1Parser.Formats.Comb.HelperComb.

Require Import ASN1Parser.tact
  Coq.Logic.ProofIrrelevance
  Lia.

(* We will consider open_type encoding first *)
Lemma open_type_non_inter {A : Set} {Pr : A -> Prop}
  (ser : Serialize A Pr)
  (get_len : A -> option nat)
  (ser_ni : encode_non_inter _ _ ser)
  : encode_non_inter _ _ (open_typ_serialize ser get_len).
Proof.
  unfold encode_non_inter. intros.
  unfold open_typ_serialize, opt_bind in H.
  repeat destruct_enc.
  destruct_if_in_new. destruct_enc. 
  inversion H; subst. clear_redu_all.

  (*
        |- len -|- encoding -|- buffers
    bf   b       b0           bf'

   *)
  
  eapply append_non_inter_proof_helper.
  - unfold det_enc in E0.
    eassert (G := T_Correct _ _  LengthDet.uncons_len_det_format).
    eapply (fmt_enc_ni G). apply E0. 

  - eapply append_non_inter_proof_helper.
    + eapply ser_ni. apply E1.
    + (* Here, put-n-nat might be good or bad *)
      unfold put_n_nat in E3. 
      destruct_if_in_new.  
      eapply ByteBufferProp.BPP.put_n_bits_non_inter.
      apply E3. 
Qed.

Lemma open_type_encode_consist {A : Set} {Pr : A -> Prop}
  (ser : Serialize A Pr)
  (get_len : A -> option nat)
  (ser_cst : encode_consistent _ _ ser)
  (ser_ni : encode_non_inter _ _ ser)
  : encode_consistent _ _ (open_typ_serialize ser get_len).
Proof.
  unfold encode_consistent. intros.
  unfold open_typ_serialize, opt_bind in *.
  repeat destruct_enc. repeat destruct_if_in_new.
  repeat destruct_enc. 
  inversion H. inversion H0. subst. clear_redu_all. 

  unfold put_n_nat in *. destruct_if_in_new. 
  eapply encode_consist_proof_helper.
  - eapply ByteBufferProp.BPP.put_n_bits_consistent.
    + apply E7. 
    + rewrite E6. encode_eq.
  - eapply BPP.put_n_bits_non_inter.
    eauto. 
  - eapply BPP.put_n_bits_non_inter. 
    eauto. 
  - eapply encode_consist_proof_helper.
    + eapply ser_cst. 
      * apply E3. 
      * rewrite E1. encode_eq.
    + eapply ser_ni. apply E3.
    + eapply ser_ni. apply E1.
    + unfold det_enc in *.
      assert (G := T_Correct _ _  LengthDet.uncons_len_det_format).
      eapply (fmt_enc_consist G).
      * apply E2.
      * rewrite E0. encode_eq. 
Qed.

Lemma skip_some_bits_consist (n : nat) :
  decode_consistent _ _ (skip_some_bits n).
Proof.
  unfold decode_consistent.  intros.  unfold skip_some_bits in *.
  destruct (Compare_dec.le_dec n 48).
  - assert (G := fmt_dec_consist (BPP.basic_n_bit_format_correct n l)).
    apply G. apply H. 
  - unfold fail_parse in *.  inversion H.
Qed.

Require Import ASN1Parser.Array.BitRep.

Lemma open_type_decode_consist {A : Set} {Pr : A -> Prop}
  (par : Parse A Pr)
  (par_cst : decode_consistent _ _ par)
  : decode_consistent _ _ (open_typ_parse par).
Proof.
  unfold decode_consistent. intros.
  unfold open_typ_parse, bind_parse, return_parse in *.
  repeat (destruct_enc).
  destruct_if_in_new. 
  destruct_enc.  destruct x1.
  shelve.
  simpl in H. unfold fail_parse in H. inversion H.
  Unshelve.
  rewrite PeanoNat.Nat.eqb_refl in H. inversion H. subst. 
  
  clear_redu_all.

  unfold det_dec in *.
  eassert (G1 := fmt_dec_consist (T_Correct _ _ LengthDet.uncons_len_det_format)
                   _ _ _ _ _ _ E).
  eassert (G2 := par_cst _ _ _ _ _ _ E0).
  eassert (G3 := skip_some_bits_consist _ _ _ _ _ _ _ E2).

  split_and.
  assert (LE := BProp.le_pos_trans _ _ _ H2 H0).
  
  split.
  - eapply BProp.le_pos_trans.
    + apply H4.
    + auto.
  - intros.
    destruct (EQ.equiv_b_split H6 p H4 LE).
    split_and.
    rewrite (H5 _ _ _ H9).

    destruct (EQ.equiv_b_split H11 _ H2 H0).
    split_and.
    rewrite (H3 _ _ _ H13).

    assert (S1 := H1 _ _ _ H15).

    (* Now NTS p0 - p = x2 - x0 *)
    eassert (EL := EQ.equiv_b_eq_len H13).
    unfold BProp.pos_to_len in EL.
    rewrite <- EL, E1, S1.
    rewrite PeanoNat.Nat.eqb_refl. 
    decode_eq.
Qed.

(* Open type surj. We need some good property on get_len.
   That is if the encoding works, then get_len should be
   the same length. 
 *)
Lemma open_type_surj {A : Set} {Pr : A -> Prop}
  (ser : Serialize A Pr)
  (par : Parse A Pr)
  (get_len : A -> option nat)
  (par_cs : format_correct_surj _ _ ser par)
  (gl_crt : format_to_len_correct _ _ ser par get_len)
  (ser_ni : encode_non_inter _ _ ser)
  (par_dc : decode_consistent _ _ par)
  : format_correct_surj _ _ (open_typ_serialize ser get_len) (open_typ_parse par).
Proof.
  unfold format_correct_surj. intros.
  unfold open_typ_serialize, opt_bind in H.
  repeat destruct_enc. destruct_if_in_new. destruct_enc. 
  inversion H. subst. clear_redu_all. 

  unfold open_typ_parse.
  assert (PN := E3). 
  unfold put_n_nat in E3. 
  destruct_if_in_new. 
  
  (*
    Again we have

        |- len -|- encoding -|- buffers -|
        bf      b            b0          bf'

        pos     p            p0          pos'
   *)
  unfold det_enc in E0. 
  eassert (G1 := fmt_surj (T_Correct _ _ LengthDet.uncons_len_det_format) _ _ _ _ _ _ E0).
  
  eassert (EB1 := BPP.put_n_bits_non_inter _  _ _ _ _ _ _ E3).
  eassert (EB2 := ser_ni _ _ _ _ _ _ E1).
  
  destruct (fmt_dec_consist (T_Correct _ _ LengthDet.uncons_len_det_format)  _ _ _ _ _ _ G1).
  split_and.

  assert (EQ.equiv_b b bf' pos p pos p).
  { eapply EQ.equiv_b_trans.
    - eapply equiv_b_le_zero; eauto. 
    - eapply EQ.equiv_b_le;
        try (apply H2); try (apply BProp.pos_zero_le_all); auto. 
  }   
  
  eassert (G2 := H0 bf' pos p H5).
  unfold det_dec. rewrite G2. 

  eassert (G3 := par_cs _ _ _ _ _ _ E1). 
  destruct (par_dc _ _ _ _ _ _ G3 ). clear H8. 
  assert (EQ.equiv_b b0 bf' p p0 p p0).
  { eapply equiv_b_le_zero; eauto. } 
  eassert (G4 := H9 bf' p p0 H8).
  rewrite G4.

  eassert (LC := proj1 gl_crt _ _ _ _ _ _ E1).
  rewrite E in LC. inversion LC.
  rewrite <- H11 in *.
  
  rewrite PeanoNat.Nat.eqb_refl. unfold bind_parse, return_parse.
  unfold skip_some_bits.
  unfold get_remaining_bits in E4.
  rewrite PeanoNat.Nat.leb_le in E4. 
  
  destruct (Compare_dec.le_dec (get_byte_len n * 8 - n) 48); try Lia.lia.
  
  eassert (G5 := fmt_surj (BPP.basic_n_bit_format_correct (get_byte_len n * 8 - n) l1)).
  eassert (G6 := G5 _ _ _ _ _ _ PN).
  rewrite G6.  rewrite PeanoNat.Nat.eqb_refl. 
  decode_eq.
Qed. 

Ltac destruct_match_dec_fun :=
  match goal with
  | [ H : context[ match ?X with
                   | left _ => _
                   | right _  => _
                   end _ _  = Some _ ] |- _ ] =>
      let E := fresh "E" in 
      destruct X eqn:E
  end. 

(*Lemma serialize_T_same_len {A : Set} {P : A -> Prop}
                           (s : AbsFormat.Format A P)
  : forall {a : A} {bf bf' : BA.Buffer} {pos pos' : BA.Pos} {pf : P a},
    (Serialize_T s) bf pos a = Some (bf', pos', pf) ->
    BA.len bf = BA.len bf'.
Proof.
  intros. eapply FCP.same_len_after_enc.
  - apply CT.basic_encode_non_inter.
  - apply H.
Qed.
 *)

Lemma open_type_inj_same {A : Set} {Pr : A -> Prop}
  (ser : Serialize A Pr)
  (par : Parse A Pr)
  (get_len : A -> option nat)
  (par_cs : format_correct_inj_same _ _ ser par)
  (gl_crt : format_to_len_correct _ _ ser par get_len)
  (ser_ni : encode_non_inter _ _ ser)
(*  (par_dc : decode_consistent _ _ par) *)
  : format_correct_inj_same _ _
      (open_typ_serialize ser get_len) (open_typ_parse par).
Proof.
  unfold format_correct_inj_same. intros.
  unfold open_typ_parse, bind_parse, return_parse,
    skip_some_bits, fail_parse in H.
  repeat destruct_enc. destruct_if_in_new.
  destruct_enc. destruct_match_dec_fun. 
  shelve.
  (* First rid of the incorrect case *)
  inversion E2.
  Unshelve. 
  destruct x1.
  shelve.
  simpl in H. inversion H.
  Unshelve. 
  rewrite PeanoNat.Nat.eqb_refl in H.
  inversion H. subst. 
  
  unfold open_typ_serialize, opt_bind.

  destruct (par_cs _ _ _ _ _ E0 bf0 H0).
  split_and.
  eassert (L1 :=  proj1 gl_crt _ _ _ _ _ _ H2).
  rewrite L1. 

  unfold det_dec in E. unfold det_enc.
  (* Need to add 'same ver' proof for det *)
  rewrite (LengthDet.det_SameVer _ _ _ _ _ _ E) in E.
  
  destruct (fmt_inj_same (T_Correct _ _ LengthDet.uncons_len_det_format)
                    _ _ _ _ _ E bf0 H0).
  split_and.
  rewrite PeanoNat.Nat.eqb_eq in E1. subst.
  rewrite H4.

  eassert (BA.len x1 = BA.len bf). 
  { eassert (G := same_len_after_enc _ 
                    (fmt_enc_ni (T_Correct _ _ LengthDet.uncons_len_det_format)) H4).
    Lia.lia. }
  
  destruct (par_cs _ _ _ _ _ E0 x1 H1). split_and.
  rewrite H7, PeanoNat.Nat.eqb_refl. 

  assert (BA.len x = BA.len bf).
  { assert (BA.len x1 = BA.len x).
    eapply same_len_after_enc.
    - apply ser_ni.
    - apply H7.
    - Lia.lia. } 

  rewrite (SameVerProp.basic_bit_SameVer _ _ _ _ _ _ _ E2) in E2.
  
  destruct (fmt_inj_same
                  (BPP.basic_n_bit_format_correct
                     (get_byte_len (BA.to_nat p0 - BA.to_nat p) * 8 -
                        (BA.to_nat p0 - BA.to_nat p)) l1)
                 _ _ _ _ _ E2 x H6).  split_and.
  simpl in H10.
  
  unfold get_remaining_bits. 
  rewrite H10.
  exists x2. split.
  - encode_eq.
  - eassert (G := fmt_enc_ni
                      (BPP.basic_n_bit_format_correct
                         (get_byte_len (BA.to_nat p0 - BA.to_nat p) * 8 -
                            (BA.to_nat p0 - BA.to_nat p)) l1) _ _ _ _ _ _
                      H10).
    split_and.
    eapply format_correct_inj_helper with (b:=x). 
    + eapply format_correct_inj_helper with (b:=x1).
      { apply H5. }
      { apply H8. }
      { eapply ser_ni. apply H7. }
    + apply H11.
    + apply H9.
Qed.

Require Import ASN1Parser.Formats.ValidEncProp.

Lemma get_remaining_bits_le_INT_MAX n : get_remaining_bits n <= INT_MAX_LEN.
Proof.
  unfold get_remaining_bits, INT_MAX_LEN, get_byte_len.
  assert (G := PeanoNat.Nat.div_mod_eq (n + 7) 8). lia.
Qed.

Lemma get_byte_len_le_n n : n <= get_byte_len n * 8.
  unfold get_byte_len.
  apply BPP.div_plus_one.
Qed.

Lemma zero_le_pow2 n : 0 < Nat.pow 2 n.
  assert (G := PeanoNat.Nat.pow_nonzero 2 n).
  lia.
Qed.


(* We didn't use implication form because now it is easier to deal with in proofs. 
   And note that this can be easily be transformed into implication through
   applying Decidable.imp_simp

   Correctness of get-len? Should we make sure that decode correctly 
   implies get-len returns Some
 *)

(* This is difficult because the length might be subject to change
   during decoding. 
 *)
Lemma open_type_inj_diff {A : Set} {Pr : A -> Prop}
  (ser : Serialize A Pr)
  (par : Parse A Pr)
  (get_len : A -> option nat)
  (par_cs : format_correct_inj_diff _ _ ser par get_len)
  (gl_crt : format_to_len_correct _ _ ser par get_len)
  (ser_ni : encode_non_inter _ _ ser)
(*  (par_dc : decode_consistent _ _ par) *)
  : format_correct_inj_diff  _ _ 
      (open_typ_serialize ser get_len) (open_typ_parse par) (open_type_to_len get_len).
Proof.
  unfold format_correct_inj_diff. intros.
   unfold open_typ_parse, bind_parse, return_parse,
    skip_some_bits, fail_parse in H.
  repeat destruct_enc. destruct_if_in_new.
  destruct_enc. destruct_match_dec_fun. 
  shelve.
  (* First rid of the incorrect case *)
  inversion E2.
  Unshelve. 
  destruct x1.
  shelve.
  simpl in H. inversion H.
  Unshelve. 
  rewrite PeanoNat.Nat.eqb_refl in H.
  inversion H. subst.

  unfold open_typ_serialize, opt_bind.

  (* Here, get-len is set to give a Some matching, however, 
     we can defer the argument later
   *)
  destruct (get_len a) eqn:El.
  - destruct uncons_len_valid_enc.

  (*destruct (fmt_inj_diff (T_Correct _ _ LengthDet.uncons_len_det_format)
              _ _ _ _ _ _ E). *)
    destruct (par_cs _ _ _ _ _ _ E0).
    
    destruct (put_n_nat_valid (get_remaining_bits n) (get_remaining_bits_le_INT_MAX n)).

    exists (x0 + x1 + x2). intros.
    
    assert (BA.to_nat pos0 + x0 <= BA.len bf0). { lia. } 

    destruct (Compare_dec.lt_dec (get_byte_len n) (Nat.pow 2 14)).
    + eassert (K1 := H0 _ _ (get_byte_len n) l2 H4). 

      destruct_ex. split_and. subst. right.
      unfold det_enc. 
      rewrite H6. 

      assert (L0 : BA.len bf0 = BA.len x3).
      { apply (same_len_after_enc _
                 (fmt_enc_ni (T_Correct _ _ LengthDet.uncons_len_det_format)) H6). }
      assert (BA.to_nat x4 + x1 <= BA.len x3). { lia. }

      eassert (K2 := H1 _ _ H5).
      destruct K2.
      { rewrite El in H8. destruct (H8 l2). }
      destruct_ex. split_and. 
      rewrite H9.

      eassert (En := (proj1 gl_crt) _ _ _ _ _ _ H9). rewrite El in En.  inversion En.
      rewrite PeanoNat.Nat.eqb_refl.

      assert (L1 : BA.len x3 = BA.len x5).
      { apply (same_len_after_enc _ ser_ni H9). }
      assert (BA.to_nat x6 + x2 <= BA.len x5). { lia. }
      eassert (K3 := H2 _ _ 0 (zero_le_pow2 _ ) H8).
      subst.
      destruct_ex. split_and.
      rewrite H12. exists x7. exists x8.
      split.
      * encode_eq.
      * lia. 
      
    + (* Consider the wrong case first *)
      (* I can directly derive it from n0 *)
      left.
      unfold open_type_to_len.
      rewrite El. unfold opt_bind.  Opaque Nat.pow.  simpl.

      assert (G1 := get_byte_len_le_n n).
      assert (n <= S
                    ((if
                         fst
                           (if Nat.ltb (get_byte_len n) (Nat.pow 2 7)
                            then (false, get_byte_len n)
                            else (true, get_byte_len n))
                       then 15
                       else 7) + get_byte_len n * 8)).
      { lia. }
      apply get_byte_len_mono in H5. 
      lia. 
  - eassert (G' := (proj2 gl_crt) _ _ _ _ _ _ E0).
    destruct G'. rewrite El in H0.  inversion H0. 
Qed.

(*Eval compute in (fun n => Nat.eqb (get_remaining_bits n + n) (get_byte_len n * 8)) 3. *)

Lemma get_remaining_plus_n_eq_byte_len (n : nat) :
  get_remaining_bits n + n = get_byte_len n * 8.
Proof. 
  unfold get_remaining_bits, get_byte_len.
  assert (G := BPP.div_plus_one 7 n). lia.
Qed.

Lemma open_type_to_len_correct {A : Set} {P : A -> Prop}
  (ser : Serialize A P)
  (par : Parse A P)
  (tl : A -> option nat)
  (ser_ni : encode_non_inter _ _ ser)
  : format_to_len_correct _ _ ser par tl ->
    format_to_len_correct _ _
      (open_typ_serialize ser tl)
      (open_typ_parse par)
      (open_type_to_len tl).
Proof.
  intros.
  unfold format_to_len_correct.
  split.
  - intros. destruct H as [H H'].
    unfold open_typ_serialize, opt_bind in H0.
    repeat destruct_enc.
    destruct_if_in_new. destruct_enc. inversion H0. subst. clear H0.

    unfold open_type_to_len. unfold opt_bind.  rewrite E. 

    eassert (G := proj1 (fmt_len_c (T_Correct _ _ LengthDet.uncons_len_det_format))
                    _ _ _ _ _ _ E0).
    rewrite G.  f_equal.  

    (* ser correct *)
    eassert (S1 := H _ _ _ _ _ _ E1). rewrite E in S1.
    inversion S1.

    (* put-n-nat put those remaining bits here *)
    eassert (S2 := proj1 (fmt_len_c (BPP.basic_n_bit_format_correct
                                       (get_remaining_bits n)
                                       ( get_remaining_bits_le_INT_MAX n)))
                     _ _ _ _ _ _ E3).
    
    unfold n_nat_to_len in S2. inversion S2. 

    assert (EN := get_remaining_plus_n_eq_byte_len n). subst.
    clear S2.  clear S1.
    rewrite <- EN.  rewrite H2.

    (* Now, i just need to show that positions have a right order *)
    
    eassert (P1 := fmt_enc_ni (T_Correct _ _ LengthDet.uncons_len_det_format)
                     _ _ _ _ _ _ E0). 
    eassert (P2 := fmt_enc_ni (BPP.basic_n_bit_format_correct
                                 (get_remaining_bits  (BA.to_nat p0 - BA.to_nat p))
                                 ( get_remaining_bits_le_INT_MAX  (BA.to_nat p0 - BA.to_nat p)))
                     _ _ _ _ _ _ E3).
    eassert (P3 := ser_ni _ _ _ _ _ _ E1).
    split_and. unfold BProp.le_pos in *.  lia.
  - intros. unfold open_typ_parse, bind_parse, return_parse in H0. 
    repeat destruct_enc. destruct_if_in_new.
    destruct_enc. destruct (Nat.eqb x1 0) eqn:Ex1.
    { inversion H0. subst. clear H0.
      unfold open_type_to_len.  unfold opt_bind.

      destruct H as [H' H].
      eassert (G := H _ _ _ _ _ _ E0). destruct_ex.
      rewrite H0.  simpl.
      eauto. }

    { (* fail_parse case *)
      unfold fail_parse in H0.  inversion H0. }
Qed.

