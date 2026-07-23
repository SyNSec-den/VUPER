Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombProp
  ASN1Parser.Array.BitRep
  ASN1Parser.Formats.Term.Unit
  ASN1Parser.Formats.Comb.ListFormat
(*  ASN1Parser.Formats.Comb.HelperProp *)
  ASN1Parser.tact.

Require Import Lia. 

Ltac inv_len H := simpl in H;
                  let pf1 := fresh "pf" in
                  let pf2 := fresh "pf" in
                  destruct H as [pf1 pf2];
                  inversion pf2.

(* We will first prove properties of list_serial and list_parse *)
Lemma list_non_inter
  {A : Set} {P : A -> Prop}
  (ser : Serialize A P) (n : nat)
  (ser_ni : encode_non_inter _ _ ser)
  :  encode_non_inter _ _ (list_serial ser n).
Proof.
  induction n;
    unfold encode_non_inter; intros.
  - destruct a.
    + simpl in H. unfold put_fixed_item in H.
      destruct_enc.
      inversion H. subst. 
      eapply put_unit_non_inter.
      apply E.
    + inv_len pf. 
  - destruct a.
    + inv_len pf. 
    + simpl in H.
      repeat (destruct_enc).
      inversion H. subst. clear H.
      eapply append_non_inter_proof_helper.
      * eapply ser_ni.
        apply E.
      * eapply IHn.
        apply E0.
Qed.

Lemma list_encode_consist
  {A : Set} {P : A -> Prop}
  (ser : Serialize A P) (n : nat)
  (ser_ni : encode_non_inter _ _ ser)
  (ser_ec : encode_consistent _ _ ser)
  :  encode_consistent _ _ (list_serial ser n).
Proof.
  induction n; unfold encode_consistent; intros.
  - destruct a.
    + simpl in H, H0. unfold put_fixed_item in *.
      repeat destruct_enc.
      inversion H. inversion H0. subst. 
      eapply put_unit_consist.
      * apply E0.
      * rewrite E. encode_eq.
    + inv_len pf. 
  - destruct a.
    + inv_len pf.
    + simpl in H, H0.
      repeat destruct_enc. inversion H. inversion H0.
      subst.
      eapply encode_consist_proof_helper.
      * eapply IHn.
        { apply E2. }
        { rewrite E0. encode_eq. }
      * eapply (list_non_inter ser n ser_ni).
        apply E2.
      * eapply (list_non_inter ser n ser_ni).
        apply E0.
      * eapply ser_ec.
        { apply E1. }
        { rewrite E. encode_eq. }
Qed.

Lemma list_decode_consist
  {A : Set} {P : A -> Prop}
  (par : Parse A P) (n : nat)
  (par_dc : decode_consistent _ _ par)
  :  decode_consistent _ _ (list_parse par n).
Proof.
  induction n; unfold decode_consistent; intros.
  - destruct a.
    + simpl in *. unfold read_fixed_item in *.
      destruct_enc.  inversion H.  subst. destruct s, x, t. 
      apply read_unit_consist in E. split_and.
      split; auto. 
      intros.  apply H1 in H4.
      rewrite H4. decode_eq. 
    + inv_len pf.
  - destruct a.
    + inv_len pf.
    + simpl in H.
      apply bind_parse_consist; auto; intros.
      apply bind_parse_consist.
      * apply IHn.
      * intros.  apply return_parse_consist.
Qed.
      
Lemma list_surj
  {A : Set} {P : A -> Prop}
  (ser : Serialize A P)
  (par : Parse A P) (n : nat)
  (ser_ni : encode_non_inter _ _ ser)
  (par_dc : decode_consistent _ _ par)
  (fmt_sur : format_correct_surj _ _ ser par)
  : format_correct_surj _ _ (list_serial ser n) (list_parse par n).
Proof.
  induction n; unfold format_correct_surj; intros.
  - destruct a.
    + simpl in *. unfold put_fixed_item in H. 
      destruct_enc. inversion H. subst. destruct t.
      unfold read_fixed_item.
      apply unit_format_surj in E.
      rewrite E. decode_eq.
    + inv_len pf.
  - destruct a.
    + inv_len pf.
    + simpl. simpl in H.
      repeat destruct_enc. inversion H. subst. 
      unfold bind_parse, return_parse.

      (*
        ser   |  (list ser)  |
        bf    b              bf'
       *)
      
      eassert (G := fmt_sur _ _ _ _ _ _ E).
      eassert (EN := list_non_inter ser n ser_ni _ _ _ _ _ _ E0).
      eassert (DC := par_dc _ _ _ _ _ _ G).
      
      split_and. unfold BProp.le_pos in H0.
      eassert (EB := equiv_b_le_zero _ _ pos _ H0 H2).
      apply H1 in EB.  rewrite EB. 

      eassert (G1 := IHn _ _ _ _ _ _ E0).
      rewrite G1.
      decode_eq.
Qed.

Lemma list_inj_same
  {A : Set} {P : A -> Prop}
  (ser : Serialize A P)
  (par : Parse A P) (n : nat)
  (ser_ni : encode_non_inter _ _ ser)
  (fmt_inj : format_correct_inj_same _ _ ser par)
  : format_correct_inj_same _ _ (list_serial ser n) (list_parse par n).
Proof.
  induction n; unfold format_correct_inj_same; intros. 
  - destruct a.
    + simpl in H. unfold read_fixed_item in H.
      destruct_enc. destruct s, x, t.
      eassert (SV := read_unit_SameVer _ _ _ _ _ E). subst.
      apply unit_format_inj in E.
      apply E in H0.  simpl.
      destruct H0, H0.  
      unfold put_fixed_item. rewrite H0.  
      apply put_unit_pos_no_change in H0. destruct H0. 
      inversion H. subst. 
      exists x. 
      split.
      * encode_eq.
      * auto. 
    + inv_len pf.
  - destruct a.
    + inv_len pf.
    + simpl in H. simpl.
      unfold bind_parse, return_parse in H.
      repeat destruct_enc.
      inversion H.  subst. 
      apply  flg_add_to_same in H5. destruct H5.
      subst. clear H. 
      
      eassert (G1 := fmt_inj _ _ _ _ _ E bf0 H0).
      destruct G1. split_and.
      rewrite H1.
      (* 
       bf -- x -- bf0'?

       NTS len x = len bf
       *)
      eassert (EL := same_len_after_enc _ ser_ni H1).
      apply eq_sym in EL. rewrite H0 in EL. 
      eassert (G2 := IHn _ _ _ _ _ E0 x EL).
      destruct G2. split_and.  
      rewrite H7.  exists x0. split.
      * encode_eq.
      * eapply format_correct_inj_helper.
        { apply H2. }
        { auto. }
        { eapply list_non_inter.
          - apply ser_ni.
          - apply H7. }
Qed.

Lemma list_to_len_correct
  {A : Set} {P : A -> Prop}
  (ser : Serialize A P)
  (par : Parse A P)
  (a_to_len : A -> option nat) (n : nat)
  (ser_ni : encode_non_inter _ _ ser)
  : format_to_len_correct _ _ ser par a_to_len -> 
    format_to_len_correct _ _ (list_serial ser n) (list_parse par n) (list_to_len a_to_len n).
Proof.
  intros. induction n.
  - intros. unfold format_to_len_correct. split.
    + simpl in *. destruct a; intros. 
      * unfold put_fixed_item in H0. 
        destruct_enc.  inversion H0. subst.
        destruct t. 
        apply put_unit_pos_no_change in E. split_and.  subst.
        f_equal. rewrite PeanoNat.Nat.sub_diag. reflexivity.
      * inversion H0.
    + intros. simpl.  simpl in H0.
      destruct a.
      * exists 0. auto.
      * simpl in pf. split_and.
        lia.
  - unfold format_to_len_correct in *.
    split_and. split; intros. 
    + simpl in H. destruct a.
      * inversion H.  
      * destruct_enc. destruct_enc.  inversion H. subst.
        simpl.
        
        eassert (L1 := ser_ni _ _ _ _ _ _ E).
        eassert (L2 := list_non_inter ser n ser_ni _ _ _ _ _ _ E0).
        split_and.
        
        unfold BProp.le_pos in H7, H4. 

        apply H2 in E. apply H0 in E0. rewrite E, E0.
        unfold add_opt. f_equal. unfold BProp.le_pos in H10. lia.
    + destruct a.
      * split_and. simpl in H5. lia.
      * simpl. simpl in H. unfold bind_parse, return_parse in H.
        repeat destruct_enc. inversion H. subst. clear H.

        apply H3 in E. apply H1 in E0. destruct_ex.
        rewrite H4. rewrite H. simpl. exists (x0 + x). auto. 
Qed.

Opaque Nat.pow. 
Lemma list_inj_diff
  {A : Set} {P : A -> Prop}
  (ser : Serialize A P)
  (par : Parse A P)
  (to_len : A -> option nat) 
  (n : nat)
  (ser_ni : encode_non_inter _ _ ser)
  (*  (ser_ec : encode_consistent _ _ ser) *)
  (tl_crt : format_to_len_correct _ _ ser par to_len)
  (fmt_inj : format_correct_inj_diff _ _ ser par to_len )
  : format_correct_inj_diff _ _ (list_serial ser n) (list_parse par n)
      (list_to_len to_len n).
Proof.
  induction n; unfold format_correct_inj_diff; intros.
  - destruct a.
    + exists (BA.len bf). intros.
      simpl in H.  unfold read_fixed_item in H.
      destruct_enc.  inversion H. subst. clear H.
      destruct s, x, t.
      simpl.  unfold put_fixed_item.
      eassert (SV := read_unit_SameVer _ _ _ _ _ E). subst.

      unfold put_unit.
      assert (L1 : BA.to_nat pos0 <= BA.len bf0).
      { lia. } 
      right. 
      destruct_match_goal; destruct_if_in_new; 
      inversion E0; subst.
      * exists bf0. exists pos0.
        split.
        { encode_eq. }
        { lia. }
      * lia. 
    + inv_len pf.
  - destruct a.
    + inv_len pf.
    + simpl in H.  unfold bind_parse, return_parse in H.
      repeat destruct_enc. inversion H.  subst. clear H. 
      eassert (G1 := fmt_inj _ _ _ _ _ _ E). 
      eassert (G2 := IHn _ _ _ _ _ _ E0). 
      simpl. 
      destruct_ex.  exists (x0 + x).  intros.
 
      assert (BA.to_nat pos0 + x0 <= BA.len bf0). { lia. }
      assert (B1 := H0 _ _  H2).

      eassert (K1 := (proj2 tl_crt) _ _ _ _ _ _ E ). 
      eassert (K2 := (proj2 (list_to_len_correct _ _ _ _ ser_ni tl_crt))
                       _ _ _ _ _ _ E0).
      destruct_ex. rewrite H4, H3. simpl.
      
      destruct B1.
      { left.  rewrite H4 in H5.
        assert (x2 <= x2 + x1). { lia. }
        apply get_byte_len_mono in H6. lia. } 
                
      destruct_ex. split_and.
      rewrite H6.

      eassert (EL := same_len_after_enc ser ser_ni H6). 
      assert (BA.to_nat x4 + x <= BA.len x3). { lia. }
      eassert (B2 := H _ _ H11).
      destruct B2.
      { left. rewrite H3 in H12. 
        assert (x1 <= x2 + x1). { lia. }
        apply get_byte_len_mono in H13. lia. } 
                
      destruct_ex. split_and. 
      rewrite H13. 

      right. 
      exists x5. exists x6. 
      split.
      * encode_eq.
      * lia. 
Qed.


Lemma list_format_correct {A : Set} {P : A -> Prop} 
  (fmt : T_Format A P) (n : nat)
  : format_correct (list_serial (T_Serial A P fmt) n)
      (list_parse (T_Parse A P fmt) n) (list_to_len (T_to_len A P fmt) n).
Proof.
  intros. destruct fmt. simpl. unfold format_correct in *.  split_and.
  split.
  { apply list_encode_consist; auto. } split.
  { apply list_decode_consist; auto. } split.
  { apply list_non_inter; auto. } split.
  { apply list_surj; auto. } split.
  { apply list_inj_same; auto. } split.
  { apply list_inj_diff; auto. }
  apply list_to_len_correct; auto.
Qed.

Definition list_format {A : Set} {P : A -> Prop} 
  (fmt : T_Format A P) (n : nat)
  : T_Format (list A) (fun la => list_and P la /\ length la = n) :=
  mk_format (list A) (fun la => list_and P la /\ length la = n)
    (list_serial (T_Serial _ _ fmt) n)
    (list_parse (T_Parse _ _ fmt) n)
    (list_to_len (T_to_len _ _ fmt) n)
    (list_format_correct fmt n).

