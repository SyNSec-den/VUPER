Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombProp
  ASN1Parser.Formats.Comb.SeqProd
  ASN1Parser.Formats.Comb.HelperComb
  ASN1Parser.Formats.Comb.HelperProp
  ASN1Parser.Array.ByteBuffer
  ASN1Parser.Formats.Comb.Choice.

Require Import ASN1Parser.tact
  Lia
  Coq.Logic.ProofIrrelevance.

Lemma get_nth_nil {A : Type} n (dft : A) :
    List.nth n (nil (A:=A)) dft = dft. 
Proof.
  rewrite List.nth_overflow; simpl; auto. 
  apply PeanoNat.Nat.le_0_l.
Qed.

(*Lemma get_nth_serial_overflow (l : list typ)
  (ser : get_serial_prod l)
  (n : nat)
  (lengh_le : length l <= n)  
  : get_nth_serial l ser n = unit_enc.  *)

Definition get_cond_prodc
  (l : list typ)
  (ser : get_serial_prodc l)
  (cond : encode_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a;
      apply (cond _ _ (fst ser) /\ IHl (snd ser)). 
Defined.

Definition get_cond_de_prodc
  (l : list typ)
  (par : get_parse_prodc l)
  (cond : decode_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a;
      apply (cond _ _ (fst par) /\ IHl (snd par)). 
Defined.

Definition get_cond_both_prodc
  (l : list typ)
  (ser : get_serial_prodc l)
  (par : get_parse_prodc l)
  (cond : en_decode_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a. 
    apply (cond _ _ (fst ser) (fst par) /\ IHl (snd ser) (snd par)). 
Defined.

(* The only proposition is format_to_len_correct. *)
Definition get_cond_tl_prodc
  (l : list typ)
  (ser : get_serial_prodc l)
  (par : get_parse_prodc l)
  (tl : get_to_len_prodc l)
  (cond : en_de_tl_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a.
    apply (cond  _ _ (fst ser) (fst par) (fst tl) /\ IHl (snd ser) (snd par) (snd tl)).
Defined.

Lemma get_nth_cond_prod
  (l : list typ) :
  forall (ser : get_serial_prodc l)
         (cond : encode_cond_type)
         (n : nat)
         (length_le : n < length2 l)
         (cond_pf : get_cond_prodc l ser cond),
    cond _ _ (get_nth_serial l ser n).
Proof.
  induction l.
  - intros. inversion length_le. 
    
  - intros. destruct a, ser, cond_pf. 
    simpl in H, H0.
    destruct n.
    (* Case n = 0, which is solved by s *)
    + simpl.  apply H.
      
    (* Case n < length l, which is solved by IHl *)
    + simpl. simpl in length_le.   apply IHl; auto.
      apply le_S_n. auto.
Qed.      


Lemma get_nth_cond_tl_prod
  (l : list typ) :
  forall (ser : get_serial_prodc l)
         (par : get_parse_prodc l)
         (tl : get_to_len_prodc l)
         (cond : en_de_tl_cond_type)
         (n : nat)
         (length_le : n < length2 l)
         (tl_c : get_cond_tl_prodc l ser par tl cond),
    cond _ _ (get_nth_serial l ser n) (get_nth_parse l par n) (get_nth_to_len l tl n).
Proof.
  induction l. 
  - intros. simpl in length_le.  lia.
  - intros. destruct a, ser, par, tl. 

    destruct n.
    + simpl in *. destruct tl_c. assumption.
    + simpl in *. split_and. apply IHl; auto. lia. 
Qed.

Lemma choice_0_non_inter
  (l : list typ) 
  (ser : get_serial_prodc l)
  (non_inter_prod : get_cond_prodc l ser encode_non_inter)
  (n : nat)
  (length_le : n < length2 l)
  : encode_non_inter _ _ (choice_0_serial l ser n). 
Proof.
  unfold encode_non_inter. intros. 
  unfold choice_0_serial, get_nth_serial in H. 

  eassert (G := get_nth_cond_prod l ser _ n length_le
                  non_inter_prod _ _ _ _ _ _ H).
  apply G.
Qed.

(* When length l >= 2 *)
Lemma choice_non_inter_ge2
  (l : list typ)
  (length_l_ge2 : 2 <= length2 l)
  (pf1 : length_cond l)
  (ser : get_serial_prodc l)
  (non_iter_prod : get_cond_prodc l ser encode_non_inter) :
  encode_non_inter _ _  (choice_serial l pf1 ser).
Proof. 
  unfold choice_serial, encode_non_inter.
  intros.
  destruct_match_new. repeat destruct_let.

  assert ( projT1 a < length2 l ). { lia. }
  eassert (G := choice_0_non_inter l ser non_iter_prod (projT1 a) H0
                  _ _ _ _ _ _ H).

  eapply append_non_inter_proof_helper.
  - shelve. 
  - apply G.
    Unshelve. 
    eassert (G1 := T_Correct _ _ (NonNeg.nat_format (length2 l - 1) pf1)).
    unfold format_correct in G1.
    split_and. eapply H2. apply E.
Qed.

Lemma choice_0_encode_consist
  (l : list typ) 
  (ser : get_serial_prodc l)
  (enc_consist_prod : get_cond_prodc l ser encode_consistent)
  (n : nat)
  (length_le : n < length2 l)
  : encode_consistent _ _ (choice_0_serial l ser n). 
Proof.
  unfold encode_consistent. intros. 
  unfold choice_0_serial, get_nth_serial in H, H0.

  eassert (G := get_nth_cond_prod l ser _ n length_le
                  enc_consist_prod _ _ _ _ _ _ _ _ _ _ H H0).
  apply G.
Qed.

(* For this part, it seems we again need the non_inter property to
   make it possible. 
 *)
Lemma choice_encode_consist
  (l : list typ)
  (length_l_ge2 : 2 <= length2 l)
  (pf1 : length_cond l)
  (ser : get_serial_prodc l)
  (non_iter_prod : get_cond_prodc l ser encode_non_inter)
  (enc_consist_prod : get_cond_prodc l ser encode_consistent) :
  encode_consistent _ _  (choice_serial l pf1 ser).
Proof.
  unfold encode_consistent. intros. 
  unfold choice_serial in *.
  repeat (destruct_match_new; repeat destruct_let).

  assert (projT1 a < length2 l). { lia. }
  eassert (G :=  choice_0_encode_consist l ser enc_consist_prod _ H1).
  eassert (G1 := choice_0_non_inter l ser non_iter_prod _ H1). 
  
  eassert (Eq1 := G _ _ _ _ _ _ _ _ _ _ H H0).
  
  eassert (NI1 := G1 _ _ _ _ _ _ H).
  eassert (NI2 := G1 _ _ _ _ _ _ H0). 

  split_and.
  rewrite (proof_irrelevance _ _ l0) in E0.
  
  eapply encode_consist_proof_helper.
  - apply Eq1.
  - apply H3.
  - apply H2.
  - eassert (G2 := T_Correct _ _ (NonNeg.nat_format (length2 l - 1) pf1)).
    unfold format_correct in G2.
    split_and. 
    + eapply H6. eapply E0. apply E.
Qed.

Lemma get_nth_cond_de_prod
  (l : list typ) :
  forall (par : get_parse_prodc l)
         (cond : decode_cond_type)
         (n : nat)
         (length_le : n < length2 l)
         (cond_pf : get_cond_de_prodc l par cond),
    cond _ _ (get_nth_parse l par n).
Proof.
  induction l.
  - intros. inversion length_le. 
    
  - intros. destruct a, par, cond_pf. 
    simpl in H, H0.
    destruct n.
    (* Case n = 0, which is solved by s *)
    + simpl.  apply H.
      
    (* Case n < length l, which is solved by IHl *)
    + simpl. simpl in length_le.   apply IHl; auto.
      apply le_S_n. auto.
Qed. 

Lemma choice_decode_consist
  (l : list typ)
  (length_l_ge2 : 2 <= length2 l)
  (pf1 : length_cond l)
  (par : get_parse_prodc l)
  (dec_consist_prod : get_cond_de_prodc l par decode_consistent) :
  decode_consistent _ _  (choice_parse l pf1 par).
Proof.
  unfold decode_consistent.
  intros. unfold choice_parse in *.
  apply bind_parse_consist.
  - eassert (G2 := T_Correct _ _ (NonNeg.nat_format (length2 l - 1) pf1)).
     unfold format_correct in G2.
    split_and. apply H2.
  - intros. apply bind_parse_consist.
    + assert (a0 < length2 l). { lia. }
      apply get_nth_cond_de_prod; auto.
    + intros. apply return_parse_consist.
  - auto.
Qed.


Lemma get_nth_cond_both_prod
  (l : list typ) :
  forall (ser : get_serial_prodc l)
         (par : get_parse_prodc l)
         (cond : en_decode_cond_type)
         (n : nat)
         (length_le : n < length2 l)
         (cond_pf : get_cond_both_prodc l ser par cond),
    cond _ _ (get_nth_serial l ser n) (get_nth_parse l par n).
Proof.
  induction l.
  - intros. inversion length_le. 
    
  - intros. destruct a, ser, par, cond_pf. 
    simpl in H, H0.
    destruct n.
    (* Case n = 0, which is solved by s *)
    + simpl.  apply H.
      
    (* Case n < length l, which is solved by IHl *)
    + simpl. simpl in length_le.   apply IHl; auto.
      apply le_S_n. auto.
Qed. 

Lemma choice_surj
  (l : list typ)
  (length_l_ge2 : 2 <= length2 l)
  (pf1 : length_cond l)
  (ser : get_serial_prodc l)
  (par : get_parse_prodc l)
  (non_inter_prod : get_cond_prodc l ser encode_non_inter)
  (surj_prod : get_cond_both_prodc l ser par format_correct_surj) :
  format_correct_surj _ _  (choice_serial l pf1 ser) (choice_parse l pf1 par).
Proof.
  unfold format_correct_surj. intros.
  unfold choice_serial in H.
  destruct_enc. 
  unfold choice_parse.
  eassert (G2 := T_Correct _ _ (NonNeg.nat_format (length2 l - 1) pf1)).

  eassert (G := fmt_surj G2 _ _ _ _ _ _ E). 
  unfold bind_parse, return_parse.

  assert ( projT1 a < length2 l). { lia. }
  eassert (G1 := choice_0_non_inter l ser non_inter_prod _ H0). 
  
  eassert (E2 := G1 _ _ _ _ _ _ H).
  eassert (NP := fmt_dec_consist G2 _ _ _ _ _ _ G).

  split_and. 
  assert (PT2 := H2 _ _ _ (equiv_b_le_zero _ _ _ _ H1 H3)).
  unfold nat_parse. rewrite PT2.

  unfold choice_0_serial in H.
  eassert (CE := get_nth_cond_both_prod l ser par _ _ H0 surj_prod
                   _ _ _ _ _ _ H).
  rewrite CE.
  destruct a.
  decode_eq. 
Qed.

Ltac destruct_choice_parse H :=
  unfold choice_parse, bind_parse, return_parse in H;
  repeat destruct_enc;
  inversion H; subst; clear H. 


Lemma choice_inj_same
  (l : list typ)
  (length_l_ge2 : 2 <= length2 l)
  (pf1 : length_cond l)
  (ser : get_serial_prodc l)
  (par : get_parse_prodc l)
  (non_inter_prod : get_cond_prodc l ser encode_non_inter)
  (inj_prod : get_cond_both_prodc l ser par format_correct_inj_same) :
  format_correct_inj_same _ _  (choice_serial l pf1 ser) (choice_parse l pf1 par).
Proof.
  unfold format_correct_inj_same. intros.

  destruct_choice_parse H.
  
  unfold nat_parse in E. 
  (* Here, we can say if it is a basic type, then the
     flg should always be SameVer.
   *)
  eassert (ES := NonNeg.nat_format_SameVer  _ _ _ _ _ _ _ E).  subst.

  (* inj *)
  eassert (G' := T_Correct _ _ (NonNeg.nat_format  (length2 l - 1) pf1)).

  destruct (fmt_inj_same G' _ _ _ _ _ E _ H0).
  split_and.
  
  unfold choice_serial, nat_serial, projT1, projT2.  rewrite H1.  

  unfold choice_0_serial.
  assert (x < length2 l). { lia. }

  eassert (EL := same_len_after_enc _
                   (fmt_enc_ni G')
                   H1).
  rewrite EL in H0. 
  eassert (G := get_nth_cond_both_prod l ser par _ x H inj_prod
                  _ _ _ _ _ E0 x1 H0).
  destruct_ex. split_and. 
  rewrite H4.  exists x2. split.
  - encode_eq.
  - 
    (* Here, the situation is
       bf - 
       x1 - pos -- p
       x2          p -- pos'

       We need second to be non-inter, i.e., we
       simply need 
     *)
    eapply format_correct_inj_helper.
    + apply H2.
    + auto.
    + eapply choice_0_non_inter.
      * apply non_inter_prod.
      * apply H. 
      * unfold choice_0_serial.  apply H4.
Qed.


Require Import ASN1Parser.Array.BitRep.

Lemma choice_to_len_correct
  (l : list typ)
  (length_l_ge2 : 2 <= length2 l)
  (pf1 : length_cond l)
  (ser : get_serial_prodc l)
  (par : get_parse_prodc l)
  (tl : get_to_len_prodc l)
  (non_inter_prod : get_cond_prodc l ser encode_non_inter)
  (tl_c : get_cond_tl_prodc l ser par tl format_to_len_correct)
  : format_to_len_correct _ _ (choice_serial l pf1 ser) (choice_parse l pf1 par)
      (choice_to_len l tl).
Proof.
  unfold choice_serial, choice_to_len, format_to_len_correct. split.
  - intros.
    destruct_enc.
    destruct a. simpl in *. 
    assert (Nat.leb x (length2 l) = true). { rewrite PeanoNat.Nat.leb_le. lia. }
    rewrite H0.
    unfold choice_0_serial in H.

    assert (x < length2 l). { lia. } 
    eassert (G := proj1 (get_nth_cond_tl_prod l ser par tl _ x H1 tl_c) _ _ _ _ _ _ H).
    eassert (G' := get_nth_cond_prod l ser _ x H1 non_inter_prod _ _ _ _ _ _ H).
    unfold get_nth_to_len in G. simpl in G.  rewrite G.

    f_equal. unfold nat_serial in E.
    assert (C := T_Correct _ _ (NonNeg.nat_format (length2 l - 1) pf1)). 
    eassert (C1 := proj1 (fmt_len_c C) _ _ _ _ _ _ E).
    assert (C2 := fmt_enc_ni C _ _ _ _ _ _ E).
    simpl in C1. unfold n_nat_to_len in C1.
    inversion C1. rewrite H3.

    split_and.  unfold BProp.le_pos in *.
    lia.
  - intros. destruct a. simpl in *.  unfold choice_parse, bind_parse, return_parse in H.
    repeat destruct_enc. inversion H.  subst. clear H. clear H2.
    
    assert (Nat.leb x (length2 l) = true). { rewrite PeanoNat.Nat.leb_le. lia. } 
    rewrite H.
    assert (x < length2 l). { lia. } 
    eassert (G := proj2 (get_nth_cond_tl_prod l ser par tl _ x H0 tl_c) _ _ _ _ _ _ E0 ).
    unfold get_nth_to_len in G. destruct_ex. rewrite H1.
    eauto. 
Qed.

Opaque Nat.pow.
Lemma choice_inj_diff
  (l : list typ)
  (length_l_ge2 : 2 <= length2 l)
  (pf1 : length_cond l)
  (ser : get_serial_prodc l)
  (par : get_parse_prodc l)
  (tl : get_to_len_prodc l)
  (non_inter_prod : get_cond_prodc l ser encode_non_inter)
  (gl_crt : get_cond_tl_prodc l ser par tl  format_to_len_correct) 
  (inj_prod : get_cond_tl_prodc l ser par tl  format_correct_inj_diff) :
  format_correct_inj_diff _ _  (choice_serial l pf1 ser) (choice_parse l pf1 par)
    (choice_to_len l tl).
Proof.
  unfold format_correct_inj_diff. intros.
  destruct_choice_parse H.  

  unfold nat_parse in E.
  eassert (G2 := T_Correct _ _ (NonNeg.nat_format (length2 l - 1) pf1)).
  eassert (G := fmt_inj_diff G2 _ _ _ _ _ _ E).
  destruct_ex.

  assert (x < length2 l). { lia. }
  eassert (G1 :=  get_nth_cond_tl_prod l ser par tl _ x H0 inj_prod
                    _ _ _ _ _ _ E0).
  destruct_ex.
  exists (x1 + x2). intros.
  unfold choice_serial, nat_serial, projT1, projT2. 

  assert (BA.to_nat pos0 + x1 <= BA.len bf0). { lia. }
  assert (G' := H _ _  H3).

  eassert (K1 := proj2 (fmt_len_c (T_Correct _ _ (NonNeg.nat_format  (length2 l - 1) pf1))) _ _ _ _ _ _ E).
  assert (x < length2 l). { lia. } 
  eassert (K2 := (proj2 (get_nth_cond_tl_prod l ser par tl _ x H4 gl_crt))
                   _ _ _ _ _ _ E0).

  destruct_ex. unfold choice_to_len.
  assert (Nat.leb x (length2 l) = true). { rewrite PeanoNat.Nat.leb_le. lia. }
  rewrite H7. unfold get_nth_to_len in H5.
  simpl in H6. unfold n_nat_to_len in H6. rewrite H6, H5. 
  
  destruct G'.
  { left. simpl in H8. inversion H6. rewrite H10 in H8.
    rewrite H10. assert (x4 <= x4 + x3). { lia. }
    apply get_byte_len_mono in H9. simpl. lia. } 

  destruct_ex. split_and. 
  rewrite H9. 

  eassert (G3 := fmt_enc_ni G2). 
  assert (BA.to_nat x6 + x2 <= BA.len x5). 
  { eassert (G := same_len_after_enc _ ( G3 ) H9). 
    lia. } 

  eassert (G' := H1 _ _ H8).

  destruct G'.
  { left. unfold get_nth_to_len in H11.  rewrite H5 in H11.
    assert (x3 <= x4 + x3). { lia. }
    apply get_byte_len_mono in H12. simpl. lia. } 

  right. 
  destruct_ex. split_and. 
  unfold choice_0_serial. exists x7. exists x8.
  split. 
  - rewrite H12. encode_eq.
  - lia. 
Qed.

Require Import ASN1Parser.Formats.Term.Unit.

Ltac id_l l := induction l; simpl; auto.
Ltac fmt_l a f := destruct a; destruct f; simpl; split; auto. 

(* Need to derive properties from formats *)

Definition fmt_to_prodc (l : list typ) (fmts : get_formats l)
  (X : forall A : Set, (A -> Prop) -> Type)
  (T_X : forall (T : Set) (T_Cond : T -> Prop),
      T_Format T T_Cond -> X T T_Cond)
  (X_empty :  X Empty_set (fun _ : _ => True))
      : list_to_prod l (fun t => X (typ_set t) (typ_cond t)) empty_typ.
  induction l. 
  - apply X_empty.
  - destruct fmts. 
    apply (T_X _ _ t, IHl l0).
Defined.

Definition fmt_to_prod_no_condc (l : list typ) (fmts : get_formats l)
  (X : forall A : Set, Type)
  (T_X : forall (T : Set) (T_Cond : T -> Prop), T_Format T T_Cond -> X T)
  (X_empty : X Empty_set)
  : list_to_prod l (fun t => X (typ_set t)) empty_typ.
  induction l.
  - apply X_empty.
  - destruct fmts.
    apply (T_X _ _ t, IHl l0). 
Defined.

(* Some proofs about empty *)
Definition put_empty : Serialize  Empty_set (fun _ : Empty_set => True).
  unfold Serialize. intros. destruct a.
Defined.

Definition read_empty : Parse Empty_set (fun _ : Empty_set => True).
  unfold Parse. intros. apply None.
Defined.

Definition empty_to_len : Empty_set -> option nat.
  intros. destruct H.
Defined.

Lemma empty_format_correct : format_correct put_empty read_empty empty_to_len.
Proof.
  unfold format_correct.
  split.
  { unfold encode_consistent. destruct a. }
  split.
  { unfold decode_consistent. intros. destruct a. }
  split.
  { unfold encode_non_inter. intros. destruct a. }
  split.
  { unfold format_correct_surj. intros. destruct a. }
  split.
  { unfold format_correct_inj_same. intros. destruct a. }
  split.
  { unfold format_correct_inj_diff. intros. destruct a. }
  unfold format_to_len_correct. split; intros; destruct a.
Qed. 
    
Definition empty_format : T_Format Empty_set (fun _ : Empty_set => True) :=
  mk_format
    _ _
    put_empty
    read_empty
    empty_to_len
    empty_format_correct. 

Lemma fmts_to_conj_enc_ni (l : list typ) (fmts : get_formats l)
  : get_cond_prodc l (fmt_to_prodc l fmts Serialize T_Serial put_empty) encode_non_inter.
Proof. id_l l. fmt_l a fmts. eapply fmt_enc_ni. apply t. Qed.

Lemma fmts_to_conj_enc_consist (l : list typ) (fmts : get_formats l)
  : get_cond_prodc l (fmt_to_prodc l fmts Serialize T_Serial put_empty) encode_consistent.
Proof. id_l l. fmt_l a fmts. eapply fmt_enc_consist. apply t. Qed.

Lemma fmts_to_conj_dec_consist (l : list typ) (fmts : get_formats l)
  : get_cond_de_prodc l (fmt_to_prodc l fmts Parse T_Parse read_empty) decode_consistent.
Proof.
  id_l l. fmt_l a fmts. eapply fmt_dec_consist. apply t.
Qed.

Lemma fmts_to_conj_surj (l : list typ) (fmts : get_formats l)
  : get_cond_both_prodc l
      (fmt_to_prodc l fmts Serialize T_Serial put_empty)
      (fmt_to_prodc l fmts Parse T_Parse read_empty)
      format_correct_surj.
Proof. id_l l. fmt_l a fmts. eapply fmt_surj. apply t. Qed.

Lemma fmts_to_conj_inj_same (l : list typ) (fmts : get_formats l)
  : get_cond_both_prodc l
      (fmt_to_prodc l fmts Serialize T_Serial put_empty)
      (fmt_to_prodc l fmts Parse T_Parse read_empty)
      format_correct_inj_same.
Proof. id_l l. fmt_l a fmts. eapply fmt_inj_same. apply t. Qed.

Lemma fmts_to_conj_inj_diff (l : list typ) (fmts : get_formats l)
  : get_cond_tl_prodc l
      (fmt_to_prodc l fmts Serialize T_Serial put_empty)
      (fmt_to_prodc l fmts Parse T_Parse read_empty)
      (fmt_to_prod_no_condc l fmts _ (T_to_len) empty_to_len)
      format_correct_inj_diff.
Proof. id_l l. fmt_l a fmts. eapply fmt_inj_diff. apply t. Qed.

Lemma fmts_to_conj_fmt_c (l : list typ) (fmts : get_formats l)
  :  get_cond_tl_prodc l
       (fmt_to_prodc l fmts Serialize T_Serial put_empty)
       (fmt_to_prodc l fmts Parse T_Parse read_empty)
       (fmt_to_prod_no_condc l fmts _ (T_to_len) empty_to_len)
       format_to_len_correct.
Proof. id_l l. fmt_l a fmts. eapply fmt_len_c.  apply t. Qed.

Hint Resolve choice_encode_consist choice_non_inter_ge2
  choice_decode_consist choice_surj choice_inj_same
  choice_inj_same choice_inj_diff
  choice_to_len_correct : choice_db.

Hint Resolve fmts_to_conj_enc_consist fmts_to_conj_enc_ni
  fmts_to_conj_dec_consist fmts_to_conj_surj
  fmts_to_conj_inj_same fmts_to_conj_inj_diff
  fmts_to_conj_fmt_c : fmt_conj_db.

(* Need to see how the extraction works here *)

Lemma choice_format_correct :
  forall (l : list typ) (pf1 : length_cond l)  (length_l_ge2 : 2 <= length2 l)
         (fmts : get_formats l),
    format_correct
      (choice_serial l pf1 (fmt_to_prodc l fmts Serialize T_Serial put_empty))
      (choice_parse l pf1 (fmt_to_prodc l fmts Parse T_Parse read_empty))
      (choice_to_len l
         (fmt_to_prod_no_condc l fmts (fun T : Set => T -> option nat) T_to_len
            empty_to_len)).
Proof.
  intros. 
  unfold format_correct. repeat (split; auto with choice_db fmt_conj_db). 
Qed.
