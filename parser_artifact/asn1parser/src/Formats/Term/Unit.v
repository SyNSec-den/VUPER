Require Import
          ASN1Parser.Formats.Comb
          ASN1Parser.Array.BitRep
          ASN1Parser.tact.


(* Put-unit also need to check if it is valid position *)
Definition put_unit : Serialize unit (fun _ => True) :=
  fun bf pos z =>
    match (Compare_dec.le_dec (BA.to_nat pos) (BA.len bf)) with
    | left _ => Some (bf, pos, I)
    | right _ => None
    end.

Definition read_unit : Parse unit (fun _ => True) :=
  fun bf pos =>
    match (Compare_dec.le_dec (BA.to_nat pos) (BA.len bf)) with
    | left _ => Some (exist (fun (_ : unit) => True) tt I, pos, SameVer)
    | right _ => None
    end.

Definition unit_to_len := (fun _ : unit => Some 0). 

Lemma put_unit_non_inter : 
  encode_non_inter _ _ put_unit.
Proof.
  unfold encode_non_inter.  intros. unfold put_unit in H.
  destruct_if_in_new. 
  inversion H. subst.
  split.
  - apply EQ.equiv_b_refl. unfold EQ.valid_pos_pair.
    split; auto. 
    rewrite BProp.pos_zero_equals_zero.
    apply PeanoNat.Nat.le_0_l.
  - split.
    + apply EQ.equiv_b_refl. unfold EQ.valid_pos_pair.
      rewrite BProp.pos_end_equals_len.
      split; auto.
    + apply BProp.le_pos_refl.
Qed.

Lemma put_unit_consist : 
  encode_consistent _ _ put_unit.
Proof.
  unfold encode_consistent. intros.
  unfold put_unit in *.
  repeat destruct_if_in_new. inversion H. inversion H0. subst.
  apply EQ.equiv_b_nil; auto.
Qed.


  
Lemma read_unit_consist : 
  decode_consistent _ _ read_unit.
Proof.
  unfold decode_consistent. intros.
  unfold read_unit in H.
  destruct_if_in_new.  inversion H. subst.
  split; try apply BProp.le_pos_refl.
  intros.
  unfold read_unit.
  assert (EL := EQ.equiv_b_eq_len H0).  
  apply EQ.equiv_b_implies_valid_pair in H0.
  unfold EQ.valid_pos_pair in H0. split_and.
  unfold BProp.pos_to_len in EL.
  rewrite PeanoNat.Nat.sub_diag in EL.  
  assert (pos0 = pos0').
  { assert (BA.to_nat pos0 = BA.to_nat pos0').
    - Lia.lia.
    - rewrite <- (BProp.of_to_nat pos0),
        <- (BProp.of_to_nat pos0').
      rewrite H1.  auto.
  }
  rewrite H1.
  
  destruct_match_dec_goal; try Lia.lia.
  decode_eq. 
Qed.

Lemma unit_format_surj : 
  format_correct_surj _ _ put_unit read_unit. 
Proof.
  unfold format_correct_surj. intros.
  unfold put_unit in H. destruct_if_in_new.
  inversion H; subst.

  unfold read_unit.
  rewrite E. destruct a. decode_eq. 
Qed.

Lemma unit_format_inj : 
  format_correct_inj_same _ _ put_unit read_unit.
Proof.
  unfold format_correct_inj_same. intros.
  exists bf0.
  unfold read_unit in H.
  destruct_if_in_new. inversion H. subst.
  unfold put_unit.
  rewrite H0, E. split.
  - encode_eq. 
  - apply EQ.equiv_b_nil; auto.
    rewrite H0.  auto.
Qed.



Lemma unit_format_inj_diff : 
  format_correct_inj_diff _ _ put_unit read_unit unit_to_len.
Proof.
  unfold format_correct_inj_diff. intros.
  unfold read_unit in H. unfold put_unit.
  exists (BA.to_nat pos). intros.
  destruct_match_dec_new. inversion H. subst.
  right. 
  exists bf0. exists pos0.
  destruct_match_dec_goal; try Lia.lia.
  split. 
  - encode_eq.
  - apply PeanoNat.Nat.le_add_r.
Qed.

Lemma unit_to_len_correct : 
  format_to_len_correct _ _ put_unit read_unit unit_to_len.
Proof.
  unfold format_to_len_correct. split.
  - intros. unfold put_unit in H.
    destruct_match_dec_new. inversion H.  subst.
    f_equal. rewrite PeanoNat.Nat.sub_diag. reflexivity.
  - intros.  unfold unit_to_len.  exists 0. auto. 
Qed.
  
Lemma unit_format_correct :
  format_correct put_unit read_unit unit_to_len.
Proof.
  unfold format_correct. split.
  { apply put_unit_consist. } split.
  { apply read_unit_consist. } split. 
  { apply put_unit_non_inter. } split.
  { apply unit_format_surj. } split.
  { apply unit_format_inj. } split.
  { apply unit_format_inj_diff. }
  apply unit_to_len_correct.
Qed.

Definition unit_format : T_Format unit (fun _ => True) :=
  mk_format unit (fun _ => True)
    put_unit
    read_unit
    (fun _ => Some 0)
    unit_format_correct.

Lemma read_unit_SameVer : forall s bf pos pos' flg,
    read_unit bf pos = Some (s, pos', flg) -> flg = SameVer.
Proof.
  intros. unfold read_unit in H.
  destruct_match_dec_new. inversion H. reflexivity.
Qed.
  
Lemma put_unit_pos_no_change :
  forall bf bf' pos pos', 
    put_unit bf pos tt = Some (bf', pos', I) ->
    (bf = bf' /\ pos = pos').
Proof.
  intros.
  unfold put_unit in H. destruct_if_in.
  auto.
Qed.

Lemma put_unit_len_longer :
  encode_len_longer put_unit.
Proof.
  unfold encode_len_longer. intros.
  unfold put_unit in *. destruct_if_in_new.  inversion H0. subst.
  assert (BA.to_nat pos' <= BA.len bf0). { Lia.lia. } 
  destruct_if_goal.
  - exists bf0. encode_eq.
  - destruct (n H1).
Qed.
