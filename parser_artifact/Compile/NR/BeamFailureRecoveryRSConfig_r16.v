Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.CandidateBeamRS_r16.

Opaque CandidateBeamRS_r16__cond CandidateBeamRS_r16__Format.

Definition BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__Type := list CandidateBeamRS_r16__Type.

Lemma BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__helper1 : (0 <= 1 <= maxNrofCandidateBeams_r16)%Z. unfold maxNrofCandidateBeams_r16.
 lia. Qed.
Lemma BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCandidateBeams_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCandidateBeams_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__cond (z : BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCandidateBeams_r16)%Z /\ (list_and CandidateBeamRS_r16__cond z) .

Require Import NR.CandidateBeamRS_r16.

Opaque CandidateBeamRS_r16__cond CandidateBeamRS_r16__Format.

Definition BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__Type := list CandidateBeamRS_r16__Type.

Lemma BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__helper1 : (0 <= 1 <= maxNrofCandidateBeams_r16)%Z. unfold maxNrofCandidateBeams_r16.
 lia. Qed.
Lemma BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCandidateBeams_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCandidateBeams_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__cond (z : BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCandidateBeams_r16)%Z /\ (list_and CandidateBeamRS_r16__cond z) .

Record BeamFailureRecoveryRSConfig_r16__ext0O__Type : Set :=
  make__BeamFailureRecoveryRSConfig_r16__ext0O__Type {
    BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17 : option BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__Type ;
}.
Definition BeamFailureRecoveryRSConfig_r16__ext0O__list := (
 Opt BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__Type BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__cond ::
 nil).
Definition BeamFailureRecoveryRSConfig_r16__ext0O__cond z := 
  opt_cond BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__cond (BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17 z) /\
  True.

Definition BeamFailureRecoveryRSConfig_r16__ext0__Type := BeamFailureRecoveryRSConfig_r16__ext0O__Type.
Definition BeamFailureRecoveryRSConfig_r16__ext0__cond := BeamFailureRecoveryRSConfig_r16__ext0O__cond.

Record BeamFailureRecoveryRSConfig_r16__Type : Set :=
  make__BeamFailureRecoveryRSConfig_r16__Type {
    BeamFailureRecoveryRSConfig_r16__rsrp_ThresholdBFR_r16 : option RSRP_Range__Type ;
    BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16 : option BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__Type ;
    BeamFailureRecoveryRSConfig_r16__ext0 : option BeamFailureRecoveryRSConfig_r16__ext0__Type ;
}.
Definition BeamFailureRecoveryRSConfig_r16__root_list : list seq_elem := (
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__Type BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__cond ::
 nil).
Definition BeamFailureRecoveryRSConfig_r16__ext_list : list typ := (
  typ_cons BeamFailureRecoveryRSConfig_r16__ext0__Type BeamFailureRecoveryRSConfig_r16__ext0__cond ::
  nil).
Definition BeamFailureRecoveryRSConfig_r16__cond (z : BeamFailureRecoveryRSConfig_r16__Type) := 
(  opt_cond RSRP_Range__cond (BeamFailureRecoveryRSConfig_r16__rsrp_ThresholdBFR_r16 z) /\
  opt_cond BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__cond (BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16 z) /\
  True) /\ 
(  opt_cond BeamFailureRecoveryRSConfig_r16__ext0__cond (BeamFailureRecoveryRSConfig_r16__ext0 z) /\
  True).


Opaque Byte.to_nat Byte.of_nat.
Opaque bind_parse restrict_parse proj_parse return_parse.
Opaque restrict_serialize proj_serialize sigma_serialize append_serialize proj2_serialize.

Opaque read_n_nat read_unit.
Opaque put_n_nat put_unit. 

Opaque opt_bind opt_serialize dft_serialize prepend_serialize list_serial.
Opaque opt_parse list_parse dft_parse fail_parse append_parse
  bind_parse return_parse.

Opaque Z.to_nat Z.of_nat Z.sub Z.add Z.le Z.lt Z.pow Z.opp Z.ltb.
Opaque Nat.mul Nat.shiftr Nat.shiftl Nat.div Nat.modulo Nat.leb Nat.ltb Nat.add
  Nat.sub Nat.land Nat.lor Nat.eqb  Nat.log2 Nat.pow Nat.even PeanoNat.Nat.lnot.
Opaque Compare_dec.le_dec Compare_dec.le_lt_dec ZArith_dec.Z_le_dec lt_eq_lt_dec_new. 
Opaque sumbool_and1 list_and list_and_cons list_cons_S flg_add. 

Opaque list_to_len.
   Opaque length Compare_dec.le_dec Compare_dec.lt_dec PeanoNat.Nat.eq_dec.
   Opaque bool__Format int__Format octet_string_nc__Format bit_string_nc__Format.

   Opaque ByteIdx_to_nat nat_to_ByteIdx add_opt list_bool_format normally_small_len_det_format
  get_byte_len to_parse_skip  open_typ_serialize open_typ_parse open_type_to_len.
  

Opaque seq_cond seq_ext_cond choice_cond.
Definition BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__Format : T_Format BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__Type BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__cond := seq_of_format CandidateBeamRS_r16__Format 1 maxNrofCandidateBeams_r16 BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__helper1 BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__helper2.

Opaque BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__cond BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__Format.

Definition BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__Format : T_Format BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__Type BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__cond := seq_of_format CandidateBeamRS_r16__Format 1 maxNrofCandidateBeams_r16 BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__helper1 BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__helper2.

Opaque BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__cond BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__Format.


Definition BeamFailureRecoveryRSConfig_r16__ext0O__Format_Type := Eval cbn in seq_format_prod BeamFailureRecoveryRSConfig_r16__ext0O__list.
Definition BeamFailureRecoveryRSConfig_r16__ext0O__Format_list : BeamFailureRecoveryRSConfig_r16__ext0O__Format_Type :=
  (BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17__Format, unit_format).
Definition BeamFailureRecoveryRSConfig_r16__ext0O__list__Format := (*Eval compute in *) seq_format BeamFailureRecoveryRSConfig_r16__ext0O__list BeamFailureRecoveryRSConfig_r16__ext0O__Format_list.
Definition BeamFailureRecoveryRSConfig_r16__ext0O__F1 z :=
  (BeamFailureRecoveryRSConfig_r16__ext0O__candidateBeamRS_List2_r17 z, tt).
Definition BeamFailureRecoveryRSConfig_r16__ext0O__F2 (y : seq_type BeamFailureRecoveryRSConfig_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__BeamFailureRecoveryRSConfig_r16__ext0O__Type i0
  end.
Lemma BeamFailureRecoveryRSConfig_r16__ext0O__F1F2_cond (z : BeamFailureRecoveryRSConfig_r16__ext0O__Type)
  : BeamFailureRecoveryRSConfig_r16__ext0O__cond z ->
  (seq_cond BeamFailureRecoveryRSConfig_r16__ext0O__list (BeamFailureRecoveryRSConfig_r16__ext0O__F1 z)).
intro H. unfold BeamFailureRecoveryRSConfig_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma BeamFailureRecoveryRSConfig_r16__ext0O__F1F2_cond2 (z : BeamFailureRecoveryRSConfig_r16__ext0O__Type)
 : BeamFailureRecoveryRSConfig_r16__ext0O__F2 (BeamFailureRecoveryRSConfig_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BeamFailureRecoveryRSConfig_r16__ext0O__F2F1_cond (y : seq_type BeamFailureRecoveryRSConfig_r16__ext0O__list)
  : seq_cond BeamFailureRecoveryRSConfig_r16__ext0O__list y ->
 (BeamFailureRecoveryRSConfig_r16__ext0O__cond (BeamFailureRecoveryRSConfig_r16__ext0O__F2 y)) /\  BeamFailureRecoveryRSConfig_r16__ext0O__F1 (BeamFailureRecoveryRSConfig_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BeamFailureRecoveryRSConfig_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold BeamFailureRecoveryRSConfig_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BeamFailureRecoveryRSConfig_r16__ext0O__Format : T_Format BeamFailureRecoveryRSConfig_r16__ext0O__Type BeamFailureRecoveryRSConfig_r16__ext0O__cond :=
        proj2_format  BeamFailureRecoveryRSConfig_r16__ext0O__cond BeamFailureRecoveryRSConfig_r16__ext0O__list__Format
    BeamFailureRecoveryRSConfig_r16__ext0O__F1 BeamFailureRecoveryRSConfig_r16__ext0O__F2 BeamFailureRecoveryRSConfig_r16__ext0O__F1F2_cond  BeamFailureRecoveryRSConfig_r16__ext0O__F1F2_cond2 BeamFailureRecoveryRSConfig_r16__ext0O__F2F1_cond.
Opaque BeamFailureRecoveryRSConfig_r16__ext0O__cond BeamFailureRecoveryRSConfig_r16__ext0O__Format.

Definition BeamFailureRecoveryRSConfig_r16__ext0__check_all_none (b : BeamFailureRecoveryRSConfig_r16__ext0O__Type) : bool :=
match b with 
  | make__BeamFailureRecoveryRSConfig_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition BeamFailureRecoveryRSConfig_r16__ext0__Format : T_Format BeamFailureRecoveryRSConfig_r16__ext0__Type BeamFailureRecoveryRSConfig_r16__ext0__cond :=
  restrict_add_format BeamFailureRecoveryRSConfig_r16__ext0__check_all_none BeamFailureRecoveryRSConfig_r16__ext0O__Format.

Opaque BeamFailureRecoveryRSConfig_r16__ext0__cond BeamFailureRecoveryRSConfig_r16__ext0__Format.


Definition BeamFailureRecoveryRSConfig_r16__root_Format_Type := Eval cbn in seq_format_prod BeamFailureRecoveryRSConfig_r16__root_list.
Definition BeamFailureRecoveryRSConfig_r16__root_Format_list : BeamFailureRecoveryRSConfig_r16__root_Format_Type :=
  (RSRP_Range__Format, (BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16__Format, unit_format)).

Definition BeamFailureRecoveryRSConfig_r16__ext_Format_Type := Eval cbn in get_formats BeamFailureRecoveryRSConfig_r16__ext_list.
Definition BeamFailureRecoveryRSConfig_r16__ext_Format_list : BeamFailureRecoveryRSConfig_r16__ext_Format_Type :=
  (BeamFailureRecoveryRSConfig_r16__ext0__Format, unit__Format).

Definition BeamFailureRecoveryRSConfig_r16__list_type : Set := (seq_type BeamFailureRecoveryRSConfig_r16__root_list) * (seq_ext_type BeamFailureRecoveryRSConfig_r16__ext_list).
Definition BeamFailureRecoveryRSConfig_r16__list_cond (z : BeamFailureRecoveryRSConfig_r16__list_type) : Prop :=
        (seq_cond BeamFailureRecoveryRSConfig_r16__root_list (fst z)) /\ (seq_ext_cond BeamFailureRecoveryRSConfig_r16__ext_list (snd z)).
Definition BeamFailureRecoveryRSConfig_r16__list_format : T_Format BeamFailureRecoveryRSConfig_r16__list_type BeamFailureRecoveryRSConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format BeamFailureRecoveryRSConfig_r16__root_list BeamFailureRecoveryRSConfig_r16__root_Format_list BeamFailureRecoveryRSConfig_r16__ext_list BeamFailureRecoveryRSConfig_r16__ext_Format_list.

Opaque BeamFailureRecoveryRSConfig_r16__list_format.
Definition BeamFailureRecoveryRSConfig_r16__F1 (z : BeamFailureRecoveryRSConfig_r16__Type) : BeamFailureRecoveryRSConfig_r16__list_type :=
  (((BeamFailureRecoveryRSConfig_r16__rsrp_ThresholdBFR_r16 z, (BeamFailureRecoveryRSConfig_r16__candidateBeamRS_List_r16 z, tt))), (
(BeamFailureRecoveryRSConfig_r16__ext0 z, tt))).
Definition BeamFailureRecoveryRSConfig_r16__F2 (y : BeamFailureRecoveryRSConfig_r16__list_type) : BeamFailureRecoveryRSConfig_r16__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__BeamFailureRecoveryRSConfig_r16__Type j0 j1 i0
  end.
Definition BeamFailureRecoveryRSConfig_r16__helper1 : (forall a : BeamFailureRecoveryRSConfig_r16__Type, BeamFailureRecoveryRSConfig_r16__cond a -> BeamFailureRecoveryRSConfig_r16__list_cond (BeamFailureRecoveryRSConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BeamFailureRecoveryRSConfig_r16__helper2 : (forall a : BeamFailureRecoveryRSConfig_r16__Type, BeamFailureRecoveryRSConfig_r16__F2 (BeamFailureRecoveryRSConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BeamFailureRecoveryRSConfig_r16__helper3 : (forall b : BeamFailureRecoveryRSConfig_r16__list_type, BeamFailureRecoveryRSConfig_r16__list_cond b -> BeamFailureRecoveryRSConfig_r16__cond (BeamFailureRecoveryRSConfig_r16__F2 b) /\ BeamFailureRecoveryRSConfig_r16__F1 (BeamFailureRecoveryRSConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BeamFailureRecoveryRSConfig_r16__cond, BeamFailureRecoveryRSConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BeamFailureRecoveryRSConfig_r16__Format : T_Format BeamFailureRecoveryRSConfig_r16__Type BeamFailureRecoveryRSConfig_r16__cond :=
 proj2_format BeamFailureRecoveryRSConfig_r16__cond BeamFailureRecoveryRSConfig_r16__list_format  BeamFailureRecoveryRSConfig_r16__F1 BeamFailureRecoveryRSConfig_r16__F2 BeamFailureRecoveryRSConfig_r16__helper1 BeamFailureRecoveryRSConfig_r16__helper2 BeamFailureRecoveryRSConfig_r16__helper3.

Opaque BeamFailureRecoveryRSConfig_r16__cond BeamFailureRecoveryRSConfig_r16__Format.

