Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MultiFrequencyBandListNR_SIB.

Opaque MultiFrequencyBandListNR_SIB__cond MultiFrequencyBandListNR_SIB__Format.

Lemma FrequencyInfoDL_SIB__offsetToPointA__helper1 : (0 <= 2199)%Z.  lia. Qed.
Lemma FrequencyInfoDL_SIB__offsetToPointA__helper2 : to_bit_sz (Z.to_nat (2199 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2199 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply FrequencyInfoDL_SIB__offsetToPointA__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FrequencyInfoDL_SIB__offsetToPointA__Type := Z.
Definition FrequencyInfoDL_SIB__offsetToPointA__cond := (fun z => (0 <= z <= 2199)%Z).
Require Import NR.SCS_SpecificCarrier.

Opaque SCS_SpecificCarrier__cond SCS_SpecificCarrier__Format.

Definition FrequencyInfoDL_SIB__scs_SpecificCarrierList__Type := list SCS_SpecificCarrier__Type.

Lemma FrequencyInfoDL_SIB__scs_SpecificCarrierList__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma FrequencyInfoDL_SIB__scs_SpecificCarrierList__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FrequencyInfoDL_SIB__scs_SpecificCarrierList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FrequencyInfoDL_SIB__scs_SpecificCarrierList__cond (z : FrequencyInfoDL_SIB__scs_SpecificCarrierList__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SCS_SpecificCarrier__cond z) .

Record FrequencyInfoDL_SIB__Type : Set :=
  make__FrequencyInfoDL_SIB__Type {
    FrequencyInfoDL_SIB__frequencyBandList : MultiFrequencyBandListNR_SIB__Type ;
    FrequencyInfoDL_SIB__offsetToPointA : Z ;
    FrequencyInfoDL_SIB__scs_SpecificCarrierList : FrequencyInfoDL_SIB__scs_SpecificCarrierList__Type ;
}.
Definition FrequencyInfoDL_SIB__list := (
 Nor MultiFrequencyBandListNR_SIB__Type MultiFrequencyBandListNR_SIB__cond ::
 Nor Z FrequencyInfoDL_SIB__offsetToPointA__cond ::
 Nor FrequencyInfoDL_SIB__scs_SpecificCarrierList__Type FrequencyInfoDL_SIB__scs_SpecificCarrierList__cond ::
 nil).
Definition FrequencyInfoDL_SIB__cond z := 
  MultiFrequencyBandListNR_SIB__cond (FrequencyInfoDL_SIB__frequencyBandList z) /\
  FrequencyInfoDL_SIB__offsetToPointA__cond (FrequencyInfoDL_SIB__offsetToPointA z) /\
  FrequencyInfoDL_SIB__scs_SpecificCarrierList__cond (FrequencyInfoDL_SIB__scs_SpecificCarrierList z) /\
  True.


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
Definition FrequencyInfoDL_SIB__offsetToPointA__Format : T_Format Z FrequencyInfoDL_SIB__offsetToPointA__cond :=
 ranged_int_format (0) (2199) FrequencyInfoDL_SIB__offsetToPointA__helper1 FrequencyInfoDL_SIB__offsetToPointA__helper2.

Opaque FrequencyInfoDL_SIB__offsetToPointA__cond FrequencyInfoDL_SIB__offsetToPointA__Format.

Definition FrequencyInfoDL_SIB__scs_SpecificCarrierList__Format : T_Format FrequencyInfoDL_SIB__scs_SpecificCarrierList__Type FrequencyInfoDL_SIB__scs_SpecificCarrierList__cond := seq_of_format SCS_SpecificCarrier__Format 1 maxSCSs FrequencyInfoDL_SIB__scs_SpecificCarrierList__helper1 FrequencyInfoDL_SIB__scs_SpecificCarrierList__helper2.

Opaque FrequencyInfoDL_SIB__scs_SpecificCarrierList__cond FrequencyInfoDL_SIB__scs_SpecificCarrierList__Format.


Definition FrequencyInfoDL_SIB__Format_Type := Eval cbn in seq_format_prod FrequencyInfoDL_SIB__list.
Definition FrequencyInfoDL_SIB__Format_list : FrequencyInfoDL_SIB__Format_Type :=
  (MultiFrequencyBandListNR_SIB__Format, (FrequencyInfoDL_SIB__offsetToPointA__Format, (FrequencyInfoDL_SIB__scs_SpecificCarrierList__Format, unit_format))).
Definition FrequencyInfoDL_SIB__list__Format := (*Eval compute in *) seq_format FrequencyInfoDL_SIB__list FrequencyInfoDL_SIB__Format_list.
Definition FrequencyInfoDL_SIB__F1 z :=
  (FrequencyInfoDL_SIB__frequencyBandList z, (FrequencyInfoDL_SIB__offsetToPointA z, (FrequencyInfoDL_SIB__scs_SpecificCarrierList z, tt))).
Definition FrequencyInfoDL_SIB__F2 (y : seq_type FrequencyInfoDL_SIB__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FrequencyInfoDL_SIB__Type i0 i1 i2
  end.
Lemma FrequencyInfoDL_SIB__F1F2_cond (z : FrequencyInfoDL_SIB__Type)
  : FrequencyInfoDL_SIB__cond z ->
  (seq_cond FrequencyInfoDL_SIB__list (FrequencyInfoDL_SIB__F1 z)).
intro H. unfold FrequencyInfoDL_SIB__cond in H. simpl. auto. Qed.
Lemma FrequencyInfoDL_SIB__F1F2_cond2 (z : FrequencyInfoDL_SIB__Type)
 : FrequencyInfoDL_SIB__F2 (FrequencyInfoDL_SIB__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FrequencyInfoDL_SIB__F2F1_cond (y : seq_type FrequencyInfoDL_SIB__list)
  : seq_cond FrequencyInfoDL_SIB__list y ->
 (FrequencyInfoDL_SIB__cond (FrequencyInfoDL_SIB__F2 y)) /\  FrequencyInfoDL_SIB__F1 (FrequencyInfoDL_SIB__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FrequencyInfoDL_SIB__cond. simpl in *. auto.
 - simpl. unfold FrequencyInfoDL_SIB__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FrequencyInfoDL_SIB__Format : T_Format FrequencyInfoDL_SIB__Type FrequencyInfoDL_SIB__cond :=
        proj2_format  FrequencyInfoDL_SIB__cond FrequencyInfoDL_SIB__list__Format
    FrequencyInfoDL_SIB__F1 FrequencyInfoDL_SIB__F2 FrequencyInfoDL_SIB__F1F2_cond  FrequencyInfoDL_SIB__F1F2_cond2 FrequencyInfoDL_SIB__F2F1_cond.
Opaque FrequencyInfoDL_SIB__cond FrequencyInfoDL_SIB__Format.

