Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Lemma CO_DurationsPerCell_r16__positionInDCI_r16__helper1 : (0 <= maxSFI_DCI_PayloadSize_1)%Z. unfold maxSFI_DCI_PayloadSize_1.
 lia. Qed.
Lemma CO_DurationsPerCell_r16__positionInDCI_r16__helper2 : to_bit_sz (Z.to_nat (maxSFI_DCI_PayloadSize_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSFI_DCI_PayloadSize_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CO_DurationsPerCell_r16__positionInDCI_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CO_DurationsPerCell_r16__positionInDCI_r16__Type := Z.
Definition CO_DurationsPerCell_r16__positionInDCI_r16__cond := (fun z => (0 <= z <= maxSFI_DCI_PayloadSize_1)%Z).
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.CO_Duration_r16.

Opaque CO_Duration_r16__cond CO_Duration_r16__Format.

Definition CO_DurationsPerCell_r16__co_DurationList_r16__Type := list CO_Duration_r16__Type.

Lemma CO_DurationsPerCell_r16__co_DurationList_r16__helper1 : (0 <= 1 <= 64)%Z.  lia. Qed.
Lemma CO_DurationsPerCell_r16__co_DurationList_r16__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CO_DurationsPerCell_r16__co_DurationList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CO_DurationsPerCell_r16__co_DurationList_r16__cond (z : CO_DurationsPerCell_r16__co_DurationList_r16__Type) :=  (1 <= Z.of_nat (length z) <= 64)%Z /\ (list_and CO_Duration_r16__cond z) .

Record CO_DurationsPerCell_r16__Type : Set :=
  make__CO_DurationsPerCell_r16__Type {
    CO_DurationsPerCell_r16__servingCellId_r16 : ServCellIndex__Type ;
    CO_DurationsPerCell_r16__positionInDCI_r16 : Z ;
    CO_DurationsPerCell_r16__subcarrierSpacing_r16 : SubcarrierSpacing__Type ;
    CO_DurationsPerCell_r16__co_DurationList_r16 : CO_DurationsPerCell_r16__co_DurationList_r16__Type ;
}.
Definition CO_DurationsPerCell_r16__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor Z CO_DurationsPerCell_r16__positionInDCI_r16__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor CO_DurationsPerCell_r16__co_DurationList_r16__Type CO_DurationsPerCell_r16__co_DurationList_r16__cond ::
 nil).
Definition CO_DurationsPerCell_r16__cond z := 
  ServCellIndex__cond (CO_DurationsPerCell_r16__servingCellId_r16 z) /\
  CO_DurationsPerCell_r16__positionInDCI_r16__cond (CO_DurationsPerCell_r16__positionInDCI_r16 z) /\
  SubcarrierSpacing__cond (CO_DurationsPerCell_r16__subcarrierSpacing_r16 z) /\
  CO_DurationsPerCell_r16__co_DurationList_r16__cond (CO_DurationsPerCell_r16__co_DurationList_r16 z) /\
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
Definition CO_DurationsPerCell_r16__positionInDCI_r16__Format : T_Format Z CO_DurationsPerCell_r16__positionInDCI_r16__cond :=
 ranged_int_format (0) (maxSFI_DCI_PayloadSize_1) CO_DurationsPerCell_r16__positionInDCI_r16__helper1 CO_DurationsPerCell_r16__positionInDCI_r16__helper2.

Opaque CO_DurationsPerCell_r16__positionInDCI_r16__cond CO_DurationsPerCell_r16__positionInDCI_r16__Format.

Definition CO_DurationsPerCell_r16__co_DurationList_r16__Format : T_Format CO_DurationsPerCell_r16__co_DurationList_r16__Type CO_DurationsPerCell_r16__co_DurationList_r16__cond := seq_of_format CO_Duration_r16__Format 1 64 CO_DurationsPerCell_r16__co_DurationList_r16__helper1 CO_DurationsPerCell_r16__co_DurationList_r16__helper2.

Opaque CO_DurationsPerCell_r16__co_DurationList_r16__cond CO_DurationsPerCell_r16__co_DurationList_r16__Format.


Definition CO_DurationsPerCell_r16__Format_Type := Eval cbn in seq_format_prod CO_DurationsPerCell_r16__list.
Definition CO_DurationsPerCell_r16__Format_list : CO_DurationsPerCell_r16__Format_Type :=
  (ServCellIndex__Format, (CO_DurationsPerCell_r16__positionInDCI_r16__Format, (SubcarrierSpacing__Format, (CO_DurationsPerCell_r16__co_DurationList_r16__Format, unit_format)))).
Definition CO_DurationsPerCell_r16__list__Format := (*Eval compute in *) seq_format CO_DurationsPerCell_r16__list CO_DurationsPerCell_r16__Format_list.
Definition CO_DurationsPerCell_r16__F1 z :=
  (CO_DurationsPerCell_r16__servingCellId_r16 z, (CO_DurationsPerCell_r16__positionInDCI_r16 z, (CO_DurationsPerCell_r16__subcarrierSpacing_r16 z, (CO_DurationsPerCell_r16__co_DurationList_r16 z, tt)))).
Definition CO_DurationsPerCell_r16__F2 (y : seq_type CO_DurationsPerCell_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CO_DurationsPerCell_r16__Type i0 i1 i2 i3
  end.
Lemma CO_DurationsPerCell_r16__F1F2_cond (z : CO_DurationsPerCell_r16__Type)
  : CO_DurationsPerCell_r16__cond z ->
  (seq_cond CO_DurationsPerCell_r16__list (CO_DurationsPerCell_r16__F1 z)).
intro H. unfold CO_DurationsPerCell_r16__cond in H. simpl. auto. Qed.
Lemma CO_DurationsPerCell_r16__F1F2_cond2 (z : CO_DurationsPerCell_r16__Type)
 : CO_DurationsPerCell_r16__F2 (CO_DurationsPerCell_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CO_DurationsPerCell_r16__F2F1_cond (y : seq_type CO_DurationsPerCell_r16__list)
  : seq_cond CO_DurationsPerCell_r16__list y ->
 (CO_DurationsPerCell_r16__cond (CO_DurationsPerCell_r16__F2 y)) /\  CO_DurationsPerCell_r16__F1 (CO_DurationsPerCell_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CO_DurationsPerCell_r16__cond. simpl in *. auto.
 - simpl. unfold CO_DurationsPerCell_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CO_DurationsPerCell_r16__Format : T_Format CO_DurationsPerCell_r16__Type CO_DurationsPerCell_r16__cond :=
        proj2_format  CO_DurationsPerCell_r16__cond CO_DurationsPerCell_r16__list__Format
    CO_DurationsPerCell_r16__F1 CO_DurationsPerCell_r16__F2 CO_DurationsPerCell_r16__F1F2_cond  CO_DurationsPerCell_r16__F1F2_cond2 CO_DurationsPerCell_r16__F2F1_cond.
Opaque CO_DurationsPerCell_r16__cond CO_DurationsPerCell_r16__Format.

