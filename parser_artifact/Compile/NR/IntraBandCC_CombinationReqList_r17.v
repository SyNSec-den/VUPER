Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__Type := list ServCellIndex__Type.

Lemma IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__cond (z : IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.IntraBandCC_Combination_r17.

Opaque IntraBandCC_Combination_r17__cond IntraBandCC_Combination_r17__Format.

Definition IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__Type := list IntraBandCC_Combination_r17__Type.

Lemma IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__helper1 : (0 <= 1 <= maxNrofReqComDC_Location_r17)%Z. unfold maxNrofReqComDC_Location_r17.
 lia. Qed.
Lemma IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofReqComDC_Location_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofReqComDC_Location_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__cond (z : IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofReqComDC_Location_r17)%Z /\ (list_and IntraBandCC_Combination_r17__cond z) .

Record IntraBandCC_CombinationReqList_r17__Type : Set :=
  make__IntraBandCC_CombinationReqList_r17__Type {
    IntraBandCC_CombinationReqList_r17__servCellIndexList_r17 : IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__Type ;
    IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17 : IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__Type ;
}.
Definition IntraBandCC_CombinationReqList_r17__list := (
 Nor IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__Type IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__cond ::
 Nor IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__Type IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__cond ::
 nil).
Definition IntraBandCC_CombinationReqList_r17__cond z := 
  IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__cond (IntraBandCC_CombinationReqList_r17__servCellIndexList_r17 z) /\
  IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__cond (IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17 z) /\
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
Definition IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__Format : T_Format IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__Type IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCells IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__helper1 IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__helper2.

Opaque IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__cond IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__Format.

Definition IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__Format : T_Format IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__Type IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__cond := seq_of_format IntraBandCC_Combination_r17__Format 1 maxNrofReqComDC_Location_r17 IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__helper1 IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__helper2.

Opaque IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__cond IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__Format.


Definition IntraBandCC_CombinationReqList_r17__Format_Type := Eval cbn in seq_format_prod IntraBandCC_CombinationReqList_r17__list.
Definition IntraBandCC_CombinationReqList_r17__Format_list : IntraBandCC_CombinationReqList_r17__Format_Type :=
  (IntraBandCC_CombinationReqList_r17__servCellIndexList_r17__Format, (IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17__Format, unit_format)).
Definition IntraBandCC_CombinationReqList_r17__list__Format := (*Eval compute in *) seq_format IntraBandCC_CombinationReqList_r17__list IntraBandCC_CombinationReqList_r17__Format_list.
Definition IntraBandCC_CombinationReqList_r17__F1 z :=
  (IntraBandCC_CombinationReqList_r17__servCellIndexList_r17 z, (IntraBandCC_CombinationReqList_r17__cc_CombinationList_r17 z, tt)).
Definition IntraBandCC_CombinationReqList_r17__F2 (y : seq_type IntraBandCC_CombinationReqList_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__IntraBandCC_CombinationReqList_r17__Type i0 i1
  end.
Lemma IntraBandCC_CombinationReqList_r17__F1F2_cond (z : IntraBandCC_CombinationReqList_r17__Type)
  : IntraBandCC_CombinationReqList_r17__cond z ->
  (seq_cond IntraBandCC_CombinationReqList_r17__list (IntraBandCC_CombinationReqList_r17__F1 z)).
intro H. unfold IntraBandCC_CombinationReqList_r17__cond in H. simpl. auto. Qed.
Lemma IntraBandCC_CombinationReqList_r17__F1F2_cond2 (z : IntraBandCC_CombinationReqList_r17__Type)
 : IntraBandCC_CombinationReqList_r17__F2 (IntraBandCC_CombinationReqList_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma IntraBandCC_CombinationReqList_r17__F2F1_cond (y : seq_type IntraBandCC_CombinationReqList_r17__list)
  : seq_cond IntraBandCC_CombinationReqList_r17__list y ->
 (IntraBandCC_CombinationReqList_r17__cond (IntraBandCC_CombinationReqList_r17__F2 y)) /\  IntraBandCC_CombinationReqList_r17__F1 (IntraBandCC_CombinationReqList_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold IntraBandCC_CombinationReqList_r17__cond. simpl in *. auto.
 - simpl. unfold IntraBandCC_CombinationReqList_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition IntraBandCC_CombinationReqList_r17__Format : T_Format IntraBandCC_CombinationReqList_r17__Type IntraBandCC_CombinationReqList_r17__cond :=
        proj2_format  IntraBandCC_CombinationReqList_r17__cond IntraBandCC_CombinationReqList_r17__list__Format
    IntraBandCC_CombinationReqList_r17__F1 IntraBandCC_CombinationReqList_r17__F2 IntraBandCC_CombinationReqList_r17__F1F2_cond  IntraBandCC_CombinationReqList_r17__F1F2_cond2 IntraBandCC_CombinationReqList_r17__F2F1_cond.
Opaque IntraBandCC_CombinationReqList_r17__cond IntraBandCC_CombinationReqList_r17__Format.

