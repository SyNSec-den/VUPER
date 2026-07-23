Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FrequencyInfoUL_SIB.

Opaque FrequencyInfoUL_SIB__cond FrequencyInfoUL_SIB__Format.

Require Import NR.BWP_UplinkCommon.

Opaque BWP_UplinkCommon__cond BWP_UplinkCommon__Format.

Require Import NR.TimeAlignmentTimer.

Opaque TimeAlignmentTimer__cond TimeAlignmentTimer__Format.

Record UplinkConfigCommonSIB__Type : Set :=
  make__UplinkConfigCommonSIB__Type {
    UplinkConfigCommonSIB__frequencyInfoUL : FrequencyInfoUL_SIB__Type ;
    UplinkConfigCommonSIB__initialUplinkBWP : BWP_UplinkCommon__Type ;
    UplinkConfigCommonSIB__timeAlignmentTimerCommon : TimeAlignmentTimer__Type ;
}.
Definition UplinkConfigCommonSIB__list := (
 Nor FrequencyInfoUL_SIB__Type FrequencyInfoUL_SIB__cond ::
 Nor BWP_UplinkCommon__Type BWP_UplinkCommon__cond ::
 Nor TimeAlignmentTimer__Type TimeAlignmentTimer__cond ::
 nil).
Definition UplinkConfigCommonSIB__cond z := 
  FrequencyInfoUL_SIB__cond (UplinkConfigCommonSIB__frequencyInfoUL z) /\
  BWP_UplinkCommon__cond (UplinkConfigCommonSIB__initialUplinkBWP z) /\
  TimeAlignmentTimer__cond (UplinkConfigCommonSIB__timeAlignmentTimerCommon z) /\
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

Definition UplinkConfigCommonSIB__Format_Type := Eval cbn in seq_format_prod UplinkConfigCommonSIB__list.
Definition UplinkConfigCommonSIB__Format_list : UplinkConfigCommonSIB__Format_Type :=
  (FrequencyInfoUL_SIB__Format, (BWP_UplinkCommon__Format, (TimeAlignmentTimer__Format, unit_format))).
Definition UplinkConfigCommonSIB__list__Format := (*Eval compute in *) seq_format UplinkConfigCommonSIB__list UplinkConfigCommonSIB__Format_list.
Definition UplinkConfigCommonSIB__F1 z :=
  (UplinkConfigCommonSIB__frequencyInfoUL z, (UplinkConfigCommonSIB__initialUplinkBWP z, (UplinkConfigCommonSIB__timeAlignmentTimerCommon z, tt))).
Definition UplinkConfigCommonSIB__F2 (y : seq_type UplinkConfigCommonSIB__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UplinkConfigCommonSIB__Type i0 i1 i2
  end.
Lemma UplinkConfigCommonSIB__F1F2_cond (z : UplinkConfigCommonSIB__Type)
  : UplinkConfigCommonSIB__cond z ->
  (seq_cond UplinkConfigCommonSIB__list (UplinkConfigCommonSIB__F1 z)).
intro H. unfold UplinkConfigCommonSIB__cond in H. simpl. auto. Qed.
Lemma UplinkConfigCommonSIB__F1F2_cond2 (z : UplinkConfigCommonSIB__Type)
 : UplinkConfigCommonSIB__F2 (UplinkConfigCommonSIB__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkConfigCommonSIB__F2F1_cond (y : seq_type UplinkConfigCommonSIB__list)
  : seq_cond UplinkConfigCommonSIB__list y ->
 (UplinkConfigCommonSIB__cond (UplinkConfigCommonSIB__F2 y)) /\  UplinkConfigCommonSIB__F1 (UplinkConfigCommonSIB__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkConfigCommonSIB__cond. simpl in *. auto.
 - simpl. unfold UplinkConfigCommonSIB__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkConfigCommonSIB__Format : T_Format UplinkConfigCommonSIB__Type UplinkConfigCommonSIB__cond :=
        proj2_format  UplinkConfigCommonSIB__cond UplinkConfigCommonSIB__list__Format
    UplinkConfigCommonSIB__F1 UplinkConfigCommonSIB__F2 UplinkConfigCommonSIB__F1F2_cond  UplinkConfigCommonSIB__F1F2_cond2 UplinkConfigCommonSIB__F2F1_cond.
Opaque UplinkConfigCommonSIB__cond UplinkConfigCommonSIB__Format.

