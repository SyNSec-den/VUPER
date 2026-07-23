Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FrequencyInfoUL.

Opaque FrequencyInfoUL__cond FrequencyInfoUL__Format.

Require Import NR.BWP_UplinkCommon.

Opaque BWP_UplinkCommon__cond BWP_UplinkCommon__Format.

Require Import NR.TimeAlignmentTimer.

Opaque TimeAlignmentTimer__cond TimeAlignmentTimer__Format.

Record UplinkConfigCommon__Type : Set :=
  make__UplinkConfigCommon__Type {
    UplinkConfigCommon__frequencyInfoUL : option FrequencyInfoUL__Type ;
    UplinkConfigCommon__initialUplinkBWP : option BWP_UplinkCommon__Type ;
    UplinkConfigCommon__dummy : TimeAlignmentTimer__Type ;
}.
Definition UplinkConfigCommon__list := (
 Opt FrequencyInfoUL__Type FrequencyInfoUL__cond ::
 Opt BWP_UplinkCommon__Type BWP_UplinkCommon__cond ::
 Nor TimeAlignmentTimer__Type TimeAlignmentTimer__cond ::
 nil).
Definition UplinkConfigCommon__cond z := 
  opt_cond FrequencyInfoUL__cond (UplinkConfigCommon__frequencyInfoUL z) /\
  opt_cond BWP_UplinkCommon__cond (UplinkConfigCommon__initialUplinkBWP z) /\
  TimeAlignmentTimer__cond (UplinkConfigCommon__dummy z) /\
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

Definition UplinkConfigCommon__Format_Type := Eval cbn in seq_format_prod UplinkConfigCommon__list.
Definition UplinkConfigCommon__Format_list : UplinkConfigCommon__Format_Type :=
  (FrequencyInfoUL__Format, (BWP_UplinkCommon__Format, (TimeAlignmentTimer__Format, unit_format))).
Definition UplinkConfigCommon__list__Format := (*Eval compute in *) seq_format UplinkConfigCommon__list UplinkConfigCommon__Format_list.
Definition UplinkConfigCommon__F1 z :=
  (UplinkConfigCommon__frequencyInfoUL z, (UplinkConfigCommon__initialUplinkBWP z, (UplinkConfigCommon__dummy z, tt))).
Definition UplinkConfigCommon__F2 (y : seq_type UplinkConfigCommon__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UplinkConfigCommon__Type i0 i1 i2
  end.
Lemma UplinkConfigCommon__F1F2_cond (z : UplinkConfigCommon__Type)
  : UplinkConfigCommon__cond z ->
  (seq_cond UplinkConfigCommon__list (UplinkConfigCommon__F1 z)).
intro H. unfold UplinkConfigCommon__cond in H. simpl. auto. Qed.
Lemma UplinkConfigCommon__F1F2_cond2 (z : UplinkConfigCommon__Type)
 : UplinkConfigCommon__F2 (UplinkConfigCommon__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkConfigCommon__F2F1_cond (y : seq_type UplinkConfigCommon__list)
  : seq_cond UplinkConfigCommon__list y ->
 (UplinkConfigCommon__cond (UplinkConfigCommon__F2 y)) /\  UplinkConfigCommon__F1 (UplinkConfigCommon__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkConfigCommon__cond. simpl in *. auto.
 - simpl. unfold UplinkConfigCommon__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkConfigCommon__Format : T_Format UplinkConfigCommon__Type UplinkConfigCommon__cond :=
        proj2_format  UplinkConfigCommon__cond UplinkConfigCommon__list__Format
    UplinkConfigCommon__F1 UplinkConfigCommon__F2 UplinkConfigCommon__F1F2_cond  UplinkConfigCommon__F1F2_cond2 UplinkConfigCommon__F2F1_cond.
Opaque UplinkConfigCommon__cond UplinkConfigCommon__Format.

