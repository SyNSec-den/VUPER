Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRQ_Range.

Opaque RSRQ_Range__cond RSRQ_Range__Format.

Require Import NR.SINR_Range.

Opaque SINR_Range__cond SINR_Range__Format.

Record MeasQuantityResults__Type : Set :=
  make__MeasQuantityResults__Type {
    MeasQuantityResults__rsrp : option RSRP_Range__Type ;
    MeasQuantityResults__rsrq : option RSRQ_Range__Type ;
    MeasQuantityResults__sinr : option SINR_Range__Type ;
}.
Definition MeasQuantityResults__list := (
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt RSRQ_Range__Type RSRQ_Range__cond ::
 Opt SINR_Range__Type SINR_Range__cond ::
 nil).
Definition MeasQuantityResults__cond z := 
  opt_cond RSRP_Range__cond (MeasQuantityResults__rsrp z) /\
  opt_cond RSRQ_Range__cond (MeasQuantityResults__rsrq z) /\
  opt_cond SINR_Range__cond (MeasQuantityResults__sinr z) /\
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

Definition MeasQuantityResults__Format_Type := Eval cbn in seq_format_prod MeasQuantityResults__list.
Definition MeasQuantityResults__Format_list : MeasQuantityResults__Format_Type :=
  (RSRP_Range__Format, (RSRQ_Range__Format, (SINR_Range__Format, unit_format))).
Definition MeasQuantityResults__list__Format := (*Eval compute in *) seq_format MeasQuantityResults__list MeasQuantityResults__Format_list.
Definition MeasQuantityResults__F1 z :=
  (MeasQuantityResults__rsrp z, (MeasQuantityResults__rsrq z, (MeasQuantityResults__sinr z, tt))).
Definition MeasQuantityResults__F2 (y : seq_type MeasQuantityResults__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasQuantityResults__Type i0 i1 i2
  end.
Lemma MeasQuantityResults__F1F2_cond (z : MeasQuantityResults__Type)
  : MeasQuantityResults__cond z ->
  (seq_cond MeasQuantityResults__list (MeasQuantityResults__F1 z)).
intro H. unfold MeasQuantityResults__cond in H. simpl. auto. Qed.
Lemma MeasQuantityResults__F1F2_cond2 (z : MeasQuantityResults__Type)
 : MeasQuantityResults__F2 (MeasQuantityResults__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasQuantityResults__F2F1_cond (y : seq_type MeasQuantityResults__list)
  : seq_cond MeasQuantityResults__list y ->
 (MeasQuantityResults__cond (MeasQuantityResults__F2 y)) /\  MeasQuantityResults__F1 (MeasQuantityResults__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasQuantityResults__cond. simpl in *. auto.
 - simpl. unfold MeasQuantityResults__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasQuantityResults__Format : T_Format MeasQuantityResults__Type MeasQuantityResults__cond :=
        proj2_format  MeasQuantityResults__cond MeasQuantityResults__list__Format
    MeasQuantityResults__F1 MeasQuantityResults__F2 MeasQuantityResults__F1F2_cond  MeasQuantityResults__F1F2_cond2 MeasQuantityResults__F2F1_cond.
Opaque MeasQuantityResults__cond MeasQuantityResults__Format.

