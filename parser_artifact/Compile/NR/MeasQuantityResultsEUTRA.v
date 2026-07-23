Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSRP_RangeEUTRA.

Opaque RSRP_RangeEUTRA__cond RSRP_RangeEUTRA__Format.

Require Import NR.RSRQ_RangeEUTRA.

Opaque RSRQ_RangeEUTRA__cond RSRQ_RangeEUTRA__Format.

Require Import NR.SINR_RangeEUTRA.

Opaque SINR_RangeEUTRA__cond SINR_RangeEUTRA__Format.

Record MeasQuantityResultsEUTRA__Type : Set :=
  make__MeasQuantityResultsEUTRA__Type {
    MeasQuantityResultsEUTRA__rsrp : option RSRP_RangeEUTRA__Type ;
    MeasQuantityResultsEUTRA__rsrq : option RSRQ_RangeEUTRA__Type ;
    MeasQuantityResultsEUTRA__sinr : option SINR_RangeEUTRA__Type ;
}.
Definition MeasQuantityResultsEUTRA__list := (
 Opt RSRP_RangeEUTRA__Type RSRP_RangeEUTRA__cond ::
 Opt RSRQ_RangeEUTRA__Type RSRQ_RangeEUTRA__cond ::
 Opt SINR_RangeEUTRA__Type SINR_RangeEUTRA__cond ::
 nil).
Definition MeasQuantityResultsEUTRA__cond z := 
  opt_cond RSRP_RangeEUTRA__cond (MeasQuantityResultsEUTRA__rsrp z) /\
  opt_cond RSRQ_RangeEUTRA__cond (MeasQuantityResultsEUTRA__rsrq z) /\
  opt_cond SINR_RangeEUTRA__cond (MeasQuantityResultsEUTRA__sinr z) /\
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

Definition MeasQuantityResultsEUTRA__Format_Type := Eval cbn in seq_format_prod MeasQuantityResultsEUTRA__list.
Definition MeasQuantityResultsEUTRA__Format_list : MeasQuantityResultsEUTRA__Format_Type :=
  (RSRP_RangeEUTRA__Format, (RSRQ_RangeEUTRA__Format, (SINR_RangeEUTRA__Format, unit_format))).
Definition MeasQuantityResultsEUTRA__list__Format := (*Eval compute in *) seq_format MeasQuantityResultsEUTRA__list MeasQuantityResultsEUTRA__Format_list.
Definition MeasQuantityResultsEUTRA__F1 z :=
  (MeasQuantityResultsEUTRA__rsrp z, (MeasQuantityResultsEUTRA__rsrq z, (MeasQuantityResultsEUTRA__sinr z, tt))).
Definition MeasQuantityResultsEUTRA__F2 (y : seq_type MeasQuantityResultsEUTRA__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasQuantityResultsEUTRA__Type i0 i1 i2
  end.
Lemma MeasQuantityResultsEUTRA__F1F2_cond (z : MeasQuantityResultsEUTRA__Type)
  : MeasQuantityResultsEUTRA__cond z ->
  (seq_cond MeasQuantityResultsEUTRA__list (MeasQuantityResultsEUTRA__F1 z)).
intro H. unfold MeasQuantityResultsEUTRA__cond in H. simpl. auto. Qed.
Lemma MeasQuantityResultsEUTRA__F1F2_cond2 (z : MeasQuantityResultsEUTRA__Type)
 : MeasQuantityResultsEUTRA__F2 (MeasQuantityResultsEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasQuantityResultsEUTRA__F2F1_cond (y : seq_type MeasQuantityResultsEUTRA__list)
  : seq_cond MeasQuantityResultsEUTRA__list y ->
 (MeasQuantityResultsEUTRA__cond (MeasQuantityResultsEUTRA__F2 y)) /\  MeasQuantityResultsEUTRA__F1 (MeasQuantityResultsEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasQuantityResultsEUTRA__cond. simpl in *. auto.
 - simpl. unfold MeasQuantityResultsEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasQuantityResultsEUTRA__Format : T_Format MeasQuantityResultsEUTRA__Type MeasQuantityResultsEUTRA__cond :=
        proj2_format  MeasQuantityResultsEUTRA__cond MeasQuantityResultsEUTRA__list__Format
    MeasQuantityResultsEUTRA__F1 MeasQuantityResultsEUTRA__F2 MeasQuantityResultsEUTRA__F1F2_cond  MeasQuantityResultsEUTRA__F1F2_cond2 MeasQuantityResultsEUTRA__F2F1_cond.
Opaque MeasQuantityResultsEUTRA__cond MeasQuantityResultsEUTRA__Format.

