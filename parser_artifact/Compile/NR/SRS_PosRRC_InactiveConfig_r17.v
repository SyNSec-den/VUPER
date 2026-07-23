Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_PosConfig_r17.

Opaque SRS_PosConfig_r17__cond SRS_PosConfig_r17__Format.

Require Import NR.SRS_PosConfig_r17.

Opaque SRS_PosConfig_r17__cond SRS_PosConfig_r17__Format.

Require Import NR.BWP.

Opaque BWP__cond BWP__Format.

Require Import NR.BWP.

Opaque BWP__cond BWP__Format.

Require Import NR.TimeAlignmentTimer.

Opaque TimeAlignmentTimer__cond TimeAlignmentTimer__Format.

Require Import NR.RSRP_ChangeThreshold_r17.

Opaque RSRP_ChangeThreshold_r17__cond RSRP_ChangeThreshold_r17__Format.

Record SRS_PosRRC_InactiveConfig_r17__Type : Set :=
  make__SRS_PosRRC_InactiveConfig_r17__Type {
    SRS_PosRRC_InactiveConfig_r17__srs_PosConfigNUL_r17 : option SRS_PosConfig_r17__Type ;
    SRS_PosRRC_InactiveConfig_r17__srs_PosConfigSUL_r17 : option SRS_PosConfig_r17__Type ;
    SRS_PosRRC_InactiveConfig_r17__bwp_NUL_r17 : option BWP__Type ;
    SRS_PosRRC_InactiveConfig_r17__bwp_SUL_r17 : option BWP__Type ;
    SRS_PosRRC_InactiveConfig_r17__inactivePosSRS_TimeAlignmentTimer_r17 : option TimeAlignmentTimer__Type ;
    SRS_PosRRC_InactiveConfig_r17__inactivePosSRS_RSRP_ChangeThreshold_r17 : option RSRP_ChangeThreshold_r17__Type ;
}.
Definition SRS_PosRRC_InactiveConfig_r17__list := (
 Opt SRS_PosConfig_r17__Type SRS_PosConfig_r17__cond ::
 Opt SRS_PosConfig_r17__Type SRS_PosConfig_r17__cond ::
 Opt BWP__Type BWP__cond ::
 Opt BWP__Type BWP__cond ::
 Opt TimeAlignmentTimer__Type TimeAlignmentTimer__cond ::
 Opt RSRP_ChangeThreshold_r17__Type RSRP_ChangeThreshold_r17__cond ::
 nil).
Definition SRS_PosRRC_InactiveConfig_r17__cond z := 
  opt_cond SRS_PosConfig_r17__cond (SRS_PosRRC_InactiveConfig_r17__srs_PosConfigNUL_r17 z) /\
  opt_cond SRS_PosConfig_r17__cond (SRS_PosRRC_InactiveConfig_r17__srs_PosConfigSUL_r17 z) /\
  opt_cond BWP__cond (SRS_PosRRC_InactiveConfig_r17__bwp_NUL_r17 z) /\
  opt_cond BWP__cond (SRS_PosRRC_InactiveConfig_r17__bwp_SUL_r17 z) /\
  opt_cond TimeAlignmentTimer__cond (SRS_PosRRC_InactiveConfig_r17__inactivePosSRS_TimeAlignmentTimer_r17 z) /\
  opt_cond RSRP_ChangeThreshold_r17__cond (SRS_PosRRC_InactiveConfig_r17__inactivePosSRS_RSRP_ChangeThreshold_r17 z) /\
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

Definition SRS_PosRRC_InactiveConfig_r17__Format_Type := Eval cbn in seq_format_prod SRS_PosRRC_InactiveConfig_r17__list.
Definition SRS_PosRRC_InactiveConfig_r17__Format_list : SRS_PosRRC_InactiveConfig_r17__Format_Type :=
  (SRS_PosConfig_r17__Format, (SRS_PosConfig_r17__Format, (BWP__Format, (BWP__Format, (TimeAlignmentTimer__Format, (RSRP_ChangeThreshold_r17__Format, unit_format)))))).
Definition SRS_PosRRC_InactiveConfig_r17__list__Format := (*Eval compute in *) seq_format SRS_PosRRC_InactiveConfig_r17__list SRS_PosRRC_InactiveConfig_r17__Format_list.
Definition SRS_PosRRC_InactiveConfig_r17__F1 z :=
  (SRS_PosRRC_InactiveConfig_r17__srs_PosConfigNUL_r17 z, (SRS_PosRRC_InactiveConfig_r17__srs_PosConfigSUL_r17 z, (SRS_PosRRC_InactiveConfig_r17__bwp_NUL_r17 z, (SRS_PosRRC_InactiveConfig_r17__bwp_SUL_r17 z, (SRS_PosRRC_InactiveConfig_r17__inactivePosSRS_TimeAlignmentTimer_r17 z, (SRS_PosRRC_InactiveConfig_r17__inactivePosSRS_RSRP_ChangeThreshold_r17 z, tt)))))).
Definition SRS_PosRRC_InactiveConfig_r17__F2 (y : seq_type SRS_PosRRC_InactiveConfig_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__SRS_PosRRC_InactiveConfig_r17__Type i0 i1 i2 i3 i4 i5
  end.
Lemma SRS_PosRRC_InactiveConfig_r17__F1F2_cond (z : SRS_PosRRC_InactiveConfig_r17__Type)
  : SRS_PosRRC_InactiveConfig_r17__cond z ->
  (seq_cond SRS_PosRRC_InactiveConfig_r17__list (SRS_PosRRC_InactiveConfig_r17__F1 z)).
intro H. unfold SRS_PosRRC_InactiveConfig_r17__cond in H. simpl. auto. Qed.
Lemma SRS_PosRRC_InactiveConfig_r17__F1F2_cond2 (z : SRS_PosRRC_InactiveConfig_r17__Type)
 : SRS_PosRRC_InactiveConfig_r17__F2 (SRS_PosRRC_InactiveConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_PosRRC_InactiveConfig_r17__F2F1_cond (y : seq_type SRS_PosRRC_InactiveConfig_r17__list)
  : seq_cond SRS_PosRRC_InactiveConfig_r17__list y ->
 (SRS_PosRRC_InactiveConfig_r17__cond (SRS_PosRRC_InactiveConfig_r17__F2 y)) /\  SRS_PosRRC_InactiveConfig_r17__F1 (SRS_PosRRC_InactiveConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_PosRRC_InactiveConfig_r17__cond. simpl in *. auto.
 - simpl. unfold SRS_PosRRC_InactiveConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_PosRRC_InactiveConfig_r17__Format : T_Format SRS_PosRRC_InactiveConfig_r17__Type SRS_PosRRC_InactiveConfig_r17__cond :=
        proj2_format  SRS_PosRRC_InactiveConfig_r17__cond SRS_PosRRC_InactiveConfig_r17__list__Format
    SRS_PosRRC_InactiveConfig_r17__F1 SRS_PosRRC_InactiveConfig_r17__F2 SRS_PosRRC_InactiveConfig_r17__F1F2_cond  SRS_PosRRC_InactiveConfig_r17__F1F2_cond2 SRS_PosRRC_InactiveConfig_r17__F2F1_cond.
Opaque SRS_PosRRC_InactiveConfig_r17__cond SRS_PosRRC_InactiveConfig_r17__Format.

