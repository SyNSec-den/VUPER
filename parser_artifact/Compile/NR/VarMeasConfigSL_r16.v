Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_UE_Variables.
Require Import NR.SL_MeasIdList_r16.

Opaque SL_MeasIdList_r16__cond SL_MeasIdList_r16__Format.

Require Import NR.SL_MeasObjectList_r16.

Opaque SL_MeasObjectList_r16__cond SL_MeasObjectList_r16__Format.

Require Import NR.SL_ReportConfigList_r16.

Opaque SL_ReportConfigList_r16__cond SL_ReportConfigList_r16__Format.

Require Import NR.SL_QuantityConfig_r16.

Opaque SL_QuantityConfig_r16__cond SL_QuantityConfig_r16__Format.

Record VarMeasConfigSL_r16__Type : Set :=
  make__VarMeasConfigSL_r16__Type {
    VarMeasConfigSL_r16__sl_MeasIdList_r16 : option SL_MeasIdList_r16__Type ;
    VarMeasConfigSL_r16__sl_MeasObjectList_r16 : option SL_MeasObjectList_r16__Type ;
    VarMeasConfigSL_r16__sl_reportConfigList_r16 : option SL_ReportConfigList_r16__Type ;
    VarMeasConfigSL_r16__sl_QuantityConfig_r16 : option SL_QuantityConfig_r16__Type ;
}.
Definition VarMeasConfigSL_r16__list := (
 Opt SL_MeasIdList_r16__Type SL_MeasIdList_r16__cond ::
 Opt SL_MeasObjectList_r16__Type SL_MeasObjectList_r16__cond ::
 Opt SL_ReportConfigList_r16__Type SL_ReportConfigList_r16__cond ::
 Opt SL_QuantityConfig_r16__Type SL_QuantityConfig_r16__cond ::
 nil).
Definition VarMeasConfigSL_r16__cond z := 
  opt_cond SL_MeasIdList_r16__cond (VarMeasConfigSL_r16__sl_MeasIdList_r16 z) /\
  opt_cond SL_MeasObjectList_r16__cond (VarMeasConfigSL_r16__sl_MeasObjectList_r16 z) /\
  opt_cond SL_ReportConfigList_r16__cond (VarMeasConfigSL_r16__sl_reportConfigList_r16 z) /\
  opt_cond SL_QuantityConfig_r16__cond (VarMeasConfigSL_r16__sl_QuantityConfig_r16 z) /\
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

Definition VarMeasConfigSL_r16__Format_Type := Eval cbn in seq_format_prod VarMeasConfigSL_r16__list.
Definition VarMeasConfigSL_r16__Format_list : VarMeasConfigSL_r16__Format_Type :=
  (SL_MeasIdList_r16__Format, (SL_MeasObjectList_r16__Format, (SL_ReportConfigList_r16__Format, (SL_QuantityConfig_r16__Format, unit_format)))).
Definition VarMeasConfigSL_r16__list__Format := (*Eval compute in *) seq_format VarMeasConfigSL_r16__list VarMeasConfigSL_r16__Format_list.
Definition VarMeasConfigSL_r16__F1 z :=
  (VarMeasConfigSL_r16__sl_MeasIdList_r16 z, (VarMeasConfigSL_r16__sl_MeasObjectList_r16 z, (VarMeasConfigSL_r16__sl_reportConfigList_r16 z, (VarMeasConfigSL_r16__sl_QuantityConfig_r16 z, tt)))).
Definition VarMeasConfigSL_r16__F2 (y : seq_type VarMeasConfigSL_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__VarMeasConfigSL_r16__Type i0 i1 i2 i3
  end.
Lemma VarMeasConfigSL_r16__F1F2_cond (z : VarMeasConfigSL_r16__Type)
  : VarMeasConfigSL_r16__cond z ->
  (seq_cond VarMeasConfigSL_r16__list (VarMeasConfigSL_r16__F1 z)).
intro H. unfold VarMeasConfigSL_r16__cond in H. simpl. auto. Qed.
Lemma VarMeasConfigSL_r16__F1F2_cond2 (z : VarMeasConfigSL_r16__Type)
 : VarMeasConfigSL_r16__F2 (VarMeasConfigSL_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma VarMeasConfigSL_r16__F2F1_cond (y : seq_type VarMeasConfigSL_r16__list)
  : seq_cond VarMeasConfigSL_r16__list y ->
 (VarMeasConfigSL_r16__cond (VarMeasConfigSL_r16__F2 y)) /\  VarMeasConfigSL_r16__F1 (VarMeasConfigSL_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold VarMeasConfigSL_r16__cond. simpl in *. auto.
 - simpl. unfold VarMeasConfigSL_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition VarMeasConfigSL_r16__Format : T_Format VarMeasConfigSL_r16__Type VarMeasConfigSL_r16__cond :=
        proj2_format  VarMeasConfigSL_r16__cond VarMeasConfigSL_r16__list__Format
    VarMeasConfigSL_r16__F1 VarMeasConfigSL_r16__F2 VarMeasConfigSL_r16__F1F2_cond  VarMeasConfigSL_r16__F1F2_cond2 VarMeasConfigSL_r16__F2F1_cond.
Opaque VarMeasConfigSL_r16__cond VarMeasConfigSL_r16__Format.

