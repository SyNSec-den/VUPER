Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RSSI_Range_r16.

Opaque RSSI_Range_r16__cond RSSI_Range_r16__Format.

Record MeasRSSI_ReportConfig_r16__Type : Set :=
  make__MeasRSSI_ReportConfig_r16__Type {
    MeasRSSI_ReportConfig_r16__channelOccupancyThreshold_r16 : option RSSI_Range_r16__Type ;
}.
Definition MeasRSSI_ReportConfig_r16__list := (
 Opt RSSI_Range_r16__Type RSSI_Range_r16__cond ::
 nil).
Definition MeasRSSI_ReportConfig_r16__cond z := 
  opt_cond RSSI_Range_r16__cond (MeasRSSI_ReportConfig_r16__channelOccupancyThreshold_r16 z) /\
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

Definition MeasRSSI_ReportConfig_r16__Format_Type := Eval cbn in seq_format_prod MeasRSSI_ReportConfig_r16__list.
Definition MeasRSSI_ReportConfig_r16__Format_list : MeasRSSI_ReportConfig_r16__Format_Type :=
  (RSSI_Range_r16__Format, unit_format).
Definition MeasRSSI_ReportConfig_r16__list__Format := (*Eval compute in *) seq_format MeasRSSI_ReportConfig_r16__list MeasRSSI_ReportConfig_r16__Format_list.
Definition MeasRSSI_ReportConfig_r16__F1 z :=
  (MeasRSSI_ReportConfig_r16__channelOccupancyThreshold_r16 z, tt).
Definition MeasRSSI_ReportConfig_r16__F2 (y : seq_type MeasRSSI_ReportConfig_r16__list) :=
  match y with
  | (i0, _)=>
    make__MeasRSSI_ReportConfig_r16__Type i0
  end.
Lemma MeasRSSI_ReportConfig_r16__F1F2_cond (z : MeasRSSI_ReportConfig_r16__Type)
  : MeasRSSI_ReportConfig_r16__cond z ->
  (seq_cond MeasRSSI_ReportConfig_r16__list (MeasRSSI_ReportConfig_r16__F1 z)).
intro H. unfold MeasRSSI_ReportConfig_r16__cond in H. simpl. auto. Qed.
Lemma MeasRSSI_ReportConfig_r16__F1F2_cond2 (z : MeasRSSI_ReportConfig_r16__Type)
 : MeasRSSI_ReportConfig_r16__F2 (MeasRSSI_ReportConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasRSSI_ReportConfig_r16__F2F1_cond (y : seq_type MeasRSSI_ReportConfig_r16__list)
  : seq_cond MeasRSSI_ReportConfig_r16__list y ->
 (MeasRSSI_ReportConfig_r16__cond (MeasRSSI_ReportConfig_r16__F2 y)) /\  MeasRSSI_ReportConfig_r16__F1 (MeasRSSI_ReportConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasRSSI_ReportConfig_r16__cond. simpl in *. auto.
 - simpl. unfold MeasRSSI_ReportConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasRSSI_ReportConfig_r16__Format : T_Format MeasRSSI_ReportConfig_r16__Type MeasRSSI_ReportConfig_r16__cond :=
        proj2_format  MeasRSSI_ReportConfig_r16__cond MeasRSSI_ReportConfig_r16__list__Format
    MeasRSSI_ReportConfig_r16__F1 MeasRSSI_ReportConfig_r16__F2 MeasRSSI_ReportConfig_r16__F1F2_cond  MeasRSSI_ReportConfig_r16__F1F2_cond2 MeasRSSI_ReportConfig_r16__F2F1_cond.
Opaque MeasRSSI_ReportConfig_r16__cond MeasRSSI_ReportConfig_r16__Format.

