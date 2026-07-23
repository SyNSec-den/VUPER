Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.MultiFrequencyBandListNR.

Opaque MultiFrequencyBandListNR__cond MultiFrequencyBandListNR__Format.

Require Import NR.CellListNR_r16.

Opaque CellListNR_r16__cond CellListNR_r16__Format.

Inductive MeasIdleCarrierNR_r16__reportQuantities_r16__Type : Set :=
 | MeasIdleCarrierNR_r16__reportQuantities_r16__rsrp
 | MeasIdleCarrierNR_r16__reportQuantities_r16__rsrq
 | MeasIdleCarrierNR_r16__reportQuantities_r16__both
.
Definition MeasIdleCarrierNR_r16__reportQuantities_r16__cond := (fun (_ : MeasIdleCarrierNR_r16__reportQuantities_r16__Type) => True).
Lemma MeasIdleCarrierNR_r16__reportQuantities_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasIdleCarrierNR_r16__reportQuantities_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MeasIdleCarrierNR_r16__reportQuantities_r16__nat__helper.

Definition MeasIdleCarrierNR_r16__reportQuantities_r16__F1 t :=
  match t with
  | MeasIdleCarrierNR_r16__reportQuantities_r16__rsrp => 0
  | MeasIdleCarrierNR_r16__reportQuantities_r16__rsrq => 1
  | MeasIdleCarrierNR_r16__reportQuantities_r16__both => 2
  end.
Definition MeasIdleCarrierNR_r16__reportQuantities_r16__F2 n :=
  match n with
  | 0 => MeasIdleCarrierNR_r16__reportQuantities_r16__rsrp
  | 1 => MeasIdleCarrierNR_r16__reportQuantities_r16__rsrq
  | 2 => MeasIdleCarrierNR_r16__reportQuantities_r16__both
  | _ => MeasIdleCarrierNR_r16__reportQuantities_r16__rsrp
  end.
Lemma MeasIdleCarrierNR_r16__reportQuantities_r16__F1F2 : forall x : MeasIdleCarrierNR_r16__reportQuantities_r16__Type, (MeasIdleCarrierNR_r16__reportQuantities_r16__F1 x <= 2) /\ MeasIdleCarrierNR_r16__reportQuantities_r16__F2 (MeasIdleCarrierNR_r16__reportQuantities_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasIdleCarrierNR_r16__reportQuantities_r16__F2F1 : forall (y : nat) (H : y <= 2), MeasIdleCarrierNR_r16__reportQuantities_r16__F1 (MeasIdleCarrierNR_r16__reportQuantities_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRQ_Range.

Opaque RSRQ_Range__cond RSRQ_Range__Format.

Record MeasIdleCarrierNR_r16__qualityThreshold_r16__Type : Set :=
  make__MeasIdleCarrierNR_r16__qualityThreshold_r16__Type {
    MeasIdleCarrierNR_r16__qualityThreshold_r16__idleRSRP_Threshold_NR_r16 : option RSRP_Range__Type ;
    MeasIdleCarrierNR_r16__qualityThreshold_r16__idleRSRQ_Threshold_NR_r16 : option RSRQ_Range__Type ;
}.
Definition MeasIdleCarrierNR_r16__qualityThreshold_r16__list := (
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt RSRQ_Range__Type RSRQ_Range__cond ::
 nil).
Definition MeasIdleCarrierNR_r16__qualityThreshold_r16__cond z := 
  opt_cond RSRP_Range__cond (MeasIdleCarrierNR_r16__qualityThreshold_r16__idleRSRP_Threshold_NR_r16 z) /\
  opt_cond RSRQ_Range__cond (MeasIdleCarrierNR_r16__qualityThreshold_r16__idleRSRQ_Threshold_NR_r16 z) /\
  True.

Lemma MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__helper1 : (2 <= maxNrofSS_BlocksToAverage)%Z. unfold maxNrofSS_BlocksToAverage.
 lia. Qed.
Lemma MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSS_BlocksToAverage - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSS_BlocksToAverage - 2))%Z). { apply Zorder.Zle_minus_le_0. apply MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__Type := Z.
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__cond := (fun z => (2 <= z <= maxNrofSS_BlocksToAverage)%Z).
Require Import NR.ThresholdNR.

Opaque ThresholdNR__cond ThresholdNR__Format.

Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Require Import NR.SSB_ToMeasure.

Opaque SSB_ToMeasure__cond SSB_ToMeasure__Format.

Require Import NR.SS_RSSI_Measurement.

Opaque SS_RSSI_Measurement__cond SS_RSSI_Measurement__Format.

Record MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Type : Set :=
  make__MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Type {
    MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16 : option Z ;
    MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__absThreshSS_BlocksConsolidation_r16 : option ThresholdNR__Type ;
    MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__smtc_r16 : option SSB_MTC__Type ;
    MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__ssb_ToMeasure_r16 : option SSB_ToMeasure__Type ;
    MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__deriveSSB_IndexFromCell_r16 : bool ;
    MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__ss_RSSI_Measurement_r16 : option SS_RSSI_Measurement__Type ;
}.
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list := (
 Opt Z MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__cond ::
 Opt ThresholdNR__Type ThresholdNR__cond ::
 Opt SSB_MTC__Type SSB_MTC__cond ::
 Opt SSB_ToMeasure__Type SSB_ToMeasure__cond ::
 Nor bool (fun _ => True) ::
 Opt SS_RSSI_Measurement__Type SS_RSSI_Measurement__cond ::
 nil).
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond z := 
  opt_cond MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__cond (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16 z) /\
  opt_cond ThresholdNR__cond (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__absThreshSS_BlocksConsolidation_r16 z) /\
  opt_cond SSB_MTC__cond (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__smtc_r16 z) /\
  opt_cond SSB_ToMeasure__cond (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__ssb_ToMeasure_r16 z) /\
  (fun _ => True) (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__deriveSSB_IndexFromCell_r16 z) /\
  opt_cond SS_RSSI_Measurement__cond (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__ss_RSSI_Measurement_r16 z) /\
  True.

Require Import NR.BeamMeasConfigIdle_NR_r16.

Opaque BeamMeasConfigIdle_NR_r16__cond BeamMeasConfigIdle_NR_r16__Format.

Record MeasIdleCarrierNR_r16__Type : Set :=
  make__MeasIdleCarrierNR_r16__Type {
    MeasIdleCarrierNR_r16__carrierFreq_r16 : ARFCN_ValueNR__Type ;
    MeasIdleCarrierNR_r16__ssbSubcarrierSpacing_r16 : SubcarrierSpacing__Type ;
    MeasIdleCarrierNR_r16__frequencyBandList : option MultiFrequencyBandListNR__Type ;
    MeasIdleCarrierNR_r16__measCellListNR_r16 : option CellListNR_r16__Type ;
    MeasIdleCarrierNR_r16__reportQuantities_r16 : MeasIdleCarrierNR_r16__reportQuantities_r16__Type ;
    MeasIdleCarrierNR_r16__qualityThreshold_r16 : option MeasIdleCarrierNR_r16__qualityThreshold_r16__Type ;
    MeasIdleCarrierNR_r16__ssb_MeasConfig_r16 : option MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Type ;
    MeasIdleCarrierNR_r16__beamMeasConfigIdle_r16 : option BeamMeasConfigIdle_NR_r16__Type ;
}.
Definition MeasIdleCarrierNR_r16__root_list : list seq_elem := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt MultiFrequencyBandListNR__Type MultiFrequencyBandListNR__cond ::
 Opt CellListNR_r16__Type CellListNR_r16__cond ::
 Nor MeasIdleCarrierNR_r16__reportQuantities_r16__Type MeasIdleCarrierNR_r16__reportQuantities_r16__cond ::
 Opt MeasIdleCarrierNR_r16__qualityThreshold_r16__Type MeasIdleCarrierNR_r16__qualityThreshold_r16__cond ::
 Opt MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Type MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond ::
 Opt BeamMeasConfigIdle_NR_r16__Type BeamMeasConfigIdle_NR_r16__cond ::
 nil).
Definition MeasIdleCarrierNR_r16__ext_list : list typ := (
  nil).
Definition MeasIdleCarrierNR_r16__cond (z : MeasIdleCarrierNR_r16__Type) := 
(  ARFCN_ValueNR__cond (MeasIdleCarrierNR_r16__carrierFreq_r16 z) /\
  SubcarrierSpacing__cond (MeasIdleCarrierNR_r16__ssbSubcarrierSpacing_r16 z) /\
  opt_cond MultiFrequencyBandListNR__cond (MeasIdleCarrierNR_r16__frequencyBandList z) /\
  opt_cond CellListNR_r16__cond (MeasIdleCarrierNR_r16__measCellListNR_r16 z) /\
  MeasIdleCarrierNR_r16__reportQuantities_r16__cond (MeasIdleCarrierNR_r16__reportQuantities_r16 z) /\
  opt_cond MeasIdleCarrierNR_r16__qualityThreshold_r16__cond (MeasIdleCarrierNR_r16__qualityThreshold_r16 z) /\
  opt_cond MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16 z) /\
  opt_cond BeamMeasConfigIdle_NR_r16__cond (MeasIdleCarrierNR_r16__beamMeasConfigIdle_r16 z) /\
  True) /\ 
(  True).


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
Definition MeasIdleCarrierNR_r16__reportQuantities_r16__Format : T_Format MeasIdleCarrierNR_r16__reportQuantities_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasIdleCarrierNR_r16__reportQuantities_r16__nat__Format MeasIdleCarrierNR_r16__reportQuantities_r16__F1 MeasIdleCarrierNR_r16__reportQuantities_r16__F2 MeasIdleCarrierNR_r16__reportQuantities_r16__F1F2 MeasIdleCarrierNR_r16__reportQuantities_r16__F2F1.

Opaque MeasIdleCarrierNR_r16__reportQuantities_r16__cond MeasIdleCarrierNR_r16__reportQuantities_r16__Format.


Definition MeasIdleCarrierNR_r16__qualityThreshold_r16__Format_Type := Eval cbn in seq_format_prod MeasIdleCarrierNR_r16__qualityThreshold_r16__list.
Definition MeasIdleCarrierNR_r16__qualityThreshold_r16__Format_list : MeasIdleCarrierNR_r16__qualityThreshold_r16__Format_Type :=
  (RSRP_Range__Format, (RSRQ_Range__Format, unit_format)).
Definition MeasIdleCarrierNR_r16__qualityThreshold_r16__list__Format := (*Eval compute in *) seq_format MeasIdleCarrierNR_r16__qualityThreshold_r16__list MeasIdleCarrierNR_r16__qualityThreshold_r16__Format_list.
Definition MeasIdleCarrierNR_r16__qualityThreshold_r16__F1 z :=
  (MeasIdleCarrierNR_r16__qualityThreshold_r16__idleRSRP_Threshold_NR_r16 z, (MeasIdleCarrierNR_r16__qualityThreshold_r16__idleRSRQ_Threshold_NR_r16 z, tt)).
Definition MeasIdleCarrierNR_r16__qualityThreshold_r16__F2 (y : seq_type MeasIdleCarrierNR_r16__qualityThreshold_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasIdleCarrierNR_r16__qualityThreshold_r16__Type i0 i1
  end.
Lemma MeasIdleCarrierNR_r16__qualityThreshold_r16__F1F2_cond (z : MeasIdleCarrierNR_r16__qualityThreshold_r16__Type)
  : MeasIdleCarrierNR_r16__qualityThreshold_r16__cond z ->
  (seq_cond MeasIdleCarrierNR_r16__qualityThreshold_r16__list (MeasIdleCarrierNR_r16__qualityThreshold_r16__F1 z)).
intro H. unfold MeasIdleCarrierNR_r16__qualityThreshold_r16__cond in H. simpl. auto. Qed.
Lemma MeasIdleCarrierNR_r16__qualityThreshold_r16__F1F2_cond2 (z : MeasIdleCarrierNR_r16__qualityThreshold_r16__Type)
 : MeasIdleCarrierNR_r16__qualityThreshold_r16__F2 (MeasIdleCarrierNR_r16__qualityThreshold_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasIdleCarrierNR_r16__qualityThreshold_r16__F2F1_cond (y : seq_type MeasIdleCarrierNR_r16__qualityThreshold_r16__list)
  : seq_cond MeasIdleCarrierNR_r16__qualityThreshold_r16__list y ->
 (MeasIdleCarrierNR_r16__qualityThreshold_r16__cond (MeasIdleCarrierNR_r16__qualityThreshold_r16__F2 y)) /\  MeasIdleCarrierNR_r16__qualityThreshold_r16__F1 (MeasIdleCarrierNR_r16__qualityThreshold_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasIdleCarrierNR_r16__qualityThreshold_r16__cond. simpl in *. auto.
 - simpl. unfold MeasIdleCarrierNR_r16__qualityThreshold_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasIdleCarrierNR_r16__qualityThreshold_r16__Format : T_Format MeasIdleCarrierNR_r16__qualityThreshold_r16__Type MeasIdleCarrierNR_r16__qualityThreshold_r16__cond :=
        proj2_format  MeasIdleCarrierNR_r16__qualityThreshold_r16__cond MeasIdleCarrierNR_r16__qualityThreshold_r16__list__Format
    MeasIdleCarrierNR_r16__qualityThreshold_r16__F1 MeasIdleCarrierNR_r16__qualityThreshold_r16__F2 MeasIdleCarrierNR_r16__qualityThreshold_r16__F1F2_cond  MeasIdleCarrierNR_r16__qualityThreshold_r16__F1F2_cond2 MeasIdleCarrierNR_r16__qualityThreshold_r16__F2F1_cond.
Opaque MeasIdleCarrierNR_r16__qualityThreshold_r16__cond MeasIdleCarrierNR_r16__qualityThreshold_r16__Format.

Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__Format : T_Format Z MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__cond :=
 ranged_int_format (2) (maxNrofSS_BlocksToAverage) MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__helper1 MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__helper2.

Opaque MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__cond MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__Format.


Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Format_Type := Eval cbn in seq_format_prod MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list.
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Format_list : MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Format_Type :=
  (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16__Format, (ThresholdNR__Format, (SSB_MTC__Format, (SSB_ToMeasure__Format, (bool__Format, (SS_RSSI_Measurement__Format, unit_format)))))).
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list__Format := (*Eval compute in *) seq_format MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Format_list.
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1 z :=
  (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__nrofSS_BlocksToAverage_r16 z, (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__absThreshSS_BlocksConsolidation_r16 z, (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__smtc_r16 z, (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__ssb_ToMeasure_r16 z, (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__deriveSSB_IndexFromCell_r16 z, (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__ss_RSSI_Measurement_r16 z, tt)))))).
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F2 (y : seq_type MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Type i0 i1 i2 i3 i4 i5
  end.
Lemma MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1F2_cond (z : MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Type)
  : MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond z ->
  (seq_cond MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1 z)).
intro H. unfold MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond in H. simpl. auto. Qed.
Lemma MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1F2_cond2 (z : MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Type)
 : MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F2 (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F2F1_cond (y : seq_type MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list)
  : seq_cond MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list y ->
 (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F2 y)) /\  MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1 (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond. simpl in *. auto.
 - simpl. unfold MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Format : T_Format MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Type MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond :=
        proj2_format  MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__list__Format
    MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1 MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F2 MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1F2_cond  MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F1F2_cond2 MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__F2F1_cond.
Opaque MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__cond MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Format.


Definition MeasIdleCarrierNR_r16__root_Format_Type := Eval cbn in seq_format_prod MeasIdleCarrierNR_r16__root_list.
Definition MeasIdleCarrierNR_r16__root_Format_list : MeasIdleCarrierNR_r16__root_Format_Type :=
  (ARFCN_ValueNR__Format, (SubcarrierSpacing__Format, (MultiFrequencyBandListNR__Format, (CellListNR_r16__Format, (MeasIdleCarrierNR_r16__reportQuantities_r16__Format, (MeasIdleCarrierNR_r16__qualityThreshold_r16__Format, (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16__Format, (BeamMeasConfigIdle_NR_r16__Format, unit_format)))))))).

Definition MeasIdleCarrierNR_r16__ext_Format_Type := Eval cbn in get_formats MeasIdleCarrierNR_r16__ext_list.
Definition MeasIdleCarrierNR_r16__ext_Format_list : MeasIdleCarrierNR_r16__ext_Format_Type :=
  unit__Format.

Definition MeasIdleCarrierNR_r16__list_type : Set := (seq_type MeasIdleCarrierNR_r16__root_list) * (seq_ext_type MeasIdleCarrierNR_r16__ext_list).
Definition MeasIdleCarrierNR_r16__list_cond (z : MeasIdleCarrierNR_r16__list_type) : Prop :=
        (seq_cond MeasIdleCarrierNR_r16__root_list (fst z)) /\ (seq_ext_cond MeasIdleCarrierNR_r16__ext_list (snd z)).
Definition MeasIdleCarrierNR_r16__list_format : T_Format MeasIdleCarrierNR_r16__list_type MeasIdleCarrierNR_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasIdleCarrierNR_r16__root_list MeasIdleCarrierNR_r16__root_Format_list MeasIdleCarrierNR_r16__ext_list MeasIdleCarrierNR_r16__ext_Format_list.

Opaque MeasIdleCarrierNR_r16__list_format.
Definition MeasIdleCarrierNR_r16__F1 (z : MeasIdleCarrierNR_r16__Type) : MeasIdleCarrierNR_r16__list_type :=
  (((MeasIdleCarrierNR_r16__carrierFreq_r16 z, (MeasIdleCarrierNR_r16__ssbSubcarrierSpacing_r16 z, (MeasIdleCarrierNR_r16__frequencyBandList z, (MeasIdleCarrierNR_r16__measCellListNR_r16 z, (MeasIdleCarrierNR_r16__reportQuantities_r16 z, (MeasIdleCarrierNR_r16__qualityThreshold_r16 z, (MeasIdleCarrierNR_r16__ssb_MeasConfig_r16 z, (MeasIdleCarrierNR_r16__beamMeasConfigIdle_r16 z, tt))))))))), (
tt)).
Definition MeasIdleCarrierNR_r16__F2 (y : MeasIdleCarrierNR_r16__list_type) : MeasIdleCarrierNR_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), _)=>
    make__MeasIdleCarrierNR_r16__Type j0 j1 j2 j3 j4 j5 j6 j7
  end.
Definition MeasIdleCarrierNR_r16__helper1 : (forall a : MeasIdleCarrierNR_r16__Type, MeasIdleCarrierNR_r16__cond a -> MeasIdleCarrierNR_r16__list_cond (MeasIdleCarrierNR_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasIdleCarrierNR_r16__helper2 : (forall a : MeasIdleCarrierNR_r16__Type, MeasIdleCarrierNR_r16__F2 (MeasIdleCarrierNR_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasIdleCarrierNR_r16__helper3 : (forall b : MeasIdleCarrierNR_r16__list_type, MeasIdleCarrierNR_r16__list_cond b -> MeasIdleCarrierNR_r16__cond (MeasIdleCarrierNR_r16__F2 b) /\ MeasIdleCarrierNR_r16__F1 (MeasIdleCarrierNR_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasIdleCarrierNR_r16__cond, MeasIdleCarrierNR_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasIdleCarrierNR_r16__Format : T_Format MeasIdleCarrierNR_r16__Type MeasIdleCarrierNR_r16__cond :=
 proj2_format MeasIdleCarrierNR_r16__cond MeasIdleCarrierNR_r16__list_format  MeasIdleCarrierNR_r16__F1 MeasIdleCarrierNR_r16__F2 MeasIdleCarrierNR_r16__helper1 MeasIdleCarrierNR_r16__helper2 MeasIdleCarrierNR_r16__helper3.

Opaque MeasIdleCarrierNR_r16__cond MeasIdleCarrierNR_r16__Format.

