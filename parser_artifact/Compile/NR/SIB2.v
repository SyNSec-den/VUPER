Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__helper1 : (2 <= maxNrofSS_BlocksToAverage)%Z. unfold maxNrofSS_BlocksToAverage.
 lia. Qed.
Lemma SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__helper2 : to_bit_sz (Z.to_nat (maxNrofSS_BlocksToAverage - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSS_BlocksToAverage - 2))%Z). { apply Zorder.Zle_minus_le_0. apply SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__Type := Z.
Definition SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__cond := (fun z => (2 <= z <= maxNrofSS_BlocksToAverage)%Z).
Require Import NR.ThresholdNR.

Opaque ThresholdNR__cond ThresholdNR__Format.

Require Import NR.RangeToBestCell.

Opaque RangeToBestCell__cond RangeToBestCell__Format.

Inductive SIB2__cellReselectionInfoCommon__q_Hyst__Type : Set :=
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB0
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB1
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB2
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB3
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB4
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB5
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB6
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB8
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB10
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB12
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB14
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB16
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB18
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB20
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB22
 | SIB2__cellReselectionInfoCommon__q_Hyst__dB24
.
Definition SIB2__cellReselectionInfoCommon__q_Hyst__cond := (fun (_ : SIB2__cellReselectionInfoCommon__q_Hyst__Type) => True).
Lemma SIB2__cellReselectionInfoCommon__q_Hyst__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__cellReselectionInfoCommon__q_Hyst__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SIB2__cellReselectionInfoCommon__q_Hyst__nat__helper.

Definition SIB2__cellReselectionInfoCommon__q_Hyst__F1 t :=
  match t with
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB0 => 0
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB1 => 1
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB2 => 2
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB3 => 3
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB4 => 4
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB5 => 5
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB6 => 6
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB8 => 7
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB10 => 8
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB12 => 9
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB14 => 10
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB16 => 11
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB18 => 12
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB20 => 13
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB22 => 14
  | SIB2__cellReselectionInfoCommon__q_Hyst__dB24 => 15
  end.
Definition SIB2__cellReselectionInfoCommon__q_Hyst__F2 n :=
  match n with
  | 0 => SIB2__cellReselectionInfoCommon__q_Hyst__dB0
  | 1 => SIB2__cellReselectionInfoCommon__q_Hyst__dB1
  | 2 => SIB2__cellReselectionInfoCommon__q_Hyst__dB2
  | 3 => SIB2__cellReselectionInfoCommon__q_Hyst__dB3
  | 4 => SIB2__cellReselectionInfoCommon__q_Hyst__dB4
  | 5 => SIB2__cellReselectionInfoCommon__q_Hyst__dB5
  | 6 => SIB2__cellReselectionInfoCommon__q_Hyst__dB6
  | 7 => SIB2__cellReselectionInfoCommon__q_Hyst__dB8
  | 8 => SIB2__cellReselectionInfoCommon__q_Hyst__dB10
  | 9 => SIB2__cellReselectionInfoCommon__q_Hyst__dB12
  | 10 => SIB2__cellReselectionInfoCommon__q_Hyst__dB14
  | 11 => SIB2__cellReselectionInfoCommon__q_Hyst__dB16
  | 12 => SIB2__cellReselectionInfoCommon__q_Hyst__dB18
  | 13 => SIB2__cellReselectionInfoCommon__q_Hyst__dB20
  | 14 => SIB2__cellReselectionInfoCommon__q_Hyst__dB22
  | 15 => SIB2__cellReselectionInfoCommon__q_Hyst__dB24
  | _ => SIB2__cellReselectionInfoCommon__q_Hyst__dB0
  end.
Lemma SIB2__cellReselectionInfoCommon__q_Hyst__F1F2 : forall x : SIB2__cellReselectionInfoCommon__q_Hyst__Type, (SIB2__cellReselectionInfoCommon__q_Hyst__F1 x <= 15) /\ SIB2__cellReselectionInfoCommon__q_Hyst__F2 (SIB2__cellReselectionInfoCommon__q_Hyst__F1 x) = x. imp_solve. Qed.
Lemma SIB2__cellReselectionInfoCommon__q_Hyst__F2F1 : forall (y : nat) (H : y <= 15), SIB2__cellReselectionInfoCommon__q_Hyst__F1 (SIB2__cellReselectionInfoCommon__q_Hyst__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MobilityStateParameters.

Opaque MobilityStateParameters__cond MobilityStateParameters__Format.

Inductive SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Type : Set :=
 | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_6
 | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_4
 | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_2
 | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB0
.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__cond := (fun (_ : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Type) => True).
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__nat__helper.

Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F1 t :=
  match t with
  | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_6 => 0
  | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_4 => 1
  | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_2 => 2
  | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB0 => 3
  end.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F2 n :=
  match n with
  | 0 => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_6
  | 1 => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_4
  | 2 => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_2
  | 3 => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB0
  | _ => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__dB_6
  end.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F1F2 : forall x : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Type, (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F1 x <= 3) /\ SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F2 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F1 x) = x. imp_solve. Qed.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F2F1 : forall (y : nat) (H : y <= 3), SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F1 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F2 y) = y. enum_solve H y. Qed.

Inductive SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Type : Set :=
 | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_6
 | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_4
 | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_2
 | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB0
.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__cond := (fun (_ : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Type) => True).
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__nat__helper.

Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F1 t :=
  match t with
  | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_6 => 0
  | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_4 => 1
  | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_2 => 2
  | SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB0 => 3
  end.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F2 n :=
  match n with
  | 0 => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_6
  | 1 => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_4
  | 2 => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_2
  | 3 => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB0
  | _ => SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__dB_6
  end.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F1F2 : forall x : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Type, (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F1 x <= 3) /\ SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F2 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F1 x) = x. imp_solve. Qed.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F2F1 : forall (y : nat) (H : y <= 3), SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F1 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F2 y) = y. enum_solve H y. Qed.

Record SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Type : Set :=
  make__SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Type {
    SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Type ;
    SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Type ;
}.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list := (
 Nor SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__cond ::
 Nor SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__cond ::
 nil).
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond z := 
  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__cond (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium z) /\
  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__cond (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High z) /\
  True.

Record SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Type : Set :=
  make__SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Type {
    SIB2__cellReselectionInfoCommon__speedStateReselectionPars__mobilityStateParameters : MobilityStateParameters__Type ;
    SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Type ;
}.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list := (
 Nor MobilityStateParameters__Type MobilityStateParameters__cond ::
 Nor SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond ::
 nil).
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond z := 
  MobilityStateParameters__cond (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__mobilityStateParameters z) /\
  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF z) /\
  True.

Record SIB2__cellReselectionInfoCommon__Type : Set :=
  make__SIB2__cellReselectionInfoCommon__Type {
    SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage : option Z ;
    SIB2__cellReselectionInfoCommon__absThreshSS_BlocksConsolidation : option ThresholdNR__Type ;
    SIB2__cellReselectionInfoCommon__rangeToBestCell : option RangeToBestCell__Type ;
    SIB2__cellReselectionInfoCommon__q_Hyst : SIB2__cellReselectionInfoCommon__q_Hyst__Type ;
    SIB2__cellReselectionInfoCommon__speedStateReselectionPars : option SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Type ;
}.
Definition SIB2__cellReselectionInfoCommon__root_list : list seq_elem := (
 Opt Z SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__cond ::
 Opt ThresholdNR__Type ThresholdNR__cond ::
 Opt RangeToBestCell__Type RangeToBestCell__cond ::
 Nor SIB2__cellReselectionInfoCommon__q_Hyst__Type SIB2__cellReselectionInfoCommon__q_Hyst__cond ::
 Opt SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond ::
 nil).
Definition SIB2__cellReselectionInfoCommon__ext_list : list typ := (
  nil).
Definition SIB2__cellReselectionInfoCommon__cond (z : SIB2__cellReselectionInfoCommon__Type) := 
(  opt_cond SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__cond (SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage z) /\
  opt_cond ThresholdNR__cond (SIB2__cellReselectionInfoCommon__absThreshSS_BlocksConsolidation z) /\
  opt_cond RangeToBestCell__cond (SIB2__cellReselectionInfoCommon__rangeToBestCell z) /\
  SIB2__cellReselectionInfoCommon__q_Hyst__cond (SIB2__cellReselectionInfoCommon__q_Hyst z) /\
  opt_cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond (SIB2__cellReselectionInfoCommon__speedStateReselectionPars z) /\
  True) /\ 
(  True).

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Require Import NR.CellReselectionPriority.

Opaque CellReselectionPriority__cond CellReselectionPriority__Format.

Require Import NR.CellReselectionSubPriority.

Opaque CellReselectionSubPriority__cond CellReselectionSubPriority__Format.

Record SIB2__cellReselectionServingFreqInfo__Type : Set :=
  make__SIB2__cellReselectionServingFreqInfo__Type {
    SIB2__cellReselectionServingFreqInfo__s_NonIntraSearchP : option ReselectionThreshold__Type ;
    SIB2__cellReselectionServingFreqInfo__s_NonIntraSearchQ : option ReselectionThresholdQ__Type ;
    SIB2__cellReselectionServingFreqInfo__threshServingLowP : ReselectionThreshold__Type ;
    SIB2__cellReselectionServingFreqInfo__threshServingLowQ : option ReselectionThresholdQ__Type ;
    SIB2__cellReselectionServingFreqInfo__cellReselectionPriority : CellReselectionPriority__Type ;
    SIB2__cellReselectionServingFreqInfo__cellReselectionSubPriority : option CellReselectionSubPriority__Type ;
}.
Definition SIB2__cellReselectionServingFreqInfo__root_list : list seq_elem := (
 Opt ReselectionThreshold__Type ReselectionThreshold__cond ::
 Opt ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 Nor ReselectionThreshold__Type ReselectionThreshold__cond ::
 Opt ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 Nor CellReselectionPriority__Type CellReselectionPriority__cond ::
 Opt CellReselectionSubPriority__Type CellReselectionSubPriority__cond ::
 nil).
Definition SIB2__cellReselectionServingFreqInfo__ext_list : list typ := (
  nil).
Definition SIB2__cellReselectionServingFreqInfo__cond (z : SIB2__cellReselectionServingFreqInfo__Type) := 
(  opt_cond ReselectionThreshold__cond (SIB2__cellReselectionServingFreqInfo__s_NonIntraSearchP z) /\
  opt_cond ReselectionThresholdQ__cond (SIB2__cellReselectionServingFreqInfo__s_NonIntraSearchQ z) /\
  ReselectionThreshold__cond (SIB2__cellReselectionServingFreqInfo__threshServingLowP z) /\
  opt_cond ReselectionThresholdQ__cond (SIB2__cellReselectionServingFreqInfo__threshServingLowQ z) /\
  CellReselectionPriority__cond (SIB2__cellReselectionServingFreqInfo__cellReselectionPriority z) /\
  opt_cond CellReselectionSubPriority__cond (SIB2__cellReselectionServingFreqInfo__cellReselectionSubPriority z) /\
  True) /\ 
(  True).

Require Import NR.Q_RxLevMin.

Opaque Q_RxLevMin__cond Q_RxLevMin__Format.

Require Import NR.Q_RxLevMin.

Opaque Q_RxLevMin__cond Q_RxLevMin__Format.

Require Import NR.Q_QualMin.

Opaque Q_QualMin__cond Q_QualMin__Format.

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Require Import NR.T_Reselection.

Opaque T_Reselection__cond T_Reselection__Format.

Require Import NR.MultiFrequencyBandListNR_SIB.

Opaque MultiFrequencyBandListNR_SIB__cond MultiFrequencyBandListNR_SIB__Format.

Require Import NR.MultiFrequencyBandListNR_SIB.

Opaque MultiFrequencyBandListNR_SIB__cond MultiFrequencyBandListNR_SIB__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Require Import NR.SS_RSSI_Measurement.

Opaque SS_RSSI_Measurement__cond SS_RSSI_Measurement__Format.

Require Import NR.SSB_ToMeasure.

Opaque SSB_ToMeasure__cond SSB_ToMeasure__Format.

Require Import NR.SpeedStateScaleFactors.

Opaque SpeedStateScaleFactors__cond SpeedStateScaleFactors__Format.

Record SIB2__intraFreqCellReselectionInfo__ext0O__Type : Set :=
  make__SIB2__intraFreqCellReselectionInfo__ext0O__Type {
    SIB2__intraFreqCellReselectionInfo__ext0O__t_ReselectionNR_SF : option SpeedStateScaleFactors__Type ;
}.
Definition SIB2__intraFreqCellReselectionInfo__ext0O__list := (
 Opt SpeedStateScaleFactors__Type SpeedStateScaleFactors__cond ::
 nil).
Definition SIB2__intraFreqCellReselectionInfo__ext0O__cond z := 
  opt_cond SpeedStateScaleFactors__cond (SIB2__intraFreqCellReselectionInfo__ext0O__t_ReselectionNR_SF z) /\
  True.

Definition SIB2__intraFreqCellReselectionInfo__ext0__Type := SIB2__intraFreqCellReselectionInfo__ext0O__Type.
Definition SIB2__intraFreqCellReselectionInfo__ext0__cond := SIB2__intraFreqCellReselectionInfo__ext0O__cond.

Require Import NR.SSB_MTC2_LP_r16.

Opaque SSB_MTC2_LP_r16__cond SSB_MTC2_LP_r16__Format.

Require Import NR.SSB_PositionQCL_Relation_r16.

Opaque SSB_PositionQCL_Relation_r16__cond SSB_PositionQCL_Relation_r16__Format.

Record SIB2__intraFreqCellReselectionInfo__ext1O__Type : Set :=
  make__SIB2__intraFreqCellReselectionInfo__ext1O__Type {
    SIB2__intraFreqCellReselectionInfo__ext1O__smtc2_LP_r16 : option SSB_MTC2_LP_r16__Type ;
    SIB2__intraFreqCellReselectionInfo__ext1O__ssb_PositionQCL_Common_r16 : option SSB_PositionQCL_Relation_r16__Type ;
}.
Definition SIB2__intraFreqCellReselectionInfo__ext1O__list := (
 Opt SSB_MTC2_LP_r16__Type SSB_MTC2_LP_r16__cond ::
 Opt SSB_PositionQCL_Relation_r16__Type SSB_PositionQCL_Relation_r16__cond ::
 nil).
Definition SIB2__intraFreqCellReselectionInfo__ext1O__cond z := 
  opt_cond SSB_MTC2_LP_r16__cond (SIB2__intraFreqCellReselectionInfo__ext1O__smtc2_LP_r16 z) /\
  opt_cond SSB_PositionQCL_Relation_r16__cond (SIB2__intraFreqCellReselectionInfo__ext1O__ssb_PositionQCL_Common_r16 z) /\
  True.

Definition SIB2__intraFreqCellReselectionInfo__ext1__Type := SIB2__intraFreqCellReselectionInfo__ext1O__Type.
Definition SIB2__intraFreqCellReselectionInfo__ext1__cond := SIB2__intraFreqCellReselectionInfo__ext1O__cond.

Require Import NR.SSB_PositionQCL_Relation_r17.

Opaque SSB_PositionQCL_Relation_r17__cond SSB_PositionQCL_Relation_r17__Format.

Record SIB2__intraFreqCellReselectionInfo__ext2O__Type : Set :=
  make__SIB2__intraFreqCellReselectionInfo__ext2O__Type {
    SIB2__intraFreqCellReselectionInfo__ext2O__ssb_PositionQCL_Common_r17 : option SSB_PositionQCL_Relation_r17__Type ;
}.
Definition SIB2__intraFreqCellReselectionInfo__ext2O__list := (
 Opt SSB_PositionQCL_Relation_r17__Type SSB_PositionQCL_Relation_r17__cond ::
 nil).
Definition SIB2__intraFreqCellReselectionInfo__ext2O__cond z := 
  opt_cond SSB_PositionQCL_Relation_r17__cond (SIB2__intraFreqCellReselectionInfo__ext2O__ssb_PositionQCL_Common_r17 z) /\
  True.

Definition SIB2__intraFreqCellReselectionInfo__ext2__Type := SIB2__intraFreqCellReselectionInfo__ext2O__Type.
Definition SIB2__intraFreqCellReselectionInfo__ext2__cond := SIB2__intraFreqCellReselectionInfo__ext2O__cond.

Require Import NR.SSB_MTC4List_r17.

Opaque SSB_MTC4List_r17__cond SSB_MTC4List_r17__Format.

Record SIB2__intraFreqCellReselectionInfo__ext3O__Type : Set :=
  make__SIB2__intraFreqCellReselectionInfo__ext3O__Type {
    SIB2__intraFreqCellReselectionInfo__ext3O__smtc4list_r17 : option SSB_MTC4List_r17__Type ;
}.
Definition SIB2__intraFreqCellReselectionInfo__ext3O__list := (
 Opt SSB_MTC4List_r17__Type SSB_MTC4List_r17__cond ::
 nil).
Definition SIB2__intraFreqCellReselectionInfo__ext3O__cond z := 
  opt_cond SSB_MTC4List_r17__cond (SIB2__intraFreqCellReselectionInfo__ext3O__smtc4list_r17 z) /\
  True.

Definition SIB2__intraFreqCellReselectionInfo__ext3__Type := SIB2__intraFreqCellReselectionInfo__ext3O__Type.
Definition SIB2__intraFreqCellReselectionInfo__ext3__cond := SIB2__intraFreqCellReselectionInfo__ext3O__cond.

Record SIB2__intraFreqCellReselectionInfo__Type : Set :=
  make__SIB2__intraFreqCellReselectionInfo__Type {
    SIB2__intraFreqCellReselectionInfo__q_RxLevMin : Q_RxLevMin__Type ;
    SIB2__intraFreqCellReselectionInfo__q_RxLevMinSUL : option Q_RxLevMin__Type ;
    SIB2__intraFreqCellReselectionInfo__q_QualMin : option Q_QualMin__Type ;
    SIB2__intraFreqCellReselectionInfo__s_IntraSearchP : ReselectionThreshold__Type ;
    SIB2__intraFreqCellReselectionInfo__s_IntraSearchQ : option ReselectionThresholdQ__Type ;
    SIB2__intraFreqCellReselectionInfo__t_ReselectionNR : T_Reselection__Type ;
    SIB2__intraFreqCellReselectionInfo__frequencyBandList : option MultiFrequencyBandListNR_SIB__Type ;
    SIB2__intraFreqCellReselectionInfo__frequencyBandListSUL : option MultiFrequencyBandListNR_SIB__Type ;
    SIB2__intraFreqCellReselectionInfo__p_Max : option P_Max__Type ;
    SIB2__intraFreqCellReselectionInfo__smtc : option SSB_MTC__Type ;
    SIB2__intraFreqCellReselectionInfo__ss_RSSI_Measurement : option SS_RSSI_Measurement__Type ;
    SIB2__intraFreqCellReselectionInfo__ssb_ToMeasure : option SSB_ToMeasure__Type ;
    SIB2__intraFreqCellReselectionInfo__deriveSSB_IndexFromCell : bool ;
    SIB2__intraFreqCellReselectionInfo__ext0 : option SIB2__intraFreqCellReselectionInfo__ext0__Type ;
    SIB2__intraFreqCellReselectionInfo__ext1 : option SIB2__intraFreqCellReselectionInfo__ext1__Type ;
    SIB2__intraFreqCellReselectionInfo__ext2 : option SIB2__intraFreqCellReselectionInfo__ext2__Type ;
    SIB2__intraFreqCellReselectionInfo__ext3 : option SIB2__intraFreqCellReselectionInfo__ext3__Type ;
}.
Definition SIB2__intraFreqCellReselectionInfo__root_list : list seq_elem := (
 Nor Q_RxLevMin__Type Q_RxLevMin__cond ::
 Opt Q_RxLevMin__Type Q_RxLevMin__cond ::
 Opt Q_QualMin__Type Q_QualMin__cond ::
 Nor ReselectionThreshold__Type ReselectionThreshold__cond ::
 Opt ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 Nor T_Reselection__Type T_Reselection__cond ::
 Opt MultiFrequencyBandListNR_SIB__Type MultiFrequencyBandListNR_SIB__cond ::
 Opt MultiFrequencyBandListNR_SIB__Type MultiFrequencyBandListNR_SIB__cond ::
 Opt P_Max__Type P_Max__cond ::
 Opt SSB_MTC__Type SSB_MTC__cond ::
 Opt SS_RSSI_Measurement__Type SS_RSSI_Measurement__cond ::
 Opt SSB_ToMeasure__Type SSB_ToMeasure__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition SIB2__intraFreqCellReselectionInfo__ext_list : list typ := (
  typ_cons SIB2__intraFreqCellReselectionInfo__ext0__Type SIB2__intraFreqCellReselectionInfo__ext0__cond ::
  typ_cons SIB2__intraFreqCellReselectionInfo__ext1__Type SIB2__intraFreqCellReselectionInfo__ext1__cond ::
  typ_cons SIB2__intraFreqCellReselectionInfo__ext2__Type SIB2__intraFreqCellReselectionInfo__ext2__cond ::
  typ_cons SIB2__intraFreqCellReselectionInfo__ext3__Type SIB2__intraFreqCellReselectionInfo__ext3__cond ::
  nil).
Definition SIB2__intraFreqCellReselectionInfo__cond (z : SIB2__intraFreqCellReselectionInfo__Type) := 
(  Q_RxLevMin__cond (SIB2__intraFreqCellReselectionInfo__q_RxLevMin z) /\
  opt_cond Q_RxLevMin__cond (SIB2__intraFreqCellReselectionInfo__q_RxLevMinSUL z) /\
  opt_cond Q_QualMin__cond (SIB2__intraFreqCellReselectionInfo__q_QualMin z) /\
  ReselectionThreshold__cond (SIB2__intraFreqCellReselectionInfo__s_IntraSearchP z) /\
  opt_cond ReselectionThresholdQ__cond (SIB2__intraFreqCellReselectionInfo__s_IntraSearchQ z) /\
  T_Reselection__cond (SIB2__intraFreqCellReselectionInfo__t_ReselectionNR z) /\
  opt_cond MultiFrequencyBandListNR_SIB__cond (SIB2__intraFreqCellReselectionInfo__frequencyBandList z) /\
  opt_cond MultiFrequencyBandListNR_SIB__cond (SIB2__intraFreqCellReselectionInfo__frequencyBandListSUL z) /\
  opt_cond P_Max__cond (SIB2__intraFreqCellReselectionInfo__p_Max z) /\
  opt_cond SSB_MTC__cond (SIB2__intraFreqCellReselectionInfo__smtc z) /\
  opt_cond SS_RSSI_Measurement__cond (SIB2__intraFreqCellReselectionInfo__ss_RSSI_Measurement z) /\
  opt_cond SSB_ToMeasure__cond (SIB2__intraFreqCellReselectionInfo__ssb_ToMeasure z) /\
  (fun _ => True) (SIB2__intraFreqCellReselectionInfo__deriveSSB_IndexFromCell z) /\
  True) /\ 
(  opt_cond SIB2__intraFreqCellReselectionInfo__ext0__cond (SIB2__intraFreqCellReselectionInfo__ext0 z) /\
  opt_cond SIB2__intraFreqCellReselectionInfo__ext1__cond (SIB2__intraFreqCellReselectionInfo__ext1 z) /\
  opt_cond SIB2__intraFreqCellReselectionInfo__ext2__cond (SIB2__intraFreqCellReselectionInfo__ext2 z) /\
  opt_cond SIB2__intraFreqCellReselectionInfo__ext3__cond (SIB2__intraFreqCellReselectionInfo__ext3 z) /\
  True).

Inductive SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Type : Set :=
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB3
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB6
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB9
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB12
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB15
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare3
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare2
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare1
.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__cond := (fun (_ : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Type) => True).
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__nat__helper.

Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F1 t :=
  match t with
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB3 => 0
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB6 => 1
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB9 => 2
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB12 => 3
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB15 => 4
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare3 => 5
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare2 => 6
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare1 => 7
  end.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F2 n :=
  match n with
  | 0 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB3
  | 1 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB6
  | 2 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB9
  | 3 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB12
  | 4 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB15
  | 5 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare3
  | 6 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare2
  | 7 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__spare1
  | _ => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__dB3
  end.
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F1F2 : forall x : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Type, (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F1 x <= 7) /\ SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F2 (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F1 x) = x. imp_solve. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F2F1 : forall (y : nat) (H : y <= 7), SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F1 (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Type : Set :=
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s5
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s10
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s20
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s30
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s60
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s120
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s180
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s240
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s300
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare7
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare6
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare5
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare4
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare3
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare2
 | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare1
.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__cond := (fun (_ : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Type) => True).
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__nat__helper.

Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F1 t :=
  match t with
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s5 => 0
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s10 => 1
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s20 => 2
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s30 => 3
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s60 => 4
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s120 => 5
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s180 => 6
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s240 => 7
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s300 => 8
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare7 => 9
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare6 => 10
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare5 => 11
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare4 => 12
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare3 => 13
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare2 => 14
  | SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare1 => 15
  end.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F2 n :=
  match n with
  | 0 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s5
  | 1 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s10
  | 2 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s20
  | 3 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s30
  | 4 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s60
  | 5 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s120
  | 6 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s180
  | 7 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s240
  | 8 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s300
  | 9 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare7
  | 10 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare6
  | 11 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare5
  | 12 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare4
  | 13 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare3
  | 14 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare2
  | 15 => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__spare1
  | _ => SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__s5
  end.
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F1F2 : forall x : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Type, (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F1 x <= 15) /\ SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F2 (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F1 x) = x. imp_solve. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F2F1 : forall (y : nat) (H : y <= 15), SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F1 (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F2 y) = y. enum_solve H y. Qed.

Record SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Type : Set :=
  make__SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Type {
    SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16 : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Type ;
    SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16 : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Type ;
}.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list := (
 Nor SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Type SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__cond ::
 Nor SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Type SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__cond ::
 nil).
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond z := 
  SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16 z) /\
  SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16 z) /\
  True.

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Record SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Type : Set :=
  make__SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Type {
    SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__s_SearchThresholdP_r16 : ReselectionThreshold__Type ;
    SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__s_SearchThresholdQ_r16 : option ReselectionThresholdQ__Type ;
}.
Definition SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list := (
 Nor ReselectionThreshold__Type ReselectionThreshold__cond ::
 Opt ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 nil).
Definition SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond z := 
  ReselectionThreshold__cond (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__s_SearchThresholdP_r16 z) /\
  opt_cond ReselectionThresholdQ__cond (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__s_SearchThresholdQ_r16 z) /\
  True.

Inductive SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Type : Set :=
 | SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__true
.
Definition SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__cond := (fun (_ : SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Type) => True).
Lemma SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__nat__helper.

Definition SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F1 t :=
  match t with
  | SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__true => 0
  end.
Definition SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F2 n :=
  match n with
  | 0 => SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__true
  | _ => SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__true
  end.
Lemma SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F1F2 : forall x : SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Type, (SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F1 x <= 0) /\ SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F2 (SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F1 x) = x. imp_solve. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F2F1 : forall (y : nat) (H : y <= 0), SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F1 (SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Type : Set :=
 | SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__true
.
Definition SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__cond := (fun (_ : SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Type) => True).
Lemma SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__nat__helper.

Definition SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F1 t :=
  match t with
  | SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__true => 0
  end.
Definition SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F2 n :=
  match n with
  | 0 => SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__true
  | _ => SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__true
  end.
Lemma SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F1F2 : forall x : SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Type, (SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F1 x <= 0) /\ SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F2 (SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F1 x) = x. imp_solve. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F2F1 : forall (y : nat) (H : y <= 0), SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F1 (SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F2 y) = y. enum_solve H y. Qed.

Record SIB2__ext0O__relaxedMeasurement_r16__Type : Set :=
  make__SIB2__ext0O__relaxedMeasurement_r16__Type {
    SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16 : option SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Type ;
    SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16 : option SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Type ;
    SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16 : option SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Type ;
    SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16 : option SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Type ;
}.
Definition SIB2__ext0O__relaxedMeasurement_r16__list := (
 Opt SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Type SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond ::
 Opt SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Type SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond ::
 Opt SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Type SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__cond ::
 Opt SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Type SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__cond ::
 nil).
Definition SIB2__ext0O__relaxedMeasurement_r16__cond z := 
  opt_cond SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16 z) /\
  opt_cond SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16 z) /\
  opt_cond SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16 z) /\
  opt_cond SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16 z) /\
  True.

Record SIB2__ext0O__Type : Set :=
  make__SIB2__ext0O__Type {
    SIB2__ext0O__relaxedMeasurement_r16 : option SIB2__ext0O__relaxedMeasurement_r16__Type ;
}.
Definition SIB2__ext0O__list := (
 Opt SIB2__ext0O__relaxedMeasurement_r16__Type SIB2__ext0O__relaxedMeasurement_r16__cond ::
 nil).
Definition SIB2__ext0O__cond z := 
  opt_cond SIB2__ext0O__relaxedMeasurement_r16__cond (SIB2__ext0O__relaxedMeasurement_r16 z) /\
  True.

Definition SIB2__ext0__Type := SIB2__ext0O__Type.
Definition SIB2__ext0__cond := SIB2__ext0O__cond.

Lemma SIB2__ext1O__cellEquivalentSize_r17__helper1 : (2 <= 16)%Z.  lia. Qed.
Lemma SIB2__ext1O__cellEquivalentSize_r17__helper2 : to_bit_sz (Z.to_nat (16 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply SIB2__ext1O__cellEquivalentSize_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SIB2__ext1O__cellEquivalentSize_r17__Type := Z.
Definition SIB2__ext1O__cellEquivalentSize_r17__cond := (fun z => (2 <= z <= 16)%Z).
Inductive SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Type : Set :=
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB2
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB3
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB6
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB9
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB12
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB15
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__spare2
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__spare1
.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__cond := (fun (_ : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Type) => True).
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__nat__helper.

Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F1 t :=
  match t with
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB2 => 0
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB3 => 1
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB6 => 2
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB9 => 3
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB12 => 4
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB15 => 5
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__spare2 => 6
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__spare1 => 7
  end.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F2 n :=
  match n with
  | 0 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB2
  | 1 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB3
  | 2 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB6
  | 3 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB9
  | 4 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB12
  | 5 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB15
  | 6 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__spare2
  | 7 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__spare1
  | _ => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__dB2
  end.
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F1F2 : forall x : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Type, (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F1 x <= 7) /\ SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F2 (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F2F1 : forall (y : nat) (H : y <= 7), SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F1 (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Type : Set :=
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s5
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s10
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s20
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s30
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s60
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s120
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s180
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s240
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s300
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare7
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare6
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare5
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare4
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare3
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare2
 | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare1
.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__cond := (fun (_ : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Type) => True).
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__nat__helper.

Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F1 t :=
  match t with
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s5 => 0
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s10 => 1
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s20 => 2
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s30 => 3
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s60 => 4
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s120 => 5
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s180 => 6
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s240 => 7
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s300 => 8
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare7 => 9
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare6 => 10
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare5 => 11
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare4 => 12
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare3 => 13
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare2 => 14
  | SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare1 => 15
  end.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F2 n :=
  match n with
  | 0 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s5
  | 1 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s10
  | 2 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s20
  | 3 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s30
  | 4 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s60
  | 5 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s120
  | 6 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s180
  | 7 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s240
  | 8 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s300
  | 9 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare7
  | 10 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare6
  | 11 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare5
  | 12 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare4
  | 13 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare3
  | 14 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare2
  | 15 => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__spare1
  | _ => SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__s5
  end.
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F1F2 : forall x : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Type, (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F1 x <= 15) /\ SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F2 (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F2F1 : forall (y : nat) (H : y <= 15), SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F1 (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F2 y) = y. enum_solve H y. Qed.

Record SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Type : Set :=
  make__SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Type {
    SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17 : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Type ;
    SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17 : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Type ;
}.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list := (
 Nor SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Type SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__cond ::
 Nor SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Type SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__cond ::
 nil).
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond z := 
  SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__cond (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17 z) /\
  SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__cond (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17 z) /\
  True.

Require Import NR.ReselectionThreshold.

Opaque ReselectionThreshold__cond ReselectionThreshold__Format.

Require Import NR.ReselectionThresholdQ.

Opaque ReselectionThresholdQ__cond ReselectionThresholdQ__Format.

Record SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Type : Set :=
  make__SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Type {
    SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__s_SearchThresholdP2_r17 : ReselectionThreshold__Type ;
    SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__s_SearchThresholdQ2_r17 : option ReselectionThresholdQ__Type ;
}.
Definition SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list := (
 Nor ReselectionThreshold__Type ReselectionThreshold__cond ::
 Opt ReselectionThresholdQ__Type ReselectionThresholdQ__cond ::
 nil).
Definition SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond z := 
  ReselectionThreshold__cond (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__s_SearchThresholdP2_r17 z) /\
  opt_cond ReselectionThresholdQ__cond (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__s_SearchThresholdQ2_r17 z) /\
  True.

Inductive SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Type : Set :=
 | SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__true
.
Definition SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__cond := (fun (_ : SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Type) => True).
Lemma SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__nat__helper.

Definition SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F1 t :=
  match t with
  | SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__true => 0
  end.
Definition SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F2 n :=
  match n with
  | 0 => SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__true
  | _ => SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__true
  end.
Lemma SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F1F2 : forall x : SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Type, (SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F1 x <= 0) /\ SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F2 (SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F1 x) = x. imp_solve. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F2F1 : forall (y : nat) (H : y <= 0), SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F1 (SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F2 y) = y. enum_solve H y. Qed.

Record SIB2__ext1O__relaxedMeasurement_r17__Type : Set :=
  make__SIB2__ext1O__relaxedMeasurement_r17__Type {
    SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17 : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Type ;
    SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17 : option SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Type ;
    SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17 : option SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Type ;
}.
Definition SIB2__ext1O__relaxedMeasurement_r17__list := (
 Nor SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Type SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond ::
 Opt SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Type SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond ::
 Opt SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Type SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__cond ::
 nil).
Definition SIB2__ext1O__relaxedMeasurement_r17__cond z := 
  SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17 z) /\
  opt_cond SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17 z) /\
  opt_cond SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__cond (SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17 z) /\
  True.

Record SIB2__ext1O__Type : Set :=
  make__SIB2__ext1O__Type {
    SIB2__ext1O__cellEquivalentSize_r17 : option Z ;
    SIB2__ext1O__relaxedMeasurement_r17 : option SIB2__ext1O__relaxedMeasurement_r17__Type ;
}.
Definition SIB2__ext1O__list := (
 Opt Z SIB2__ext1O__cellEquivalentSize_r17__cond ::
 Opt SIB2__ext1O__relaxedMeasurement_r17__Type SIB2__ext1O__relaxedMeasurement_r17__cond ::
 nil).
Definition SIB2__ext1O__cond z := 
  opt_cond SIB2__ext1O__cellEquivalentSize_r17__cond (SIB2__ext1O__cellEquivalentSize_r17 z) /\
  opt_cond SIB2__ext1O__relaxedMeasurement_r17__cond (SIB2__ext1O__relaxedMeasurement_r17 z) /\
  True.

Definition SIB2__ext1__Type := SIB2__ext1O__Type.
Definition SIB2__ext1__cond := SIB2__ext1O__cond.

Record SIB2__Type : Set :=
  make__SIB2__Type {
    SIB2__cellReselectionInfoCommon : SIB2__cellReselectionInfoCommon__Type ;
    SIB2__cellReselectionServingFreqInfo : SIB2__cellReselectionServingFreqInfo__Type ;
    SIB2__intraFreqCellReselectionInfo : SIB2__intraFreqCellReselectionInfo__Type ;
    SIB2__ext0 : option SIB2__ext0__Type ;
    SIB2__ext1 : option SIB2__ext1__Type ;
}.
Definition SIB2__root_list : list seq_elem := (
 Nor SIB2__cellReselectionInfoCommon__Type SIB2__cellReselectionInfoCommon__cond ::
 Nor SIB2__cellReselectionServingFreqInfo__Type SIB2__cellReselectionServingFreqInfo__cond ::
 Nor SIB2__intraFreqCellReselectionInfo__Type SIB2__intraFreqCellReselectionInfo__cond ::
 nil).
Definition SIB2__ext_list : list typ := (
  typ_cons SIB2__ext0__Type SIB2__ext0__cond ::
  typ_cons SIB2__ext1__Type SIB2__ext1__cond ::
  nil).
Definition SIB2__cond (z : SIB2__Type) := 
(  SIB2__cellReselectionInfoCommon__cond (SIB2__cellReselectionInfoCommon z) /\
  SIB2__cellReselectionServingFreqInfo__cond (SIB2__cellReselectionServingFreqInfo z) /\
  SIB2__intraFreqCellReselectionInfo__cond (SIB2__intraFreqCellReselectionInfo z) /\
  True) /\ 
(  opt_cond SIB2__ext0__cond (SIB2__ext0 z) /\
  opt_cond SIB2__ext1__cond (SIB2__ext1 z) /\
  True).


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
Definition SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__Format : T_Format Z SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__cond :=
 ranged_int_format (2) (maxNrofSS_BlocksToAverage) SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__helper1 SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__helper2.

Opaque SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__cond SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__Format.

Definition SIB2__cellReselectionInfoCommon__q_Hyst__Format : T_Format SIB2__cellReselectionInfoCommon__q_Hyst__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__cellReselectionInfoCommon__q_Hyst__nat__Format SIB2__cellReselectionInfoCommon__q_Hyst__F1 SIB2__cellReselectionInfoCommon__q_Hyst__F2 SIB2__cellReselectionInfoCommon__q_Hyst__F1F2 SIB2__cellReselectionInfoCommon__q_Hyst__F2F1.

Opaque SIB2__cellReselectionInfoCommon__q_Hyst__cond SIB2__cellReselectionInfoCommon__q_Hyst__Format.

Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Format : T_Format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__nat__Format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F1 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F2 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F1F2 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__F2F1.

Opaque SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Format.

Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Format : T_Format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__nat__Format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F1 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F2 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F1F2 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__F2F1.

Opaque SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Format.


Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Format_Type := Eval cbn in seq_format_prod SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Format_list : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Format_Type :=
  (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium__Format, (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High__Format, unit_format)).
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list__Format := (*Eval compute in *) seq_format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Format_list.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1 z :=
  (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_Medium z, (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__sf_High z, tt)).
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F2 (y : seq_type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Type i0 i1
  end.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1F2_cond (z : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Type)
  : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond z ->
  (seq_cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1 z)).
intro H. unfold SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond in H. simpl. auto. Qed.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1F2_cond2 (z : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Type)
 : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F2 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F2F1_cond (y : seq_type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list)
  : seq_cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list y ->
 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F2 y)) /\  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond. simpl in *. auto.
 - simpl. unfold SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Format : T_Format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond :=
        proj2_format  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__list__Format
    SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F2 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1F2_cond  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F1F2_cond2 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__F2F1_cond.
Opaque SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Format.


Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Format_Type := Eval cbn in seq_format_prod SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Format_list : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Format_Type :=
  (MobilityStateParameters__Format, (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF__Format, unit_format)).
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list__Format := (*Eval compute in *) seq_format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Format_list.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1 z :=
  (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__mobilityStateParameters z, (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__q_HystSF z, tt)).
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F2 (y : seq_type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Type i0 i1
  end.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1F2_cond (z : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Type)
  : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond z ->
  (seq_cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1 z)).
intro H. unfold SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond in H. simpl. auto. Qed.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1F2_cond2 (z : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Type)
 : SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F2 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F2F1_cond (y : seq_type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list)
  : seq_cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list y ->
 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F2 y)) /\  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1 (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond. simpl in *. auto.
 - simpl. unfold SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Format : T_Format SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Type SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond :=
        proj2_format  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__list__Format
    SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F2 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1F2_cond  SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F1F2_cond2 SIB2__cellReselectionInfoCommon__speedStateReselectionPars__F2F1_cond.
Opaque SIB2__cellReselectionInfoCommon__speedStateReselectionPars__cond SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Format.


Definition SIB2__cellReselectionInfoCommon__root_Format_Type := Eval cbn in seq_format_prod SIB2__cellReselectionInfoCommon__root_list.
Definition SIB2__cellReselectionInfoCommon__root_Format_list : SIB2__cellReselectionInfoCommon__root_Format_Type :=
  (SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage__Format, (ThresholdNR__Format, (RangeToBestCell__Format, (SIB2__cellReselectionInfoCommon__q_Hyst__Format, (SIB2__cellReselectionInfoCommon__speedStateReselectionPars__Format, unit_format))))).

Definition SIB2__cellReselectionInfoCommon__ext_Format_Type := Eval cbn in get_formats SIB2__cellReselectionInfoCommon__ext_list.
Definition SIB2__cellReselectionInfoCommon__ext_Format_list : SIB2__cellReselectionInfoCommon__ext_Format_Type :=
  unit__Format.

Definition SIB2__cellReselectionInfoCommon__list_type : Set := (seq_type SIB2__cellReselectionInfoCommon__root_list) * (seq_ext_type SIB2__cellReselectionInfoCommon__ext_list).
Definition SIB2__cellReselectionInfoCommon__list_cond (z : SIB2__cellReselectionInfoCommon__list_type) : Prop :=
        (seq_cond SIB2__cellReselectionInfoCommon__root_list (fst z)) /\ (seq_ext_cond SIB2__cellReselectionInfoCommon__ext_list (snd z)).
Definition SIB2__cellReselectionInfoCommon__list_format : T_Format SIB2__cellReselectionInfoCommon__list_type SIB2__cellReselectionInfoCommon__list_cond :=
 (* Eval compute in *) seq_ext_format SIB2__cellReselectionInfoCommon__root_list SIB2__cellReselectionInfoCommon__root_Format_list SIB2__cellReselectionInfoCommon__ext_list SIB2__cellReselectionInfoCommon__ext_Format_list.

Opaque SIB2__cellReselectionInfoCommon__list_format.
Definition SIB2__cellReselectionInfoCommon__F1 (z : SIB2__cellReselectionInfoCommon__Type) : SIB2__cellReselectionInfoCommon__list_type :=
  (((SIB2__cellReselectionInfoCommon__nrofSS_BlocksToAverage z, (SIB2__cellReselectionInfoCommon__absThreshSS_BlocksConsolidation z, (SIB2__cellReselectionInfoCommon__rangeToBestCell z, (SIB2__cellReselectionInfoCommon__q_Hyst z, (SIB2__cellReselectionInfoCommon__speedStateReselectionPars z, tt)))))), (
tt)).
Definition SIB2__cellReselectionInfoCommon__F2 (y : SIB2__cellReselectionInfoCommon__list_type) : SIB2__cellReselectionInfoCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__SIB2__cellReselectionInfoCommon__Type j0 j1 j2 j3 j4
  end.
Definition SIB2__cellReselectionInfoCommon__helper1 : (forall a : SIB2__cellReselectionInfoCommon__Type, SIB2__cellReselectionInfoCommon__cond a -> SIB2__cellReselectionInfoCommon__list_cond (SIB2__cellReselectionInfoCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB2__cellReselectionInfoCommon__helper2 : (forall a : SIB2__cellReselectionInfoCommon__Type, SIB2__cellReselectionInfoCommon__F2 (SIB2__cellReselectionInfoCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB2__cellReselectionInfoCommon__helper3 : (forall b : SIB2__cellReselectionInfoCommon__list_type, SIB2__cellReselectionInfoCommon__list_cond b -> SIB2__cellReselectionInfoCommon__cond (SIB2__cellReselectionInfoCommon__F2 b) /\ SIB2__cellReselectionInfoCommon__F1 (SIB2__cellReselectionInfoCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB2__cellReselectionInfoCommon__cond, SIB2__cellReselectionInfoCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB2__cellReselectionInfoCommon__Format : T_Format SIB2__cellReselectionInfoCommon__Type SIB2__cellReselectionInfoCommon__cond :=
 proj2_format SIB2__cellReselectionInfoCommon__cond SIB2__cellReselectionInfoCommon__list_format  SIB2__cellReselectionInfoCommon__F1 SIB2__cellReselectionInfoCommon__F2 SIB2__cellReselectionInfoCommon__helper1 SIB2__cellReselectionInfoCommon__helper2 SIB2__cellReselectionInfoCommon__helper3.

Opaque SIB2__cellReselectionInfoCommon__cond SIB2__cellReselectionInfoCommon__Format.


Definition SIB2__cellReselectionServingFreqInfo__root_Format_Type := Eval cbn in seq_format_prod SIB2__cellReselectionServingFreqInfo__root_list.
Definition SIB2__cellReselectionServingFreqInfo__root_Format_list : SIB2__cellReselectionServingFreqInfo__root_Format_Type :=
  (ReselectionThreshold__Format, (ReselectionThresholdQ__Format, (ReselectionThreshold__Format, (ReselectionThresholdQ__Format, (CellReselectionPriority__Format, (CellReselectionSubPriority__Format, unit_format)))))).

Definition SIB2__cellReselectionServingFreqInfo__ext_Format_Type := Eval cbn in get_formats SIB2__cellReselectionServingFreqInfo__ext_list.
Definition SIB2__cellReselectionServingFreqInfo__ext_Format_list : SIB2__cellReselectionServingFreqInfo__ext_Format_Type :=
  unit__Format.

Definition SIB2__cellReselectionServingFreqInfo__list_type : Set := (seq_type SIB2__cellReselectionServingFreqInfo__root_list) * (seq_ext_type SIB2__cellReselectionServingFreqInfo__ext_list).
Definition SIB2__cellReselectionServingFreqInfo__list_cond (z : SIB2__cellReselectionServingFreqInfo__list_type) : Prop :=
        (seq_cond SIB2__cellReselectionServingFreqInfo__root_list (fst z)) /\ (seq_ext_cond SIB2__cellReselectionServingFreqInfo__ext_list (snd z)).
Definition SIB2__cellReselectionServingFreqInfo__list_format : T_Format SIB2__cellReselectionServingFreqInfo__list_type SIB2__cellReselectionServingFreqInfo__list_cond :=
 (* Eval compute in *) seq_ext_format SIB2__cellReselectionServingFreqInfo__root_list SIB2__cellReselectionServingFreqInfo__root_Format_list SIB2__cellReselectionServingFreqInfo__ext_list SIB2__cellReselectionServingFreqInfo__ext_Format_list.

Opaque SIB2__cellReselectionServingFreqInfo__list_format.
Definition SIB2__cellReselectionServingFreqInfo__F1 (z : SIB2__cellReselectionServingFreqInfo__Type) : SIB2__cellReselectionServingFreqInfo__list_type :=
  (((SIB2__cellReselectionServingFreqInfo__s_NonIntraSearchP z, (SIB2__cellReselectionServingFreqInfo__s_NonIntraSearchQ z, (SIB2__cellReselectionServingFreqInfo__threshServingLowP z, (SIB2__cellReselectionServingFreqInfo__threshServingLowQ z, (SIB2__cellReselectionServingFreqInfo__cellReselectionPriority z, (SIB2__cellReselectionServingFreqInfo__cellReselectionSubPriority z, tt))))))), (
tt)).
Definition SIB2__cellReselectionServingFreqInfo__F2 (y : SIB2__cellReselectionServingFreqInfo__list_type) : SIB2__cellReselectionServingFreqInfo__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__SIB2__cellReselectionServingFreqInfo__Type j0 j1 j2 j3 j4 j5
  end.
Definition SIB2__cellReselectionServingFreqInfo__helper1 : (forall a : SIB2__cellReselectionServingFreqInfo__Type, SIB2__cellReselectionServingFreqInfo__cond a -> SIB2__cellReselectionServingFreqInfo__list_cond (SIB2__cellReselectionServingFreqInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB2__cellReselectionServingFreqInfo__helper2 : (forall a : SIB2__cellReselectionServingFreqInfo__Type, SIB2__cellReselectionServingFreqInfo__F2 (SIB2__cellReselectionServingFreqInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB2__cellReselectionServingFreqInfo__helper3 : (forall b : SIB2__cellReselectionServingFreqInfo__list_type, SIB2__cellReselectionServingFreqInfo__list_cond b -> SIB2__cellReselectionServingFreqInfo__cond (SIB2__cellReselectionServingFreqInfo__F2 b) /\ SIB2__cellReselectionServingFreqInfo__F1 (SIB2__cellReselectionServingFreqInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB2__cellReselectionServingFreqInfo__cond, SIB2__cellReselectionServingFreqInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB2__cellReselectionServingFreqInfo__Format : T_Format SIB2__cellReselectionServingFreqInfo__Type SIB2__cellReselectionServingFreqInfo__cond :=
 proj2_format SIB2__cellReselectionServingFreqInfo__cond SIB2__cellReselectionServingFreqInfo__list_format  SIB2__cellReselectionServingFreqInfo__F1 SIB2__cellReselectionServingFreqInfo__F2 SIB2__cellReselectionServingFreqInfo__helper1 SIB2__cellReselectionServingFreqInfo__helper2 SIB2__cellReselectionServingFreqInfo__helper3.

Opaque SIB2__cellReselectionServingFreqInfo__cond SIB2__cellReselectionServingFreqInfo__Format.


Definition SIB2__intraFreqCellReselectionInfo__ext0O__Format_Type := Eval cbn in seq_format_prod SIB2__intraFreqCellReselectionInfo__ext0O__list.
Definition SIB2__intraFreqCellReselectionInfo__ext0O__Format_list : SIB2__intraFreqCellReselectionInfo__ext0O__Format_Type :=
  (SpeedStateScaleFactors__Format, unit_format).
Definition SIB2__intraFreqCellReselectionInfo__ext0O__list__Format := (*Eval compute in *) seq_format SIB2__intraFreqCellReselectionInfo__ext0O__list SIB2__intraFreqCellReselectionInfo__ext0O__Format_list.
Definition SIB2__intraFreqCellReselectionInfo__ext0O__F1 z :=
  (SIB2__intraFreqCellReselectionInfo__ext0O__t_ReselectionNR_SF z, tt).
Definition SIB2__intraFreqCellReselectionInfo__ext0O__F2 (y : seq_type SIB2__intraFreqCellReselectionInfo__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SIB2__intraFreqCellReselectionInfo__ext0O__Type i0
  end.
Lemma SIB2__intraFreqCellReselectionInfo__ext0O__F1F2_cond (z : SIB2__intraFreqCellReselectionInfo__ext0O__Type)
  : SIB2__intraFreqCellReselectionInfo__ext0O__cond z ->
  (seq_cond SIB2__intraFreqCellReselectionInfo__ext0O__list (SIB2__intraFreqCellReselectionInfo__ext0O__F1 z)).
intro H. unfold SIB2__intraFreqCellReselectionInfo__ext0O__cond in H. simpl. auto. Qed.
Lemma SIB2__intraFreqCellReselectionInfo__ext0O__F1F2_cond2 (z : SIB2__intraFreqCellReselectionInfo__ext0O__Type)
 : SIB2__intraFreqCellReselectionInfo__ext0O__F2 (SIB2__intraFreqCellReselectionInfo__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__intraFreqCellReselectionInfo__ext0O__F2F1_cond (y : seq_type SIB2__intraFreqCellReselectionInfo__ext0O__list)
  : seq_cond SIB2__intraFreqCellReselectionInfo__ext0O__list y ->
 (SIB2__intraFreqCellReselectionInfo__ext0O__cond (SIB2__intraFreqCellReselectionInfo__ext0O__F2 y)) /\  SIB2__intraFreqCellReselectionInfo__ext0O__F1 (SIB2__intraFreqCellReselectionInfo__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__intraFreqCellReselectionInfo__ext0O__cond. simpl in *. auto.
 - simpl. unfold SIB2__intraFreqCellReselectionInfo__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__intraFreqCellReselectionInfo__ext0O__Format : T_Format SIB2__intraFreqCellReselectionInfo__ext0O__Type SIB2__intraFreqCellReselectionInfo__ext0O__cond :=
        proj2_format  SIB2__intraFreqCellReselectionInfo__ext0O__cond SIB2__intraFreqCellReselectionInfo__ext0O__list__Format
    SIB2__intraFreqCellReselectionInfo__ext0O__F1 SIB2__intraFreqCellReselectionInfo__ext0O__F2 SIB2__intraFreqCellReselectionInfo__ext0O__F1F2_cond  SIB2__intraFreqCellReselectionInfo__ext0O__F1F2_cond2 SIB2__intraFreqCellReselectionInfo__ext0O__F2F1_cond.
Opaque SIB2__intraFreqCellReselectionInfo__ext0O__cond SIB2__intraFreqCellReselectionInfo__ext0O__Format.

Definition SIB2__intraFreqCellReselectionInfo__ext0__check_all_none (b : SIB2__intraFreqCellReselectionInfo__ext0O__Type) : bool :=
match b with 
  | make__SIB2__intraFreqCellReselectionInfo__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SIB2__intraFreqCellReselectionInfo__ext0__Format : T_Format SIB2__intraFreqCellReselectionInfo__ext0__Type SIB2__intraFreqCellReselectionInfo__ext0__cond :=
  restrict_add_format SIB2__intraFreqCellReselectionInfo__ext0__check_all_none SIB2__intraFreqCellReselectionInfo__ext0O__Format.

Opaque SIB2__intraFreqCellReselectionInfo__ext0__cond SIB2__intraFreqCellReselectionInfo__ext0__Format.


Definition SIB2__intraFreqCellReselectionInfo__ext1O__Format_Type := Eval cbn in seq_format_prod SIB2__intraFreqCellReselectionInfo__ext1O__list.
Definition SIB2__intraFreqCellReselectionInfo__ext1O__Format_list : SIB2__intraFreqCellReselectionInfo__ext1O__Format_Type :=
  (SSB_MTC2_LP_r16__Format, (SSB_PositionQCL_Relation_r16__Format, unit_format)).
Definition SIB2__intraFreqCellReselectionInfo__ext1O__list__Format := (*Eval compute in *) seq_format SIB2__intraFreqCellReselectionInfo__ext1O__list SIB2__intraFreqCellReselectionInfo__ext1O__Format_list.
Definition SIB2__intraFreqCellReselectionInfo__ext1O__F1 z :=
  (SIB2__intraFreqCellReselectionInfo__ext1O__smtc2_LP_r16 z, (SIB2__intraFreqCellReselectionInfo__ext1O__ssb_PositionQCL_Common_r16 z, tt)).
Definition SIB2__intraFreqCellReselectionInfo__ext1O__F2 (y : seq_type SIB2__intraFreqCellReselectionInfo__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB2__intraFreqCellReselectionInfo__ext1O__Type i0 i1
  end.
Lemma SIB2__intraFreqCellReselectionInfo__ext1O__F1F2_cond (z : SIB2__intraFreqCellReselectionInfo__ext1O__Type)
  : SIB2__intraFreqCellReselectionInfo__ext1O__cond z ->
  (seq_cond SIB2__intraFreqCellReselectionInfo__ext1O__list (SIB2__intraFreqCellReselectionInfo__ext1O__F1 z)).
intro H. unfold SIB2__intraFreqCellReselectionInfo__ext1O__cond in H. simpl. auto. Qed.
Lemma SIB2__intraFreqCellReselectionInfo__ext1O__F1F2_cond2 (z : SIB2__intraFreqCellReselectionInfo__ext1O__Type)
 : SIB2__intraFreqCellReselectionInfo__ext1O__F2 (SIB2__intraFreqCellReselectionInfo__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__intraFreqCellReselectionInfo__ext1O__F2F1_cond (y : seq_type SIB2__intraFreqCellReselectionInfo__ext1O__list)
  : seq_cond SIB2__intraFreqCellReselectionInfo__ext1O__list y ->
 (SIB2__intraFreqCellReselectionInfo__ext1O__cond (SIB2__intraFreqCellReselectionInfo__ext1O__F2 y)) /\  SIB2__intraFreqCellReselectionInfo__ext1O__F1 (SIB2__intraFreqCellReselectionInfo__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__intraFreqCellReselectionInfo__ext1O__cond. simpl in *. auto.
 - simpl. unfold SIB2__intraFreqCellReselectionInfo__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__intraFreqCellReselectionInfo__ext1O__Format : T_Format SIB2__intraFreqCellReselectionInfo__ext1O__Type SIB2__intraFreqCellReselectionInfo__ext1O__cond :=
        proj2_format  SIB2__intraFreqCellReselectionInfo__ext1O__cond SIB2__intraFreqCellReselectionInfo__ext1O__list__Format
    SIB2__intraFreqCellReselectionInfo__ext1O__F1 SIB2__intraFreqCellReselectionInfo__ext1O__F2 SIB2__intraFreqCellReselectionInfo__ext1O__F1F2_cond  SIB2__intraFreqCellReselectionInfo__ext1O__F1F2_cond2 SIB2__intraFreqCellReselectionInfo__ext1O__F2F1_cond.
Opaque SIB2__intraFreqCellReselectionInfo__ext1O__cond SIB2__intraFreqCellReselectionInfo__ext1O__Format.

Definition SIB2__intraFreqCellReselectionInfo__ext1__check_all_none (b : SIB2__intraFreqCellReselectionInfo__ext1O__Type) : bool :=
match b with 
  | make__SIB2__intraFreqCellReselectionInfo__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition SIB2__intraFreqCellReselectionInfo__ext1__Format : T_Format SIB2__intraFreqCellReselectionInfo__ext1__Type SIB2__intraFreqCellReselectionInfo__ext1__cond :=
  restrict_add_format SIB2__intraFreqCellReselectionInfo__ext1__check_all_none SIB2__intraFreqCellReselectionInfo__ext1O__Format.

Opaque SIB2__intraFreqCellReselectionInfo__ext1__cond SIB2__intraFreqCellReselectionInfo__ext1__Format.


Definition SIB2__intraFreqCellReselectionInfo__ext2O__Format_Type := Eval cbn in seq_format_prod SIB2__intraFreqCellReselectionInfo__ext2O__list.
Definition SIB2__intraFreqCellReselectionInfo__ext2O__Format_list : SIB2__intraFreqCellReselectionInfo__ext2O__Format_Type :=
  (SSB_PositionQCL_Relation_r17__Format, unit_format).
Definition SIB2__intraFreqCellReselectionInfo__ext2O__list__Format := (*Eval compute in *) seq_format SIB2__intraFreqCellReselectionInfo__ext2O__list SIB2__intraFreqCellReselectionInfo__ext2O__Format_list.
Definition SIB2__intraFreqCellReselectionInfo__ext2O__F1 z :=
  (SIB2__intraFreqCellReselectionInfo__ext2O__ssb_PositionQCL_Common_r17 z, tt).
Definition SIB2__intraFreqCellReselectionInfo__ext2O__F2 (y : seq_type SIB2__intraFreqCellReselectionInfo__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__SIB2__intraFreqCellReselectionInfo__ext2O__Type i0
  end.
Lemma SIB2__intraFreqCellReselectionInfo__ext2O__F1F2_cond (z : SIB2__intraFreqCellReselectionInfo__ext2O__Type)
  : SIB2__intraFreqCellReselectionInfo__ext2O__cond z ->
  (seq_cond SIB2__intraFreqCellReselectionInfo__ext2O__list (SIB2__intraFreqCellReselectionInfo__ext2O__F1 z)).
intro H. unfold SIB2__intraFreqCellReselectionInfo__ext2O__cond in H. simpl. auto. Qed.
Lemma SIB2__intraFreqCellReselectionInfo__ext2O__F1F2_cond2 (z : SIB2__intraFreqCellReselectionInfo__ext2O__Type)
 : SIB2__intraFreqCellReselectionInfo__ext2O__F2 (SIB2__intraFreqCellReselectionInfo__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__intraFreqCellReselectionInfo__ext2O__F2F1_cond (y : seq_type SIB2__intraFreqCellReselectionInfo__ext2O__list)
  : seq_cond SIB2__intraFreqCellReselectionInfo__ext2O__list y ->
 (SIB2__intraFreqCellReselectionInfo__ext2O__cond (SIB2__intraFreqCellReselectionInfo__ext2O__F2 y)) /\  SIB2__intraFreqCellReselectionInfo__ext2O__F1 (SIB2__intraFreqCellReselectionInfo__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__intraFreqCellReselectionInfo__ext2O__cond. simpl in *. auto.
 - simpl. unfold SIB2__intraFreqCellReselectionInfo__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__intraFreqCellReselectionInfo__ext2O__Format : T_Format SIB2__intraFreqCellReselectionInfo__ext2O__Type SIB2__intraFreqCellReselectionInfo__ext2O__cond :=
        proj2_format  SIB2__intraFreqCellReselectionInfo__ext2O__cond SIB2__intraFreqCellReselectionInfo__ext2O__list__Format
    SIB2__intraFreqCellReselectionInfo__ext2O__F1 SIB2__intraFreqCellReselectionInfo__ext2O__F2 SIB2__intraFreqCellReselectionInfo__ext2O__F1F2_cond  SIB2__intraFreqCellReselectionInfo__ext2O__F1F2_cond2 SIB2__intraFreqCellReselectionInfo__ext2O__F2F1_cond.
Opaque SIB2__intraFreqCellReselectionInfo__ext2O__cond SIB2__intraFreqCellReselectionInfo__ext2O__Format.

Definition SIB2__intraFreqCellReselectionInfo__ext2__check_all_none (b : SIB2__intraFreqCellReselectionInfo__ext2O__Type) : bool :=
match b with 
  | make__SIB2__intraFreqCellReselectionInfo__ext2O__Type None  => false 
  | _ => true 
 end.
Definition SIB2__intraFreqCellReselectionInfo__ext2__Format : T_Format SIB2__intraFreqCellReselectionInfo__ext2__Type SIB2__intraFreqCellReselectionInfo__ext2__cond :=
  restrict_add_format SIB2__intraFreqCellReselectionInfo__ext2__check_all_none SIB2__intraFreqCellReselectionInfo__ext2O__Format.

Opaque SIB2__intraFreqCellReselectionInfo__ext2__cond SIB2__intraFreqCellReselectionInfo__ext2__Format.


Definition SIB2__intraFreqCellReselectionInfo__ext3O__Format_Type := Eval cbn in seq_format_prod SIB2__intraFreqCellReselectionInfo__ext3O__list.
Definition SIB2__intraFreqCellReselectionInfo__ext3O__Format_list : SIB2__intraFreqCellReselectionInfo__ext3O__Format_Type :=
  (SSB_MTC4List_r17__Format, unit_format).
Definition SIB2__intraFreqCellReselectionInfo__ext3O__list__Format := (*Eval compute in *) seq_format SIB2__intraFreqCellReselectionInfo__ext3O__list SIB2__intraFreqCellReselectionInfo__ext3O__Format_list.
Definition SIB2__intraFreqCellReselectionInfo__ext3O__F1 z :=
  (SIB2__intraFreqCellReselectionInfo__ext3O__smtc4list_r17 z, tt).
Definition SIB2__intraFreqCellReselectionInfo__ext3O__F2 (y : seq_type SIB2__intraFreqCellReselectionInfo__ext3O__list) :=
  match y with
  | (i0, _)=>
    make__SIB2__intraFreqCellReselectionInfo__ext3O__Type i0
  end.
Lemma SIB2__intraFreqCellReselectionInfo__ext3O__F1F2_cond (z : SIB2__intraFreqCellReselectionInfo__ext3O__Type)
  : SIB2__intraFreqCellReselectionInfo__ext3O__cond z ->
  (seq_cond SIB2__intraFreqCellReselectionInfo__ext3O__list (SIB2__intraFreqCellReselectionInfo__ext3O__F1 z)).
intro H. unfold SIB2__intraFreqCellReselectionInfo__ext3O__cond in H. simpl. auto. Qed.
Lemma SIB2__intraFreqCellReselectionInfo__ext3O__F1F2_cond2 (z : SIB2__intraFreqCellReselectionInfo__ext3O__Type)
 : SIB2__intraFreqCellReselectionInfo__ext3O__F2 (SIB2__intraFreqCellReselectionInfo__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__intraFreqCellReselectionInfo__ext3O__F2F1_cond (y : seq_type SIB2__intraFreqCellReselectionInfo__ext3O__list)
  : seq_cond SIB2__intraFreqCellReselectionInfo__ext3O__list y ->
 (SIB2__intraFreqCellReselectionInfo__ext3O__cond (SIB2__intraFreqCellReselectionInfo__ext3O__F2 y)) /\  SIB2__intraFreqCellReselectionInfo__ext3O__F1 (SIB2__intraFreqCellReselectionInfo__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__intraFreqCellReselectionInfo__ext3O__cond. simpl in *. auto.
 - simpl. unfold SIB2__intraFreqCellReselectionInfo__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__intraFreqCellReselectionInfo__ext3O__Format : T_Format SIB2__intraFreqCellReselectionInfo__ext3O__Type SIB2__intraFreqCellReselectionInfo__ext3O__cond :=
        proj2_format  SIB2__intraFreqCellReselectionInfo__ext3O__cond SIB2__intraFreqCellReselectionInfo__ext3O__list__Format
    SIB2__intraFreqCellReselectionInfo__ext3O__F1 SIB2__intraFreqCellReselectionInfo__ext3O__F2 SIB2__intraFreqCellReselectionInfo__ext3O__F1F2_cond  SIB2__intraFreqCellReselectionInfo__ext3O__F1F2_cond2 SIB2__intraFreqCellReselectionInfo__ext3O__F2F1_cond.
Opaque SIB2__intraFreqCellReselectionInfo__ext3O__cond SIB2__intraFreqCellReselectionInfo__ext3O__Format.

Definition SIB2__intraFreqCellReselectionInfo__ext3__check_all_none (b : SIB2__intraFreqCellReselectionInfo__ext3O__Type) : bool :=
match b with 
  | make__SIB2__intraFreqCellReselectionInfo__ext3O__Type None  => false 
  | _ => true 
 end.
Definition SIB2__intraFreqCellReselectionInfo__ext3__Format : T_Format SIB2__intraFreqCellReselectionInfo__ext3__Type SIB2__intraFreqCellReselectionInfo__ext3__cond :=
  restrict_add_format SIB2__intraFreqCellReselectionInfo__ext3__check_all_none SIB2__intraFreqCellReselectionInfo__ext3O__Format.

Opaque SIB2__intraFreqCellReselectionInfo__ext3__cond SIB2__intraFreqCellReselectionInfo__ext3__Format.


Definition SIB2__intraFreqCellReselectionInfo__root_Format_Type := Eval cbn in seq_format_prod SIB2__intraFreqCellReselectionInfo__root_list.
Definition SIB2__intraFreqCellReselectionInfo__root_Format_list : SIB2__intraFreqCellReselectionInfo__root_Format_Type :=
  (Q_RxLevMin__Format, (Q_RxLevMin__Format, (Q_QualMin__Format, (ReselectionThreshold__Format, (ReselectionThresholdQ__Format, (T_Reselection__Format, (MultiFrequencyBandListNR_SIB__Format, (MultiFrequencyBandListNR_SIB__Format, (P_Max__Format, (SSB_MTC__Format, (SS_RSSI_Measurement__Format, (SSB_ToMeasure__Format, (bool__Format, unit_format))))))))))))).

Definition SIB2__intraFreqCellReselectionInfo__ext_Format_Type := Eval cbn in get_formats SIB2__intraFreqCellReselectionInfo__ext_list.
Definition SIB2__intraFreqCellReselectionInfo__ext_Format_list : SIB2__intraFreqCellReselectionInfo__ext_Format_Type :=
  (SIB2__intraFreqCellReselectionInfo__ext0__Format, (SIB2__intraFreqCellReselectionInfo__ext1__Format, (SIB2__intraFreqCellReselectionInfo__ext2__Format, (SIB2__intraFreqCellReselectionInfo__ext3__Format, unit__Format)))).

Definition SIB2__intraFreqCellReselectionInfo__list_type : Set := (seq_type SIB2__intraFreqCellReselectionInfo__root_list) * (seq_ext_type SIB2__intraFreqCellReselectionInfo__ext_list).
Definition SIB2__intraFreqCellReselectionInfo__list_cond (z : SIB2__intraFreqCellReselectionInfo__list_type) : Prop :=
        (seq_cond SIB2__intraFreqCellReselectionInfo__root_list (fst z)) /\ (seq_ext_cond SIB2__intraFreqCellReselectionInfo__ext_list (snd z)).
Definition SIB2__intraFreqCellReselectionInfo__list_format : T_Format SIB2__intraFreqCellReselectionInfo__list_type SIB2__intraFreqCellReselectionInfo__list_cond :=
 (* Eval compute in *) seq_ext_format SIB2__intraFreqCellReselectionInfo__root_list SIB2__intraFreqCellReselectionInfo__root_Format_list SIB2__intraFreqCellReselectionInfo__ext_list SIB2__intraFreqCellReselectionInfo__ext_Format_list.

Opaque SIB2__intraFreqCellReselectionInfo__list_format.
Definition SIB2__intraFreqCellReselectionInfo__F1 (z : SIB2__intraFreqCellReselectionInfo__Type) : SIB2__intraFreqCellReselectionInfo__list_type :=
  (((SIB2__intraFreqCellReselectionInfo__q_RxLevMin z, (SIB2__intraFreqCellReselectionInfo__q_RxLevMinSUL z, (SIB2__intraFreqCellReselectionInfo__q_QualMin z, (SIB2__intraFreqCellReselectionInfo__s_IntraSearchP z, (SIB2__intraFreqCellReselectionInfo__s_IntraSearchQ z, (SIB2__intraFreqCellReselectionInfo__t_ReselectionNR z, (SIB2__intraFreqCellReselectionInfo__frequencyBandList z, (SIB2__intraFreqCellReselectionInfo__frequencyBandListSUL z, (SIB2__intraFreqCellReselectionInfo__p_Max z, (SIB2__intraFreqCellReselectionInfo__smtc z, (SIB2__intraFreqCellReselectionInfo__ss_RSSI_Measurement z, (SIB2__intraFreqCellReselectionInfo__ssb_ToMeasure z, (SIB2__intraFreqCellReselectionInfo__deriveSSB_IndexFromCell z, tt)))))))))))))), (
(SIB2__intraFreqCellReselectionInfo__ext0 z, (SIB2__intraFreqCellReselectionInfo__ext1 z, (SIB2__intraFreqCellReselectionInfo__ext2 z, (SIB2__intraFreqCellReselectionInfo__ext3 z, tt)))))).
Definition SIB2__intraFreqCellReselectionInfo__F2 (y : SIB2__intraFreqCellReselectionInfo__list_type) : SIB2__intraFreqCellReselectionInfo__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, _))))))))))))), (i0, (i1, (i2, (i3, _)))))=>
    make__SIB2__intraFreqCellReselectionInfo__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 i0 i1 i2 i3
  end.
Definition SIB2__intraFreqCellReselectionInfo__helper1 : (forall a : SIB2__intraFreqCellReselectionInfo__Type, SIB2__intraFreqCellReselectionInfo__cond a -> SIB2__intraFreqCellReselectionInfo__list_cond (SIB2__intraFreqCellReselectionInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB2__intraFreqCellReselectionInfo__helper2 : (forall a : SIB2__intraFreqCellReselectionInfo__Type, SIB2__intraFreqCellReselectionInfo__F2 (SIB2__intraFreqCellReselectionInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB2__intraFreqCellReselectionInfo__helper3 : (forall b : SIB2__intraFreqCellReselectionInfo__list_type, SIB2__intraFreqCellReselectionInfo__list_cond b -> SIB2__intraFreqCellReselectionInfo__cond (SIB2__intraFreqCellReselectionInfo__F2 b) /\ SIB2__intraFreqCellReselectionInfo__F1 (SIB2__intraFreqCellReselectionInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB2__intraFreqCellReselectionInfo__cond, SIB2__intraFreqCellReselectionInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB2__intraFreqCellReselectionInfo__Format : T_Format SIB2__intraFreqCellReselectionInfo__Type SIB2__intraFreqCellReselectionInfo__cond :=
 proj2_format SIB2__intraFreqCellReselectionInfo__cond SIB2__intraFreqCellReselectionInfo__list_format  SIB2__intraFreqCellReselectionInfo__F1 SIB2__intraFreqCellReselectionInfo__F2 SIB2__intraFreqCellReselectionInfo__helper1 SIB2__intraFreqCellReselectionInfo__helper2 SIB2__intraFreqCellReselectionInfo__helper3.

Opaque SIB2__intraFreqCellReselectionInfo__cond SIB2__intraFreqCellReselectionInfo__Format.

Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Format : T_Format SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__nat__Format SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F1 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F2 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F1F2 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__F2F1.

Opaque SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__cond SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Format.

Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Format : T_Format SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__nat__Format SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F1 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F2 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F1F2 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__F2F1.

Opaque SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__cond SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Format.


Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Format_Type := Eval cbn in seq_format_prod SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Format_list : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Format_Type :=
  (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16__Format, (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16__Format, unit_format)).
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list__Format := (*Eval compute in *) seq_format SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Format_list.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1 z :=
  (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__s_SearchDeltaP_r16 z, (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__t_SearchDeltaP_r16 z, tt)).
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F2 (y : seq_type SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Type i0 i1
  end.
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1F2_cond (z : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Type)
  : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond z ->
  (seq_cond SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1 z)).
intro H. unfold SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond in H. simpl. auto. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1F2_cond2 (z : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Type)
 : SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F2 (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F2F1_cond (y : seq_type SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list)
  : seq_cond SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list y ->
 (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F2 y)) /\  SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1 (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond. simpl in *. auto.
 - simpl. unfold SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Format : T_Format SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Type SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond :=
        proj2_format  SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__list__Format
    SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F2 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1F2_cond  SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F1F2_cond2 SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__F2F1_cond.
Opaque SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__cond SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Format.


Definition SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Format_Type := Eval cbn in seq_format_prod SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list.
Definition SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Format_list : SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Format_Type :=
  (ReselectionThreshold__Format, (ReselectionThresholdQ__Format, unit_format)).
Definition SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list__Format := (*Eval compute in *) seq_format SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Format_list.
Definition SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1 z :=
  (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__s_SearchThresholdP_r16 z, (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__s_SearchThresholdQ_r16 z, tt)).
Definition SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F2 (y : seq_type SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Type i0 i1
  end.
Lemma SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1F2_cond (z : SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Type)
  : SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond z ->
  (seq_cond SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1 z)).
intro H. unfold SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond in H. simpl. auto. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1F2_cond2 (z : SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Type)
 : SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F2 (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F2F1_cond (y : seq_type SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list)
  : seq_cond SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list y ->
 (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F2 y)) /\  SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1 (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond. simpl in *. auto.
 - simpl. unfold SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Format : T_Format SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Type SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond :=
        proj2_format  SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__list__Format
    SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1 SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F2 SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1F2_cond  SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F1F2_cond2 SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__F2F1_cond.
Opaque SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__cond SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Format.

Definition SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Format : T_Format SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__nat__Format SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F1 SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F2 SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F1F2 SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__F2F1.

Opaque SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__cond SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Format.

Definition SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Format : T_Format SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__nat__Format SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F1 SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F2 SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F1F2 SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__F2F1.

Opaque SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__cond SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Format.


Definition SIB2__ext0O__relaxedMeasurement_r16__Format_Type := Eval cbn in seq_format_prod SIB2__ext0O__relaxedMeasurement_r16__list.
Definition SIB2__ext0O__relaxedMeasurement_r16__Format_list : SIB2__ext0O__relaxedMeasurement_r16__Format_Type :=
  (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16__Format, (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16__Format, (SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16__Format, (SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16__Format, unit_format)))).
Definition SIB2__ext0O__relaxedMeasurement_r16__list__Format := (*Eval compute in *) seq_format SIB2__ext0O__relaxedMeasurement_r16__list SIB2__ext0O__relaxedMeasurement_r16__Format_list.
Definition SIB2__ext0O__relaxedMeasurement_r16__F1 z :=
  (SIB2__ext0O__relaxedMeasurement_r16__lowMobilityEvaluation_r16 z, (SIB2__ext0O__relaxedMeasurement_r16__cellEdgeEvaluation_r16 z, (SIB2__ext0O__relaxedMeasurement_r16__combineRelaxedMeasCondition_r16 z, (SIB2__ext0O__relaxedMeasurement_r16__highPriorityMeasRelax_r16 z, tt)))).
Definition SIB2__ext0O__relaxedMeasurement_r16__F2 (y : seq_type SIB2__ext0O__relaxedMeasurement_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SIB2__ext0O__relaxedMeasurement_r16__Type i0 i1 i2 i3
  end.
Lemma SIB2__ext0O__relaxedMeasurement_r16__F1F2_cond (z : SIB2__ext0O__relaxedMeasurement_r16__Type)
  : SIB2__ext0O__relaxedMeasurement_r16__cond z ->
  (seq_cond SIB2__ext0O__relaxedMeasurement_r16__list (SIB2__ext0O__relaxedMeasurement_r16__F1 z)).
intro H. unfold SIB2__ext0O__relaxedMeasurement_r16__cond in H. simpl. auto. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__F1F2_cond2 (z : SIB2__ext0O__relaxedMeasurement_r16__Type)
 : SIB2__ext0O__relaxedMeasurement_r16__F2 (SIB2__ext0O__relaxedMeasurement_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__ext0O__relaxedMeasurement_r16__F2F1_cond (y : seq_type SIB2__ext0O__relaxedMeasurement_r16__list)
  : seq_cond SIB2__ext0O__relaxedMeasurement_r16__list y ->
 (SIB2__ext0O__relaxedMeasurement_r16__cond (SIB2__ext0O__relaxedMeasurement_r16__F2 y)) /\  SIB2__ext0O__relaxedMeasurement_r16__F1 (SIB2__ext0O__relaxedMeasurement_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__ext0O__relaxedMeasurement_r16__cond. simpl in *. auto.
 - simpl. unfold SIB2__ext0O__relaxedMeasurement_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__ext0O__relaxedMeasurement_r16__Format : T_Format SIB2__ext0O__relaxedMeasurement_r16__Type SIB2__ext0O__relaxedMeasurement_r16__cond :=
        proj2_format  SIB2__ext0O__relaxedMeasurement_r16__cond SIB2__ext0O__relaxedMeasurement_r16__list__Format
    SIB2__ext0O__relaxedMeasurement_r16__F1 SIB2__ext0O__relaxedMeasurement_r16__F2 SIB2__ext0O__relaxedMeasurement_r16__F1F2_cond  SIB2__ext0O__relaxedMeasurement_r16__F1F2_cond2 SIB2__ext0O__relaxedMeasurement_r16__F2F1_cond.
Opaque SIB2__ext0O__relaxedMeasurement_r16__cond SIB2__ext0O__relaxedMeasurement_r16__Format.


Definition SIB2__ext0O__Format_Type := Eval cbn in seq_format_prod SIB2__ext0O__list.
Definition SIB2__ext0O__Format_list : SIB2__ext0O__Format_Type :=
  (SIB2__ext0O__relaxedMeasurement_r16__Format, unit_format).
Definition SIB2__ext0O__list__Format := (*Eval compute in *) seq_format SIB2__ext0O__list SIB2__ext0O__Format_list.
Definition SIB2__ext0O__F1 z :=
  (SIB2__ext0O__relaxedMeasurement_r16 z, tt).
Definition SIB2__ext0O__F2 (y : seq_type SIB2__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SIB2__ext0O__Type i0
  end.
Lemma SIB2__ext0O__F1F2_cond (z : SIB2__ext0O__Type)
  : SIB2__ext0O__cond z ->
  (seq_cond SIB2__ext0O__list (SIB2__ext0O__F1 z)).
intro H. unfold SIB2__ext0O__cond in H. simpl. auto. Qed.
Lemma SIB2__ext0O__F1F2_cond2 (z : SIB2__ext0O__Type)
 : SIB2__ext0O__F2 (SIB2__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__ext0O__F2F1_cond (y : seq_type SIB2__ext0O__list)
  : seq_cond SIB2__ext0O__list y ->
 (SIB2__ext0O__cond (SIB2__ext0O__F2 y)) /\  SIB2__ext0O__F1 (SIB2__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__ext0O__cond. simpl in *. auto.
 - simpl. unfold SIB2__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__ext0O__Format : T_Format SIB2__ext0O__Type SIB2__ext0O__cond :=
        proj2_format  SIB2__ext0O__cond SIB2__ext0O__list__Format
    SIB2__ext0O__F1 SIB2__ext0O__F2 SIB2__ext0O__F1F2_cond  SIB2__ext0O__F1F2_cond2 SIB2__ext0O__F2F1_cond.
Opaque SIB2__ext0O__cond SIB2__ext0O__Format.

Definition SIB2__ext0__check_all_none (b : SIB2__ext0O__Type) : bool :=
match b with 
  | make__SIB2__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SIB2__ext0__Format : T_Format SIB2__ext0__Type SIB2__ext0__cond :=
  restrict_add_format SIB2__ext0__check_all_none SIB2__ext0O__Format.

Opaque SIB2__ext0__cond SIB2__ext0__Format.

Definition SIB2__ext1O__cellEquivalentSize_r17__Format : T_Format Z SIB2__ext1O__cellEquivalentSize_r17__cond :=
 ranged_int_format (2) (16) SIB2__ext1O__cellEquivalentSize_r17__helper1 SIB2__ext1O__cellEquivalentSize_r17__helper2.

Opaque SIB2__ext1O__cellEquivalentSize_r17__cond SIB2__ext1O__cellEquivalentSize_r17__Format.

Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Format : T_Format SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__nat__Format SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F1 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F2 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F1F2 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__F2F1.

Opaque SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__cond SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Format.

Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Format : T_Format SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__nat__Format SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F1 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F2 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F1F2 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__F2F1.

Opaque SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__cond SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Format.


Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Format_Type := Eval cbn in seq_format_prod SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Format_list : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Format_Type :=
  (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17__Format, (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17__Format, unit_format)).
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list__Format := (*Eval compute in *) seq_format SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Format_list.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1 z :=
  (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__s_SearchDeltaP_Stationary_r17 z, (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__t_SearchDeltaP_Stationary_r17 z, tt)).
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F2 (y : seq_type SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Type i0 i1
  end.
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1F2_cond (z : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Type)
  : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond z ->
  (seq_cond SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1 z)).
intro H. unfold SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond in H. simpl. auto. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1F2_cond2 (z : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Type)
 : SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F2 (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F2F1_cond (y : seq_type SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list)
  : seq_cond SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list y ->
 (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F2 y)) /\  SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1 (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond. simpl in *. auto.
 - simpl. unfold SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Format : T_Format SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Type SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond :=
        proj2_format  SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__list__Format
    SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F2 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1F2_cond  SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F1F2_cond2 SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__F2F1_cond.
Opaque SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__cond SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Format.


Definition SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Format_Type := Eval cbn in seq_format_prod SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list.
Definition SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Format_list : SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Format_Type :=
  (ReselectionThreshold__Format, (ReselectionThresholdQ__Format, unit_format)).
Definition SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list__Format := (*Eval compute in *) seq_format SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Format_list.
Definition SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1 z :=
  (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__s_SearchThresholdP2_r17 z, (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__s_SearchThresholdQ2_r17 z, tt)).
Definition SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F2 (y : seq_type SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Type i0 i1
  end.
Lemma SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1F2_cond (z : SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Type)
  : SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond z ->
  (seq_cond SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1 z)).
intro H. unfold SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond in H. simpl. auto. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1F2_cond2 (z : SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Type)
 : SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F2 (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F2F1_cond (y : seq_type SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list)
  : seq_cond SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list y ->
 (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F2 y)) /\  SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1 (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond. simpl in *. auto.
 - simpl. unfold SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Format : T_Format SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Type SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond :=
        proj2_format  SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__list__Format
    SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1 SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F2 SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1F2_cond  SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F1F2_cond2 SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__F2F1_cond.
Opaque SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__cond SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Format.

Definition SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Format : T_Format SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__nat__Format SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F1 SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F2 SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F1F2 SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__F2F1.

Opaque SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__cond SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Format.


Definition SIB2__ext1O__relaxedMeasurement_r17__Format_Type := Eval cbn in seq_format_prod SIB2__ext1O__relaxedMeasurement_r17__list.
Definition SIB2__ext1O__relaxedMeasurement_r17__Format_list : SIB2__ext1O__relaxedMeasurement_r17__Format_Type :=
  (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17__Format, (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17__Format, (SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17__Format, unit_format))).
Definition SIB2__ext1O__relaxedMeasurement_r17__list__Format := (*Eval compute in *) seq_format SIB2__ext1O__relaxedMeasurement_r17__list SIB2__ext1O__relaxedMeasurement_r17__Format_list.
Definition SIB2__ext1O__relaxedMeasurement_r17__F1 z :=
  (SIB2__ext1O__relaxedMeasurement_r17__stationaryMobilityEvaluation_r17 z, (SIB2__ext1O__relaxedMeasurement_r17__cellEdgeEvaluationWhileStationary_r17 z, (SIB2__ext1O__relaxedMeasurement_r17__combineRelaxedMeasCondition2_r17 z, tt))).
Definition SIB2__ext1O__relaxedMeasurement_r17__F2 (y : seq_type SIB2__ext1O__relaxedMeasurement_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SIB2__ext1O__relaxedMeasurement_r17__Type i0 i1 i2
  end.
Lemma SIB2__ext1O__relaxedMeasurement_r17__F1F2_cond (z : SIB2__ext1O__relaxedMeasurement_r17__Type)
  : SIB2__ext1O__relaxedMeasurement_r17__cond z ->
  (seq_cond SIB2__ext1O__relaxedMeasurement_r17__list (SIB2__ext1O__relaxedMeasurement_r17__F1 z)).
intro H. unfold SIB2__ext1O__relaxedMeasurement_r17__cond in H. simpl. auto. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__F1F2_cond2 (z : SIB2__ext1O__relaxedMeasurement_r17__Type)
 : SIB2__ext1O__relaxedMeasurement_r17__F2 (SIB2__ext1O__relaxedMeasurement_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__ext1O__relaxedMeasurement_r17__F2F1_cond (y : seq_type SIB2__ext1O__relaxedMeasurement_r17__list)
  : seq_cond SIB2__ext1O__relaxedMeasurement_r17__list y ->
 (SIB2__ext1O__relaxedMeasurement_r17__cond (SIB2__ext1O__relaxedMeasurement_r17__F2 y)) /\  SIB2__ext1O__relaxedMeasurement_r17__F1 (SIB2__ext1O__relaxedMeasurement_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__ext1O__relaxedMeasurement_r17__cond. simpl in *. auto.
 - simpl. unfold SIB2__ext1O__relaxedMeasurement_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__ext1O__relaxedMeasurement_r17__Format : T_Format SIB2__ext1O__relaxedMeasurement_r17__Type SIB2__ext1O__relaxedMeasurement_r17__cond :=
        proj2_format  SIB2__ext1O__relaxedMeasurement_r17__cond SIB2__ext1O__relaxedMeasurement_r17__list__Format
    SIB2__ext1O__relaxedMeasurement_r17__F1 SIB2__ext1O__relaxedMeasurement_r17__F2 SIB2__ext1O__relaxedMeasurement_r17__F1F2_cond  SIB2__ext1O__relaxedMeasurement_r17__F1F2_cond2 SIB2__ext1O__relaxedMeasurement_r17__F2F1_cond.
Opaque SIB2__ext1O__relaxedMeasurement_r17__cond SIB2__ext1O__relaxedMeasurement_r17__Format.


Definition SIB2__ext1O__Format_Type := Eval cbn in seq_format_prod SIB2__ext1O__list.
Definition SIB2__ext1O__Format_list : SIB2__ext1O__Format_Type :=
  (SIB2__ext1O__cellEquivalentSize_r17__Format, (SIB2__ext1O__relaxedMeasurement_r17__Format, unit_format)).
Definition SIB2__ext1O__list__Format := (*Eval compute in *) seq_format SIB2__ext1O__list SIB2__ext1O__Format_list.
Definition SIB2__ext1O__F1 z :=
  (SIB2__ext1O__cellEquivalentSize_r17 z, (SIB2__ext1O__relaxedMeasurement_r17 z, tt)).
Definition SIB2__ext1O__F2 (y : seq_type SIB2__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SIB2__ext1O__Type i0 i1
  end.
Lemma SIB2__ext1O__F1F2_cond (z : SIB2__ext1O__Type)
  : SIB2__ext1O__cond z ->
  (seq_cond SIB2__ext1O__list (SIB2__ext1O__F1 z)).
intro H. unfold SIB2__ext1O__cond in H. simpl. auto. Qed.
Lemma SIB2__ext1O__F1F2_cond2 (z : SIB2__ext1O__Type)
 : SIB2__ext1O__F2 (SIB2__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SIB2__ext1O__F2F1_cond (y : seq_type SIB2__ext1O__list)
  : seq_cond SIB2__ext1O__list y ->
 (SIB2__ext1O__cond (SIB2__ext1O__F2 y)) /\  SIB2__ext1O__F1 (SIB2__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SIB2__ext1O__cond. simpl in *. auto.
 - simpl. unfold SIB2__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SIB2__ext1O__Format : T_Format SIB2__ext1O__Type SIB2__ext1O__cond :=
        proj2_format  SIB2__ext1O__cond SIB2__ext1O__list__Format
    SIB2__ext1O__F1 SIB2__ext1O__F2 SIB2__ext1O__F1F2_cond  SIB2__ext1O__F1F2_cond2 SIB2__ext1O__F2F1_cond.
Opaque SIB2__ext1O__cond SIB2__ext1O__Format.

Definition SIB2__ext1__check_all_none (b : SIB2__ext1O__Type) : bool :=
match b with 
  | make__SIB2__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition SIB2__ext1__Format : T_Format SIB2__ext1__Type SIB2__ext1__cond :=
  restrict_add_format SIB2__ext1__check_all_none SIB2__ext1O__Format.

Opaque SIB2__ext1__cond SIB2__ext1__Format.


Definition SIB2__root_Format_Type := Eval cbn in seq_format_prod SIB2__root_list.
Definition SIB2__root_Format_list : SIB2__root_Format_Type :=
  (SIB2__cellReselectionInfoCommon__Format, (SIB2__cellReselectionServingFreqInfo__Format, (SIB2__intraFreqCellReselectionInfo__Format, unit_format))).

Definition SIB2__ext_Format_Type := Eval cbn in get_formats SIB2__ext_list.
Definition SIB2__ext_Format_list : SIB2__ext_Format_Type :=
  (SIB2__ext0__Format, (SIB2__ext1__Format, unit__Format)).

Definition SIB2__list_type : Set := (seq_type SIB2__root_list) * (seq_ext_type SIB2__ext_list).
Definition SIB2__list_cond (z : SIB2__list_type) : Prop :=
        (seq_cond SIB2__root_list (fst z)) /\ (seq_ext_cond SIB2__ext_list (snd z)).
Definition SIB2__list_format : T_Format SIB2__list_type SIB2__list_cond :=
 (* Eval compute in *) seq_ext_format SIB2__root_list SIB2__root_Format_list SIB2__ext_list SIB2__ext_Format_list.

Opaque SIB2__list_format.
Definition SIB2__F1 (z : SIB2__Type) : SIB2__list_type :=
  (((SIB2__cellReselectionInfoCommon z, (SIB2__cellReselectionServingFreqInfo z, (SIB2__intraFreqCellReselectionInfo z, tt)))), (
(SIB2__ext0 z, (SIB2__ext1 z, tt)))).
Definition SIB2__F2 (y : SIB2__list_type) : SIB2__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, _)))=>
    make__SIB2__Type j0 j1 j2 i0 i1
  end.
Definition SIB2__helper1 : (forall a : SIB2__Type, SIB2__cond a -> SIB2__list_cond (SIB2__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SIB2__helper2 : (forall a : SIB2__Type, SIB2__F2 (SIB2__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SIB2__helper3 : (forall b : SIB2__list_type, SIB2__list_cond b -> SIB2__cond (SIB2__F2 b) /\ SIB2__F1 (SIB2__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SIB2__cond, SIB2__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SIB2__Format : T_Format SIB2__Type SIB2__cond :=
 proj2_format SIB2__cond SIB2__list_format  SIB2__F1 SIB2__F2 SIB2__helper1 SIB2__helper2 SIB2__helper3.

Opaque SIB2__cond SIB2__Format.

