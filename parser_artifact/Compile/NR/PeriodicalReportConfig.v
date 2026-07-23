Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NR_RS_Type.

Opaque NR_RS_Type__cond NR_RS_Type__Format.

Require Import NR.ReportInterval.

Opaque ReportInterval__cond ReportInterval__Format.

Inductive PeriodicalReportConfig__reportAmount__Type : Set :=
 | PeriodicalReportConfig__reportAmount__r1
 | PeriodicalReportConfig__reportAmount__r2
 | PeriodicalReportConfig__reportAmount__r4
 | PeriodicalReportConfig__reportAmount__r8
 | PeriodicalReportConfig__reportAmount__r16
 | PeriodicalReportConfig__reportAmount__r32
 | PeriodicalReportConfig__reportAmount__r64
 | PeriodicalReportConfig__reportAmount__infinity
.
Definition PeriodicalReportConfig__reportAmount__cond := (fun (_ : PeriodicalReportConfig__reportAmount__Type) => True).
Lemma PeriodicalReportConfig__reportAmount__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PeriodicalReportConfig__reportAmount__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PeriodicalReportConfig__reportAmount__nat__helper.

Definition PeriodicalReportConfig__reportAmount__F1 t :=
  match t with
  | PeriodicalReportConfig__reportAmount__r1 => 0
  | PeriodicalReportConfig__reportAmount__r2 => 1
  | PeriodicalReportConfig__reportAmount__r4 => 2
  | PeriodicalReportConfig__reportAmount__r8 => 3
  | PeriodicalReportConfig__reportAmount__r16 => 4
  | PeriodicalReportConfig__reportAmount__r32 => 5
  | PeriodicalReportConfig__reportAmount__r64 => 6
  | PeriodicalReportConfig__reportAmount__infinity => 7
  end.
Definition PeriodicalReportConfig__reportAmount__F2 n :=
  match n with
  | 0 => PeriodicalReportConfig__reportAmount__r1
  | 1 => PeriodicalReportConfig__reportAmount__r2
  | 2 => PeriodicalReportConfig__reportAmount__r4
  | 3 => PeriodicalReportConfig__reportAmount__r8
  | 4 => PeriodicalReportConfig__reportAmount__r16
  | 5 => PeriodicalReportConfig__reportAmount__r32
  | 6 => PeriodicalReportConfig__reportAmount__r64
  | 7 => PeriodicalReportConfig__reportAmount__infinity
  | _ => PeriodicalReportConfig__reportAmount__r1
  end.
Lemma PeriodicalReportConfig__reportAmount__F1F2 : forall x : PeriodicalReportConfig__reportAmount__Type, (PeriodicalReportConfig__reportAmount__F1 x <= 7) /\ PeriodicalReportConfig__reportAmount__F2 (PeriodicalReportConfig__reportAmount__F1 x) = x. imp_solve. Qed.
Lemma PeriodicalReportConfig__reportAmount__F2F1 : forall (y : nat) (H : y <= 7), PeriodicalReportConfig__reportAmount__F1 (PeriodicalReportConfig__reportAmount__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasReportQuantity.

Opaque MeasReportQuantity__cond MeasReportQuantity__Format.

Lemma PeriodicalReportConfig__maxReportCells__helper1 : (1 <= maxCellReport)%Z. unfold maxCellReport.
 lia. Qed.
Lemma PeriodicalReportConfig__maxReportCells__helper2 : to_bit_sz (Z.to_nat (maxCellReport - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellReport - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PeriodicalReportConfig__maxReportCells__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PeriodicalReportConfig__maxReportCells__Type := Z.
Definition PeriodicalReportConfig__maxReportCells__cond := (fun z => (1 <= z <= maxCellReport)%Z).
Require Import NR.MeasReportQuantity.

Opaque MeasReportQuantity__cond MeasReportQuantity__Format.

Lemma PeriodicalReportConfig__maxNrofRS_IndexesToReport__helper1 : (1 <= maxNrofIndexesToReport)%Z. unfold maxNrofIndexesToReport.
 lia. Qed.
Lemma PeriodicalReportConfig__maxNrofRS_IndexesToReport__helper2 : to_bit_sz (Z.to_nat (maxNrofIndexesToReport - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofIndexesToReport - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PeriodicalReportConfig__maxNrofRS_IndexesToReport__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PeriodicalReportConfig__maxNrofRS_IndexesToReport__Type := Z.
Definition PeriodicalReportConfig__maxNrofRS_IndexesToReport__cond := (fun z => (1 <= z <= maxNrofIndexesToReport)%Z).
Require Import NR.MeasRSSI_ReportConfig_r16.

Opaque MeasRSSI_ReportConfig_r16__cond MeasRSSI_ReportConfig_r16__Format.

Inductive PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Type : Set :=
 | PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__true
.
Definition PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__cond := (fun (_ : PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Type) => True).
Lemma PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__nat__helper.

Definition PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F1 t :=
  match t with
  | PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__true => 0
  end.
Definition PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F2 n :=
  match n with
  | 0 => PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__true
  | _ => PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__true
  end.
Lemma PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F1F2 : forall x : PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Type, (PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F1 x <= 0) /\ PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F2 (PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F1 x) = x. imp_solve. Qed.
Lemma PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F2F1 : forall (y : nat) (H : y <= 0), PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F1 (PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.BT_NameList_r16.
Definition PeriodicalReportConfig__ext0O__includeBT_Meas_r16__Type := SetupRelease__Type BT_NameList_r16__Type.
Definition PeriodicalReportConfig__ext0O__includeBT_Meas_r16__cond := SetupRelease__cond _ BT_NameList_r16__cond.
Definition PeriodicalReportConfig__ext0O__includeBT_Meas_r16__Format : T_Format PeriodicalReportConfig__ext0O__includeBT_Meas_r16__Type PeriodicalReportConfig__ext0O__includeBT_Meas_r16__cond := SetupRelease__Format _ _ BT_NameList_r16__Format.
Opaque PeriodicalReportConfig__ext0O__includeBT_Meas_r16__cond PeriodicalReportConfig__ext0O__includeBT_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.WLAN_NameList_r16.
Definition PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__Type := SetupRelease__Type WLAN_NameList_r16__Type.
Definition PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__cond := SetupRelease__cond _ WLAN_NameList_r16__cond.
Definition PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__Format : T_Format PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__Type PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__cond := SetupRelease__Format _ _ WLAN_NameList_r16__Format.
Opaque PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__cond PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.Sensor_NameList_r16.
Definition PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__Type := SetupRelease__Type Sensor_NameList_r16__Type.
Definition PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__cond := SetupRelease__cond _ Sensor_NameList_r16__cond.
Definition PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__Format : T_Format PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__Type PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__cond := SetupRelease__Format _ _ Sensor_NameList_r16__Format.
Opaque PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__cond PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.UL_DelayValueConfig_r16.
Definition PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__Type := SetupRelease__Type UL_DelayValueConfig_r16__Type.
Definition PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__cond := SetupRelease__cond _ UL_DelayValueConfig_r16__cond.
Definition PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__Format : T_Format PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__Type PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__cond := SetupRelease__Format _ _ UL_DelayValueConfig_r16__Format.
Opaque PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__cond PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__Format.

Inductive PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Type : Set :=
 | PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__setup
.
Definition PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__cond := (fun (_ : PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Type) => True).
Lemma PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__nat__helper.

Definition PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F1 t :=
  match t with
  | PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__setup => 0
  end.
Definition PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F2 n :=
  match n with
  | 0 => PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__setup
  | _ => PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__setup
  end.
Lemma PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F1F2 : forall x : PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Type, (PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F1 x <= 0) /\ PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F2 (PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F1 x) = x. imp_solve. Qed.
Lemma PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F2F1 : forall (y : nat) (H : y <= 0), PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F1 (PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F2 y) = y. enum_solve H y. Qed.

Record PeriodicalReportConfig__ext0O__Type : Set :=
  make__PeriodicalReportConfig__ext0O__Type {
    PeriodicalReportConfig__ext0O__measRSSI_ReportConfig_r16 : option MeasRSSI_ReportConfig_r16__Type ;
    PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16 : option PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Type ;
    PeriodicalReportConfig__ext0O__includeBT_Meas_r16 : option PeriodicalReportConfig__ext0O__includeBT_Meas_r16__Type ;
    PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16 : option PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__Type ;
    PeriodicalReportConfig__ext0O__includeSensor_Meas_r16 : option PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__Type ;
    PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16 : option PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__Type ;
    PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16 : option PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Type ;
}.
Definition PeriodicalReportConfig__ext0O__list := (
 Opt MeasRSSI_ReportConfig_r16__Type MeasRSSI_ReportConfig_r16__cond ::
 Opt PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Type PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__cond ::
 Opt PeriodicalReportConfig__ext0O__includeBT_Meas_r16__Type PeriodicalReportConfig__ext0O__includeBT_Meas_r16__cond ::
 Opt PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__Type PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__cond ::
 Opt PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__Type PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__cond ::
 Opt PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__Type PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__cond ::
 Opt PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Type PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__cond ::
 nil).
Definition PeriodicalReportConfig__ext0O__cond z := 
  opt_cond MeasRSSI_ReportConfig_r16__cond (PeriodicalReportConfig__ext0O__measRSSI_ReportConfig_r16 z) /\
  opt_cond PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__cond (PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16 z) /\
  opt_cond PeriodicalReportConfig__ext0O__includeBT_Meas_r16__cond (PeriodicalReportConfig__ext0O__includeBT_Meas_r16 z) /\
  opt_cond PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__cond (PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16 z) /\
  opt_cond PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__cond (PeriodicalReportConfig__ext0O__includeSensor_Meas_r16 z) /\
  opt_cond PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__cond (PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16 z) /\
  opt_cond PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__cond (PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16 z) /\
  True.

Definition PeriodicalReportConfig__ext0__Type := PeriodicalReportConfig__ext0O__Type.
Definition PeriodicalReportConfig__ext0__cond := PeriodicalReportConfig__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.UL_ExcessDelayConfig_r17.
Definition PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__Type := SetupRelease__Type UL_ExcessDelayConfig_r17__Type.
Definition PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__cond := SetupRelease__cond _ UL_ExcessDelayConfig_r17__cond.
Definition PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__Format : T_Format PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__Type PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__cond := SetupRelease__Format _ _ UL_ExcessDelayConfig_r17__Format.
Opaque PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__cond PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__Format.

Inductive PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Type : Set :=
 | PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__true
.
Definition PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__cond := (fun (_ : PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Type) => True).
Lemma PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__nat__helper.

Definition PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F1 t :=
  match t with
  | PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__true => 0
  end.
Definition PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F2 n :=
  match n with
  | 0 => PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__true
  | _ => PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__true
  end.
Lemma PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F1F2 : forall x : PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Type, (PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F1 x <= 0) /\ PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F2 (PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F1 x) = x. imp_solve. Qed.
Lemma PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F2F1 : forall (y : nat) (H : y <= 0), PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F1 (PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_MeasReportQuantity_r16.

Opaque SL_MeasReportQuantity_r16__cond SL_MeasReportQuantity_r16__Format.

Record PeriodicalReportConfig__ext1O__Type : Set :=
  make__PeriodicalReportConfig__ext1O__Type {
    PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17 : option PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__Type ;
    PeriodicalReportConfig__ext1O__coarseLocationRequest_r17 : option PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Type ;
    PeriodicalReportConfig__ext1O__reportQuantityRelay_r17 : option SL_MeasReportQuantity_r16__Type ;
}.
Definition PeriodicalReportConfig__ext1O__list := (
 Opt PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__Type PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__cond ::
 Opt PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Type PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__cond ::
 Opt SL_MeasReportQuantity_r16__Type SL_MeasReportQuantity_r16__cond ::
 nil).
Definition PeriodicalReportConfig__ext1O__cond z := 
  opt_cond PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__cond (PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17 z) /\
  opt_cond PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__cond (PeriodicalReportConfig__ext1O__coarseLocationRequest_r17 z) /\
  opt_cond SL_MeasReportQuantity_r16__cond (PeriodicalReportConfig__ext1O__reportQuantityRelay_r17 z) /\
  True.

Definition PeriodicalReportConfig__ext1__Type := PeriodicalReportConfig__ext1O__Type.
Definition PeriodicalReportConfig__ext1__cond := PeriodicalReportConfig__ext1O__cond.

Record PeriodicalReportConfig__Type : Set :=
  make__PeriodicalReportConfig__Type {
    PeriodicalReportConfig__rsType : NR_RS_Type__Type ;
    PeriodicalReportConfig__reportInterval : ReportInterval__Type ;
    PeriodicalReportConfig__reportAmount : PeriodicalReportConfig__reportAmount__Type ;
    PeriodicalReportConfig__reportQuantityCell : MeasReportQuantity__Type ;
    PeriodicalReportConfig__maxReportCells : Z ;
    PeriodicalReportConfig__reportQuantityRS_Indexes : option MeasReportQuantity__Type ;
    PeriodicalReportConfig__maxNrofRS_IndexesToReport : option Z ;
    PeriodicalReportConfig__includeBeamMeasurements : bool ;
    PeriodicalReportConfig__useAllowedCellList : bool ;
    PeriodicalReportConfig__ext0 : option PeriodicalReportConfig__ext0__Type ;
    PeriodicalReportConfig__ext1 : option PeriodicalReportConfig__ext1__Type ;
}.
Definition PeriodicalReportConfig__root_list : list seq_elem := (
 Nor NR_RS_Type__Type NR_RS_Type__cond ::
 Nor ReportInterval__Type ReportInterval__cond ::
 Nor PeriodicalReportConfig__reportAmount__Type PeriodicalReportConfig__reportAmount__cond ::
 Nor MeasReportQuantity__Type MeasReportQuantity__cond ::
 Nor Z PeriodicalReportConfig__maxReportCells__cond ::
 Opt MeasReportQuantity__Type MeasReportQuantity__cond ::
 Opt Z PeriodicalReportConfig__maxNrofRS_IndexesToReport__cond ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 nil).
Definition PeriodicalReportConfig__ext_list : list typ := (
  typ_cons PeriodicalReportConfig__ext0__Type PeriodicalReportConfig__ext0__cond ::
  typ_cons PeriodicalReportConfig__ext1__Type PeriodicalReportConfig__ext1__cond ::
  nil).
Definition PeriodicalReportConfig__cond (z : PeriodicalReportConfig__Type) := 
(  NR_RS_Type__cond (PeriodicalReportConfig__rsType z) /\
  ReportInterval__cond (PeriodicalReportConfig__reportInterval z) /\
  PeriodicalReportConfig__reportAmount__cond (PeriodicalReportConfig__reportAmount z) /\
  MeasReportQuantity__cond (PeriodicalReportConfig__reportQuantityCell z) /\
  PeriodicalReportConfig__maxReportCells__cond (PeriodicalReportConfig__maxReportCells z) /\
  opt_cond MeasReportQuantity__cond (PeriodicalReportConfig__reportQuantityRS_Indexes z) /\
  opt_cond PeriodicalReportConfig__maxNrofRS_IndexesToReport__cond (PeriodicalReportConfig__maxNrofRS_IndexesToReport z) /\
  (fun _ => True) (PeriodicalReportConfig__includeBeamMeasurements z) /\
  (fun _ => True) (PeriodicalReportConfig__useAllowedCellList z) /\
  True) /\ 
(  opt_cond PeriodicalReportConfig__ext0__cond (PeriodicalReportConfig__ext0 z) /\
  opt_cond PeriodicalReportConfig__ext1__cond (PeriodicalReportConfig__ext1 z) /\
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
Definition PeriodicalReportConfig__reportAmount__Format : T_Format PeriodicalReportConfig__reportAmount__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PeriodicalReportConfig__reportAmount__nat__Format PeriodicalReportConfig__reportAmount__F1 PeriodicalReportConfig__reportAmount__F2 PeriodicalReportConfig__reportAmount__F1F2 PeriodicalReportConfig__reportAmount__F2F1.

Opaque PeriodicalReportConfig__reportAmount__cond PeriodicalReportConfig__reportAmount__Format.

Definition PeriodicalReportConfig__maxReportCells__Format : T_Format Z PeriodicalReportConfig__maxReportCells__cond :=
 ranged_int_format (1) (maxCellReport) PeriodicalReportConfig__maxReportCells__helper1 PeriodicalReportConfig__maxReportCells__helper2.

Opaque PeriodicalReportConfig__maxReportCells__cond PeriodicalReportConfig__maxReportCells__Format.

Definition PeriodicalReportConfig__maxNrofRS_IndexesToReport__Format : T_Format Z PeriodicalReportConfig__maxNrofRS_IndexesToReport__cond :=
 ranged_int_format (1) (maxNrofIndexesToReport) PeriodicalReportConfig__maxNrofRS_IndexesToReport__helper1 PeriodicalReportConfig__maxNrofRS_IndexesToReport__helper2.

Opaque PeriodicalReportConfig__maxNrofRS_IndexesToReport__cond PeriodicalReportConfig__maxNrofRS_IndexesToReport__Format.

Definition PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Format : T_Format PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__nat__Format PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F1 PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F2 PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F1F2 PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__F2F1.

Opaque PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__cond PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Format.

Opaque PeriodicalReportConfig__ext0O__includeBT_Meas_r16__cond PeriodicalReportConfig__ext0O__includeBT_Meas_r16__Format.

Opaque PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__cond PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__Format.

Opaque PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__cond PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__Format.

Opaque PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__cond PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__Format.

Definition PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Format : T_Format PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__nat__Format PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F1 PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F2 PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F1F2 PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__F2F1.

Opaque PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__cond PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Format.


Definition PeriodicalReportConfig__ext0O__Format_Type := Eval cbn in seq_format_prod PeriodicalReportConfig__ext0O__list.
Definition PeriodicalReportConfig__ext0O__Format_list : PeriodicalReportConfig__ext0O__Format_Type :=
  (MeasRSSI_ReportConfig_r16__Format, (PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16__Format, (PeriodicalReportConfig__ext0O__includeBT_Meas_r16__Format, (PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16__Format, (PeriodicalReportConfig__ext0O__includeSensor_Meas_r16__Format, (PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16__Format, (PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16__Format, unit_format))))))).
Definition PeriodicalReportConfig__ext0O__list__Format := (*Eval compute in *) seq_format PeriodicalReportConfig__ext0O__list PeriodicalReportConfig__ext0O__Format_list.
Definition PeriodicalReportConfig__ext0O__F1 z :=
  (PeriodicalReportConfig__ext0O__measRSSI_ReportConfig_r16 z, (PeriodicalReportConfig__ext0O__includeCommonLocationInfo_r16 z, (PeriodicalReportConfig__ext0O__includeBT_Meas_r16 z, (PeriodicalReportConfig__ext0O__includeWLAN_Meas_r16 z, (PeriodicalReportConfig__ext0O__includeSensor_Meas_r16 z, (PeriodicalReportConfig__ext0O__ul_DelayValueConfig_r16 z, (PeriodicalReportConfig__ext0O__reportAddNeighMeas_r16 z, tt))))))).
Definition PeriodicalReportConfig__ext0O__F2 (y : seq_type PeriodicalReportConfig__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__PeriodicalReportConfig__ext0O__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma PeriodicalReportConfig__ext0O__F1F2_cond (z : PeriodicalReportConfig__ext0O__Type)
  : PeriodicalReportConfig__ext0O__cond z ->
  (seq_cond PeriodicalReportConfig__ext0O__list (PeriodicalReportConfig__ext0O__F1 z)).
intro H. unfold PeriodicalReportConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma PeriodicalReportConfig__ext0O__F1F2_cond2 (z : PeriodicalReportConfig__ext0O__Type)
 : PeriodicalReportConfig__ext0O__F2 (PeriodicalReportConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PeriodicalReportConfig__ext0O__F2F1_cond (y : seq_type PeriodicalReportConfig__ext0O__list)
  : seq_cond PeriodicalReportConfig__ext0O__list y ->
 (PeriodicalReportConfig__ext0O__cond (PeriodicalReportConfig__ext0O__F2 y)) /\  PeriodicalReportConfig__ext0O__F1 (PeriodicalReportConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PeriodicalReportConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold PeriodicalReportConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PeriodicalReportConfig__ext0O__Format : T_Format PeriodicalReportConfig__ext0O__Type PeriodicalReportConfig__ext0O__cond :=
        proj2_format  PeriodicalReportConfig__ext0O__cond PeriodicalReportConfig__ext0O__list__Format
    PeriodicalReportConfig__ext0O__F1 PeriodicalReportConfig__ext0O__F2 PeriodicalReportConfig__ext0O__F1F2_cond  PeriodicalReportConfig__ext0O__F1F2_cond2 PeriodicalReportConfig__ext0O__F2F1_cond.
Opaque PeriodicalReportConfig__ext0O__cond PeriodicalReportConfig__ext0O__Format.

Definition PeriodicalReportConfig__ext0__check_all_none (b : PeriodicalReportConfig__ext0O__Type) : bool :=
match b with 
  | make__PeriodicalReportConfig__ext0O__Type None None None None None None None  => false 
  | _ => true 
 end.
Definition PeriodicalReportConfig__ext0__Format : T_Format PeriodicalReportConfig__ext0__Type PeriodicalReportConfig__ext0__cond :=
  restrict_add_format PeriodicalReportConfig__ext0__check_all_none PeriodicalReportConfig__ext0O__Format.

Opaque PeriodicalReportConfig__ext0__cond PeriodicalReportConfig__ext0__Format.

Opaque PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__cond PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__Format.

Definition PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Format : T_Format PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__nat__Format PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F1 PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F2 PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F1F2 PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__F2F1.

Opaque PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__cond PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Format.


Definition PeriodicalReportConfig__ext1O__Format_Type := Eval cbn in seq_format_prod PeriodicalReportConfig__ext1O__list.
Definition PeriodicalReportConfig__ext1O__Format_list : PeriodicalReportConfig__ext1O__Format_Type :=
  (PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17__Format, (PeriodicalReportConfig__ext1O__coarseLocationRequest_r17__Format, (SL_MeasReportQuantity_r16__Format, unit_format))).
Definition PeriodicalReportConfig__ext1O__list__Format := (*Eval compute in *) seq_format PeriodicalReportConfig__ext1O__list PeriodicalReportConfig__ext1O__Format_list.
Definition PeriodicalReportConfig__ext1O__F1 z :=
  (PeriodicalReportConfig__ext1O__ul_ExcessDelayConfig_r17 z, (PeriodicalReportConfig__ext1O__coarseLocationRequest_r17 z, (PeriodicalReportConfig__ext1O__reportQuantityRelay_r17 z, tt))).
Definition PeriodicalReportConfig__ext1O__F2 (y : seq_type PeriodicalReportConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__PeriodicalReportConfig__ext1O__Type i0 i1 i2
  end.
Lemma PeriodicalReportConfig__ext1O__F1F2_cond (z : PeriodicalReportConfig__ext1O__Type)
  : PeriodicalReportConfig__ext1O__cond z ->
  (seq_cond PeriodicalReportConfig__ext1O__list (PeriodicalReportConfig__ext1O__F1 z)).
intro H. unfold PeriodicalReportConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma PeriodicalReportConfig__ext1O__F1F2_cond2 (z : PeriodicalReportConfig__ext1O__Type)
 : PeriodicalReportConfig__ext1O__F2 (PeriodicalReportConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PeriodicalReportConfig__ext1O__F2F1_cond (y : seq_type PeriodicalReportConfig__ext1O__list)
  : seq_cond PeriodicalReportConfig__ext1O__list y ->
 (PeriodicalReportConfig__ext1O__cond (PeriodicalReportConfig__ext1O__F2 y)) /\  PeriodicalReportConfig__ext1O__F1 (PeriodicalReportConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PeriodicalReportConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold PeriodicalReportConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PeriodicalReportConfig__ext1O__Format : T_Format PeriodicalReportConfig__ext1O__Type PeriodicalReportConfig__ext1O__cond :=
        proj2_format  PeriodicalReportConfig__ext1O__cond PeriodicalReportConfig__ext1O__list__Format
    PeriodicalReportConfig__ext1O__F1 PeriodicalReportConfig__ext1O__F2 PeriodicalReportConfig__ext1O__F1F2_cond  PeriodicalReportConfig__ext1O__F1F2_cond2 PeriodicalReportConfig__ext1O__F2F1_cond.
Opaque PeriodicalReportConfig__ext1O__cond PeriodicalReportConfig__ext1O__Format.

Definition PeriodicalReportConfig__ext1__check_all_none (b : PeriodicalReportConfig__ext1O__Type) : bool :=
match b with 
  | make__PeriodicalReportConfig__ext1O__Type None None None  => false 
  | _ => true 
 end.
Definition PeriodicalReportConfig__ext1__Format : T_Format PeriodicalReportConfig__ext1__Type PeriodicalReportConfig__ext1__cond :=
  restrict_add_format PeriodicalReportConfig__ext1__check_all_none PeriodicalReportConfig__ext1O__Format.

Opaque PeriodicalReportConfig__ext1__cond PeriodicalReportConfig__ext1__Format.


Definition PeriodicalReportConfig__root_Format_Type := Eval cbn in seq_format_prod PeriodicalReportConfig__root_list.
Definition PeriodicalReportConfig__root_Format_list : PeriodicalReportConfig__root_Format_Type :=
  (NR_RS_Type__Format, (ReportInterval__Format, (PeriodicalReportConfig__reportAmount__Format, (MeasReportQuantity__Format, (PeriodicalReportConfig__maxReportCells__Format, (MeasReportQuantity__Format, (PeriodicalReportConfig__maxNrofRS_IndexesToReport__Format, (bool__Format, (bool__Format, unit_format))))))))).

Definition PeriodicalReportConfig__ext_Format_Type := Eval cbn in get_formats PeriodicalReportConfig__ext_list.
Definition PeriodicalReportConfig__ext_Format_list : PeriodicalReportConfig__ext_Format_Type :=
  (PeriodicalReportConfig__ext0__Format, (PeriodicalReportConfig__ext1__Format, unit__Format)).

Definition PeriodicalReportConfig__list_type : Set := (seq_type PeriodicalReportConfig__root_list) * (seq_ext_type PeriodicalReportConfig__ext_list).
Definition PeriodicalReportConfig__list_cond (z : PeriodicalReportConfig__list_type) : Prop :=
        (seq_cond PeriodicalReportConfig__root_list (fst z)) /\ (seq_ext_cond PeriodicalReportConfig__ext_list (snd z)).
Definition PeriodicalReportConfig__list_format : T_Format PeriodicalReportConfig__list_type PeriodicalReportConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PeriodicalReportConfig__root_list PeriodicalReportConfig__root_Format_list PeriodicalReportConfig__ext_list PeriodicalReportConfig__ext_Format_list.

Opaque PeriodicalReportConfig__list_format.
Definition PeriodicalReportConfig__F1 (z : PeriodicalReportConfig__Type) : PeriodicalReportConfig__list_type :=
  (((PeriodicalReportConfig__rsType z, (PeriodicalReportConfig__reportInterval z, (PeriodicalReportConfig__reportAmount z, (PeriodicalReportConfig__reportQuantityCell z, (PeriodicalReportConfig__maxReportCells z, (PeriodicalReportConfig__reportQuantityRS_Indexes z, (PeriodicalReportConfig__maxNrofRS_IndexesToReport z, (PeriodicalReportConfig__includeBeamMeasurements z, (PeriodicalReportConfig__useAllowedCellList z, tt)))))))))), (
(PeriodicalReportConfig__ext0 z, (PeriodicalReportConfig__ext1 z, tt)))).
Definition PeriodicalReportConfig__F2 (y : PeriodicalReportConfig__list_type) : PeriodicalReportConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), (i0, (i1, _)))=>
    make__PeriodicalReportConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 i0 i1
  end.
Definition PeriodicalReportConfig__helper1 : (forall a : PeriodicalReportConfig__Type, PeriodicalReportConfig__cond a -> PeriodicalReportConfig__list_cond (PeriodicalReportConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PeriodicalReportConfig__helper2 : (forall a : PeriodicalReportConfig__Type, PeriodicalReportConfig__F2 (PeriodicalReportConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PeriodicalReportConfig__helper3 : (forall b : PeriodicalReportConfig__list_type, PeriodicalReportConfig__list_cond b -> PeriodicalReportConfig__cond (PeriodicalReportConfig__F2 b) /\ PeriodicalReportConfig__F1 (PeriodicalReportConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PeriodicalReportConfig__cond, PeriodicalReportConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PeriodicalReportConfig__Format : T_Format PeriodicalReportConfig__Type PeriodicalReportConfig__cond :=
 proj2_format PeriodicalReportConfig__cond PeriodicalReportConfig__list_format  PeriodicalReportConfig__F1 PeriodicalReportConfig__F2 PeriodicalReportConfig__helper1 PeriodicalReportConfig__helper2 PeriodicalReportConfig__helper3.

Opaque PeriodicalReportConfig__cond PeriodicalReportConfig__Format.

