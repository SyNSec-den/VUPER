Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Require Import NR.SSB_MTC2.

Opaque SSB_MTC2__cond SSB_MTC2__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.ReferenceSignalConfig.

Opaque ReferenceSignalConfig__cond ReferenceSignalConfig__Format.

Require Import NR.ThresholdNR.

Opaque ThresholdNR__cond ThresholdNR__Format.

Require Import NR.ThresholdNR.

Opaque ThresholdNR__cond ThresholdNR__Format.

Lemma MeasObjectNR__nrofSS_BlocksToAverage__helper1 : (2 <= maxNrofSS_BlocksToAverage)%Z. unfold maxNrofSS_BlocksToAverage.
 lia. Qed.
Lemma MeasObjectNR__nrofSS_BlocksToAverage__helper2 : to_bit_sz (Z.to_nat (maxNrofSS_BlocksToAverage - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSS_BlocksToAverage - 2))%Z). { apply Zorder.Zle_minus_le_0. apply MeasObjectNR__nrofSS_BlocksToAverage__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasObjectNR__nrofSS_BlocksToAverage__Type := Z.
Definition MeasObjectNR__nrofSS_BlocksToAverage__cond := (fun z => (2 <= z <= maxNrofSS_BlocksToAverage)%Z).
Lemma MeasObjectNR__nrofCSI_RS_ResourcesToAverage__helper1 : (2 <= maxNrofCSI_RS_ResourcesToAverage)%Z. unfold maxNrofCSI_RS_ResourcesToAverage.
 lia. Qed.
Lemma MeasObjectNR__nrofCSI_RS_ResourcesToAverage__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_ResourcesToAverage - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_ResourcesToAverage - 2))%Z). { apply Zorder.Zle_minus_le_0. apply MeasObjectNR__nrofCSI_RS_ResourcesToAverage__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasObjectNR__nrofCSI_RS_ResourcesToAverage__Type := Z.
Definition MeasObjectNR__nrofCSI_RS_ResourcesToAverage__cond := (fun z => (2 <= z <= maxNrofCSI_RS_ResourcesToAverage)%Z).
Lemma MeasObjectNR__quantityConfigIndex__helper1 : (1 <= maxNrofQuantityConfig)%Z. unfold maxNrofQuantityConfig.
 lia. Qed.
Lemma MeasObjectNR__quantityConfigIndex__helper2 : to_bit_sz (Z.to_nat (maxNrofQuantityConfig - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofQuantityConfig - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasObjectNR__quantityConfigIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasObjectNR__quantityConfigIndex__Type := Z.
Definition MeasObjectNR__quantityConfigIndex__cond := (fun z => (1 <= z <= maxNrofQuantityConfig)%Z).
Require Import NR.Q_OffsetRangeList.

Opaque Q_OffsetRangeList__cond Q_OffsetRangeList__Format.

Require Import NR.PCI_List.

Opaque PCI_List__cond PCI_List__Format.

Require Import NR.CellsToAddModList.

Opaque CellsToAddModList__cond CellsToAddModList__Format.

Require Import NR.PCI_RangeIndexList.

Opaque PCI_RangeIndexList__cond PCI_RangeIndexList__Format.

Require Import NR.PCI_RangeElement.

Opaque PCI_RangeElement__cond PCI_RangeElement__Format.

Definition MeasObjectNR__excludedCellsToAddModList__Type := list PCI_RangeElement__Type.

Lemma MeasObjectNR__excludedCellsToAddModList__helper1 : (0 <= 1 <= maxNrofPCI_Ranges)%Z. unfold maxNrofPCI_Ranges.
 lia. Qed.
Lemma MeasObjectNR__excludedCellsToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofPCI_Ranges - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPCI_Ranges - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasObjectNR__excludedCellsToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasObjectNR__excludedCellsToAddModList__cond (z : MeasObjectNR__excludedCellsToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPCI_Ranges)%Z /\ (list_and PCI_RangeElement__cond z) .

Require Import NR.PCI_RangeIndexList.

Opaque PCI_RangeIndexList__cond PCI_RangeIndexList__Format.

Require Import NR.PCI_RangeElement.

Opaque PCI_RangeElement__cond PCI_RangeElement__Format.

Definition MeasObjectNR__allowedCellsToAddModList__Type := list PCI_RangeElement__Type.

Lemma MeasObjectNR__allowedCellsToAddModList__helper1 : (0 <= 1 <= maxNrofPCI_Ranges)%Z. unfold maxNrofPCI_Ranges.
 lia. Qed.
Lemma MeasObjectNR__allowedCellsToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofPCI_Ranges - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPCI_Ranges - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MeasObjectNR__allowedCellsToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MeasObjectNR__allowedCellsToAddModList__cond (z : MeasObjectNR__allowedCellsToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPCI_Ranges)%Z /\ (list_and PCI_RangeElement__cond z) .

Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Inductive MeasObjectNR__ext0O__measCycleSCell__Type : Set :=
 | MeasObjectNR__ext0O__measCycleSCell__sf160
 | MeasObjectNR__ext0O__measCycleSCell__sf256
 | MeasObjectNR__ext0O__measCycleSCell__sf320
 | MeasObjectNR__ext0O__measCycleSCell__sf512
 | MeasObjectNR__ext0O__measCycleSCell__sf640
 | MeasObjectNR__ext0O__measCycleSCell__sf1024
 | MeasObjectNR__ext0O__measCycleSCell__sf1280
.
Definition MeasObjectNR__ext0O__measCycleSCell__cond := (fun (_ : MeasObjectNR__ext0O__measCycleSCell__Type) => True).
Lemma MeasObjectNR__ext0O__measCycleSCell__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasObjectNR__ext0O__measCycleSCell__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 MeasObjectNR__ext0O__measCycleSCell__nat__helper.

Definition MeasObjectNR__ext0O__measCycleSCell__F1 t :=
  match t with
  | MeasObjectNR__ext0O__measCycleSCell__sf160 => 0
  | MeasObjectNR__ext0O__measCycleSCell__sf256 => 1
  | MeasObjectNR__ext0O__measCycleSCell__sf320 => 2
  | MeasObjectNR__ext0O__measCycleSCell__sf512 => 3
  | MeasObjectNR__ext0O__measCycleSCell__sf640 => 4
  | MeasObjectNR__ext0O__measCycleSCell__sf1024 => 5
  | MeasObjectNR__ext0O__measCycleSCell__sf1280 => 6
  end.
Definition MeasObjectNR__ext0O__measCycleSCell__F2 n :=
  match n with
  | 0 => MeasObjectNR__ext0O__measCycleSCell__sf160
  | 1 => MeasObjectNR__ext0O__measCycleSCell__sf256
  | 2 => MeasObjectNR__ext0O__measCycleSCell__sf320
  | 3 => MeasObjectNR__ext0O__measCycleSCell__sf512
  | 4 => MeasObjectNR__ext0O__measCycleSCell__sf640
  | 5 => MeasObjectNR__ext0O__measCycleSCell__sf1024
  | 6 => MeasObjectNR__ext0O__measCycleSCell__sf1280
  | _ => MeasObjectNR__ext0O__measCycleSCell__sf160
  end.
Lemma MeasObjectNR__ext0O__measCycleSCell__F1F2 : forall x : MeasObjectNR__ext0O__measCycleSCell__Type, (MeasObjectNR__ext0O__measCycleSCell__F1 x <= 6) /\ MeasObjectNR__ext0O__measCycleSCell__F2 (MeasObjectNR__ext0O__measCycleSCell__F1 x) = x. imp_solve. Qed.
Lemma MeasObjectNR__ext0O__measCycleSCell__F2F1 : forall (y : nat) (H : y <= 6), MeasObjectNR__ext0O__measCycleSCell__F1 (MeasObjectNR__ext0O__measCycleSCell__F2 y) = y. enum_solve H y. Qed.

Record MeasObjectNR__ext0O__Type : Set :=
  make__MeasObjectNR__ext0O__Type {
    MeasObjectNR__ext0O__freqBandIndicatorNR : option FreqBandIndicatorNR__Type ;
    MeasObjectNR__ext0O__measCycleSCell : option MeasObjectNR__ext0O__measCycleSCell__Type ;
}.
Definition MeasObjectNR__ext0O__list := (
 Opt FreqBandIndicatorNR__Type FreqBandIndicatorNR__cond ::
 Opt MeasObjectNR__ext0O__measCycleSCell__Type MeasObjectNR__ext0O__measCycleSCell__cond ::
 nil).
Definition MeasObjectNR__ext0O__cond z := 
  opt_cond FreqBandIndicatorNR__cond (MeasObjectNR__ext0O__freqBandIndicatorNR z) /\
  opt_cond MeasObjectNR__ext0O__measCycleSCell__cond (MeasObjectNR__ext0O__measCycleSCell z) /\
  True.

Definition MeasObjectNR__ext0__Type := MeasObjectNR__ext0O__Type.
Definition MeasObjectNR__ext0__cond := MeasObjectNR__ext0O__cond.

Require Import NR.SSB_MTC3List_r16.

Opaque SSB_MTC3List_r16__cond SSB_MTC3List_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.RMTC_Config_r16.
Definition MeasObjectNR__ext1O__rmtc_Config_r16__Type := SetupRelease__Type RMTC_Config_r16__Type.
Definition MeasObjectNR__ext1O__rmtc_Config_r16__cond := SetupRelease__cond _ RMTC_Config_r16__cond.
Definition MeasObjectNR__ext1O__rmtc_Config_r16__Format : T_Format MeasObjectNR__ext1O__rmtc_Config_r16__Type MeasObjectNR__ext1O__rmtc_Config_r16__cond := SetupRelease__Format _ _ RMTC_Config_r16__Format.
Opaque MeasObjectNR__ext1O__rmtc_Config_r16__cond MeasObjectNR__ext1O__rmtc_Config_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.T312_r16.
Definition MeasObjectNR__ext1O__t312_r16__Type := SetupRelease__Type T312_r16__Type.
Definition MeasObjectNR__ext1O__t312_r16__cond := SetupRelease__cond _ T312_r16__cond.
Definition MeasObjectNR__ext1O__t312_r16__Format : T_Format MeasObjectNR__ext1O__t312_r16__Type MeasObjectNR__ext1O__t312_r16__cond := SetupRelease__Format _ _ T312_r16__Format.
Opaque MeasObjectNR__ext1O__t312_r16__cond MeasObjectNR__ext1O__t312_r16__Format.

Record MeasObjectNR__ext1O__Type : Set :=
  make__MeasObjectNR__ext1O__Type {
    MeasObjectNR__ext1O__smtc3list_r16 : option SSB_MTC3List_r16__Type ;
    MeasObjectNR__ext1O__rmtc_Config_r16 : option MeasObjectNR__ext1O__rmtc_Config_r16__Type ;
    MeasObjectNR__ext1O__t312_r16 : option MeasObjectNR__ext1O__t312_r16__Type ;
}.
Definition MeasObjectNR__ext1O__list := (
 Opt SSB_MTC3List_r16__Type SSB_MTC3List_r16__cond ::
 Opt MeasObjectNR__ext1O__rmtc_Config_r16__Type MeasObjectNR__ext1O__rmtc_Config_r16__cond ::
 Opt MeasObjectNR__ext1O__t312_r16__Type MeasObjectNR__ext1O__t312_r16__cond ::
 nil).
Definition MeasObjectNR__ext1O__cond z := 
  opt_cond SSB_MTC3List_r16__cond (MeasObjectNR__ext1O__smtc3list_r16 z) /\
  opt_cond MeasObjectNR__ext1O__rmtc_Config_r16__cond (MeasObjectNR__ext1O__rmtc_Config_r16 z) /\
  opt_cond MeasObjectNR__ext1O__t312_r16__cond (MeasObjectNR__ext1O__t312_r16 z) /\
  True.

Definition MeasObjectNR__ext1__Type := MeasObjectNR__ext1O__Type.
Definition MeasObjectNR__ext1__cond := MeasObjectNR__ext1O__cond.

Require Import NR.MeasGapId_r17.

Opaque MeasGapId_r17__cond MeasGapId_r17__Format.

Require Import NR.MeasGapId_r17.

Opaque MeasGapId_r17__cond MeasGapId_r17__Format.

Require Import NR.SSB_MTC4List_r17.

Opaque SSB_MTC4List_r17__cond SSB_MTC4List_r17__Format.

Inductive MeasObjectNR__ext2O__measCyclePSCell_r17__Type : Set :=
 | MeasObjectNR__ext2O__measCyclePSCell_r17__ms160
 | MeasObjectNR__ext2O__measCyclePSCell_r17__ms256
 | MeasObjectNR__ext2O__measCyclePSCell_r17__ms320
 | MeasObjectNR__ext2O__measCyclePSCell_r17__ms512
 | MeasObjectNR__ext2O__measCyclePSCell_r17__ms640
 | MeasObjectNR__ext2O__measCyclePSCell_r17__ms1024
 | MeasObjectNR__ext2O__measCyclePSCell_r17__ms1280
 | MeasObjectNR__ext2O__measCyclePSCell_r17__spare1
.
Definition MeasObjectNR__ext2O__measCyclePSCell_r17__cond := (fun (_ : MeasObjectNR__ext2O__measCyclePSCell_r17__Type) => True).
Lemma MeasObjectNR__ext2O__measCyclePSCell_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasObjectNR__ext2O__measCyclePSCell_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MeasObjectNR__ext2O__measCyclePSCell_r17__nat__helper.

Definition MeasObjectNR__ext2O__measCyclePSCell_r17__F1 t :=
  match t with
  | MeasObjectNR__ext2O__measCyclePSCell_r17__ms160 => 0
  | MeasObjectNR__ext2O__measCyclePSCell_r17__ms256 => 1
  | MeasObjectNR__ext2O__measCyclePSCell_r17__ms320 => 2
  | MeasObjectNR__ext2O__measCyclePSCell_r17__ms512 => 3
  | MeasObjectNR__ext2O__measCyclePSCell_r17__ms640 => 4
  | MeasObjectNR__ext2O__measCyclePSCell_r17__ms1024 => 5
  | MeasObjectNR__ext2O__measCyclePSCell_r17__ms1280 => 6
  | MeasObjectNR__ext2O__measCyclePSCell_r17__spare1 => 7
  end.
Definition MeasObjectNR__ext2O__measCyclePSCell_r17__F2 n :=
  match n with
  | 0 => MeasObjectNR__ext2O__measCyclePSCell_r17__ms160
  | 1 => MeasObjectNR__ext2O__measCyclePSCell_r17__ms256
  | 2 => MeasObjectNR__ext2O__measCyclePSCell_r17__ms320
  | 3 => MeasObjectNR__ext2O__measCyclePSCell_r17__ms512
  | 4 => MeasObjectNR__ext2O__measCyclePSCell_r17__ms640
  | 5 => MeasObjectNR__ext2O__measCyclePSCell_r17__ms1024
  | 6 => MeasObjectNR__ext2O__measCyclePSCell_r17__ms1280
  | 7 => MeasObjectNR__ext2O__measCyclePSCell_r17__spare1
  | _ => MeasObjectNR__ext2O__measCyclePSCell_r17__ms160
  end.
Lemma MeasObjectNR__ext2O__measCyclePSCell_r17__F1F2 : forall x : MeasObjectNR__ext2O__measCyclePSCell_r17__Type, (MeasObjectNR__ext2O__measCyclePSCell_r17__F1 x <= 7) /\ MeasObjectNR__ext2O__measCyclePSCell_r17__F2 (MeasObjectNR__ext2O__measCyclePSCell_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasObjectNR__ext2O__measCyclePSCell_r17__F2F1 : forall (y : nat) (H : y <= 7), MeasObjectNR__ext2O__measCyclePSCell_r17__F1 (MeasObjectNR__ext2O__measCyclePSCell_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CellsToAddModListExt_v1710.

Opaque CellsToAddModListExt_v1710__cond CellsToAddModListExt_v1710__Format.

Record MeasObjectNR__ext2O__Type : Set :=
  make__MeasObjectNR__ext2O__Type {
    MeasObjectNR__ext2O__associatedMeasGapSSB_r17 : option MeasGapId_r17__Type ;
    MeasObjectNR__ext2O__associatedMeasGapCSIRS_r17 : option MeasGapId_r17__Type ;
    MeasObjectNR__ext2O__smtc4list_r17 : option SSB_MTC4List_r17__Type ;
    MeasObjectNR__ext2O__measCyclePSCell_r17 : option MeasObjectNR__ext2O__measCyclePSCell_r17__Type ;
    MeasObjectNR__ext2O__cellsToAddModListExt_v1710 : option CellsToAddModListExt_v1710__Type ;
}.
Definition MeasObjectNR__ext2O__list := (
 Opt MeasGapId_r17__Type MeasGapId_r17__cond ::
 Opt MeasGapId_r17__Type MeasGapId_r17__cond ::
 Opt SSB_MTC4List_r17__Type SSB_MTC4List_r17__cond ::
 Opt MeasObjectNR__ext2O__measCyclePSCell_r17__Type MeasObjectNR__ext2O__measCyclePSCell_r17__cond ::
 Opt CellsToAddModListExt_v1710__Type CellsToAddModListExt_v1710__cond ::
 nil).
Definition MeasObjectNR__ext2O__cond z := 
  opt_cond MeasGapId_r17__cond (MeasObjectNR__ext2O__associatedMeasGapSSB_r17 z) /\
  opt_cond MeasGapId_r17__cond (MeasObjectNR__ext2O__associatedMeasGapCSIRS_r17 z) /\
  opt_cond SSB_MTC4List_r17__cond (MeasObjectNR__ext2O__smtc4list_r17 z) /\
  opt_cond MeasObjectNR__ext2O__measCyclePSCell_r17__cond (MeasObjectNR__ext2O__measCyclePSCell_r17 z) /\
  opt_cond CellsToAddModListExt_v1710__cond (MeasObjectNR__ext2O__cellsToAddModListExt_v1710 z) /\
  True.

Definition MeasObjectNR__ext2__Type := MeasObjectNR__ext2O__Type.
Definition MeasObjectNR__ext2__cond := MeasObjectNR__ext2O__cond.

Require Import NR.MeasGapId_r17.

Opaque MeasGapId_r17__cond MeasGapId_r17__Format.

Require Import NR.MeasGapId_r17.

Opaque MeasGapId_r17__cond MeasGapId_r17__Format.

Record MeasObjectNR__ext3O__Type : Set :=
  make__MeasObjectNR__ext3O__Type {
    MeasObjectNR__ext3O__associatedMeasGapSSB2_v1720 : option MeasGapId_r17__Type ;
    MeasObjectNR__ext3O__associatedMeasGapCSIRS2_v1720 : option MeasGapId_r17__Type ;
}.
Definition MeasObjectNR__ext3O__list := (
 Opt MeasGapId_r17__Type MeasGapId_r17__cond ::
 Opt MeasGapId_r17__Type MeasGapId_r17__cond ::
 nil).
Definition MeasObjectNR__ext3O__cond z := 
  opt_cond MeasGapId_r17__cond (MeasObjectNR__ext3O__associatedMeasGapSSB2_v1720 z) /\
  opt_cond MeasGapId_r17__cond (MeasObjectNR__ext3O__associatedMeasGapCSIRS2_v1720 z) /\
  True.

Definition MeasObjectNR__ext3__Type := MeasObjectNR__ext3O__Type.
Definition MeasObjectNR__ext3__cond := MeasObjectNR__ext3O__cond.

Record MeasObjectNR__Type : Set :=
  make__MeasObjectNR__Type {
    MeasObjectNR__ssbFrequency : option ARFCN_ValueNR__Type ;
    MeasObjectNR__ssbSubcarrierSpacing : option SubcarrierSpacing__Type ;
    MeasObjectNR__smtc1 : option SSB_MTC__Type ;
    MeasObjectNR__smtc2 : option SSB_MTC2__Type ;
    MeasObjectNR__refFreqCSI_RS : option ARFCN_ValueNR__Type ;
    MeasObjectNR__referenceSignalConfig : ReferenceSignalConfig__Type ;
    MeasObjectNR__absThreshSS_BlocksConsolidation : option ThresholdNR__Type ;
    MeasObjectNR__absThreshCSI_RS_Consolidation : option ThresholdNR__Type ;
    MeasObjectNR__nrofSS_BlocksToAverage : option Z ;
    MeasObjectNR__nrofCSI_RS_ResourcesToAverage : option Z ;
    MeasObjectNR__quantityConfigIndex : Z ;
    MeasObjectNR__offsetMO : Q_OffsetRangeList__Type ;
    MeasObjectNR__cellsToRemoveList : option PCI_List__Type ;
    MeasObjectNR__cellsToAddModList : option CellsToAddModList__Type ;
    MeasObjectNR__excludedCellsToRemoveList : option PCI_RangeIndexList__Type ;
    MeasObjectNR__excludedCellsToAddModList : option MeasObjectNR__excludedCellsToAddModList__Type ;
    MeasObjectNR__allowedCellsToRemoveList : option PCI_RangeIndexList__Type ;
    MeasObjectNR__allowedCellsToAddModList : option MeasObjectNR__allowedCellsToAddModList__Type ;
    MeasObjectNR__ext0 : option MeasObjectNR__ext0__Type ;
    MeasObjectNR__ext1 : option MeasObjectNR__ext1__Type ;
    MeasObjectNR__ext2 : option MeasObjectNR__ext2__Type ;
    MeasObjectNR__ext3 : option MeasObjectNR__ext3__Type ;
}.
Definition MeasObjectNR__root_list : list seq_elem := (
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt SSB_MTC__Type SSB_MTC__cond ::
 Opt SSB_MTC2__Type SSB_MTC2__cond ::
 Opt ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor ReferenceSignalConfig__Type ReferenceSignalConfig__cond ::
 Opt ThresholdNR__Type ThresholdNR__cond ::
 Opt ThresholdNR__Type ThresholdNR__cond ::
 Opt Z MeasObjectNR__nrofSS_BlocksToAverage__cond ::
 Opt Z MeasObjectNR__nrofCSI_RS_ResourcesToAverage__cond ::
 Nor Z MeasObjectNR__quantityConfigIndex__cond ::
 Nor Q_OffsetRangeList__Type Q_OffsetRangeList__cond ::
 Opt PCI_List__Type PCI_List__cond ::
 Opt CellsToAddModList__Type CellsToAddModList__cond ::
 Opt PCI_RangeIndexList__Type PCI_RangeIndexList__cond ::
 Opt MeasObjectNR__excludedCellsToAddModList__Type MeasObjectNR__excludedCellsToAddModList__cond ::
 Opt PCI_RangeIndexList__Type PCI_RangeIndexList__cond ::
 Opt MeasObjectNR__allowedCellsToAddModList__Type MeasObjectNR__allowedCellsToAddModList__cond ::
 nil).
Definition MeasObjectNR__ext_list : list typ := (
  typ_cons MeasObjectNR__ext0__Type MeasObjectNR__ext0__cond ::
  typ_cons MeasObjectNR__ext1__Type MeasObjectNR__ext1__cond ::
  typ_cons MeasObjectNR__ext2__Type MeasObjectNR__ext2__cond ::
  typ_cons MeasObjectNR__ext3__Type MeasObjectNR__ext3__cond ::
  nil).
Definition MeasObjectNR__cond (z : MeasObjectNR__Type) := 
(  opt_cond ARFCN_ValueNR__cond (MeasObjectNR__ssbFrequency z) /\
  opt_cond SubcarrierSpacing__cond (MeasObjectNR__ssbSubcarrierSpacing z) /\
  opt_cond SSB_MTC__cond (MeasObjectNR__smtc1 z) /\
  opt_cond SSB_MTC2__cond (MeasObjectNR__smtc2 z) /\
  opt_cond ARFCN_ValueNR__cond (MeasObjectNR__refFreqCSI_RS z) /\
  ReferenceSignalConfig__cond (MeasObjectNR__referenceSignalConfig z) /\
  opt_cond ThresholdNR__cond (MeasObjectNR__absThreshSS_BlocksConsolidation z) /\
  opt_cond ThresholdNR__cond (MeasObjectNR__absThreshCSI_RS_Consolidation z) /\
  opt_cond MeasObjectNR__nrofSS_BlocksToAverage__cond (MeasObjectNR__nrofSS_BlocksToAverage z) /\
  opt_cond MeasObjectNR__nrofCSI_RS_ResourcesToAverage__cond (MeasObjectNR__nrofCSI_RS_ResourcesToAverage z) /\
  MeasObjectNR__quantityConfigIndex__cond (MeasObjectNR__quantityConfigIndex z) /\
  Q_OffsetRangeList__cond (MeasObjectNR__offsetMO z) /\
  opt_cond PCI_List__cond (MeasObjectNR__cellsToRemoveList z) /\
  opt_cond CellsToAddModList__cond (MeasObjectNR__cellsToAddModList z) /\
  opt_cond PCI_RangeIndexList__cond (MeasObjectNR__excludedCellsToRemoveList z) /\
  opt_cond MeasObjectNR__excludedCellsToAddModList__cond (MeasObjectNR__excludedCellsToAddModList z) /\
  opt_cond PCI_RangeIndexList__cond (MeasObjectNR__allowedCellsToRemoveList z) /\
  opt_cond MeasObjectNR__allowedCellsToAddModList__cond (MeasObjectNR__allowedCellsToAddModList z) /\
  True) /\ 
(  opt_cond MeasObjectNR__ext0__cond (MeasObjectNR__ext0 z) /\
  opt_cond MeasObjectNR__ext1__cond (MeasObjectNR__ext1 z) /\
  opt_cond MeasObjectNR__ext2__cond (MeasObjectNR__ext2 z) /\
  opt_cond MeasObjectNR__ext3__cond (MeasObjectNR__ext3 z) /\
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
Definition MeasObjectNR__nrofSS_BlocksToAverage__Format : T_Format Z MeasObjectNR__nrofSS_BlocksToAverage__cond :=
 ranged_int_format (2) (maxNrofSS_BlocksToAverage) MeasObjectNR__nrofSS_BlocksToAverage__helper1 MeasObjectNR__nrofSS_BlocksToAverage__helper2.

Opaque MeasObjectNR__nrofSS_BlocksToAverage__cond MeasObjectNR__nrofSS_BlocksToAverage__Format.

Definition MeasObjectNR__nrofCSI_RS_ResourcesToAverage__Format : T_Format Z MeasObjectNR__nrofCSI_RS_ResourcesToAverage__cond :=
 ranged_int_format (2) (maxNrofCSI_RS_ResourcesToAverage) MeasObjectNR__nrofCSI_RS_ResourcesToAverage__helper1 MeasObjectNR__nrofCSI_RS_ResourcesToAverage__helper2.

Opaque MeasObjectNR__nrofCSI_RS_ResourcesToAverage__cond MeasObjectNR__nrofCSI_RS_ResourcesToAverage__Format.

Definition MeasObjectNR__quantityConfigIndex__Format : T_Format Z MeasObjectNR__quantityConfigIndex__cond :=
 ranged_int_format (1) (maxNrofQuantityConfig) MeasObjectNR__quantityConfigIndex__helper1 MeasObjectNR__quantityConfigIndex__helper2.

Opaque MeasObjectNR__quantityConfigIndex__cond MeasObjectNR__quantityConfigIndex__Format.

Definition MeasObjectNR__excludedCellsToAddModList__Format : T_Format MeasObjectNR__excludedCellsToAddModList__Type MeasObjectNR__excludedCellsToAddModList__cond := seq_of_format PCI_RangeElement__Format 1 maxNrofPCI_Ranges MeasObjectNR__excludedCellsToAddModList__helper1 MeasObjectNR__excludedCellsToAddModList__helper2.

Opaque MeasObjectNR__excludedCellsToAddModList__cond MeasObjectNR__excludedCellsToAddModList__Format.

Definition MeasObjectNR__allowedCellsToAddModList__Format : T_Format MeasObjectNR__allowedCellsToAddModList__Type MeasObjectNR__allowedCellsToAddModList__cond := seq_of_format PCI_RangeElement__Format 1 maxNrofPCI_Ranges MeasObjectNR__allowedCellsToAddModList__helper1 MeasObjectNR__allowedCellsToAddModList__helper2.

Opaque MeasObjectNR__allowedCellsToAddModList__cond MeasObjectNR__allowedCellsToAddModList__Format.

Definition MeasObjectNR__ext0O__measCycleSCell__Format : T_Format MeasObjectNR__ext0O__measCycleSCell__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasObjectNR__ext0O__measCycleSCell__nat__Format MeasObjectNR__ext0O__measCycleSCell__F1 MeasObjectNR__ext0O__measCycleSCell__F2 MeasObjectNR__ext0O__measCycleSCell__F1F2 MeasObjectNR__ext0O__measCycleSCell__F2F1.

Opaque MeasObjectNR__ext0O__measCycleSCell__cond MeasObjectNR__ext0O__measCycleSCell__Format.


Definition MeasObjectNR__ext0O__Format_Type := Eval cbn in seq_format_prod MeasObjectNR__ext0O__list.
Definition MeasObjectNR__ext0O__Format_list : MeasObjectNR__ext0O__Format_Type :=
  (FreqBandIndicatorNR__Format, (MeasObjectNR__ext0O__measCycleSCell__Format, unit_format)).
Definition MeasObjectNR__ext0O__list__Format := (*Eval compute in *) seq_format MeasObjectNR__ext0O__list MeasObjectNR__ext0O__Format_list.
Definition MeasObjectNR__ext0O__F1 z :=
  (MeasObjectNR__ext0O__freqBandIndicatorNR z, (MeasObjectNR__ext0O__measCycleSCell z, tt)).
Definition MeasObjectNR__ext0O__F2 (y : seq_type MeasObjectNR__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasObjectNR__ext0O__Type i0 i1
  end.
Lemma MeasObjectNR__ext0O__F1F2_cond (z : MeasObjectNR__ext0O__Type)
  : MeasObjectNR__ext0O__cond z ->
  (seq_cond MeasObjectNR__ext0O__list (MeasObjectNR__ext0O__F1 z)).
intro H. unfold MeasObjectNR__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasObjectNR__ext0O__F1F2_cond2 (z : MeasObjectNR__ext0O__Type)
 : MeasObjectNR__ext0O__F2 (MeasObjectNR__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasObjectNR__ext0O__F2F1_cond (y : seq_type MeasObjectNR__ext0O__list)
  : seq_cond MeasObjectNR__ext0O__list y ->
 (MeasObjectNR__ext0O__cond (MeasObjectNR__ext0O__F2 y)) /\  MeasObjectNR__ext0O__F1 (MeasObjectNR__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasObjectNR__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasObjectNR__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasObjectNR__ext0O__Format : T_Format MeasObjectNR__ext0O__Type MeasObjectNR__ext0O__cond :=
        proj2_format  MeasObjectNR__ext0O__cond MeasObjectNR__ext0O__list__Format
    MeasObjectNR__ext0O__F1 MeasObjectNR__ext0O__F2 MeasObjectNR__ext0O__F1F2_cond  MeasObjectNR__ext0O__F1F2_cond2 MeasObjectNR__ext0O__F2F1_cond.
Opaque MeasObjectNR__ext0O__cond MeasObjectNR__ext0O__Format.

Definition MeasObjectNR__ext0__check_all_none (b : MeasObjectNR__ext0O__Type) : bool :=
match b with 
  | make__MeasObjectNR__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition MeasObjectNR__ext0__Format : T_Format MeasObjectNR__ext0__Type MeasObjectNR__ext0__cond :=
  restrict_add_format MeasObjectNR__ext0__check_all_none MeasObjectNR__ext0O__Format.

Opaque MeasObjectNR__ext0__cond MeasObjectNR__ext0__Format.

Opaque MeasObjectNR__ext1O__rmtc_Config_r16__cond MeasObjectNR__ext1O__rmtc_Config_r16__Format.

Opaque MeasObjectNR__ext1O__t312_r16__cond MeasObjectNR__ext1O__t312_r16__Format.


Definition MeasObjectNR__ext1O__Format_Type := Eval cbn in seq_format_prod MeasObjectNR__ext1O__list.
Definition MeasObjectNR__ext1O__Format_list : MeasObjectNR__ext1O__Format_Type :=
  (SSB_MTC3List_r16__Format, (MeasObjectNR__ext1O__rmtc_Config_r16__Format, (MeasObjectNR__ext1O__t312_r16__Format, unit_format))).
Definition MeasObjectNR__ext1O__list__Format := (*Eval compute in *) seq_format MeasObjectNR__ext1O__list MeasObjectNR__ext1O__Format_list.
Definition MeasObjectNR__ext1O__F1 z :=
  (MeasObjectNR__ext1O__smtc3list_r16 z, (MeasObjectNR__ext1O__rmtc_Config_r16 z, (MeasObjectNR__ext1O__t312_r16 z, tt))).
Definition MeasObjectNR__ext1O__F2 (y : seq_type MeasObjectNR__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasObjectNR__ext1O__Type i0 i1 i2
  end.
Lemma MeasObjectNR__ext1O__F1F2_cond (z : MeasObjectNR__ext1O__Type)
  : MeasObjectNR__ext1O__cond z ->
  (seq_cond MeasObjectNR__ext1O__list (MeasObjectNR__ext1O__F1 z)).
intro H. unfold MeasObjectNR__ext1O__cond in H. simpl. auto. Qed.
Lemma MeasObjectNR__ext1O__F1F2_cond2 (z : MeasObjectNR__ext1O__Type)
 : MeasObjectNR__ext1O__F2 (MeasObjectNR__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasObjectNR__ext1O__F2F1_cond (y : seq_type MeasObjectNR__ext1O__list)
  : seq_cond MeasObjectNR__ext1O__list y ->
 (MeasObjectNR__ext1O__cond (MeasObjectNR__ext1O__F2 y)) /\  MeasObjectNR__ext1O__F1 (MeasObjectNR__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasObjectNR__ext1O__cond. simpl in *. auto.
 - simpl. unfold MeasObjectNR__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasObjectNR__ext1O__Format : T_Format MeasObjectNR__ext1O__Type MeasObjectNR__ext1O__cond :=
        proj2_format  MeasObjectNR__ext1O__cond MeasObjectNR__ext1O__list__Format
    MeasObjectNR__ext1O__F1 MeasObjectNR__ext1O__F2 MeasObjectNR__ext1O__F1F2_cond  MeasObjectNR__ext1O__F1F2_cond2 MeasObjectNR__ext1O__F2F1_cond.
Opaque MeasObjectNR__ext1O__cond MeasObjectNR__ext1O__Format.

Definition MeasObjectNR__ext1__check_all_none (b : MeasObjectNR__ext1O__Type) : bool :=
match b with 
  | make__MeasObjectNR__ext1O__Type None None None  => false 
  | _ => true 
 end.
Definition MeasObjectNR__ext1__Format : T_Format MeasObjectNR__ext1__Type MeasObjectNR__ext1__cond :=
  restrict_add_format MeasObjectNR__ext1__check_all_none MeasObjectNR__ext1O__Format.

Opaque MeasObjectNR__ext1__cond MeasObjectNR__ext1__Format.

Definition MeasObjectNR__ext2O__measCyclePSCell_r17__Format : T_Format MeasObjectNR__ext2O__measCyclePSCell_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasObjectNR__ext2O__measCyclePSCell_r17__nat__Format MeasObjectNR__ext2O__measCyclePSCell_r17__F1 MeasObjectNR__ext2O__measCyclePSCell_r17__F2 MeasObjectNR__ext2O__measCyclePSCell_r17__F1F2 MeasObjectNR__ext2O__measCyclePSCell_r17__F2F1.

Opaque MeasObjectNR__ext2O__measCyclePSCell_r17__cond MeasObjectNR__ext2O__measCyclePSCell_r17__Format.


Definition MeasObjectNR__ext2O__Format_Type := Eval cbn in seq_format_prod MeasObjectNR__ext2O__list.
Definition MeasObjectNR__ext2O__Format_list : MeasObjectNR__ext2O__Format_Type :=
  (MeasGapId_r17__Format, (MeasGapId_r17__Format, (SSB_MTC4List_r17__Format, (MeasObjectNR__ext2O__measCyclePSCell_r17__Format, (CellsToAddModListExt_v1710__Format, unit_format))))).
Definition MeasObjectNR__ext2O__list__Format := (*Eval compute in *) seq_format MeasObjectNR__ext2O__list MeasObjectNR__ext2O__Format_list.
Definition MeasObjectNR__ext2O__F1 z :=
  (MeasObjectNR__ext2O__associatedMeasGapSSB_r17 z, (MeasObjectNR__ext2O__associatedMeasGapCSIRS_r17 z, (MeasObjectNR__ext2O__smtc4list_r17 z, (MeasObjectNR__ext2O__measCyclePSCell_r17 z, (MeasObjectNR__ext2O__cellsToAddModListExt_v1710 z, tt))))).
Definition MeasObjectNR__ext2O__F2 (y : seq_type MeasObjectNR__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__MeasObjectNR__ext2O__Type i0 i1 i2 i3 i4
  end.
Lemma MeasObjectNR__ext2O__F1F2_cond (z : MeasObjectNR__ext2O__Type)
  : MeasObjectNR__ext2O__cond z ->
  (seq_cond MeasObjectNR__ext2O__list (MeasObjectNR__ext2O__F1 z)).
intro H. unfold MeasObjectNR__ext2O__cond in H. simpl. auto. Qed.
Lemma MeasObjectNR__ext2O__F1F2_cond2 (z : MeasObjectNR__ext2O__Type)
 : MeasObjectNR__ext2O__F2 (MeasObjectNR__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasObjectNR__ext2O__F2F1_cond (y : seq_type MeasObjectNR__ext2O__list)
  : seq_cond MeasObjectNR__ext2O__list y ->
 (MeasObjectNR__ext2O__cond (MeasObjectNR__ext2O__F2 y)) /\  MeasObjectNR__ext2O__F1 (MeasObjectNR__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasObjectNR__ext2O__cond. simpl in *. auto.
 - simpl. unfold MeasObjectNR__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasObjectNR__ext2O__Format : T_Format MeasObjectNR__ext2O__Type MeasObjectNR__ext2O__cond :=
        proj2_format  MeasObjectNR__ext2O__cond MeasObjectNR__ext2O__list__Format
    MeasObjectNR__ext2O__F1 MeasObjectNR__ext2O__F2 MeasObjectNR__ext2O__F1F2_cond  MeasObjectNR__ext2O__F1F2_cond2 MeasObjectNR__ext2O__F2F1_cond.
Opaque MeasObjectNR__ext2O__cond MeasObjectNR__ext2O__Format.

Definition MeasObjectNR__ext2__check_all_none (b : MeasObjectNR__ext2O__Type) : bool :=
match b with 
  | make__MeasObjectNR__ext2O__Type None None None None None  => false 
  | _ => true 
 end.
Definition MeasObjectNR__ext2__Format : T_Format MeasObjectNR__ext2__Type MeasObjectNR__ext2__cond :=
  restrict_add_format MeasObjectNR__ext2__check_all_none MeasObjectNR__ext2O__Format.

Opaque MeasObjectNR__ext2__cond MeasObjectNR__ext2__Format.


Definition MeasObjectNR__ext3O__Format_Type := Eval cbn in seq_format_prod MeasObjectNR__ext3O__list.
Definition MeasObjectNR__ext3O__Format_list : MeasObjectNR__ext3O__Format_Type :=
  (MeasGapId_r17__Format, (MeasGapId_r17__Format, unit_format)).
Definition MeasObjectNR__ext3O__list__Format := (*Eval compute in *) seq_format MeasObjectNR__ext3O__list MeasObjectNR__ext3O__Format_list.
Definition MeasObjectNR__ext3O__F1 z :=
  (MeasObjectNR__ext3O__associatedMeasGapSSB2_v1720 z, (MeasObjectNR__ext3O__associatedMeasGapCSIRS2_v1720 z, tt)).
Definition MeasObjectNR__ext3O__F2 (y : seq_type MeasObjectNR__ext3O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasObjectNR__ext3O__Type i0 i1
  end.
Lemma MeasObjectNR__ext3O__F1F2_cond (z : MeasObjectNR__ext3O__Type)
  : MeasObjectNR__ext3O__cond z ->
  (seq_cond MeasObjectNR__ext3O__list (MeasObjectNR__ext3O__F1 z)).
intro H. unfold MeasObjectNR__ext3O__cond in H. simpl. auto. Qed.
Lemma MeasObjectNR__ext3O__F1F2_cond2 (z : MeasObjectNR__ext3O__Type)
 : MeasObjectNR__ext3O__F2 (MeasObjectNR__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasObjectNR__ext3O__F2F1_cond (y : seq_type MeasObjectNR__ext3O__list)
  : seq_cond MeasObjectNR__ext3O__list y ->
 (MeasObjectNR__ext3O__cond (MeasObjectNR__ext3O__F2 y)) /\  MeasObjectNR__ext3O__F1 (MeasObjectNR__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasObjectNR__ext3O__cond. simpl in *. auto.
 - simpl. unfold MeasObjectNR__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasObjectNR__ext3O__Format : T_Format MeasObjectNR__ext3O__Type MeasObjectNR__ext3O__cond :=
        proj2_format  MeasObjectNR__ext3O__cond MeasObjectNR__ext3O__list__Format
    MeasObjectNR__ext3O__F1 MeasObjectNR__ext3O__F2 MeasObjectNR__ext3O__F1F2_cond  MeasObjectNR__ext3O__F1F2_cond2 MeasObjectNR__ext3O__F2F1_cond.
Opaque MeasObjectNR__ext3O__cond MeasObjectNR__ext3O__Format.

Definition MeasObjectNR__ext3__check_all_none (b : MeasObjectNR__ext3O__Type) : bool :=
match b with 
  | make__MeasObjectNR__ext3O__Type None None  => false 
  | _ => true 
 end.
Definition MeasObjectNR__ext3__Format : T_Format MeasObjectNR__ext3__Type MeasObjectNR__ext3__cond :=
  restrict_add_format MeasObjectNR__ext3__check_all_none MeasObjectNR__ext3O__Format.

Opaque MeasObjectNR__ext3__cond MeasObjectNR__ext3__Format.


Definition MeasObjectNR__root_Format_Type := Eval cbn in seq_format_prod MeasObjectNR__root_list.
Definition MeasObjectNR__root_Format_list : MeasObjectNR__root_Format_Type :=
  (ARFCN_ValueNR__Format, (SubcarrierSpacing__Format, (SSB_MTC__Format, (SSB_MTC2__Format, (ARFCN_ValueNR__Format, (ReferenceSignalConfig__Format, (ThresholdNR__Format, (ThresholdNR__Format, (MeasObjectNR__nrofSS_BlocksToAverage__Format, (MeasObjectNR__nrofCSI_RS_ResourcesToAverage__Format, (MeasObjectNR__quantityConfigIndex__Format, (Q_OffsetRangeList__Format, (PCI_List__Format, (CellsToAddModList__Format, (PCI_RangeIndexList__Format, (MeasObjectNR__excludedCellsToAddModList__Format, (PCI_RangeIndexList__Format, (MeasObjectNR__allowedCellsToAddModList__Format, unit_format)))))))))))))))))).

Definition MeasObjectNR__ext_Format_Type := Eval cbn in get_formats MeasObjectNR__ext_list.
Definition MeasObjectNR__ext_Format_list : MeasObjectNR__ext_Format_Type :=
  (MeasObjectNR__ext0__Format, (MeasObjectNR__ext1__Format, (MeasObjectNR__ext2__Format, (MeasObjectNR__ext3__Format, unit__Format)))).

Definition MeasObjectNR__list_type : Set := (seq_type MeasObjectNR__root_list) * (seq_ext_type MeasObjectNR__ext_list).
Definition MeasObjectNR__list_cond (z : MeasObjectNR__list_type) : Prop :=
        (seq_cond MeasObjectNR__root_list (fst z)) /\ (seq_ext_cond MeasObjectNR__ext_list (snd z)).
Definition MeasObjectNR__list_format : T_Format MeasObjectNR__list_type MeasObjectNR__list_cond :=
 (* Eval compute in *) seq_ext_format MeasObjectNR__root_list MeasObjectNR__root_Format_list MeasObjectNR__ext_list MeasObjectNR__ext_Format_list.

Opaque MeasObjectNR__list_format.
Definition MeasObjectNR__F1 (z : MeasObjectNR__Type) : MeasObjectNR__list_type :=
  (((MeasObjectNR__ssbFrequency z, (MeasObjectNR__ssbSubcarrierSpacing z, (MeasObjectNR__smtc1 z, (MeasObjectNR__smtc2 z, (MeasObjectNR__refFreqCSI_RS z, (MeasObjectNR__referenceSignalConfig z, (MeasObjectNR__absThreshSS_BlocksConsolidation z, (MeasObjectNR__absThreshCSI_RS_Consolidation z, (MeasObjectNR__nrofSS_BlocksToAverage z, (MeasObjectNR__nrofCSI_RS_ResourcesToAverage z, (MeasObjectNR__quantityConfigIndex z, (MeasObjectNR__offsetMO z, (MeasObjectNR__cellsToRemoveList z, (MeasObjectNR__cellsToAddModList z, (MeasObjectNR__excludedCellsToRemoveList z, (MeasObjectNR__excludedCellsToAddModList z, (MeasObjectNR__allowedCellsToRemoveList z, (MeasObjectNR__allowedCellsToAddModList z, tt))))))))))))))))))), (
(MeasObjectNR__ext0 z, (MeasObjectNR__ext1 z, (MeasObjectNR__ext2 z, (MeasObjectNR__ext3 z, tt)))))).
Definition MeasObjectNR__F2 (y : MeasObjectNR__list_type) : MeasObjectNR__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, _)))))))))))))))))), (i0, (i1, (i2, (i3, _)))))=>
    make__MeasObjectNR__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 i0 i1 i2 i3
  end.
Definition MeasObjectNR__helper1 : (forall a : MeasObjectNR__Type, MeasObjectNR__cond a -> MeasObjectNR__list_cond (MeasObjectNR__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasObjectNR__helper2 : (forall a : MeasObjectNR__Type, MeasObjectNR__F2 (MeasObjectNR__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasObjectNR__helper3 : (forall b : MeasObjectNR__list_type, MeasObjectNR__list_cond b -> MeasObjectNR__cond (MeasObjectNR__F2 b) /\ MeasObjectNR__F1 (MeasObjectNR__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasObjectNR__cond, MeasObjectNR__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasObjectNR__Format : T_Format MeasObjectNR__Type MeasObjectNR__cond :=
 proj2_format MeasObjectNR__cond MeasObjectNR__list_format  MeasObjectNR__F1 MeasObjectNR__F2 MeasObjectNR__helper1 MeasObjectNR__helper2 MeasObjectNR__helper3.

Opaque MeasObjectNR__cond MeasObjectNR__Format.

