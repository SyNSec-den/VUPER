Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NZP_CSI_RS_Resource.

Opaque NZP_CSI_RS_Resource__cond NZP_CSI_RS_Resource__Format.

Definition CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__Type := list NZP_CSI_RS_Resource__Type.

Lemma CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__helper1 : (0 <= 1 <= maxNrofNZP_CSI_RS_Resources)%Z. unfold maxNrofNZP_CSI_RS_Resources.
 lia. Qed.
Lemma CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofNZP_CSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofNZP_CSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__cond (z : CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofNZP_CSI_RS_Resources)%Z /\ (list_and NZP_CSI_RS_Resource__cond z) .

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Definition CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__Type := list NZP_CSI_RS_ResourceId__Type.

Lemma CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__helper1 : (0 <= 1 <= maxNrofNZP_CSI_RS_Resources)%Z. unfold maxNrofNZP_CSI_RS_Resources.
 lia. Qed.
Lemma CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofNZP_CSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofNZP_CSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__cond (z : CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofNZP_CSI_RS_Resources)%Z /\ (list_and NZP_CSI_RS_ResourceId__cond z) .

Require Import NR.NZP_CSI_RS_ResourceSet.

Opaque NZP_CSI_RS_ResourceSet__cond NZP_CSI_RS_ResourceSet__Format.

Definition CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__Type := list NZP_CSI_RS_ResourceSet__Type.

Lemma CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__helper1 : (0 <= 1 <= maxNrofNZP_CSI_RS_ResourceSets)%Z. unfold maxNrofNZP_CSI_RS_ResourceSets.
 lia. Qed.
Lemma CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofNZP_CSI_RS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofNZP_CSI_RS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__cond (z : CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofNZP_CSI_RS_ResourceSets)%Z /\ (list_and NZP_CSI_RS_ResourceSet__cond z) .

Require Import NR.NZP_CSI_RS_ResourceSetId.

Opaque NZP_CSI_RS_ResourceSetId__cond NZP_CSI_RS_ResourceSetId__Format.

Definition CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__Type := list NZP_CSI_RS_ResourceSetId__Type.

Lemma CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__helper1 : (0 <= 1 <= maxNrofNZP_CSI_RS_ResourceSets)%Z. unfold maxNrofNZP_CSI_RS_ResourceSets.
 lia. Qed.
Lemma CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofNZP_CSI_RS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofNZP_CSI_RS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__cond (z : CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofNZP_CSI_RS_ResourceSets)%Z /\ (list_and NZP_CSI_RS_ResourceSetId__cond z) .

Require Import NR.CSI_IM_Resource.

Opaque CSI_IM_Resource__cond CSI_IM_Resource__Format.

Definition CSI_MeasConfig__csi_IM_ResourceToAddModList__Type := list CSI_IM_Resource__Type.

Lemma CSI_MeasConfig__csi_IM_ResourceToAddModList__helper1 : (0 <= 1 <= maxNrofCSI_IM_Resources)%Z. unfold maxNrofCSI_IM_Resources.
 lia. Qed.
Lemma CSI_MeasConfig__csi_IM_ResourceToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_IM_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_IM_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_IM_ResourceToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_IM_ResourceToAddModList__cond (z : CSI_MeasConfig__csi_IM_ResourceToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_IM_Resources)%Z /\ (list_and CSI_IM_Resource__cond z) .

Require Import NR.CSI_IM_ResourceId.

Opaque CSI_IM_ResourceId__cond CSI_IM_ResourceId__Format.

Definition CSI_MeasConfig__csi_IM_ResourceToReleaseList__Type := list CSI_IM_ResourceId__Type.

Lemma CSI_MeasConfig__csi_IM_ResourceToReleaseList__helper1 : (0 <= 1 <= maxNrofCSI_IM_Resources)%Z. unfold maxNrofCSI_IM_Resources.
 lia. Qed.
Lemma CSI_MeasConfig__csi_IM_ResourceToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_IM_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_IM_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_IM_ResourceToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_IM_ResourceToReleaseList__cond (z : CSI_MeasConfig__csi_IM_ResourceToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_IM_Resources)%Z /\ (list_and CSI_IM_ResourceId__cond z) .

Require Import NR.CSI_IM_ResourceSet.

Opaque CSI_IM_ResourceSet__cond CSI_IM_ResourceSet__Format.

Definition CSI_MeasConfig__csi_IM_ResourceSetToAddModList__Type := list CSI_IM_ResourceSet__Type.

Lemma CSI_MeasConfig__csi_IM_ResourceSetToAddModList__helper1 : (0 <= 1 <= maxNrofCSI_IM_ResourceSets)%Z. unfold maxNrofCSI_IM_ResourceSets.
 lia. Qed.
Lemma CSI_MeasConfig__csi_IM_ResourceSetToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_IM_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_IM_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_IM_ResourceSetToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_IM_ResourceSetToAddModList__cond (z : CSI_MeasConfig__csi_IM_ResourceSetToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_IM_ResourceSets)%Z /\ (list_and CSI_IM_ResourceSet__cond z) .

Require Import NR.CSI_IM_ResourceSetId.

Opaque CSI_IM_ResourceSetId__cond CSI_IM_ResourceSetId__Format.

Definition CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__Type := list CSI_IM_ResourceSetId__Type.

Lemma CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__helper1 : (0 <= 1 <= maxNrofCSI_IM_ResourceSets)%Z. unfold maxNrofCSI_IM_ResourceSets.
 lia. Qed.
Lemma CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_IM_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_IM_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__cond (z : CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_IM_ResourceSets)%Z /\ (list_and CSI_IM_ResourceSetId__cond z) .

Require Import NR.CSI_SSB_ResourceSet.

Opaque CSI_SSB_ResourceSet__cond CSI_SSB_ResourceSet__Format.

Definition CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__Type := list CSI_SSB_ResourceSet__Type.

Lemma CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__helper1 : (0 <= 1 <= maxNrofCSI_SSB_ResourceSets)%Z. unfold maxNrofCSI_SSB_ResourceSets.
 lia. Qed.
Lemma CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_SSB_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_SSB_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__cond (z : CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_SSB_ResourceSets)%Z /\ (list_and CSI_SSB_ResourceSet__cond z) .

Require Import NR.CSI_SSB_ResourceSetId.

Opaque CSI_SSB_ResourceSetId__cond CSI_SSB_ResourceSetId__Format.

Definition CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__Type := list CSI_SSB_ResourceSetId__Type.

Lemma CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__helper1 : (0 <= 1 <= maxNrofCSI_SSB_ResourceSets)%Z. unfold maxNrofCSI_SSB_ResourceSets.
 lia. Qed.
Lemma CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_SSB_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_SSB_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__cond (z : CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_SSB_ResourceSets)%Z /\ (list_and CSI_SSB_ResourceSetId__cond z) .

Require Import NR.CSI_ResourceConfig.

Opaque CSI_ResourceConfig__cond CSI_ResourceConfig__Format.

Definition CSI_MeasConfig__csi_ResourceConfigToAddModList__Type := list CSI_ResourceConfig__Type.

Lemma CSI_MeasConfig__csi_ResourceConfigToAddModList__helper1 : (0 <= 1 <= maxNrofCSI_ResourceConfigurations)%Z. unfold maxNrofCSI_ResourceConfigurations.
 lia. Qed.
Lemma CSI_MeasConfig__csi_ResourceConfigToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_ResourceConfigurations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_ResourceConfigurations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_ResourceConfigToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_ResourceConfigToAddModList__cond (z : CSI_MeasConfig__csi_ResourceConfigToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_ResourceConfigurations)%Z /\ (list_and CSI_ResourceConfig__cond z) .

Require Import NR.CSI_ResourceConfigId.

Opaque CSI_ResourceConfigId__cond CSI_ResourceConfigId__Format.

Definition CSI_MeasConfig__csi_ResourceConfigToReleaseList__Type := list CSI_ResourceConfigId__Type.

Lemma CSI_MeasConfig__csi_ResourceConfigToReleaseList__helper1 : (0 <= 1 <= maxNrofCSI_ResourceConfigurations)%Z. unfold maxNrofCSI_ResourceConfigurations.
 lia. Qed.
Lemma CSI_MeasConfig__csi_ResourceConfigToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_ResourceConfigurations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_ResourceConfigurations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_ResourceConfigToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_ResourceConfigToReleaseList__cond (z : CSI_MeasConfig__csi_ResourceConfigToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_ResourceConfigurations)%Z /\ (list_and CSI_ResourceConfigId__cond z) .

Require Import NR.CSI_ReportConfig.

Opaque CSI_ReportConfig__cond CSI_ReportConfig__Format.

Definition CSI_MeasConfig__csi_ReportConfigToAddModList__Type := list CSI_ReportConfig__Type.

Lemma CSI_MeasConfig__csi_ReportConfigToAddModList__helper1 : (0 <= 1 <= maxNrofCSI_ReportConfigurations)%Z. unfold maxNrofCSI_ReportConfigurations.
 lia. Qed.
Lemma CSI_MeasConfig__csi_ReportConfigToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_ReportConfigurations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_ReportConfigurations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_ReportConfigToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_ReportConfigToAddModList__cond (z : CSI_MeasConfig__csi_ReportConfigToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_ReportConfigurations)%Z /\ (list_and CSI_ReportConfig__cond z) .

Require Import NR.CSI_ReportConfigId.

Opaque CSI_ReportConfigId__cond CSI_ReportConfigId__Format.

Definition CSI_MeasConfig__csi_ReportConfigToReleaseList__Type := list CSI_ReportConfigId__Type.

Lemma CSI_MeasConfig__csi_ReportConfigToReleaseList__helper1 : (0 <= 1 <= maxNrofCSI_ReportConfigurations)%Z. unfold maxNrofCSI_ReportConfigurations.
 lia. Qed.
Lemma CSI_MeasConfig__csi_ReportConfigToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_ReportConfigurations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_ReportConfigurations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__csi_ReportConfigToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__csi_ReportConfigToReleaseList__cond (z : CSI_MeasConfig__csi_ReportConfigToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_ReportConfigurations)%Z /\ (list_and CSI_ReportConfigId__cond z) .

Lemma CSI_MeasConfig__reportTriggerSize__helper1 : (0 <= 6)%Z.  lia. Qed.
Lemma CSI_MeasConfig__reportTriggerSize__helper2 : to_bit_sz (Z.to_nat (6 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__reportTriggerSize__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__reportTriggerSize__Type := Z.
Definition CSI_MeasConfig__reportTriggerSize__cond := (fun z => (0 <= z <= 6)%Z).
Require Import NR.SetupRelease.
Require Import NR.CSI_AperiodicTriggerStateList.
Definition CSI_MeasConfig__aperiodicTriggerStateList__Type := SetupRelease__Type CSI_AperiodicTriggerStateList__Type.
Definition CSI_MeasConfig__aperiodicTriggerStateList__cond := SetupRelease__cond _ CSI_AperiodicTriggerStateList__cond.
Definition CSI_MeasConfig__aperiodicTriggerStateList__Format : T_Format CSI_MeasConfig__aperiodicTriggerStateList__Type CSI_MeasConfig__aperiodicTriggerStateList__cond := SetupRelease__Format _ _ CSI_AperiodicTriggerStateList__Format.
Opaque CSI_MeasConfig__aperiodicTriggerStateList__cond CSI_MeasConfig__aperiodicTriggerStateList__Format.

Require Import NR.SetupRelease.
Require Import NR.CSI_SemiPersistentOnPUSCH_TriggerStateList.
Definition CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__Type := SetupRelease__Type CSI_SemiPersistentOnPUSCH_TriggerStateList__Type.
Definition CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__cond := SetupRelease__cond _ CSI_SemiPersistentOnPUSCH_TriggerStateList__cond.
Definition CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__Format : T_Format CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__Type CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__cond := SetupRelease__Format _ _ CSI_SemiPersistentOnPUSCH_TriggerStateList__Format.
Opaque CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__cond CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__Format.

Lemma CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__helper1 : (0 <= 6)%Z.  lia. Qed.
Lemma CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (6 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__Type := Z.
Definition CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__cond := (fun z => (0 <= z <= 6)%Z).
Record CSI_MeasConfig__ext0O__Type : Set :=
  make__CSI_MeasConfig__ext0O__Type {
    CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16 : option Z ;
}.
Definition CSI_MeasConfig__ext0O__list := (
 Opt Z CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__cond ::
 nil).
Definition CSI_MeasConfig__ext0O__cond z := 
  opt_cond CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__cond (CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16 z) /\
  True.

Definition CSI_MeasConfig__ext0__Type := CSI_MeasConfig__ext0O__Type.
Definition CSI_MeasConfig__ext0__cond := CSI_MeasConfig__ext0O__cond.

Require Import NR.SCellActivationRS_Config_r17.

Opaque SCellActivationRS_Config_r17__cond SCellActivationRS_Config_r17__Format.

Definition CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__Type := list SCellActivationRS_Config_r17__Type.

Lemma CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__helper1 : (0 <= 1 <= maxNrofSCellActRS_r17)%Z. unfold maxNrofSCellActRS_r17.
 lia. Qed.
Lemma CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSCellActRS_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSCellActRS_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__cond (z : CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSCellActRS_r17)%Z /\ (list_and SCellActivationRS_Config_r17__cond z) .

Require Import NR.SCellActivationRS_ConfigId_r17.

Opaque SCellActivationRS_ConfigId_r17__cond SCellActivationRS_ConfigId_r17__Format.

Definition CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__Type := list SCellActivationRS_ConfigId_r17__Type.

Lemma CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofSCellActRS_r17)%Z. unfold maxNrofSCellActRS_r17.
 lia. Qed.
Lemma CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSCellActRS_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSCellActRS_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__cond (z : CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSCellActRS_r17)%Z /\ (list_and SCellActivationRS_ConfigId_r17__cond z) .

Record CSI_MeasConfig__ext1O__Type : Set :=
  make__CSI_MeasConfig__ext1O__Type {
    CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17 : option CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__Type ;
    CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17 : option CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__Type ;
}.
Definition CSI_MeasConfig__ext1O__list := (
 Opt CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__Type CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__cond ::
 Opt CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__Type CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__cond ::
 nil).
Definition CSI_MeasConfig__ext1O__cond z := 
  opt_cond CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__cond (CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17 z) /\
  opt_cond CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__cond (CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17 z) /\
  True.

Definition CSI_MeasConfig__ext1__Type := CSI_MeasConfig__ext1O__Type.
Definition CSI_MeasConfig__ext1__cond := CSI_MeasConfig__ext1O__cond.

Record CSI_MeasConfig__Type : Set :=
  make__CSI_MeasConfig__Type {
    CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList : option CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__Type ;
    CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList : option CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__Type ;
    CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList : option CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__Type ;
    CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList : option CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__Type ;
    CSI_MeasConfig__csi_IM_ResourceToAddModList : option CSI_MeasConfig__csi_IM_ResourceToAddModList__Type ;
    CSI_MeasConfig__csi_IM_ResourceToReleaseList : option CSI_MeasConfig__csi_IM_ResourceToReleaseList__Type ;
    CSI_MeasConfig__csi_IM_ResourceSetToAddModList : option CSI_MeasConfig__csi_IM_ResourceSetToAddModList__Type ;
    CSI_MeasConfig__csi_IM_ResourceSetToReleaseList : option CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__Type ;
    CSI_MeasConfig__csi_SSB_ResourceSetToAddModList : option CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__Type ;
    CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList : option CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__Type ;
    CSI_MeasConfig__csi_ResourceConfigToAddModList : option CSI_MeasConfig__csi_ResourceConfigToAddModList__Type ;
    CSI_MeasConfig__csi_ResourceConfigToReleaseList : option CSI_MeasConfig__csi_ResourceConfigToReleaseList__Type ;
    CSI_MeasConfig__csi_ReportConfigToAddModList : option CSI_MeasConfig__csi_ReportConfigToAddModList__Type ;
    CSI_MeasConfig__csi_ReportConfigToReleaseList : option CSI_MeasConfig__csi_ReportConfigToReleaseList__Type ;
    CSI_MeasConfig__reportTriggerSize : option Z ;
    CSI_MeasConfig__aperiodicTriggerStateList : option CSI_MeasConfig__aperiodicTriggerStateList__Type ;
    CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList : option CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__Type ;
    CSI_MeasConfig__ext0 : option CSI_MeasConfig__ext0__Type ;
    CSI_MeasConfig__ext1 : option CSI_MeasConfig__ext1__Type ;
}.
Definition CSI_MeasConfig__root_list : list seq_elem := (
 Opt CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__Type CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__cond ::
 Opt CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__Type CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__cond ::
 Opt CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__Type CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__cond ::
 Opt CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__Type CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__cond ::
 Opt CSI_MeasConfig__csi_IM_ResourceToAddModList__Type CSI_MeasConfig__csi_IM_ResourceToAddModList__cond ::
 Opt CSI_MeasConfig__csi_IM_ResourceToReleaseList__Type CSI_MeasConfig__csi_IM_ResourceToReleaseList__cond ::
 Opt CSI_MeasConfig__csi_IM_ResourceSetToAddModList__Type CSI_MeasConfig__csi_IM_ResourceSetToAddModList__cond ::
 Opt CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__Type CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__cond ::
 Opt CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__Type CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__cond ::
 Opt CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__Type CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__cond ::
 Opt CSI_MeasConfig__csi_ResourceConfigToAddModList__Type CSI_MeasConfig__csi_ResourceConfigToAddModList__cond ::
 Opt CSI_MeasConfig__csi_ResourceConfigToReleaseList__Type CSI_MeasConfig__csi_ResourceConfigToReleaseList__cond ::
 Opt CSI_MeasConfig__csi_ReportConfigToAddModList__Type CSI_MeasConfig__csi_ReportConfigToAddModList__cond ::
 Opt CSI_MeasConfig__csi_ReportConfigToReleaseList__Type CSI_MeasConfig__csi_ReportConfigToReleaseList__cond ::
 Opt Z CSI_MeasConfig__reportTriggerSize__cond ::
 Opt CSI_MeasConfig__aperiodicTriggerStateList__Type CSI_MeasConfig__aperiodicTriggerStateList__cond ::
 Opt CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__Type CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__cond ::
 nil).
Definition CSI_MeasConfig__ext_list : list typ := (
  typ_cons CSI_MeasConfig__ext0__Type CSI_MeasConfig__ext0__cond ::
  typ_cons CSI_MeasConfig__ext1__Type CSI_MeasConfig__ext1__cond ::
  nil).
Definition CSI_MeasConfig__cond (z : CSI_MeasConfig__Type) := 
(  opt_cond CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__cond (CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList z) /\
  opt_cond CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__cond (CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList z) /\
  opt_cond CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__cond (CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList z) /\
  opt_cond CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__cond (CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList z) /\
  opt_cond CSI_MeasConfig__csi_IM_ResourceToAddModList__cond (CSI_MeasConfig__csi_IM_ResourceToAddModList z) /\
  opt_cond CSI_MeasConfig__csi_IM_ResourceToReleaseList__cond (CSI_MeasConfig__csi_IM_ResourceToReleaseList z) /\
  opt_cond CSI_MeasConfig__csi_IM_ResourceSetToAddModList__cond (CSI_MeasConfig__csi_IM_ResourceSetToAddModList z) /\
  opt_cond CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__cond (CSI_MeasConfig__csi_IM_ResourceSetToReleaseList z) /\
  opt_cond CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__cond (CSI_MeasConfig__csi_SSB_ResourceSetToAddModList z) /\
  opt_cond CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__cond (CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList z) /\
  opt_cond CSI_MeasConfig__csi_ResourceConfigToAddModList__cond (CSI_MeasConfig__csi_ResourceConfigToAddModList z) /\
  opt_cond CSI_MeasConfig__csi_ResourceConfigToReleaseList__cond (CSI_MeasConfig__csi_ResourceConfigToReleaseList z) /\
  opt_cond CSI_MeasConfig__csi_ReportConfigToAddModList__cond (CSI_MeasConfig__csi_ReportConfigToAddModList z) /\
  opt_cond CSI_MeasConfig__csi_ReportConfigToReleaseList__cond (CSI_MeasConfig__csi_ReportConfigToReleaseList z) /\
  opt_cond CSI_MeasConfig__reportTriggerSize__cond (CSI_MeasConfig__reportTriggerSize z) /\
  opt_cond CSI_MeasConfig__aperiodicTriggerStateList__cond (CSI_MeasConfig__aperiodicTriggerStateList z) /\
  opt_cond CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__cond (CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList z) /\
  True) /\ 
(  opt_cond CSI_MeasConfig__ext0__cond (CSI_MeasConfig__ext0 z) /\
  opt_cond CSI_MeasConfig__ext1__cond (CSI_MeasConfig__ext1 z) /\
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
Definition CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__Format : T_Format CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__Type CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__cond := seq_of_format NZP_CSI_RS_Resource__Format 1 maxNrofNZP_CSI_RS_Resources CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__helper1 CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__helper2.

Opaque CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__cond CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__Format.

Definition CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__Format : T_Format CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__Type CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__cond := seq_of_format NZP_CSI_RS_ResourceId__Format 1 maxNrofNZP_CSI_RS_Resources CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__helper1 CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__helper2.

Opaque CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__cond CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__Format.

Definition CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__Format : T_Format CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__Type CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__cond := seq_of_format NZP_CSI_RS_ResourceSet__Format 1 maxNrofNZP_CSI_RS_ResourceSets CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__helper1 CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__helper2.

Opaque CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__cond CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__Format.

Definition CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__Format : T_Format CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__Type CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__cond := seq_of_format NZP_CSI_RS_ResourceSetId__Format 1 maxNrofNZP_CSI_RS_ResourceSets CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__helper1 CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__helper2.

Opaque CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__cond CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__Format.

Definition CSI_MeasConfig__csi_IM_ResourceToAddModList__Format : T_Format CSI_MeasConfig__csi_IM_ResourceToAddModList__Type CSI_MeasConfig__csi_IM_ResourceToAddModList__cond := seq_of_format CSI_IM_Resource__Format 1 maxNrofCSI_IM_Resources CSI_MeasConfig__csi_IM_ResourceToAddModList__helper1 CSI_MeasConfig__csi_IM_ResourceToAddModList__helper2.

Opaque CSI_MeasConfig__csi_IM_ResourceToAddModList__cond CSI_MeasConfig__csi_IM_ResourceToAddModList__Format.

Definition CSI_MeasConfig__csi_IM_ResourceToReleaseList__Format : T_Format CSI_MeasConfig__csi_IM_ResourceToReleaseList__Type CSI_MeasConfig__csi_IM_ResourceToReleaseList__cond := seq_of_format CSI_IM_ResourceId__Format 1 maxNrofCSI_IM_Resources CSI_MeasConfig__csi_IM_ResourceToReleaseList__helper1 CSI_MeasConfig__csi_IM_ResourceToReleaseList__helper2.

Opaque CSI_MeasConfig__csi_IM_ResourceToReleaseList__cond CSI_MeasConfig__csi_IM_ResourceToReleaseList__Format.

Definition CSI_MeasConfig__csi_IM_ResourceSetToAddModList__Format : T_Format CSI_MeasConfig__csi_IM_ResourceSetToAddModList__Type CSI_MeasConfig__csi_IM_ResourceSetToAddModList__cond := seq_of_format CSI_IM_ResourceSet__Format 1 maxNrofCSI_IM_ResourceSets CSI_MeasConfig__csi_IM_ResourceSetToAddModList__helper1 CSI_MeasConfig__csi_IM_ResourceSetToAddModList__helper2.

Opaque CSI_MeasConfig__csi_IM_ResourceSetToAddModList__cond CSI_MeasConfig__csi_IM_ResourceSetToAddModList__Format.

Definition CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__Format : T_Format CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__Type CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__cond := seq_of_format CSI_IM_ResourceSetId__Format 1 maxNrofCSI_IM_ResourceSets CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__helper1 CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__helper2.

Opaque CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__cond CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__Format.

Definition CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__Format : T_Format CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__Type CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__cond := seq_of_format CSI_SSB_ResourceSet__Format 1 maxNrofCSI_SSB_ResourceSets CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__helper1 CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__helper2.

Opaque CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__cond CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__Format.

Definition CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__Format : T_Format CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__Type CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__cond := seq_of_format CSI_SSB_ResourceSetId__Format 1 maxNrofCSI_SSB_ResourceSets CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__helper1 CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__helper2.

Opaque CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__cond CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__Format.

Definition CSI_MeasConfig__csi_ResourceConfigToAddModList__Format : T_Format CSI_MeasConfig__csi_ResourceConfigToAddModList__Type CSI_MeasConfig__csi_ResourceConfigToAddModList__cond := seq_of_format CSI_ResourceConfig__Format 1 maxNrofCSI_ResourceConfigurations CSI_MeasConfig__csi_ResourceConfigToAddModList__helper1 CSI_MeasConfig__csi_ResourceConfigToAddModList__helper2.

Opaque CSI_MeasConfig__csi_ResourceConfigToAddModList__cond CSI_MeasConfig__csi_ResourceConfigToAddModList__Format.

Definition CSI_MeasConfig__csi_ResourceConfigToReleaseList__Format : T_Format CSI_MeasConfig__csi_ResourceConfigToReleaseList__Type CSI_MeasConfig__csi_ResourceConfigToReleaseList__cond := seq_of_format CSI_ResourceConfigId__Format 1 maxNrofCSI_ResourceConfigurations CSI_MeasConfig__csi_ResourceConfigToReleaseList__helper1 CSI_MeasConfig__csi_ResourceConfigToReleaseList__helper2.

Opaque CSI_MeasConfig__csi_ResourceConfigToReleaseList__cond CSI_MeasConfig__csi_ResourceConfigToReleaseList__Format.

Definition CSI_MeasConfig__csi_ReportConfigToAddModList__Format : T_Format CSI_MeasConfig__csi_ReportConfigToAddModList__Type CSI_MeasConfig__csi_ReportConfigToAddModList__cond := seq_of_format CSI_ReportConfig__Format 1 maxNrofCSI_ReportConfigurations CSI_MeasConfig__csi_ReportConfigToAddModList__helper1 CSI_MeasConfig__csi_ReportConfigToAddModList__helper2.

Opaque CSI_MeasConfig__csi_ReportConfigToAddModList__cond CSI_MeasConfig__csi_ReportConfigToAddModList__Format.

Definition CSI_MeasConfig__csi_ReportConfigToReleaseList__Format : T_Format CSI_MeasConfig__csi_ReportConfigToReleaseList__Type CSI_MeasConfig__csi_ReportConfigToReleaseList__cond := seq_of_format CSI_ReportConfigId__Format 1 maxNrofCSI_ReportConfigurations CSI_MeasConfig__csi_ReportConfigToReleaseList__helper1 CSI_MeasConfig__csi_ReportConfigToReleaseList__helper2.

Opaque CSI_MeasConfig__csi_ReportConfigToReleaseList__cond CSI_MeasConfig__csi_ReportConfigToReleaseList__Format.

Definition CSI_MeasConfig__reportTriggerSize__Format : T_Format Z CSI_MeasConfig__reportTriggerSize__cond :=
 ranged_int_format (0) (6) CSI_MeasConfig__reportTriggerSize__helper1 CSI_MeasConfig__reportTriggerSize__helper2.

Opaque CSI_MeasConfig__reportTriggerSize__cond CSI_MeasConfig__reportTriggerSize__Format.

Opaque CSI_MeasConfig__aperiodicTriggerStateList__cond CSI_MeasConfig__aperiodicTriggerStateList__Format.

Opaque CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__cond CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__Format.

Definition CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__Format : T_Format Z CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__cond :=
 ranged_int_format (0) (6) CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__helper1 CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__helper2.

Opaque CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__cond CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__Format.


Definition CSI_MeasConfig__ext0O__Format_Type := Eval cbn in seq_format_prod CSI_MeasConfig__ext0O__list.
Definition CSI_MeasConfig__ext0O__Format_list : CSI_MeasConfig__ext0O__Format_Type :=
  (CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16__Format, unit_format).
Definition CSI_MeasConfig__ext0O__list__Format := (*Eval compute in *) seq_format CSI_MeasConfig__ext0O__list CSI_MeasConfig__ext0O__Format_list.
Definition CSI_MeasConfig__ext0O__F1 z :=
  (CSI_MeasConfig__ext0O__reportTriggerSizeDCI_0_2_r16 z, tt).
Definition CSI_MeasConfig__ext0O__F2 (y : seq_type CSI_MeasConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CSI_MeasConfig__ext0O__Type i0
  end.
Lemma CSI_MeasConfig__ext0O__F1F2_cond (z : CSI_MeasConfig__ext0O__Type)
  : CSI_MeasConfig__ext0O__cond z ->
  (seq_cond CSI_MeasConfig__ext0O__list (CSI_MeasConfig__ext0O__F1 z)).
intro H. unfold CSI_MeasConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma CSI_MeasConfig__ext0O__F1F2_cond2 (z : CSI_MeasConfig__ext0O__Type)
 : CSI_MeasConfig__ext0O__F2 (CSI_MeasConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_MeasConfig__ext0O__F2F1_cond (y : seq_type CSI_MeasConfig__ext0O__list)
  : seq_cond CSI_MeasConfig__ext0O__list y ->
 (CSI_MeasConfig__ext0O__cond (CSI_MeasConfig__ext0O__F2 y)) /\  CSI_MeasConfig__ext0O__F1 (CSI_MeasConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_MeasConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold CSI_MeasConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_MeasConfig__ext0O__Format : T_Format CSI_MeasConfig__ext0O__Type CSI_MeasConfig__ext0O__cond :=
        proj2_format  CSI_MeasConfig__ext0O__cond CSI_MeasConfig__ext0O__list__Format
    CSI_MeasConfig__ext0O__F1 CSI_MeasConfig__ext0O__F2 CSI_MeasConfig__ext0O__F1F2_cond  CSI_MeasConfig__ext0O__F1F2_cond2 CSI_MeasConfig__ext0O__F2F1_cond.
Opaque CSI_MeasConfig__ext0O__cond CSI_MeasConfig__ext0O__Format.

Definition CSI_MeasConfig__ext0__check_all_none (b : CSI_MeasConfig__ext0O__Type) : bool :=
match b with 
  | make__CSI_MeasConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CSI_MeasConfig__ext0__Format : T_Format CSI_MeasConfig__ext0__Type CSI_MeasConfig__ext0__cond :=
  restrict_add_format CSI_MeasConfig__ext0__check_all_none CSI_MeasConfig__ext0O__Format.

Opaque CSI_MeasConfig__ext0__cond CSI_MeasConfig__ext0__Format.

Definition CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__Format : T_Format CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__Type CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__cond := seq_of_format SCellActivationRS_Config_r17__Format 1 maxNrofSCellActRS_r17 CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__helper1 CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__helper2.

Opaque CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__cond CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__Format.

Definition CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__Format : T_Format CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__Type CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__cond := seq_of_format SCellActivationRS_ConfigId_r17__Format 1 maxNrofSCellActRS_r17 CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__helper1 CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__helper2.

Opaque CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__cond CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__Format.


Definition CSI_MeasConfig__ext1O__Format_Type := Eval cbn in seq_format_prod CSI_MeasConfig__ext1O__list.
Definition CSI_MeasConfig__ext1O__Format_list : CSI_MeasConfig__ext1O__Format_Type :=
  (CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17__Format, (CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17__Format, unit_format)).
Definition CSI_MeasConfig__ext1O__list__Format := (*Eval compute in *) seq_format CSI_MeasConfig__ext1O__list CSI_MeasConfig__ext1O__Format_list.
Definition CSI_MeasConfig__ext1O__F1 z :=
  (CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToAddModList_r17 z, (CSI_MeasConfig__ext1O__sCellActivationRS_ConfigToReleaseList_r17 z, tt)).
Definition CSI_MeasConfig__ext1O__F2 (y : seq_type CSI_MeasConfig__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_MeasConfig__ext1O__Type i0 i1
  end.
Lemma CSI_MeasConfig__ext1O__F1F2_cond (z : CSI_MeasConfig__ext1O__Type)
  : CSI_MeasConfig__ext1O__cond z ->
  (seq_cond CSI_MeasConfig__ext1O__list (CSI_MeasConfig__ext1O__F1 z)).
intro H. unfold CSI_MeasConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma CSI_MeasConfig__ext1O__F1F2_cond2 (z : CSI_MeasConfig__ext1O__Type)
 : CSI_MeasConfig__ext1O__F2 (CSI_MeasConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_MeasConfig__ext1O__F2F1_cond (y : seq_type CSI_MeasConfig__ext1O__list)
  : seq_cond CSI_MeasConfig__ext1O__list y ->
 (CSI_MeasConfig__ext1O__cond (CSI_MeasConfig__ext1O__F2 y)) /\  CSI_MeasConfig__ext1O__F1 (CSI_MeasConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_MeasConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold CSI_MeasConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_MeasConfig__ext1O__Format : T_Format CSI_MeasConfig__ext1O__Type CSI_MeasConfig__ext1O__cond :=
        proj2_format  CSI_MeasConfig__ext1O__cond CSI_MeasConfig__ext1O__list__Format
    CSI_MeasConfig__ext1O__F1 CSI_MeasConfig__ext1O__F2 CSI_MeasConfig__ext1O__F1F2_cond  CSI_MeasConfig__ext1O__F1F2_cond2 CSI_MeasConfig__ext1O__F2F1_cond.
Opaque CSI_MeasConfig__ext1O__cond CSI_MeasConfig__ext1O__Format.

Definition CSI_MeasConfig__ext1__check_all_none (b : CSI_MeasConfig__ext1O__Type) : bool :=
match b with 
  | make__CSI_MeasConfig__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition CSI_MeasConfig__ext1__Format : T_Format CSI_MeasConfig__ext1__Type CSI_MeasConfig__ext1__cond :=
  restrict_add_format CSI_MeasConfig__ext1__check_all_none CSI_MeasConfig__ext1O__Format.

Opaque CSI_MeasConfig__ext1__cond CSI_MeasConfig__ext1__Format.


Definition CSI_MeasConfig__root_Format_Type := Eval cbn in seq_format_prod CSI_MeasConfig__root_list.
Definition CSI_MeasConfig__root_Format_list : CSI_MeasConfig__root_Format_Type :=
  (CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList__Format, (CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList__Format, (CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList__Format, (CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList__Format, (CSI_MeasConfig__csi_IM_ResourceToAddModList__Format, (CSI_MeasConfig__csi_IM_ResourceToReleaseList__Format, (CSI_MeasConfig__csi_IM_ResourceSetToAddModList__Format, (CSI_MeasConfig__csi_IM_ResourceSetToReleaseList__Format, (CSI_MeasConfig__csi_SSB_ResourceSetToAddModList__Format, (CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList__Format, (CSI_MeasConfig__csi_ResourceConfigToAddModList__Format, (CSI_MeasConfig__csi_ResourceConfigToReleaseList__Format, (CSI_MeasConfig__csi_ReportConfigToAddModList__Format, (CSI_MeasConfig__csi_ReportConfigToReleaseList__Format, (CSI_MeasConfig__reportTriggerSize__Format, (CSI_MeasConfig__aperiodicTriggerStateList__Format, (CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList__Format, unit_format))))))))))))))))).

Definition CSI_MeasConfig__ext_Format_Type := Eval cbn in get_formats CSI_MeasConfig__ext_list.
Definition CSI_MeasConfig__ext_Format_list : CSI_MeasConfig__ext_Format_Type :=
  (CSI_MeasConfig__ext0__Format, (CSI_MeasConfig__ext1__Format, unit__Format)).

Definition CSI_MeasConfig__list_type : Set := (seq_type CSI_MeasConfig__root_list) * (seq_ext_type CSI_MeasConfig__ext_list).
Definition CSI_MeasConfig__list_cond (z : CSI_MeasConfig__list_type) : Prop :=
        (seq_cond CSI_MeasConfig__root_list (fst z)) /\ (seq_ext_cond CSI_MeasConfig__ext_list (snd z)).
Definition CSI_MeasConfig__list_format : T_Format CSI_MeasConfig__list_type CSI_MeasConfig__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_MeasConfig__root_list CSI_MeasConfig__root_Format_list CSI_MeasConfig__ext_list CSI_MeasConfig__ext_Format_list.

Opaque CSI_MeasConfig__list_format.
Definition CSI_MeasConfig__F1 (z : CSI_MeasConfig__Type) : CSI_MeasConfig__list_type :=
  (((CSI_MeasConfig__nzp_CSI_RS_ResourceToAddModList z, (CSI_MeasConfig__nzp_CSI_RS_ResourceToReleaseList z, (CSI_MeasConfig__nzp_CSI_RS_ResourceSetToAddModList z, (CSI_MeasConfig__nzp_CSI_RS_ResourceSetToReleaseList z, (CSI_MeasConfig__csi_IM_ResourceToAddModList z, (CSI_MeasConfig__csi_IM_ResourceToReleaseList z, (CSI_MeasConfig__csi_IM_ResourceSetToAddModList z, (CSI_MeasConfig__csi_IM_ResourceSetToReleaseList z, (CSI_MeasConfig__csi_SSB_ResourceSetToAddModList z, (CSI_MeasConfig__csi_SSB_ResourceSetToReleaseList z, (CSI_MeasConfig__csi_ResourceConfigToAddModList z, (CSI_MeasConfig__csi_ResourceConfigToReleaseList z, (CSI_MeasConfig__csi_ReportConfigToAddModList z, (CSI_MeasConfig__csi_ReportConfigToReleaseList z, (CSI_MeasConfig__reportTriggerSize z, (CSI_MeasConfig__aperiodicTriggerStateList z, (CSI_MeasConfig__semiPersistentOnPUSCH_TriggerStateList z, tt)))))))))))))))))), (
(CSI_MeasConfig__ext0 z, (CSI_MeasConfig__ext1 z, tt)))).
Definition CSI_MeasConfig__F2 (y : CSI_MeasConfig__list_type) : CSI_MeasConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, _))))))))))))))))), (i0, (i1, _)))=>
    make__CSI_MeasConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 i0 i1
  end.
Definition CSI_MeasConfig__helper1 : (forall a : CSI_MeasConfig__Type, CSI_MeasConfig__cond a -> CSI_MeasConfig__list_cond (CSI_MeasConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_MeasConfig__helper2 : (forall a : CSI_MeasConfig__Type, CSI_MeasConfig__F2 (CSI_MeasConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_MeasConfig__helper3 : (forall b : CSI_MeasConfig__list_type, CSI_MeasConfig__list_cond b -> CSI_MeasConfig__cond (CSI_MeasConfig__F2 b) /\ CSI_MeasConfig__F1 (CSI_MeasConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_MeasConfig__cond, CSI_MeasConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_MeasConfig__Format : T_Format CSI_MeasConfig__Type CSI_MeasConfig__cond :=
 proj2_format CSI_MeasConfig__cond CSI_MeasConfig__list_format  CSI_MeasConfig__F1 CSI_MeasConfig__F2 CSI_MeasConfig__helper1 CSI_MeasConfig__helper2 CSI_MeasConfig__helper3.

Opaque CSI_MeasConfig__cond CSI_MeasConfig__Format.

