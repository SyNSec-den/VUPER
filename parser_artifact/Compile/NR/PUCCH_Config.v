Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUCCH_ResourceSet.

Opaque PUCCH_ResourceSet__cond PUCCH_ResourceSet__Format.

Definition PUCCH_Config__resourceSetToAddModList__Type := list PUCCH_ResourceSet__Type.

Lemma PUCCH_Config__resourceSetToAddModList__helper1 : (0 <= 1 <= maxNrofPUCCH_ResourceSets)%Z. unfold maxNrofPUCCH_ResourceSets.
 lia. Qed.
Lemma PUCCH_Config__resourceSetToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__resourceSetToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__resourceSetToAddModList__cond (z : PUCCH_Config__resourceSetToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_ResourceSets)%Z /\ (list_and PUCCH_ResourceSet__cond z) .

Require Import NR.PUCCH_ResourceSetId.

Opaque PUCCH_ResourceSetId__cond PUCCH_ResourceSetId__Format.

Definition PUCCH_Config__resourceSetToReleaseList__Type := list PUCCH_ResourceSetId__Type.

Lemma PUCCH_Config__resourceSetToReleaseList__helper1 : (0 <= 1 <= maxNrofPUCCH_ResourceSets)%Z. unfold maxNrofPUCCH_ResourceSets.
 lia. Qed.
Lemma PUCCH_Config__resourceSetToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__resourceSetToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__resourceSetToReleaseList__cond (z : PUCCH_Config__resourceSetToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_ResourceSets)%Z /\ (list_and PUCCH_ResourceSetId__cond z) .

Require Import NR.PUCCH_Resource.

Opaque PUCCH_Resource__cond PUCCH_Resource__Format.

Definition PUCCH_Config__resourceToAddModList__Type := list PUCCH_Resource__Type.

Lemma PUCCH_Config__resourceToAddModList__helper1 : (0 <= 1 <= maxNrofPUCCH_Resources)%Z. unfold maxNrofPUCCH_Resources.
 lia. Qed.
Lemma PUCCH_Config__resourceToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__resourceToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__resourceToAddModList__cond (z : PUCCH_Config__resourceToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_Resources)%Z /\ (list_and PUCCH_Resource__cond z) .

Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Definition PUCCH_Config__resourceToReleaseList__Type := list PUCCH_ResourceId__Type.

Lemma PUCCH_Config__resourceToReleaseList__helper1 : (0 <= 1 <= maxNrofPUCCH_Resources)%Z. unfold maxNrofPUCCH_Resources.
 lia. Qed.
Lemma PUCCH_Config__resourceToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__resourceToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__resourceToReleaseList__cond (z : PUCCH_Config__resourceToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_Resources)%Z /\ (list_and PUCCH_ResourceId__cond z) .

Require Import NR.SetupRelease.
Require Import NR.PUCCH_FormatConfig.
Definition PUCCH_Config__format1__Type := SetupRelease__Type PUCCH_FormatConfig__Type.
Definition PUCCH_Config__format1__cond := SetupRelease__cond _ PUCCH_FormatConfig__cond.
Definition PUCCH_Config__format1__Format : T_Format PUCCH_Config__format1__Type PUCCH_Config__format1__cond := SetupRelease__Format _ _ PUCCH_FormatConfig__Format.
Opaque PUCCH_Config__format1__cond PUCCH_Config__format1__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_FormatConfig.
Definition PUCCH_Config__format2__Type := SetupRelease__Type PUCCH_FormatConfig__Type.
Definition PUCCH_Config__format2__cond := SetupRelease__cond _ PUCCH_FormatConfig__cond.
Definition PUCCH_Config__format2__Format : T_Format PUCCH_Config__format2__Type PUCCH_Config__format2__cond := SetupRelease__Format _ _ PUCCH_FormatConfig__Format.
Opaque PUCCH_Config__format2__cond PUCCH_Config__format2__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_FormatConfig.
Definition PUCCH_Config__format3__Type := SetupRelease__Type PUCCH_FormatConfig__Type.
Definition PUCCH_Config__format3__cond := SetupRelease__cond _ PUCCH_FormatConfig__cond.
Definition PUCCH_Config__format3__Format : T_Format PUCCH_Config__format3__Type PUCCH_Config__format3__cond := SetupRelease__Format _ _ PUCCH_FormatConfig__Format.
Opaque PUCCH_Config__format3__cond PUCCH_Config__format3__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_FormatConfig.
Definition PUCCH_Config__format4__Type := SetupRelease__Type PUCCH_FormatConfig__Type.
Definition PUCCH_Config__format4__cond := SetupRelease__cond _ PUCCH_FormatConfig__cond.
Definition PUCCH_Config__format4__Format : T_Format PUCCH_Config__format4__Type PUCCH_Config__format4__cond := SetupRelease__Format _ _ PUCCH_FormatConfig__Format.
Opaque PUCCH_Config__format4__cond PUCCH_Config__format4__Format.

Require Import NR.SchedulingRequestResourceConfig.

Opaque SchedulingRequestResourceConfig__cond SchedulingRequestResourceConfig__Format.

Definition PUCCH_Config__schedulingRequestResourceToAddModList__Type := list SchedulingRequestResourceConfig__Type.

Lemma PUCCH_Config__schedulingRequestResourceToAddModList__helper1 : (0 <= 1 <= maxNrofSR_Resources)%Z. unfold maxNrofSR_Resources.
 lia. Qed.
Lemma PUCCH_Config__schedulingRequestResourceToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofSR_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSR_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__schedulingRequestResourceToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__schedulingRequestResourceToAddModList__cond (z : PUCCH_Config__schedulingRequestResourceToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSR_Resources)%Z /\ (list_and SchedulingRequestResourceConfig__cond z) .

Require Import NR.SchedulingRequestResourceId.

Opaque SchedulingRequestResourceId__cond SchedulingRequestResourceId__Format.

Definition PUCCH_Config__schedulingRequestResourceToReleaseList__Type := list SchedulingRequestResourceId__Type.

Lemma PUCCH_Config__schedulingRequestResourceToReleaseList__helper1 : (0 <= 1 <= maxNrofSR_Resources)%Z. unfold maxNrofSR_Resources.
 lia. Qed.
Lemma PUCCH_Config__schedulingRequestResourceToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofSR_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSR_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__schedulingRequestResourceToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__schedulingRequestResourceToReleaseList__cond (z : PUCCH_Config__schedulingRequestResourceToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSR_Resources)%Z /\ (list_and SchedulingRequestResourceId__cond z) .

Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Definition PUCCH_Config__multi_CSI_PUCCH_ResourceList__Type := list PUCCH_ResourceId__Type.

Lemma PUCCH_Config__multi_CSI_PUCCH_ResourceList__helper1 : (0 <= 1 <= 2)%Z.  lia. Qed.
Lemma PUCCH_Config__multi_CSI_PUCCH_ResourceList__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__multi_CSI_PUCCH_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__multi_CSI_PUCCH_ResourceList__cond (z : PUCCH_Config__multi_CSI_PUCCH_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= 2)%Z /\ (list_and PUCCH_ResourceId__cond z) .

Lemma PUCCH_Config__dl_DataToUL_ACK__seq_of__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma PUCCH_Config__dl_DataToUL_ACK__seq_of__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__dl_DataToUL_ACK__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__dl_DataToUL_ACK__seq_of__Type := Z.
Definition PUCCH_Config__dl_DataToUL_ACK__seq_of__cond := (fun z => (0 <= z <= 15)%Z).
Definition PUCCH_Config__dl_DataToUL_ACK__Type := list Z.

Lemma PUCCH_Config__dl_DataToUL_ACK__helper1 : (0 <= 1 <= 8)%Z.  lia. Qed.
Lemma PUCCH_Config__dl_DataToUL_ACK__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__dl_DataToUL_ACK__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__dl_DataToUL_ACK__cond (z : PUCCH_Config__dl_DataToUL_ACK__Type) :=  (1 <= Z.of_nat (length z) <= 8)%Z /\ (list_and PUCCH_Config__dl_DataToUL_ACK__seq_of__cond z) .

Require Import NR.PUCCH_SpatialRelationInfo.

Opaque PUCCH_SpatialRelationInfo__cond PUCCH_SpatialRelationInfo__Format.

Definition PUCCH_Config__spatialRelationInfoToAddModList__Type := list PUCCH_SpatialRelationInfo__Type.

Lemma PUCCH_Config__spatialRelationInfoToAddModList__helper1 : (0 <= 1 <= maxNrofSpatialRelationInfos)%Z. unfold maxNrofSpatialRelationInfos.
 lia. Qed.
Lemma PUCCH_Config__spatialRelationInfoToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofSpatialRelationInfos - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSpatialRelationInfos - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__spatialRelationInfoToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__spatialRelationInfoToAddModList__cond (z : PUCCH_Config__spatialRelationInfoToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSpatialRelationInfos)%Z /\ (list_and PUCCH_SpatialRelationInfo__cond z) .

Require Import NR.PUCCH_SpatialRelationInfoId.

Opaque PUCCH_SpatialRelationInfoId__cond PUCCH_SpatialRelationInfoId__Format.

Definition PUCCH_Config__spatialRelationInfoToReleaseList__Type := list PUCCH_SpatialRelationInfoId__Type.

Lemma PUCCH_Config__spatialRelationInfoToReleaseList__helper1 : (0 <= 1 <= maxNrofSpatialRelationInfos)%Z. unfold maxNrofSpatialRelationInfos.
 lia. Qed.
Lemma PUCCH_Config__spatialRelationInfoToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofSpatialRelationInfos - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSpatialRelationInfos - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__spatialRelationInfoToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__spatialRelationInfoToReleaseList__cond (z : PUCCH_Config__spatialRelationInfoToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSpatialRelationInfos)%Z /\ (list_and PUCCH_SpatialRelationInfoId__cond z) .

Require Import NR.PUCCH_PowerControl.

Opaque PUCCH_PowerControl__cond PUCCH_PowerControl__Format.

Require Import NR.PUCCH_ResourceExt_v1610.

Opaque PUCCH_ResourceExt_v1610__cond PUCCH_ResourceExt_v1610__Format.

Definition PUCCH_Config__ext0O__resourceToAddModListExt_v1610__Type := list PUCCH_ResourceExt_v1610__Type.

Lemma PUCCH_Config__ext0O__resourceToAddModListExt_v1610__helper1 : (0 <= 1 <= maxNrofPUCCH_Resources)%Z. unfold maxNrofPUCCH_Resources.
 lia. Qed.
Lemma PUCCH_Config__ext0O__resourceToAddModListExt_v1610__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__resourceToAddModListExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__resourceToAddModListExt_v1610__cond (z : PUCCH_Config__ext0O__resourceToAddModListExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_Resources)%Z /\ (list_and PUCCH_ResourceExt_v1610__cond z) .

Require Import NR.SetupRelease.
Require Import NR.DL_DataToUL_ACK_r16.
Definition PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__Type := SetupRelease__Type DL_DataToUL_ACK_r16__Type.
Definition PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__cond := SetupRelease__cond _ DL_DataToUL_ACK_r16__cond.
Definition PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__Format : T_Format PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__Type PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__cond := SetupRelease__Format _ _ DL_DataToUL_ACK_r16__Format.
Opaque PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__cond PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.UL_AccessConfigListDCI_1_1_r16.
Definition PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__Type := SetupRelease__Type UL_AccessConfigListDCI_1_1_r16__Type.
Definition PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__cond := SetupRelease__cond _ UL_AccessConfigListDCI_1_1_r16__cond.
Definition PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__Format : T_Format PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__Type PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__cond := SetupRelease__Format _ _ UL_AccessConfigListDCI_1_1_r16__Format.
Opaque PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__cond PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__Format.

Inductive PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Type : Set :=
 | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__n2
 | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__n7
.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__cond := (fun (_ : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Type) => True).
Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__nat__helper.

Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F1 t :=
  match t with
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__n2 => 0
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__n7 => 1
  end.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F2 n :=
  match n with
  | 0 => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__n2
  | 1 => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__n7
  | _ => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__n2
  end.
Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F1F2 : forall x : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Type, (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F1 x <= 1) /\ PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F2 (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F2F1 : forall (y : nat) (H : y <= 1), PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F1 (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Type : Set :=
 | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__n2
 | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__n6
.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__cond := (fun (_ : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Type) => True).
Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__nat__helper.

Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F1 t :=
  match t with
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__n2 => 0
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__n6 => 1
  end.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F2 n :=
  match n with
  | 0 => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__n2
  | 1 => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__n6
  | _ => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__n2
  end.
Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F1F2 : forall x : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Type, (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F1 x <= 1) /\ PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F2 (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F2F1 : forall (y : nat) (H : y <= 1), PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F1 (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F2 y) = y. enum_solve H y. Qed.


Inductive PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type : Set :=
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16 : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Type -> PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16 : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Type -> PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type
.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list : list typ := (
typ_cons PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Type PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__cond ::
typ_cons PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Type PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__cond ::
 nil).
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__cond (c : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type) := 
  match c with
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16 t => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__cond t 
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16 t => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__cond t 
  end.

Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__len_helper1 : to_bit_sz (length PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__len_helper2 : 2 <= length2 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list.
 simpl. lia. Qed.
Require Import NR.SetupRelease.
Require Import NR.DL_DataToUL_ACK_DCI_1_2_r16.
Definition PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__Type := SetupRelease__Type DL_DataToUL_ACK_DCI_1_2_r16__Type.
Definition PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__cond := SetupRelease__cond _ DL_DataToUL_ACK_DCI_1_2_r16__cond.
Definition PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__Format : T_Format PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__Type PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__cond := SetupRelease__Format _ _ DL_DataToUL_ACK_DCI_1_2_r16__Format.
Opaque PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__cond PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__Format.

Lemma PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__Type := Z.
Definition PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__cond := (fun z => (0 <= z <= 3)%Z).
Inductive PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Type : Set :=
 | PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__enabled
.
Definition PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__cond := (fun (_ : PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Type) => True).
Lemma PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__nat__helper.

Definition PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F1 t :=
  match t with
  | PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__enabled => 0
  end.
Definition PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F2 n :=
  match n with
  | 0 => PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__enabled
  | _ => PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__enabled
  end.
Lemma PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F1F2 : forall x : PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Type, (PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F1 x <= 0) /\ PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F2 (PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F1 (PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PUCCH_SpatialRelationInfo.

Opaque PUCCH_SpatialRelationInfo__cond PUCCH_SpatialRelationInfo__Format.

Definition PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__Type := list PUCCH_SpatialRelationInfo__Type.

Lemma PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__helper1 : (0 <= 1 <= maxNrofSpatialRelationInfosDiff_r16)%Z. unfold maxNrofSpatialRelationInfosDiff_r16.
 lia. Qed.
Lemma PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__helper2 : to_bit_sz (Z.to_nat (maxNrofSpatialRelationInfosDiff_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSpatialRelationInfosDiff_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__cond (z : PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSpatialRelationInfosDiff_r16)%Z /\ (list_and PUCCH_SpatialRelationInfo__cond z) .

Require Import NR.PUCCH_SpatialRelationInfoId.

Opaque PUCCH_SpatialRelationInfoId__cond PUCCH_SpatialRelationInfoId__Format.

Definition PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__Type := list PUCCH_SpatialRelationInfoId__Type.

Lemma PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__helper1 : (0 <= 1 <= maxNrofSpatialRelationInfosDiff_r16)%Z. unfold maxNrofSpatialRelationInfosDiff_r16.
 lia. Qed.
Lemma PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__helper2 : to_bit_sz (Z.to_nat (maxNrofSpatialRelationInfosDiff_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSpatialRelationInfosDiff_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__cond (z : PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSpatialRelationInfosDiff_r16)%Z /\ (list_and PUCCH_SpatialRelationInfoId__cond z) .

Require Import NR.PUCCH_SpatialRelationInfoExt_r16.

Opaque PUCCH_SpatialRelationInfoExt_r16__cond PUCCH_SpatialRelationInfoExt_r16__Format.

Definition PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__Type := list PUCCH_SpatialRelationInfoExt_r16__Type.

Lemma PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__helper1 : (0 <= 1 <= maxNrofSpatialRelationInfos_r16)%Z. unfold maxNrofSpatialRelationInfos_r16.
 lia. Qed.
Lemma PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__helper2 : to_bit_sz (Z.to_nat (maxNrofSpatialRelationInfos_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSpatialRelationInfos_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__cond (z : PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSpatialRelationInfos_r16)%Z /\ (list_and PUCCH_SpatialRelationInfoExt_r16__cond z) .

Require Import NR.PUCCH_SpatialRelationInfoId_r16.

Opaque PUCCH_SpatialRelationInfoId_r16__cond PUCCH_SpatialRelationInfoId_r16__Format.

Definition PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__Type := list PUCCH_SpatialRelationInfoId_r16__Type.

Lemma PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__helper1 : (0 <= 1 <= maxNrofSpatialRelationInfos_r16)%Z. unfold maxNrofSpatialRelationInfos_r16.
 lia. Qed.
Lemma PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__helper2 : to_bit_sz (Z.to_nat (maxNrofSpatialRelationInfos_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSpatialRelationInfos_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__cond (z : PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSpatialRelationInfos_r16)%Z /\ (list_and PUCCH_SpatialRelationInfoId_r16__cond z) .

Require Import NR.PUCCH_ResourceGroup_r16.

Opaque PUCCH_ResourceGroup_r16__cond PUCCH_ResourceGroup_r16__Format.

Definition PUCCH_Config__ext0O__resourceGroupToAddModList_r16__Type := list PUCCH_ResourceGroup_r16__Type.

Lemma PUCCH_Config__ext0O__resourceGroupToAddModList_r16__helper1 : (0 <= 1 <= maxNrofPUCCH_ResourceGroups_r16)%Z. unfold maxNrofPUCCH_ResourceGroups_r16.
 lia. Qed.
Lemma PUCCH_Config__ext0O__resourceGroupToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_ResourceGroups_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_ResourceGroups_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__resourceGroupToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__resourceGroupToAddModList_r16__cond (z : PUCCH_Config__ext0O__resourceGroupToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_ResourceGroups_r16)%Z /\ (list_and PUCCH_ResourceGroup_r16__cond z) .

Require Import NR.PUCCH_ResourceGroupId_r16.

Opaque PUCCH_ResourceGroupId_r16__cond PUCCH_ResourceGroupId_r16__Format.

Definition PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__Type := list PUCCH_ResourceGroupId_r16__Type.

Lemma PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofPUCCH_ResourceGroups_r16)%Z. unfold maxNrofPUCCH_ResourceGroups_r16.
 lia. Qed.
Lemma PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPUCCH_ResourceGroups_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUCCH_ResourceGroups_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__cond (z : PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUCCH_ResourceGroups_r16)%Z /\ (list_and PUCCH_ResourceGroupId_r16__cond z) .

Require Import NR.SetupRelease.
Require Import NR.SPS_PUCCH_AN_List_r16.
Definition PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__Type := SetupRelease__Type SPS_PUCCH_AN_List_r16__Type.
Definition PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__cond := SetupRelease__cond _ SPS_PUCCH_AN_List_r16__cond.
Definition PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__Format : T_Format PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__Type PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__cond := SetupRelease__Format _ _ SPS_PUCCH_AN_List_r16__Format.
Opaque PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__cond PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__Format.

Require Import NR.SchedulingRequestResourceConfigExt_v1610.

Opaque SchedulingRequestResourceConfigExt_v1610__cond SchedulingRequestResourceConfigExt_v1610__Format.

Definition PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__Type := list SchedulingRequestResourceConfigExt_v1610__Type.

Lemma PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__helper1 : (0 <= 1 <= maxNrofSR_Resources)%Z. unfold maxNrofSR_Resources.
 lia. Qed.
Lemma PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__helper2 : to_bit_sz (Z.to_nat (maxNrofSR_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSR_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__cond (z : PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSR_Resources)%Z /\ (list_and SchedulingRequestResourceConfigExt_v1610__cond z) .

Record PUCCH_Config__ext0O__Type : Set :=
  make__PUCCH_Config__ext0O__Type {
    PUCCH_Config__ext0O__resourceToAddModListExt_v1610 : option PUCCH_Config__ext0O__resourceToAddModListExt_v1610__Type ;
    PUCCH_Config__ext0O__dl_DataToUL_ACK_r16 : option PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__Type ;
    PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16 : option PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__Type ;
    PUCCH_Config__ext0O__subslotLengthForPUCCH_r16 : option PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type ;
    PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16 : option PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__Type ;
    PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16 : option Z ;
    PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16 : option PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Type ;
    PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610 : option PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__Type ;
    PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610 : option PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__Type ;
    PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610 : option PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__Type ;
    PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610 : option PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__Type ;
    PUCCH_Config__ext0O__resourceGroupToAddModList_r16 : option PUCCH_Config__ext0O__resourceGroupToAddModList_r16__Type ;
    PUCCH_Config__ext0O__resourceGroupToReleaseList_r16 : option PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__Type ;
    PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16 : option PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__Type ;
    PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610 : option PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__Type ;
}.
Definition PUCCH_Config__ext0O__list := (
 Opt PUCCH_Config__ext0O__resourceToAddModListExt_v1610__Type PUCCH_Config__ext0O__resourceToAddModListExt_v1610__cond ::
 Opt PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__Type PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__cond ::
 Opt PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__Type PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__cond ::
 Opt PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__cond ::
 Opt PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__Type PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__cond ::
 Opt Z PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__cond ::
 Opt PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Type PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__cond ::
 Opt PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__Type PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__cond ::
 Opt PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__Type PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__cond ::
 Opt PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__Type PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__cond ::
 Opt PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__Type PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__cond ::
 Opt PUCCH_Config__ext0O__resourceGroupToAddModList_r16__Type PUCCH_Config__ext0O__resourceGroupToAddModList_r16__cond ::
 Opt PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__Type PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__cond ::
 Opt PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__Type PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__cond ::
 Opt PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__Type PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__cond ::
 nil).
Definition PUCCH_Config__ext0O__cond z := 
  opt_cond PUCCH_Config__ext0O__resourceToAddModListExt_v1610__cond (PUCCH_Config__ext0O__resourceToAddModListExt_v1610 z) /\
  opt_cond PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__cond (PUCCH_Config__ext0O__dl_DataToUL_ACK_r16 z) /\
  opt_cond PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__cond (PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16 z) /\
  opt_cond PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__cond (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16 z) /\
  opt_cond PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__cond (PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16 z) /\
  opt_cond PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__cond (PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16 z) /\
  opt_cond PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__cond (PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16 z) /\
  opt_cond PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__cond (PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610 z) /\
  opt_cond PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__cond (PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610 z) /\
  opt_cond PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__cond (PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610 z) /\
  opt_cond PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__cond (PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610 z) /\
  opt_cond PUCCH_Config__ext0O__resourceGroupToAddModList_r16__cond (PUCCH_Config__ext0O__resourceGroupToAddModList_r16 z) /\
  opt_cond PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__cond (PUCCH_Config__ext0O__resourceGroupToReleaseList_r16 z) /\
  opt_cond PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__cond (PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16 z) /\
  opt_cond PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__cond (PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610 z) /\
  True.

Definition PUCCH_Config__ext0__Type := PUCCH_Config__ext0O__Type.
Definition PUCCH_Config__ext0__cond := PUCCH_Config__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_FormatConfig.
Definition PUCCH_Config__ext1O__format0_r17__Type := SetupRelease__Type PUCCH_FormatConfig__Type.
Definition PUCCH_Config__ext1O__format0_r17__cond := SetupRelease__cond _ PUCCH_FormatConfig__cond.
Definition PUCCH_Config__ext1O__format0_r17__Format : T_Format PUCCH_Config__ext1O__format0_r17__Type PUCCH_Config__ext1O__format0_r17__cond := SetupRelease__Format _ _ PUCCH_FormatConfig__Format.
Opaque PUCCH_Config__ext1O__format0_r17__cond PUCCH_Config__ext1O__format0_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_FormatConfigExt_r17.
Definition PUCCH_Config__ext1O__format2Ext_r17__Type := SetupRelease__Type PUCCH_FormatConfigExt_r17__Type.
Definition PUCCH_Config__ext1O__format2Ext_r17__cond := SetupRelease__cond _ PUCCH_FormatConfigExt_r17__cond.
Definition PUCCH_Config__ext1O__format2Ext_r17__Format : T_Format PUCCH_Config__ext1O__format2Ext_r17__Type PUCCH_Config__ext1O__format2Ext_r17__cond := SetupRelease__Format _ _ PUCCH_FormatConfigExt_r17__Format.
Opaque PUCCH_Config__ext1O__format2Ext_r17__cond PUCCH_Config__ext1O__format2Ext_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_FormatConfigExt_r17.
Definition PUCCH_Config__ext1O__format3Ext_r17__Type := SetupRelease__Type PUCCH_FormatConfigExt_r17__Type.
Definition PUCCH_Config__ext1O__format3Ext_r17__cond := SetupRelease__cond _ PUCCH_FormatConfigExt_r17__cond.
Definition PUCCH_Config__ext1O__format3Ext_r17__Format : T_Format PUCCH_Config__ext1O__format3Ext_r17__Type PUCCH_Config__ext1O__format3Ext_r17__cond := SetupRelease__Format _ _ PUCCH_FormatConfigExt_r17__Format.
Opaque PUCCH_Config__ext1O__format3Ext_r17__cond PUCCH_Config__ext1O__format3Ext_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_FormatConfigExt_r17.
Definition PUCCH_Config__ext1O__format4Ext_r17__Type := SetupRelease__Type PUCCH_FormatConfigExt_r17__Type.
Definition PUCCH_Config__ext1O__format4Ext_r17__cond := SetupRelease__cond _ PUCCH_FormatConfigExt_r17__cond.
Definition PUCCH_Config__ext1O__format4Ext_r17__Format : T_Format PUCCH_Config__ext1O__format4Ext_r17__Type PUCCH_Config__ext1O__format4Ext_r17__cond := SetupRelease__Format _ _ PUCCH_FormatConfigExt_r17__Format.
Opaque PUCCH_Config__ext1O__format4Ext_r17__cond PUCCH_Config__ext1O__format4Ext_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.UL_AccessConfigListDCI_1_2_r17.
Definition PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__Type := SetupRelease__Type UL_AccessConfigListDCI_1_2_r17__Type.
Definition PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__cond := SetupRelease__cond _ UL_AccessConfigListDCI_1_2_r17__cond.
Definition PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__Format : T_Format PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__Type PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__cond := SetupRelease__Format _ _ UL_AccessConfigListDCI_1_2_r17__Format.
Opaque PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__cond PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__Format.

Inductive PUCCH_Config__ext1O__mappingPattern_r17__Type : Set :=
 | PUCCH_Config__ext1O__mappingPattern_r17__cyclicMapping
 | PUCCH_Config__ext1O__mappingPattern_r17__sequentialMapping
.
Definition PUCCH_Config__ext1O__mappingPattern_r17__cond := (fun (_ : PUCCH_Config__ext1O__mappingPattern_r17__Type) => True).
Lemma PUCCH_Config__ext1O__mappingPattern_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_Config__ext1O__mappingPattern_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUCCH_Config__ext1O__mappingPattern_r17__nat__helper.

Definition PUCCH_Config__ext1O__mappingPattern_r17__F1 t :=
  match t with
  | PUCCH_Config__ext1O__mappingPattern_r17__cyclicMapping => 0
  | PUCCH_Config__ext1O__mappingPattern_r17__sequentialMapping => 1
  end.
Definition PUCCH_Config__ext1O__mappingPattern_r17__F2 n :=
  match n with
  | 0 => PUCCH_Config__ext1O__mappingPattern_r17__cyclicMapping
  | 1 => PUCCH_Config__ext1O__mappingPattern_r17__sequentialMapping
  | _ => PUCCH_Config__ext1O__mappingPattern_r17__cyclicMapping
  end.
Lemma PUCCH_Config__ext1O__mappingPattern_r17__F1F2 : forall x : PUCCH_Config__ext1O__mappingPattern_r17__Type, (PUCCH_Config__ext1O__mappingPattern_r17__F1 x <= 1) /\ PUCCH_Config__ext1O__mappingPattern_r17__F2 (PUCCH_Config__ext1O__mappingPattern_r17__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_Config__ext1O__mappingPattern_r17__F2F1 : forall (y : nat) (H : y <= 1), PUCCH_Config__ext1O__mappingPattern_r17__F1 (PUCCH_Config__ext1O__mappingPattern_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PUCCH_PowerControlSetInfo_r17.

Opaque PUCCH_PowerControlSetInfo_r17__cond PUCCH_PowerControlSetInfo_r17__Format.

Definition PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__Type := list PUCCH_PowerControlSetInfo_r17__Type.

Lemma PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__helper1 : (0 <= 1 <= maxNrofPowerControlSetInfos_r17)%Z. unfold maxNrofPowerControlSetInfos_r17.
 lia. Qed.
Lemma PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPowerControlSetInfos_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPowerControlSetInfos_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__cond (z : PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPowerControlSetInfos_r17)%Z /\ (list_and PUCCH_PowerControlSetInfo_r17__cond z) .

Require Import NR.PUCCH_PowerControlSetInfoId_r17.

Opaque PUCCH_PowerControlSetInfoId_r17__cond PUCCH_PowerControlSetInfoId_r17__Format.

Definition PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__Type := list PUCCH_PowerControlSetInfoId_r17__Type.

Lemma PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofPowerControlSetInfos_r17)%Z. unfold maxNrofPowerControlSetInfos_r17.
 lia. Qed.
Lemma PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPowerControlSetInfos_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPowerControlSetInfos_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__cond (z : PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPowerControlSetInfos_r17)%Z /\ (list_and PUCCH_PowerControlSetInfoId_r17__cond z) .

Inductive PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Type : Set :=
 | PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__enabled
.
Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__cond := (fun (_ : PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Type) => True).
Lemma PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__nat__helper.

Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F1 t :=
  match t with
  | PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__enabled => 0
  end.
Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F2 n :=
  match n with
  | 0 => PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__enabled
  | _ => PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__enabled
  end.
Lemma PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F1F2 : forall x : PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Type, (PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F1 x <= 0) /\ PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F2 (PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F1 (PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Type : Set :=
 | PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__enabled
.
Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__cond := (fun (_ : PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Type) => True).
Lemma PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__nat__helper.

Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F1 t :=
  match t with
  | PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__enabled => 0
  end.
Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F2 n :=
  match n with
  | 0 => PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__enabled
  | _ => PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__enabled
  end.
Lemma PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F1F2 : forall x : PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Type, (PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F1 x <= 0) /\ PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F2 (PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F1 (PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.DL_DataToUL_ACK_r17.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__Type := SetupRelease__Type DL_DataToUL_ACK_r17__Type.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__cond := SetupRelease__cond _ DL_DataToUL_ACK_r17__cond.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__Format : T_Format PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__Type PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__cond := SetupRelease__Format _ _ DL_DataToUL_ACK_r17__Format.
Opaque PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__cond PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.DL_DataToUL_ACK_DCI_1_2_r17.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__Type := SetupRelease__Type DL_DataToUL_ACK_DCI_1_2_r17__Type.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__cond := SetupRelease__cond _ DL_DataToUL_ACK_DCI_1_2_r17__cond.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__Format : T_Format PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__Type PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__cond := SetupRelease__Format _ _ DL_DataToUL_ACK_DCI_1_2_r17__Format.
Opaque PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__cond PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.UL_AccessConfigListDCI_1_1_r17.
Definition PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__Type := SetupRelease__Type UL_AccessConfigListDCI_1_1_r17__Type.
Definition PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__cond := SetupRelease__cond _ UL_AccessConfigListDCI_1_1_r17__cond.
Definition PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__Format : T_Format PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__Type PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__cond := SetupRelease__Format _ _ UL_AccessConfigListDCI_1_1_r17__Format.
Opaque PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__cond PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__Format.

Require Import NR.SchedulingRequestResourceConfigExt_v1700.

Opaque SchedulingRequestResourceConfigExt_v1700__cond SchedulingRequestResourceConfigExt_v1700__Format.

Definition PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__Type := list SchedulingRequestResourceConfigExt_v1700__Type.

Lemma PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__helper1 : (0 <= 1 <= maxNrofSR_Resources)%Z. unfold maxNrofSR_Resources.
 lia. Qed.
Lemma PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__helper2 : to_bit_sz (Z.to_nat (maxNrofSR_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSR_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__cond (z : PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSR_Resources)%Z /\ (list_and SchedulingRequestResourceConfigExt_v1700__cond z) .

Require Import NR.SetupRelease.
Require Import NR.DMRS_BundlingPUCCH_Config_r17.
Definition PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__Type := SetupRelease__Type DMRS_BundlingPUCCH_Config_r17__Type.
Definition PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__cond := SetupRelease__cond _ DMRS_BundlingPUCCH_Config_r17__cond.
Definition PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__Format : T_Format PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__Type PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__cond := SetupRelease__Format _ _ DMRS_BundlingPUCCH_Config_r17__Format.
Opaque PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__cond PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.DL_DataToUL_ACK_v1700.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__Type := SetupRelease__Type DL_DataToUL_ACK_v1700__Type.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__cond := SetupRelease__cond _ DL_DataToUL_ACK_v1700__cond.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__Format : T_Format PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__Type PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__cond := SetupRelease__Format _ _ DL_DataToUL_ACK_v1700__Format.
Opaque PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__cond PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__Format.

Require Import NR.SetupRelease.
Require Import NR.DL_DataToUL_ACK_MulticastDCI_Format4_1_r17.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__Type := SetupRelease__Type DL_DataToUL_ACK_MulticastDCI_Format4_1_r17__Type.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__cond := SetupRelease__cond _ DL_DataToUL_ACK_MulticastDCI_Format4_1_r17__cond.
Definition PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__Format : T_Format PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__Type PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__cond := SetupRelease__Format _ _ DL_DataToUL_ACK_MulticastDCI_Format4_1_r17__Format.
Opaque PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__cond PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SPS_PUCCH_AN_List_r16.
Definition PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__Type := SetupRelease__Type SPS_PUCCH_AN_List_r16__Type.
Definition PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__cond := SetupRelease__cond _ SPS_PUCCH_AN_List_r16__cond.
Definition PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__Format : T_Format PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__Type PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__cond := SetupRelease__Format _ _ SPS_PUCCH_AN_List_r16__Format.
Opaque PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__cond PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__Format.

Record PUCCH_Config__ext1O__Type : Set :=
  make__PUCCH_Config__ext1O__Type {
    PUCCH_Config__ext1O__format0_r17 : option PUCCH_Config__ext1O__format0_r17__Type ;
    PUCCH_Config__ext1O__format2Ext_r17 : option PUCCH_Config__ext1O__format2Ext_r17__Type ;
    PUCCH_Config__ext1O__format3Ext_r17 : option PUCCH_Config__ext1O__format3Ext_r17__Type ;
    PUCCH_Config__ext1O__format4Ext_r17 : option PUCCH_Config__ext1O__format4Ext_r17__Type ;
    PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17 : option PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__Type ;
    PUCCH_Config__ext1O__mappingPattern_r17 : option PUCCH_Config__ext1O__mappingPattern_r17__Type ;
    PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17 : option PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__Type ;
    PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17 : option PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__Type ;
    PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17 : option PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Type ;
    PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17 : option PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Type ;
    PUCCH_Config__ext1O__dl_DataToUL_ACK_r17 : option PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__Type ;
    PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17 : option PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__Type ;
    PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17 : option PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__Type ;
    PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700 : option PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__Type ;
    PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17 : option PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__Type ;
    PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700 : option PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__Type ;
    PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17 : option PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__Type ;
    PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17 : option PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__Type ;
}.
Definition PUCCH_Config__ext1O__list := (
 Opt PUCCH_Config__ext1O__format0_r17__Type PUCCH_Config__ext1O__format0_r17__cond ::
 Opt PUCCH_Config__ext1O__format2Ext_r17__Type PUCCH_Config__ext1O__format2Ext_r17__cond ::
 Opt PUCCH_Config__ext1O__format3Ext_r17__Type PUCCH_Config__ext1O__format3Ext_r17__cond ::
 Opt PUCCH_Config__ext1O__format4Ext_r17__Type PUCCH_Config__ext1O__format4Ext_r17__cond ::
 Opt PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__Type PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__cond ::
 Opt PUCCH_Config__ext1O__mappingPattern_r17__Type PUCCH_Config__ext1O__mappingPattern_r17__cond ::
 Opt PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__Type PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__cond ::
 Opt PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__Type PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__cond ::
 Opt PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Type PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__cond ::
 Opt PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Type PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__cond ::
 Opt PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__Type PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__cond ::
 Opt PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__Type PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__cond ::
 Opt PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__Type PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__cond ::
 Opt PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__Type PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__cond ::
 Opt PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__Type PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__cond ::
 Opt PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__Type PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__cond ::
 Opt PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__Type PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__cond ::
 Opt PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__Type PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__cond ::
 nil).
Definition PUCCH_Config__ext1O__cond z := 
  opt_cond PUCCH_Config__ext1O__format0_r17__cond (PUCCH_Config__ext1O__format0_r17 z) /\
  opt_cond PUCCH_Config__ext1O__format2Ext_r17__cond (PUCCH_Config__ext1O__format2Ext_r17 z) /\
  opt_cond PUCCH_Config__ext1O__format3Ext_r17__cond (PUCCH_Config__ext1O__format3Ext_r17 z) /\
  opt_cond PUCCH_Config__ext1O__format4Ext_r17__cond (PUCCH_Config__ext1O__format4Ext_r17 z) /\
  opt_cond PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__cond (PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17 z) /\
  opt_cond PUCCH_Config__ext1O__mappingPattern_r17__cond (PUCCH_Config__ext1O__mappingPattern_r17 z) /\
  opt_cond PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__cond (PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17 z) /\
  opt_cond PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__cond (PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17 z) /\
  opt_cond PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__cond (PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17 z) /\
  opt_cond PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__cond (PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17 z) /\
  opt_cond PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__cond (PUCCH_Config__ext1O__dl_DataToUL_ACK_r17 z) /\
  opt_cond PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__cond (PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17 z) /\
  opt_cond PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__cond (PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17 z) /\
  opt_cond PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__cond (PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700 z) /\
  opt_cond PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__cond (PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17 z) /\
  opt_cond PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__cond (PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700 z) /\
  opt_cond PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__cond (PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17 z) /\
  opt_cond PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__cond (PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17 z) /\
  True.

Definition PUCCH_Config__ext1__Type := PUCCH_Config__ext1O__Type.
Definition PUCCH_Config__ext1__cond := PUCCH_Config__ext1O__cond.

Record PUCCH_Config__Type : Set :=
  make__PUCCH_Config__Type {
    PUCCH_Config__resourceSetToAddModList : option PUCCH_Config__resourceSetToAddModList__Type ;
    PUCCH_Config__resourceSetToReleaseList : option PUCCH_Config__resourceSetToReleaseList__Type ;
    PUCCH_Config__resourceToAddModList : option PUCCH_Config__resourceToAddModList__Type ;
    PUCCH_Config__resourceToReleaseList : option PUCCH_Config__resourceToReleaseList__Type ;
    PUCCH_Config__format1 : option PUCCH_Config__format1__Type ;
    PUCCH_Config__format2 : option PUCCH_Config__format2__Type ;
    PUCCH_Config__format3 : option PUCCH_Config__format3__Type ;
    PUCCH_Config__format4 : option PUCCH_Config__format4__Type ;
    PUCCH_Config__schedulingRequestResourceToAddModList : option PUCCH_Config__schedulingRequestResourceToAddModList__Type ;
    PUCCH_Config__schedulingRequestResourceToReleaseList : option PUCCH_Config__schedulingRequestResourceToReleaseList__Type ;
    PUCCH_Config__multi_CSI_PUCCH_ResourceList : option PUCCH_Config__multi_CSI_PUCCH_ResourceList__Type ;
    PUCCH_Config__dl_DataToUL_ACK : option PUCCH_Config__dl_DataToUL_ACK__Type ;
    PUCCH_Config__spatialRelationInfoToAddModList : option PUCCH_Config__spatialRelationInfoToAddModList__Type ;
    PUCCH_Config__spatialRelationInfoToReleaseList : option PUCCH_Config__spatialRelationInfoToReleaseList__Type ;
    PUCCH_Config__pucch_PowerControl : option PUCCH_PowerControl__Type ;
    PUCCH_Config__ext0 : option PUCCH_Config__ext0__Type ;
    PUCCH_Config__ext1 : option PUCCH_Config__ext1__Type ;
}.
Definition PUCCH_Config__root_list : list seq_elem := (
 Opt PUCCH_Config__resourceSetToAddModList__Type PUCCH_Config__resourceSetToAddModList__cond ::
 Opt PUCCH_Config__resourceSetToReleaseList__Type PUCCH_Config__resourceSetToReleaseList__cond ::
 Opt PUCCH_Config__resourceToAddModList__Type PUCCH_Config__resourceToAddModList__cond ::
 Opt PUCCH_Config__resourceToReleaseList__Type PUCCH_Config__resourceToReleaseList__cond ::
 Opt PUCCH_Config__format1__Type PUCCH_Config__format1__cond ::
 Opt PUCCH_Config__format2__Type PUCCH_Config__format2__cond ::
 Opt PUCCH_Config__format3__Type PUCCH_Config__format3__cond ::
 Opt PUCCH_Config__format4__Type PUCCH_Config__format4__cond ::
 Opt PUCCH_Config__schedulingRequestResourceToAddModList__Type PUCCH_Config__schedulingRequestResourceToAddModList__cond ::
 Opt PUCCH_Config__schedulingRequestResourceToReleaseList__Type PUCCH_Config__schedulingRequestResourceToReleaseList__cond ::
 Opt PUCCH_Config__multi_CSI_PUCCH_ResourceList__Type PUCCH_Config__multi_CSI_PUCCH_ResourceList__cond ::
 Opt PUCCH_Config__dl_DataToUL_ACK__Type PUCCH_Config__dl_DataToUL_ACK__cond ::
 Opt PUCCH_Config__spatialRelationInfoToAddModList__Type PUCCH_Config__spatialRelationInfoToAddModList__cond ::
 Opt PUCCH_Config__spatialRelationInfoToReleaseList__Type PUCCH_Config__spatialRelationInfoToReleaseList__cond ::
 Opt PUCCH_PowerControl__Type PUCCH_PowerControl__cond ::
 nil).
Definition PUCCH_Config__ext_list : list typ := (
  typ_cons PUCCH_Config__ext0__Type PUCCH_Config__ext0__cond ::
  typ_cons PUCCH_Config__ext1__Type PUCCH_Config__ext1__cond ::
  nil).
Definition PUCCH_Config__cond (z : PUCCH_Config__Type) := 
(  opt_cond PUCCH_Config__resourceSetToAddModList__cond (PUCCH_Config__resourceSetToAddModList z) /\
  opt_cond PUCCH_Config__resourceSetToReleaseList__cond (PUCCH_Config__resourceSetToReleaseList z) /\
  opt_cond PUCCH_Config__resourceToAddModList__cond (PUCCH_Config__resourceToAddModList z) /\
  opt_cond PUCCH_Config__resourceToReleaseList__cond (PUCCH_Config__resourceToReleaseList z) /\
  opt_cond PUCCH_Config__format1__cond (PUCCH_Config__format1 z) /\
  opt_cond PUCCH_Config__format2__cond (PUCCH_Config__format2 z) /\
  opt_cond PUCCH_Config__format3__cond (PUCCH_Config__format3 z) /\
  opt_cond PUCCH_Config__format4__cond (PUCCH_Config__format4 z) /\
  opt_cond PUCCH_Config__schedulingRequestResourceToAddModList__cond (PUCCH_Config__schedulingRequestResourceToAddModList z) /\
  opt_cond PUCCH_Config__schedulingRequestResourceToReleaseList__cond (PUCCH_Config__schedulingRequestResourceToReleaseList z) /\
  opt_cond PUCCH_Config__multi_CSI_PUCCH_ResourceList__cond (PUCCH_Config__multi_CSI_PUCCH_ResourceList z) /\
  opt_cond PUCCH_Config__dl_DataToUL_ACK__cond (PUCCH_Config__dl_DataToUL_ACK z) /\
  opt_cond PUCCH_Config__spatialRelationInfoToAddModList__cond (PUCCH_Config__spatialRelationInfoToAddModList z) /\
  opt_cond PUCCH_Config__spatialRelationInfoToReleaseList__cond (PUCCH_Config__spatialRelationInfoToReleaseList z) /\
  opt_cond PUCCH_PowerControl__cond (PUCCH_Config__pucch_PowerControl z) /\
  True) /\ 
(  opt_cond PUCCH_Config__ext0__cond (PUCCH_Config__ext0 z) /\
  opt_cond PUCCH_Config__ext1__cond (PUCCH_Config__ext1 z) /\
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
Definition PUCCH_Config__resourceSetToAddModList__Format : T_Format PUCCH_Config__resourceSetToAddModList__Type PUCCH_Config__resourceSetToAddModList__cond := seq_of_format PUCCH_ResourceSet__Format 1 maxNrofPUCCH_ResourceSets PUCCH_Config__resourceSetToAddModList__helper1 PUCCH_Config__resourceSetToAddModList__helper2.

Opaque PUCCH_Config__resourceSetToAddModList__cond PUCCH_Config__resourceSetToAddModList__Format.

Definition PUCCH_Config__resourceSetToReleaseList__Format : T_Format PUCCH_Config__resourceSetToReleaseList__Type PUCCH_Config__resourceSetToReleaseList__cond := seq_of_format PUCCH_ResourceSetId__Format 1 maxNrofPUCCH_ResourceSets PUCCH_Config__resourceSetToReleaseList__helper1 PUCCH_Config__resourceSetToReleaseList__helper2.

Opaque PUCCH_Config__resourceSetToReleaseList__cond PUCCH_Config__resourceSetToReleaseList__Format.

Definition PUCCH_Config__resourceToAddModList__Format : T_Format PUCCH_Config__resourceToAddModList__Type PUCCH_Config__resourceToAddModList__cond := seq_of_format PUCCH_Resource__Format 1 maxNrofPUCCH_Resources PUCCH_Config__resourceToAddModList__helper1 PUCCH_Config__resourceToAddModList__helper2.

Opaque PUCCH_Config__resourceToAddModList__cond PUCCH_Config__resourceToAddModList__Format.

Definition PUCCH_Config__resourceToReleaseList__Format : T_Format PUCCH_Config__resourceToReleaseList__Type PUCCH_Config__resourceToReleaseList__cond := seq_of_format PUCCH_ResourceId__Format 1 maxNrofPUCCH_Resources PUCCH_Config__resourceToReleaseList__helper1 PUCCH_Config__resourceToReleaseList__helper2.

Opaque PUCCH_Config__resourceToReleaseList__cond PUCCH_Config__resourceToReleaseList__Format.

Opaque PUCCH_Config__format1__cond PUCCH_Config__format1__Format.

Opaque PUCCH_Config__format2__cond PUCCH_Config__format2__Format.

Opaque PUCCH_Config__format3__cond PUCCH_Config__format3__Format.

Opaque PUCCH_Config__format4__cond PUCCH_Config__format4__Format.

Definition PUCCH_Config__schedulingRequestResourceToAddModList__Format : T_Format PUCCH_Config__schedulingRequestResourceToAddModList__Type PUCCH_Config__schedulingRequestResourceToAddModList__cond := seq_of_format SchedulingRequestResourceConfig__Format 1 maxNrofSR_Resources PUCCH_Config__schedulingRequestResourceToAddModList__helper1 PUCCH_Config__schedulingRequestResourceToAddModList__helper2.

Opaque PUCCH_Config__schedulingRequestResourceToAddModList__cond PUCCH_Config__schedulingRequestResourceToAddModList__Format.

Definition PUCCH_Config__schedulingRequestResourceToReleaseList__Format : T_Format PUCCH_Config__schedulingRequestResourceToReleaseList__Type PUCCH_Config__schedulingRequestResourceToReleaseList__cond := seq_of_format SchedulingRequestResourceId__Format 1 maxNrofSR_Resources PUCCH_Config__schedulingRequestResourceToReleaseList__helper1 PUCCH_Config__schedulingRequestResourceToReleaseList__helper2.

Opaque PUCCH_Config__schedulingRequestResourceToReleaseList__cond PUCCH_Config__schedulingRequestResourceToReleaseList__Format.

Definition PUCCH_Config__multi_CSI_PUCCH_ResourceList__Format : T_Format PUCCH_Config__multi_CSI_PUCCH_ResourceList__Type PUCCH_Config__multi_CSI_PUCCH_ResourceList__cond := seq_of_format PUCCH_ResourceId__Format 1 2 PUCCH_Config__multi_CSI_PUCCH_ResourceList__helper1 PUCCH_Config__multi_CSI_PUCCH_ResourceList__helper2.

Opaque PUCCH_Config__multi_CSI_PUCCH_ResourceList__cond PUCCH_Config__multi_CSI_PUCCH_ResourceList__Format.

Definition PUCCH_Config__dl_DataToUL_ACK__seq_of__Format : T_Format Z PUCCH_Config__dl_DataToUL_ACK__seq_of__cond :=
 ranged_int_format (0) (15) PUCCH_Config__dl_DataToUL_ACK__seq_of__helper1 PUCCH_Config__dl_DataToUL_ACK__seq_of__helper2.

Opaque PUCCH_Config__dl_DataToUL_ACK__seq_of__cond PUCCH_Config__dl_DataToUL_ACK__seq_of__Format.

Definition PUCCH_Config__dl_DataToUL_ACK__Format : T_Format PUCCH_Config__dl_DataToUL_ACK__Type PUCCH_Config__dl_DataToUL_ACK__cond := seq_of_format PUCCH_Config__dl_DataToUL_ACK__seq_of__Format 1 8 PUCCH_Config__dl_DataToUL_ACK__helper1 PUCCH_Config__dl_DataToUL_ACK__helper2.

Opaque PUCCH_Config__dl_DataToUL_ACK__cond PUCCH_Config__dl_DataToUL_ACK__Format.

Definition PUCCH_Config__spatialRelationInfoToAddModList__Format : T_Format PUCCH_Config__spatialRelationInfoToAddModList__Type PUCCH_Config__spatialRelationInfoToAddModList__cond := seq_of_format PUCCH_SpatialRelationInfo__Format 1 maxNrofSpatialRelationInfos PUCCH_Config__spatialRelationInfoToAddModList__helper1 PUCCH_Config__spatialRelationInfoToAddModList__helper2.

Opaque PUCCH_Config__spatialRelationInfoToAddModList__cond PUCCH_Config__spatialRelationInfoToAddModList__Format.

Definition PUCCH_Config__spatialRelationInfoToReleaseList__Format : T_Format PUCCH_Config__spatialRelationInfoToReleaseList__Type PUCCH_Config__spatialRelationInfoToReleaseList__cond := seq_of_format PUCCH_SpatialRelationInfoId__Format 1 maxNrofSpatialRelationInfos PUCCH_Config__spatialRelationInfoToReleaseList__helper1 PUCCH_Config__spatialRelationInfoToReleaseList__helper2.

Opaque PUCCH_Config__spatialRelationInfoToReleaseList__cond PUCCH_Config__spatialRelationInfoToReleaseList__Format.

Definition PUCCH_Config__ext0O__resourceToAddModListExt_v1610__Format : T_Format PUCCH_Config__ext0O__resourceToAddModListExt_v1610__Type PUCCH_Config__ext0O__resourceToAddModListExt_v1610__cond := seq_of_format PUCCH_ResourceExt_v1610__Format 1 maxNrofPUCCH_Resources PUCCH_Config__ext0O__resourceToAddModListExt_v1610__helper1 PUCCH_Config__ext0O__resourceToAddModListExt_v1610__helper2.

Opaque PUCCH_Config__ext0O__resourceToAddModListExt_v1610__cond PUCCH_Config__ext0O__resourceToAddModListExt_v1610__Format.

Opaque PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__cond PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__Format.

Opaque PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__cond PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__Format.

Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Format : T_Format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__nat__Format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F1 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F2 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F1F2 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__F2F1.

Opaque PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__cond PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Format.

Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Format : T_Format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__nat__Format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F1 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F2 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F1F2 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__F2F1.

Opaque PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__cond PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Format.


Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Format_Type := Eval cbn in get_formats PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Format_list : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Format_Type :=
  (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Format, (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Format, unit__Format)).
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list__Format := Eval compute in choice_format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__len_helper1 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__len_helper2  PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Format_list.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F1 (z : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type) : (choice PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list) :=
  match z with
   | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16 t => existT _ 0 t
  | PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16 t => existT _ 1 t
  end.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__g := (fun n => typ_set (get_nth_typ PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list n)).
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F2 (y : choice PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list) : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__g n -> PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type) with
    | 0 => fun (t : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16__Type) => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__normalCP_r16 t 
    | 1 => fun (t : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16__Type) => PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__extendedCP_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type with end) n0
           end t0).

Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__helper2 :  forall (y : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type), PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__cond y -> choice_cond PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__helper3 :  forall (y : PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type), PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F2 (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__helper4 : (forall b : choice PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list, choice_cond PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list b -> PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__cond (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F2 b) /\ PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F1 (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F1 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F2.
Definition PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Format : T_Format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Type PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__cond :=
  (* Eval compute in *) proj2_format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__cond PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__list__Format PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F1 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__F2 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__helper2 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__helper3 PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__helper4.
Opaque PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__cond PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Format.

Opaque PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__cond PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__Format.

Definition PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__Format : T_Format Z PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__cond :=
 ranged_int_format (0) (3) PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__helper1 PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__helper2.

Opaque PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__cond PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__Format.

Definition PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Format : T_Format PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__nat__Format PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F1 PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F2 PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F1F2 PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__F2F1.

Opaque PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__cond PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Format.

Definition PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__Format : T_Format PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__Type PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__cond := seq_of_format PUCCH_SpatialRelationInfo__Format 1 maxNrofSpatialRelationInfosDiff_r16 PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__helper1 PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__helper2.

Opaque PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__cond PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__Format.

Definition PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__Format : T_Format PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__Type PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__cond := seq_of_format PUCCH_SpatialRelationInfoId__Format 1 maxNrofSpatialRelationInfosDiff_r16 PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__helper1 PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__helper2.

Opaque PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__cond PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__Format.

Definition PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__Format : T_Format PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__Type PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__cond := seq_of_format PUCCH_SpatialRelationInfoExt_r16__Format 1 maxNrofSpatialRelationInfos_r16 PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__helper1 PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__helper2.

Opaque PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__cond PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__Format.

Definition PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__Format : T_Format PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__Type PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__cond := seq_of_format PUCCH_SpatialRelationInfoId_r16__Format 1 maxNrofSpatialRelationInfos_r16 PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__helper1 PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__helper2.

Opaque PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__cond PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__Format.

Definition PUCCH_Config__ext0O__resourceGroupToAddModList_r16__Format : T_Format PUCCH_Config__ext0O__resourceGroupToAddModList_r16__Type PUCCH_Config__ext0O__resourceGroupToAddModList_r16__cond := seq_of_format PUCCH_ResourceGroup_r16__Format 1 maxNrofPUCCH_ResourceGroups_r16 PUCCH_Config__ext0O__resourceGroupToAddModList_r16__helper1 PUCCH_Config__ext0O__resourceGroupToAddModList_r16__helper2.

Opaque PUCCH_Config__ext0O__resourceGroupToAddModList_r16__cond PUCCH_Config__ext0O__resourceGroupToAddModList_r16__Format.

Definition PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__Format : T_Format PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__Type PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__cond := seq_of_format PUCCH_ResourceGroupId_r16__Format 1 maxNrofPUCCH_ResourceGroups_r16 PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__helper1 PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__helper2.

Opaque PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__cond PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__Format.

Opaque PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__cond PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__Format.

Definition PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__Format : T_Format PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__Type PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__cond := seq_of_format SchedulingRequestResourceConfigExt_v1610__Format 1 maxNrofSR_Resources PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__helper1 PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__helper2.

Opaque PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__cond PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__Format.


Definition PUCCH_Config__ext0O__Format_Type := Eval cbn in seq_format_prod PUCCH_Config__ext0O__list.
Definition PUCCH_Config__ext0O__Format_list : PUCCH_Config__ext0O__Format_Type :=
  (PUCCH_Config__ext0O__resourceToAddModListExt_v1610__Format, (PUCCH_Config__ext0O__dl_DataToUL_ACK_r16__Format, (PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16__Format, (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16__Format, (PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16__Format, (PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16__Format, (PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16__Format, (PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610__Format, (PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610__Format, (PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610__Format, (PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610__Format, (PUCCH_Config__ext0O__resourceGroupToAddModList_r16__Format, (PUCCH_Config__ext0O__resourceGroupToReleaseList_r16__Format, (PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16__Format, (PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610__Format, unit_format))))))))))))))).
Definition PUCCH_Config__ext0O__list__Format := (*Eval compute in *) seq_format PUCCH_Config__ext0O__list PUCCH_Config__ext0O__Format_list.
Definition PUCCH_Config__ext0O__F1 z :=
  (PUCCH_Config__ext0O__resourceToAddModListExt_v1610 z, (PUCCH_Config__ext0O__dl_DataToUL_ACK_r16 z, (PUCCH_Config__ext0O__ul_AccessConfigListDCI_1_1_r16 z, (PUCCH_Config__ext0O__subslotLengthForPUCCH_r16 z, (PUCCH_Config__ext0O__dl_DataToUL_ACK_DCI_1_2_r16 z, (PUCCH_Config__ext0O__numberOfBitsForPUCCH_ResourceIndicatorDCI_1_2_r16 z, (PUCCH_Config__ext0O__dmrs_UplinkTransformPrecodingPUCCH_r16 z, (PUCCH_Config__ext0O__spatialRelationInfoToAddModListSizeExt_v1610 z, (PUCCH_Config__ext0O__spatialRelationInfoToReleaseListSizeExt_v1610 z, (PUCCH_Config__ext0O__spatialRelationInfoToAddModListExt_v1610 z, (PUCCH_Config__ext0O__spatialRelationInfoToReleaseListExt_v1610 z, (PUCCH_Config__ext0O__resourceGroupToAddModList_r16 z, (PUCCH_Config__ext0O__resourceGroupToReleaseList_r16 z, (PUCCH_Config__ext0O__sps_PUCCH_AN_List_r16 z, (PUCCH_Config__ext0O__schedulingRequestResourceToAddModListExt_v1610 z, tt))))))))))))))).
Definition PUCCH_Config__ext0O__F2 (y : seq_type PUCCH_Config__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, _)))))))))))))))=>
    make__PUCCH_Config__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14
  end.
Lemma PUCCH_Config__ext0O__F1F2_cond (z : PUCCH_Config__ext0O__Type)
  : PUCCH_Config__ext0O__cond z ->
  (seq_cond PUCCH_Config__ext0O__list (PUCCH_Config__ext0O__F1 z)).
intro H. unfold PUCCH_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma PUCCH_Config__ext0O__F1F2_cond2 (z : PUCCH_Config__ext0O__Type)
 : PUCCH_Config__ext0O__F2 (PUCCH_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_Config__ext0O__F2F1_cond (y : seq_type PUCCH_Config__ext0O__list)
  : seq_cond PUCCH_Config__ext0O__list y ->
 (PUCCH_Config__ext0O__cond (PUCCH_Config__ext0O__F2 y)) /\  PUCCH_Config__ext0O__F1 (PUCCH_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUCCH_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_Config__ext0O__Format : T_Format PUCCH_Config__ext0O__Type PUCCH_Config__ext0O__cond :=
        proj2_format  PUCCH_Config__ext0O__cond PUCCH_Config__ext0O__list__Format
    PUCCH_Config__ext0O__F1 PUCCH_Config__ext0O__F2 PUCCH_Config__ext0O__F1F2_cond  PUCCH_Config__ext0O__F1F2_cond2 PUCCH_Config__ext0O__F2F1_cond.
Opaque PUCCH_Config__ext0O__cond PUCCH_Config__ext0O__Format.

Definition PUCCH_Config__ext0__check_all_none (b : PUCCH_Config__ext0O__Type) : bool :=
match b with 
  | make__PUCCH_Config__ext0O__Type None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition PUCCH_Config__ext0__Format : T_Format PUCCH_Config__ext0__Type PUCCH_Config__ext0__cond :=
  restrict_add_format PUCCH_Config__ext0__check_all_none PUCCH_Config__ext0O__Format.

Opaque PUCCH_Config__ext0__cond PUCCH_Config__ext0__Format.

Opaque PUCCH_Config__ext1O__format0_r17__cond PUCCH_Config__ext1O__format0_r17__Format.

Opaque PUCCH_Config__ext1O__format2Ext_r17__cond PUCCH_Config__ext1O__format2Ext_r17__Format.

Opaque PUCCH_Config__ext1O__format3Ext_r17__cond PUCCH_Config__ext1O__format3Ext_r17__Format.

Opaque PUCCH_Config__ext1O__format4Ext_r17__cond PUCCH_Config__ext1O__format4Ext_r17__Format.

Opaque PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__cond PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__Format.

Definition PUCCH_Config__ext1O__mappingPattern_r17__Format : T_Format PUCCH_Config__ext1O__mappingPattern_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_Config__ext1O__mappingPattern_r17__nat__Format PUCCH_Config__ext1O__mappingPattern_r17__F1 PUCCH_Config__ext1O__mappingPattern_r17__F2 PUCCH_Config__ext1O__mappingPattern_r17__F1F2 PUCCH_Config__ext1O__mappingPattern_r17__F2F1.

Opaque PUCCH_Config__ext1O__mappingPattern_r17__cond PUCCH_Config__ext1O__mappingPattern_r17__Format.

Definition PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__Format : T_Format PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__Type PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__cond := seq_of_format PUCCH_PowerControlSetInfo_r17__Format 1 maxNrofPowerControlSetInfos_r17 PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__helper1 PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__helper2.

Opaque PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__cond PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__Format.

Definition PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__Format : T_Format PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__Type PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__cond := seq_of_format PUCCH_PowerControlSetInfoId_r17__Format 1 maxNrofPowerControlSetInfos_r17 PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__helper1 PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__helper2.

Opaque PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__cond PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__Format.

Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Format : T_Format PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__nat__Format PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F1 PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F2 PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F1F2 PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__F2F1.

Opaque PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__cond PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Format.

Definition PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Format : T_Format PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__nat__Format PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F1 PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F2 PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F1F2 PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__F2F1.

Opaque PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__cond PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Format.

Opaque PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__cond PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__Format.

Opaque PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__cond PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__Format.

Opaque PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__cond PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__Format.

Definition PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__Format : T_Format PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__Type PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__cond := seq_of_format SchedulingRequestResourceConfigExt_v1700__Format 1 maxNrofSR_Resources PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__helper1 PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__helper2.

Opaque PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__cond PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__Format.

Opaque PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__cond PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__Format.

Opaque PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__cond PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__Format.

Opaque PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__cond PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__Format.

Opaque PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__cond PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__Format.


Definition PUCCH_Config__ext1O__Format_Type := Eval cbn in seq_format_prod PUCCH_Config__ext1O__list.
Definition PUCCH_Config__ext1O__Format_list : PUCCH_Config__ext1O__Format_Type :=
  (PUCCH_Config__ext1O__format0_r17__Format, (PUCCH_Config__ext1O__format2Ext_r17__Format, (PUCCH_Config__ext1O__format3Ext_r17__Format, (PUCCH_Config__ext1O__format4Ext_r17__Format, (PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17__Format, (PUCCH_Config__ext1O__mappingPattern_r17__Format, (PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17__Format, (PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17__Format, (PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17__Format, (PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17__Format, (PUCCH_Config__ext1O__dl_DataToUL_ACK_r17__Format, (PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17__Format, (PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17__Format, (PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700__Format, (PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17__Format, (PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700__Format, (PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17__Format, (PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17__Format, unit_format)))))))))))))))))).
Definition PUCCH_Config__ext1O__list__Format := (*Eval compute in *) seq_format PUCCH_Config__ext1O__list PUCCH_Config__ext1O__Format_list.
Definition PUCCH_Config__ext1O__F1 z :=
  (PUCCH_Config__ext1O__format0_r17 z, (PUCCH_Config__ext1O__format2Ext_r17 z, (PUCCH_Config__ext1O__format3Ext_r17 z, (PUCCH_Config__ext1O__format4Ext_r17 z, (PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_2_r17 z, (PUCCH_Config__ext1O__mappingPattern_r17 z, (PUCCH_Config__ext1O__powerControlSetInfoToAddModList_r17 z, (PUCCH_Config__ext1O__powerControlSetInfoToReleaseList_r17 z, (PUCCH_Config__ext1O__secondTPCFieldDCI_1_1_r17 z, (PUCCH_Config__ext1O__secondTPCFieldDCI_1_2_r17 z, (PUCCH_Config__ext1O__dl_DataToUL_ACK_r17 z, (PUCCH_Config__ext1O__dl_DataToUL_ACK_DCI_1_2_r17 z, (PUCCH_Config__ext1O__ul_AccessConfigListDCI_1_1_r17 z, (PUCCH_Config__ext1O__schedulingRequestResourceToAddModListExt_v1700 z, (PUCCH_Config__ext1O__dmrs_BundlingPUCCH_Config_r17 z, (PUCCH_Config__ext1O__dl_DataToUL_ACK_v1700 z, (PUCCH_Config__ext1O__dl_DataToUL_ACK_MulticastDCI_Format4_1_r17 z, (PUCCH_Config__ext1O__sps_PUCCH_AN_ListMulticast_r17 z, tt)))))))))))))))))).
Definition PUCCH_Config__ext1O__F2 (y : seq_type PUCCH_Config__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, _))))))))))))))))))=>
    make__PUCCH_Config__ext1O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17
  end.
Lemma PUCCH_Config__ext1O__F1F2_cond (z : PUCCH_Config__ext1O__Type)
  : PUCCH_Config__ext1O__cond z ->
  (seq_cond PUCCH_Config__ext1O__list (PUCCH_Config__ext1O__F1 z)).
intro H. unfold PUCCH_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma PUCCH_Config__ext1O__F1F2_cond2 (z : PUCCH_Config__ext1O__Type)
 : PUCCH_Config__ext1O__F2 (PUCCH_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_Config__ext1O__F2F1_cond (y : seq_type PUCCH_Config__ext1O__list)
  : seq_cond PUCCH_Config__ext1O__list y ->
 (PUCCH_Config__ext1O__cond (PUCCH_Config__ext1O__F2 y)) /\  PUCCH_Config__ext1O__F1 (PUCCH_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold PUCCH_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_Config__ext1O__Format : T_Format PUCCH_Config__ext1O__Type PUCCH_Config__ext1O__cond :=
        proj2_format  PUCCH_Config__ext1O__cond PUCCH_Config__ext1O__list__Format
    PUCCH_Config__ext1O__F1 PUCCH_Config__ext1O__F2 PUCCH_Config__ext1O__F1F2_cond  PUCCH_Config__ext1O__F1F2_cond2 PUCCH_Config__ext1O__F2F1_cond.
Opaque PUCCH_Config__ext1O__cond PUCCH_Config__ext1O__Format.

Definition PUCCH_Config__ext1__check_all_none (b : PUCCH_Config__ext1O__Type) : bool :=
match b with 
  | make__PUCCH_Config__ext1O__Type None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition PUCCH_Config__ext1__Format : T_Format PUCCH_Config__ext1__Type PUCCH_Config__ext1__cond :=
  restrict_add_format PUCCH_Config__ext1__check_all_none PUCCH_Config__ext1O__Format.

Opaque PUCCH_Config__ext1__cond PUCCH_Config__ext1__Format.


Definition PUCCH_Config__root_Format_Type := Eval cbn in seq_format_prod PUCCH_Config__root_list.
Definition PUCCH_Config__root_Format_list : PUCCH_Config__root_Format_Type :=
  (PUCCH_Config__resourceSetToAddModList__Format, (PUCCH_Config__resourceSetToReleaseList__Format, (PUCCH_Config__resourceToAddModList__Format, (PUCCH_Config__resourceToReleaseList__Format, (PUCCH_Config__format1__Format, (PUCCH_Config__format2__Format, (PUCCH_Config__format3__Format, (PUCCH_Config__format4__Format, (PUCCH_Config__schedulingRequestResourceToAddModList__Format, (PUCCH_Config__schedulingRequestResourceToReleaseList__Format, (PUCCH_Config__multi_CSI_PUCCH_ResourceList__Format, (PUCCH_Config__dl_DataToUL_ACK__Format, (PUCCH_Config__spatialRelationInfoToAddModList__Format, (PUCCH_Config__spatialRelationInfoToReleaseList__Format, (PUCCH_PowerControl__Format, unit_format))))))))))))))).

Definition PUCCH_Config__ext_Format_Type := Eval cbn in get_formats PUCCH_Config__ext_list.
Definition PUCCH_Config__ext_Format_list : PUCCH_Config__ext_Format_Type :=
  (PUCCH_Config__ext0__Format, (PUCCH_Config__ext1__Format, unit__Format)).

Definition PUCCH_Config__list_type : Set := (seq_type PUCCH_Config__root_list) * (seq_ext_type PUCCH_Config__ext_list).
Definition PUCCH_Config__list_cond (z : PUCCH_Config__list_type) : Prop :=
        (seq_cond PUCCH_Config__root_list (fst z)) /\ (seq_ext_cond PUCCH_Config__ext_list (snd z)).
Definition PUCCH_Config__list_format : T_Format PUCCH_Config__list_type PUCCH_Config__list_cond :=
 (* Eval compute in *) seq_ext_format PUCCH_Config__root_list PUCCH_Config__root_Format_list PUCCH_Config__ext_list PUCCH_Config__ext_Format_list.

Opaque PUCCH_Config__list_format.
Definition PUCCH_Config__F1 (z : PUCCH_Config__Type) : PUCCH_Config__list_type :=
  (((PUCCH_Config__resourceSetToAddModList z, (PUCCH_Config__resourceSetToReleaseList z, (PUCCH_Config__resourceToAddModList z, (PUCCH_Config__resourceToReleaseList z, (PUCCH_Config__format1 z, (PUCCH_Config__format2 z, (PUCCH_Config__format3 z, (PUCCH_Config__format4 z, (PUCCH_Config__schedulingRequestResourceToAddModList z, (PUCCH_Config__schedulingRequestResourceToReleaseList z, (PUCCH_Config__multi_CSI_PUCCH_ResourceList z, (PUCCH_Config__dl_DataToUL_ACK z, (PUCCH_Config__spatialRelationInfoToAddModList z, (PUCCH_Config__spatialRelationInfoToReleaseList z, (PUCCH_Config__pucch_PowerControl z, tt)))))))))))))))), (
(PUCCH_Config__ext0 z, (PUCCH_Config__ext1 z, tt)))).
Definition PUCCH_Config__F2 (y : PUCCH_Config__list_type) : PUCCH_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, _))))))))))))))), (i0, (i1, _)))=>
    make__PUCCH_Config__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 i0 i1
  end.
Definition PUCCH_Config__helper1 : (forall a : PUCCH_Config__Type, PUCCH_Config__cond a -> PUCCH_Config__list_cond (PUCCH_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUCCH_Config__helper2 : (forall a : PUCCH_Config__Type, PUCCH_Config__F2 (PUCCH_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUCCH_Config__helper3 : (forall b : PUCCH_Config__list_type, PUCCH_Config__list_cond b -> PUCCH_Config__cond (PUCCH_Config__F2 b) /\ PUCCH_Config__F1 (PUCCH_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUCCH_Config__cond, PUCCH_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUCCH_Config__Format : T_Format PUCCH_Config__Type PUCCH_Config__cond :=
 proj2_format PUCCH_Config__cond PUCCH_Config__list_format  PUCCH_Config__F1 PUCCH_Config__F2 PUCCH_Config__helper1 PUCCH_Config__helper2 PUCCH_Config__helper3.

Opaque PUCCH_Config__cond PUCCH_Config__Format.

