Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ControlResourceSet.

Opaque ControlResourceSet__cond ControlResourceSet__Format.

Definition PDCCH_Config__controlResourceSetToAddModList__Type := list ControlResourceSet__Type.

Lemma PDCCH_Config__controlResourceSetToAddModList__helper1 : (0 <= 1 <= 3)%Z.  lia. Qed.
Lemma PDCCH_Config__controlResourceSetToAddModList__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__controlResourceSetToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__controlResourceSetToAddModList__cond (z : PDCCH_Config__controlResourceSetToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= 3)%Z /\ (list_and ControlResourceSet__cond z) .

Require Import NR.ControlResourceSetId.

Opaque ControlResourceSetId__cond ControlResourceSetId__Format.

Definition PDCCH_Config__controlResourceSetToReleaseList__Type := list ControlResourceSetId__Type.

Lemma PDCCH_Config__controlResourceSetToReleaseList__helper1 : (0 <= 1 <= 3)%Z.  lia. Qed.
Lemma PDCCH_Config__controlResourceSetToReleaseList__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__controlResourceSetToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__controlResourceSetToReleaseList__cond (z : PDCCH_Config__controlResourceSetToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= 3)%Z /\ (list_and ControlResourceSetId__cond z) .

Require Import NR.SearchSpace.

Opaque SearchSpace__cond SearchSpace__Format.

Definition PDCCH_Config__searchSpacesToAddModList__Type := list SearchSpace__Type.

Lemma PDCCH_Config__searchSpacesToAddModList__helper1 : (0 <= 1 <= 10)%Z.  lia. Qed.
Lemma PDCCH_Config__searchSpacesToAddModList__helper2 : to_bit_sz (Z.to_nat (10 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__searchSpacesToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__searchSpacesToAddModList__cond (z : PDCCH_Config__searchSpacesToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= 10)%Z /\ (list_and SearchSpace__cond z) .

Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Definition PDCCH_Config__searchSpacesToReleaseList__Type := list SearchSpaceId__Type.

Lemma PDCCH_Config__searchSpacesToReleaseList__helper1 : (0 <= 1 <= 10)%Z.  lia. Qed.
Lemma PDCCH_Config__searchSpacesToReleaseList__helper2 : to_bit_sz (Z.to_nat (10 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__searchSpacesToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__searchSpacesToReleaseList__cond (z : PDCCH_Config__searchSpacesToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= 10)%Z /\ (list_and SearchSpaceId__cond z) .

Require Import NR.SetupRelease.
Require Import NR.DownlinkPreemption.
Definition PDCCH_Config__downlinkPreemption__Type := SetupRelease__Type DownlinkPreemption__Type.
Definition PDCCH_Config__downlinkPreemption__cond := SetupRelease__cond _ DownlinkPreemption__cond.
Definition PDCCH_Config__downlinkPreemption__Format : T_Format PDCCH_Config__downlinkPreemption__Type PDCCH_Config__downlinkPreemption__cond := SetupRelease__Format _ _ DownlinkPreemption__Format.
Opaque PDCCH_Config__downlinkPreemption__cond PDCCH_Config__downlinkPreemption__Format.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_TPC_CommandConfig.
Definition PDCCH_Config__tpc_PUSCH__Type := SetupRelease__Type PUSCH_TPC_CommandConfig__Type.
Definition PDCCH_Config__tpc_PUSCH__cond := SetupRelease__cond _ PUSCH_TPC_CommandConfig__cond.
Definition PDCCH_Config__tpc_PUSCH__Format : T_Format PDCCH_Config__tpc_PUSCH__Type PDCCH_Config__tpc_PUSCH__cond := SetupRelease__Format _ _ PUSCH_TPC_CommandConfig__Format.
Opaque PDCCH_Config__tpc_PUSCH__cond PDCCH_Config__tpc_PUSCH__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_TPC_CommandConfig.
Definition PDCCH_Config__tpc_PUCCH__Type := SetupRelease__Type PUCCH_TPC_CommandConfig__Type.
Definition PDCCH_Config__tpc_PUCCH__cond := SetupRelease__cond _ PUCCH_TPC_CommandConfig__cond.
Definition PDCCH_Config__tpc_PUCCH__Format : T_Format PDCCH_Config__tpc_PUCCH__Type PDCCH_Config__tpc_PUCCH__cond := SetupRelease__Format _ _ PUCCH_TPC_CommandConfig__Format.
Opaque PDCCH_Config__tpc_PUCCH__cond PDCCH_Config__tpc_PUCCH__Format.

Require Import NR.SetupRelease.
Require Import NR.SRS_TPC_CommandConfig.
Definition PDCCH_Config__tpc_SRS__Type := SetupRelease__Type SRS_TPC_CommandConfig__Type.
Definition PDCCH_Config__tpc_SRS__cond := SetupRelease__cond _ SRS_TPC_CommandConfig__cond.
Definition PDCCH_Config__tpc_SRS__Format : T_Format PDCCH_Config__tpc_SRS__Type PDCCH_Config__tpc_SRS__cond := SetupRelease__Format _ _ SRS_TPC_CommandConfig__Format.
Opaque PDCCH_Config__tpc_SRS__cond PDCCH_Config__tpc_SRS__Format.

Require Import NR.ControlResourceSet.

Opaque ControlResourceSet__cond ControlResourceSet__Format.

Definition PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__Type := list ControlResourceSet__Type.

Lemma PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__helper1 : (0 <= 1 <= 2)%Z.  lia. Qed.
Lemma PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__cond (z : PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= 2)%Z /\ (list_and ControlResourceSet__cond z) .

Require Import NR.ControlResourceSetId_r16.

Opaque ControlResourceSetId_r16__cond ControlResourceSetId_r16__Format.

Definition PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__Type := list ControlResourceSetId_r16__Type.

Lemma PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__helper1 : (0 <= 1 <= 5)%Z.  lia. Qed.
Lemma PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__helper2 : to_bit_sz (Z.to_nat (5 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__cond (z : PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__Type) :=  (1 <= Z.of_nat (length z) <= 5)%Z /\ (list_and ControlResourceSetId_r16__cond z) .

Require Import NR.SearchSpaceExt_r16.

Opaque SearchSpaceExt_r16__cond SearchSpaceExt_r16__Format.

Definition PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__Type := list SearchSpaceExt_r16__Type.

Lemma PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__helper1 : (0 <= 1 <= 10)%Z.  lia. Qed.
Lemma PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__helper2 : to_bit_sz (Z.to_nat (10 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__cond (z : PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__Type) :=  (1 <= Z.of_nat (length z) <= 10)%Z /\ (list_and SearchSpaceExt_r16__cond z) .

Require Import NR.SetupRelease.
Require Import NR.UplinkCancellation_r16.
Definition PDCCH_Config__ext0O__uplinkCancellation_r16__Type := SetupRelease__Type UplinkCancellation_r16__Type.
Definition PDCCH_Config__ext0O__uplinkCancellation_r16__cond := SetupRelease__cond _ UplinkCancellation_r16__cond.
Definition PDCCH_Config__ext0O__uplinkCancellation_r16__Format : T_Format PDCCH_Config__ext0O__uplinkCancellation_r16__Type PDCCH_Config__ext0O__uplinkCancellation_r16__cond := SetupRelease__Format _ _ UplinkCancellation_r16__Format.
Opaque PDCCH_Config__ext0O__uplinkCancellation_r16__cond PDCCH_Config__ext0O__uplinkCancellation_r16__Format.

Inductive PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Type : Set :=
 | PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__r15monitoringcapability
 | PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__r16monitoringcapability
.
Definition PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__cond := (fun (_ : PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Type) => True).
Lemma PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__nat__helper.

Definition PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F1 t :=
  match t with
  | PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__r15monitoringcapability => 0
  | PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__r16monitoringcapability => 1
  end.
Definition PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F2 n :=
  match n with
  | 0 => PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__r15monitoringcapability
  | 1 => PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__r16monitoringcapability
  | _ => PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__r15monitoringcapability
  end.
Lemma PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F1F2 : forall x : PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Type, (PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F1 x <= 1) /\ PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F2 (PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F1 x) = x. imp_solve. Qed.
Lemma PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F2F1 : forall (y : nat) (H : y <= 1), PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F1 (PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SearchSpaceSwitchConfig_r16.

Opaque SearchSpaceSwitchConfig_r16__cond SearchSpaceSwitchConfig_r16__Format.

Record PDCCH_Config__ext0O__Type : Set :=
  make__PDCCH_Config__ext0O__Type {
    PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610 : option PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__Type ;
    PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16 : option PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__Type ;
    PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16 : option PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__Type ;
    PDCCH_Config__ext0O__uplinkCancellation_r16 : option PDCCH_Config__ext0O__uplinkCancellation_r16__Type ;
    PDCCH_Config__ext0O__monitoringCapabilityConfig_r16 : option PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Type ;
    PDCCH_Config__ext0O__searchSpaceSwitchConfig_r16 : option SearchSpaceSwitchConfig_r16__Type ;
}.
Definition PDCCH_Config__ext0O__list := (
 Opt PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__Type PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__cond ::
 Opt PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__Type PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__cond ::
 Opt PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__Type PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__cond ::
 Opt PDCCH_Config__ext0O__uplinkCancellation_r16__Type PDCCH_Config__ext0O__uplinkCancellation_r16__cond ::
 Opt PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Type PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__cond ::
 Opt SearchSpaceSwitchConfig_r16__Type SearchSpaceSwitchConfig_r16__cond ::
 nil).
Definition PDCCH_Config__ext0O__cond z := 
  opt_cond PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__cond (PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610 z) /\
  opt_cond PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__cond (PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16 z) /\
  opt_cond PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__cond (PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16 z) /\
  opt_cond PDCCH_Config__ext0O__uplinkCancellation_r16__cond (PDCCH_Config__ext0O__uplinkCancellation_r16 z) /\
  opt_cond PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__cond (PDCCH_Config__ext0O__monitoringCapabilityConfig_r16 z) /\
  opt_cond SearchSpaceSwitchConfig_r16__cond (PDCCH_Config__ext0O__searchSpaceSwitchConfig_r16 z) /\
  True.

Definition PDCCH_Config__ext0__Type := PDCCH_Config__ext0O__Type.
Definition PDCCH_Config__ext0__cond := PDCCH_Config__ext0O__cond.

Require Import NR.SearchSpaceExt_v1700.

Opaque SearchSpaceExt_v1700__cond SearchSpaceExt_v1700__Format.

Definition PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__Type := list SearchSpaceExt_v1700__Type.

Lemma PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__helper1 : (0 <= 1 <= 10)%Z.  lia. Qed.
Lemma PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__helper2 : to_bit_sz (Z.to_nat (10 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__cond (z : PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__Type) :=  (1 <= Z.of_nat (length z) <= 10)%Z /\ (list_and SearchSpaceExt_v1700__cond z) .

Inductive PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Type : Set :=
 | PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__r17monitoringcapability
.
Definition PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__cond := (fun (_ : PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Type) => True).
Lemma PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__nat__helper.

Definition PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F1 t :=
  match t with
  | PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__r17monitoringcapability => 0
  end.
Definition PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F2 n :=
  match n with
  | 0 => PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__r17monitoringcapability
  | _ => PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__r17monitoringcapability
  end.
Lemma PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F1F2 : forall x : PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Type, (PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F1 x <= 0) /\ PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F2 (PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F1 x) = x. imp_solve. Qed.
Lemma PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F2F1 : forall (y : nat) (H : y <= 0), PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F1 (PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SearchSpaceSwitchConfig_r17.

Opaque SearchSpaceSwitchConfig_r17__cond SearchSpaceSwitchConfig_r17__Format.

Require Import NR.SCS_SpecificDuration_r17.

Opaque SCS_SpecificDuration_r17__cond SCS_SpecificDuration_r17__Format.

Definition PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__Type := list SCS_SpecificDuration_r17__Type.

Lemma PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__helper1 : (0 <= 1 <= 3)%Z.  lia. Qed.
Lemma PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__cond (z : PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__Type) :=  (1 <= Z.of_nat (length z) <= 3)%Z /\ (list_and SCS_SpecificDuration_r17__cond z) .

Record PDCCH_Config__ext1O__Type : Set :=
  make__PDCCH_Config__ext1O__Type {
    PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700 : option PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__Type ;
    PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710 : option PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Type ;
    PDCCH_Config__ext1O__searchSpaceSwitchConfig_r17 : option SearchSpaceSwitchConfig_r17__Type ;
    PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17 : option PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__Type ;
}.
Definition PDCCH_Config__ext1O__list := (
 Opt PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__Type PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__cond ::
 Opt PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Type PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__cond ::
 Opt SearchSpaceSwitchConfig_r17__Type SearchSpaceSwitchConfig_r17__cond ::
 Opt PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__Type PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__cond ::
 nil).
Definition PDCCH_Config__ext1O__cond z := 
  opt_cond PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__cond (PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700 z) /\
  opt_cond PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__cond (PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710 z) /\
  opt_cond SearchSpaceSwitchConfig_r17__cond (PDCCH_Config__ext1O__searchSpaceSwitchConfig_r17 z) /\
  opt_cond PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__cond (PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17 z) /\
  True.

Definition PDCCH_Config__ext1__Type := PDCCH_Config__ext1O__Type.
Definition PDCCH_Config__ext1__cond := PDCCH_Config__ext1O__cond.

Record PDCCH_Config__Type : Set :=
  make__PDCCH_Config__Type {
    PDCCH_Config__controlResourceSetToAddModList : option PDCCH_Config__controlResourceSetToAddModList__Type ;
    PDCCH_Config__controlResourceSetToReleaseList : option PDCCH_Config__controlResourceSetToReleaseList__Type ;
    PDCCH_Config__searchSpacesToAddModList : option PDCCH_Config__searchSpacesToAddModList__Type ;
    PDCCH_Config__searchSpacesToReleaseList : option PDCCH_Config__searchSpacesToReleaseList__Type ;
    PDCCH_Config__downlinkPreemption : option PDCCH_Config__downlinkPreemption__Type ;
    PDCCH_Config__tpc_PUSCH : option PDCCH_Config__tpc_PUSCH__Type ;
    PDCCH_Config__tpc_PUCCH : option PDCCH_Config__tpc_PUCCH__Type ;
    PDCCH_Config__tpc_SRS : option PDCCH_Config__tpc_SRS__Type ;
    PDCCH_Config__ext0 : option PDCCH_Config__ext0__Type ;
    PDCCH_Config__ext1 : option PDCCH_Config__ext1__Type ;
}.
Definition PDCCH_Config__root_list : list seq_elem := (
 Opt PDCCH_Config__controlResourceSetToAddModList__Type PDCCH_Config__controlResourceSetToAddModList__cond ::
 Opt PDCCH_Config__controlResourceSetToReleaseList__Type PDCCH_Config__controlResourceSetToReleaseList__cond ::
 Opt PDCCH_Config__searchSpacesToAddModList__Type PDCCH_Config__searchSpacesToAddModList__cond ::
 Opt PDCCH_Config__searchSpacesToReleaseList__Type PDCCH_Config__searchSpacesToReleaseList__cond ::
 Opt PDCCH_Config__downlinkPreemption__Type PDCCH_Config__downlinkPreemption__cond ::
 Opt PDCCH_Config__tpc_PUSCH__Type PDCCH_Config__tpc_PUSCH__cond ::
 Opt PDCCH_Config__tpc_PUCCH__Type PDCCH_Config__tpc_PUCCH__cond ::
 Opt PDCCH_Config__tpc_SRS__Type PDCCH_Config__tpc_SRS__cond ::
 nil).
Definition PDCCH_Config__ext_list : list typ := (
  typ_cons PDCCH_Config__ext0__Type PDCCH_Config__ext0__cond ::
  typ_cons PDCCH_Config__ext1__Type PDCCH_Config__ext1__cond ::
  nil).
Definition PDCCH_Config__cond (z : PDCCH_Config__Type) := 
(  opt_cond PDCCH_Config__controlResourceSetToAddModList__cond (PDCCH_Config__controlResourceSetToAddModList z) /\
  opt_cond PDCCH_Config__controlResourceSetToReleaseList__cond (PDCCH_Config__controlResourceSetToReleaseList z) /\
  opt_cond PDCCH_Config__searchSpacesToAddModList__cond (PDCCH_Config__searchSpacesToAddModList z) /\
  opt_cond PDCCH_Config__searchSpacesToReleaseList__cond (PDCCH_Config__searchSpacesToReleaseList z) /\
  opt_cond PDCCH_Config__downlinkPreemption__cond (PDCCH_Config__downlinkPreemption z) /\
  opt_cond PDCCH_Config__tpc_PUSCH__cond (PDCCH_Config__tpc_PUSCH z) /\
  opt_cond PDCCH_Config__tpc_PUCCH__cond (PDCCH_Config__tpc_PUCCH z) /\
  opt_cond PDCCH_Config__tpc_SRS__cond (PDCCH_Config__tpc_SRS z) /\
  True) /\ 
(  opt_cond PDCCH_Config__ext0__cond (PDCCH_Config__ext0 z) /\
  opt_cond PDCCH_Config__ext1__cond (PDCCH_Config__ext1 z) /\
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
Definition PDCCH_Config__controlResourceSetToAddModList__Format : T_Format PDCCH_Config__controlResourceSetToAddModList__Type PDCCH_Config__controlResourceSetToAddModList__cond := seq_of_format ControlResourceSet__Format 1 3 PDCCH_Config__controlResourceSetToAddModList__helper1 PDCCH_Config__controlResourceSetToAddModList__helper2.

Opaque PDCCH_Config__controlResourceSetToAddModList__cond PDCCH_Config__controlResourceSetToAddModList__Format.

Definition PDCCH_Config__controlResourceSetToReleaseList__Format : T_Format PDCCH_Config__controlResourceSetToReleaseList__Type PDCCH_Config__controlResourceSetToReleaseList__cond := seq_of_format ControlResourceSetId__Format 1 3 PDCCH_Config__controlResourceSetToReleaseList__helper1 PDCCH_Config__controlResourceSetToReleaseList__helper2.

Opaque PDCCH_Config__controlResourceSetToReleaseList__cond PDCCH_Config__controlResourceSetToReleaseList__Format.

Definition PDCCH_Config__searchSpacesToAddModList__Format : T_Format PDCCH_Config__searchSpacesToAddModList__Type PDCCH_Config__searchSpacesToAddModList__cond := seq_of_format SearchSpace__Format 1 10 PDCCH_Config__searchSpacesToAddModList__helper1 PDCCH_Config__searchSpacesToAddModList__helper2.

Opaque PDCCH_Config__searchSpacesToAddModList__cond PDCCH_Config__searchSpacesToAddModList__Format.

Definition PDCCH_Config__searchSpacesToReleaseList__Format : T_Format PDCCH_Config__searchSpacesToReleaseList__Type PDCCH_Config__searchSpacesToReleaseList__cond := seq_of_format SearchSpaceId__Format 1 10 PDCCH_Config__searchSpacesToReleaseList__helper1 PDCCH_Config__searchSpacesToReleaseList__helper2.

Opaque PDCCH_Config__searchSpacesToReleaseList__cond PDCCH_Config__searchSpacesToReleaseList__Format.

Opaque PDCCH_Config__downlinkPreemption__cond PDCCH_Config__downlinkPreemption__Format.

Opaque PDCCH_Config__tpc_PUSCH__cond PDCCH_Config__tpc_PUSCH__Format.

Opaque PDCCH_Config__tpc_PUCCH__cond PDCCH_Config__tpc_PUCCH__Format.

Opaque PDCCH_Config__tpc_SRS__cond PDCCH_Config__tpc_SRS__Format.

Definition PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__Format : T_Format PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__Type PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__cond := seq_of_format ControlResourceSet__Format 1 2 PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__helper1 PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__helper2.

Opaque PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__cond PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__Format.

Definition PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__Format : T_Format PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__Type PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__cond := seq_of_format ControlResourceSetId_r16__Format 1 5 PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__helper1 PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__helper2.

Opaque PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__cond PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__Format.

Definition PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__Format : T_Format PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__Type PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__cond := seq_of_format SearchSpaceExt_r16__Format 1 10 PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__helper1 PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__helper2.

Opaque PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__cond PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__Format.

Opaque PDCCH_Config__ext0O__uplinkCancellation_r16__cond PDCCH_Config__ext0O__uplinkCancellation_r16__Format.

Definition PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Format : T_Format PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__nat__Format PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F1 PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F2 PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F1F2 PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__F2F1.

Opaque PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__cond PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Format.


Definition PDCCH_Config__ext0O__Format_Type := Eval cbn in seq_format_prod PDCCH_Config__ext0O__list.
Definition PDCCH_Config__ext0O__Format_list : PDCCH_Config__ext0O__Format_Type :=
  (PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610__Format, (PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16__Format, (PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16__Format, (PDCCH_Config__ext0O__uplinkCancellation_r16__Format, (PDCCH_Config__ext0O__monitoringCapabilityConfig_r16__Format, (SearchSpaceSwitchConfig_r16__Format, unit_format)))))).
Definition PDCCH_Config__ext0O__list__Format := (*Eval compute in *) seq_format PDCCH_Config__ext0O__list PDCCH_Config__ext0O__Format_list.
Definition PDCCH_Config__ext0O__F1 z :=
  (PDCCH_Config__ext0O__controlResourceSetToAddModListSizeExt_v1610 z, (PDCCH_Config__ext0O__controlResourceSetToReleaseListSizeExt_r16 z, (PDCCH_Config__ext0O__searchSpacesToAddModListExt_r16 z, (PDCCH_Config__ext0O__uplinkCancellation_r16 z, (PDCCH_Config__ext0O__monitoringCapabilityConfig_r16 z, (PDCCH_Config__ext0O__searchSpaceSwitchConfig_r16 z, tt)))))).
Definition PDCCH_Config__ext0O__F2 (y : seq_type PDCCH_Config__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__PDCCH_Config__ext0O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma PDCCH_Config__ext0O__F1F2_cond (z : PDCCH_Config__ext0O__Type)
  : PDCCH_Config__ext0O__cond z ->
  (seq_cond PDCCH_Config__ext0O__list (PDCCH_Config__ext0O__F1 z)).
intro H. unfold PDCCH_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma PDCCH_Config__ext0O__F1F2_cond2 (z : PDCCH_Config__ext0O__Type)
 : PDCCH_Config__ext0O__F2 (PDCCH_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_Config__ext0O__F2F1_cond (y : seq_type PDCCH_Config__ext0O__list)
  : seq_cond PDCCH_Config__ext0O__list y ->
 (PDCCH_Config__ext0O__cond (PDCCH_Config__ext0O__F2 y)) /\  PDCCH_Config__ext0O__F1 (PDCCH_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold PDCCH_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_Config__ext0O__Format : T_Format PDCCH_Config__ext0O__Type PDCCH_Config__ext0O__cond :=
        proj2_format  PDCCH_Config__ext0O__cond PDCCH_Config__ext0O__list__Format
    PDCCH_Config__ext0O__F1 PDCCH_Config__ext0O__F2 PDCCH_Config__ext0O__F1F2_cond  PDCCH_Config__ext0O__F1F2_cond2 PDCCH_Config__ext0O__F2F1_cond.
Opaque PDCCH_Config__ext0O__cond PDCCH_Config__ext0O__Format.

Definition PDCCH_Config__ext0__check_all_none (b : PDCCH_Config__ext0O__Type) : bool :=
match b with 
  | make__PDCCH_Config__ext0O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition PDCCH_Config__ext0__Format : T_Format PDCCH_Config__ext0__Type PDCCH_Config__ext0__cond :=
  restrict_add_format PDCCH_Config__ext0__check_all_none PDCCH_Config__ext0O__Format.

Opaque PDCCH_Config__ext0__cond PDCCH_Config__ext0__Format.

Definition PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__Format : T_Format PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__Type PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__cond := seq_of_format SearchSpaceExt_v1700__Format 1 10 PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__helper1 PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__helper2.

Opaque PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__cond PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__Format.

Definition PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Format : T_Format PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__nat__Format PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F1 PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F2 PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F1F2 PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__F2F1.

Opaque PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__cond PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Format.

Definition PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__Format : T_Format PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__Type PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__cond := seq_of_format SCS_SpecificDuration_r17__Format 1 3 PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__helper1 PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__helper2.

Opaque PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__cond PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__Format.


Definition PDCCH_Config__ext1O__Format_Type := Eval cbn in seq_format_prod PDCCH_Config__ext1O__list.
Definition PDCCH_Config__ext1O__Format_list : PDCCH_Config__ext1O__Format_Type :=
  (PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700__Format, (PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710__Format, (SearchSpaceSwitchConfig_r17__Format, (PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17__Format, unit_format)))).
Definition PDCCH_Config__ext1O__list__Format := (*Eval compute in *) seq_format PDCCH_Config__ext1O__list PDCCH_Config__ext1O__Format_list.
Definition PDCCH_Config__ext1O__F1 z :=
  (PDCCH_Config__ext1O__searchSpacesToAddModListExt_v1700 z, (PDCCH_Config__ext1O__monitoringCapabilityConfig_v1710 z, (PDCCH_Config__ext1O__searchSpaceSwitchConfig_r17 z, (PDCCH_Config__ext1O__pdcch_SkippingDurationList_r17 z, tt)))).
Definition PDCCH_Config__ext1O__F2 (y : seq_type PDCCH_Config__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PDCCH_Config__ext1O__Type i0 i1 i2 i3
  end.
Lemma PDCCH_Config__ext1O__F1F2_cond (z : PDCCH_Config__ext1O__Type)
  : PDCCH_Config__ext1O__cond z ->
  (seq_cond PDCCH_Config__ext1O__list (PDCCH_Config__ext1O__F1 z)).
intro H. unfold PDCCH_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma PDCCH_Config__ext1O__F1F2_cond2 (z : PDCCH_Config__ext1O__Type)
 : PDCCH_Config__ext1O__F2 (PDCCH_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_Config__ext1O__F2F1_cond (y : seq_type PDCCH_Config__ext1O__list)
  : seq_cond PDCCH_Config__ext1O__list y ->
 (PDCCH_Config__ext1O__cond (PDCCH_Config__ext1O__F2 y)) /\  PDCCH_Config__ext1O__F1 (PDCCH_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold PDCCH_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_Config__ext1O__Format : T_Format PDCCH_Config__ext1O__Type PDCCH_Config__ext1O__cond :=
        proj2_format  PDCCH_Config__ext1O__cond PDCCH_Config__ext1O__list__Format
    PDCCH_Config__ext1O__F1 PDCCH_Config__ext1O__F2 PDCCH_Config__ext1O__F1F2_cond  PDCCH_Config__ext1O__F1F2_cond2 PDCCH_Config__ext1O__F2F1_cond.
Opaque PDCCH_Config__ext1O__cond PDCCH_Config__ext1O__Format.

Definition PDCCH_Config__ext1__check_all_none (b : PDCCH_Config__ext1O__Type) : bool :=
match b with 
  | make__PDCCH_Config__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition PDCCH_Config__ext1__Format : T_Format PDCCH_Config__ext1__Type PDCCH_Config__ext1__cond :=
  restrict_add_format PDCCH_Config__ext1__check_all_none PDCCH_Config__ext1O__Format.

Opaque PDCCH_Config__ext1__cond PDCCH_Config__ext1__Format.


Definition PDCCH_Config__root_Format_Type := Eval cbn in seq_format_prod PDCCH_Config__root_list.
Definition PDCCH_Config__root_Format_list : PDCCH_Config__root_Format_Type :=
  (PDCCH_Config__controlResourceSetToAddModList__Format, (PDCCH_Config__controlResourceSetToReleaseList__Format, (PDCCH_Config__searchSpacesToAddModList__Format, (PDCCH_Config__searchSpacesToReleaseList__Format, (PDCCH_Config__downlinkPreemption__Format, (PDCCH_Config__tpc_PUSCH__Format, (PDCCH_Config__tpc_PUCCH__Format, (PDCCH_Config__tpc_SRS__Format, unit_format)))))))).

Definition PDCCH_Config__ext_Format_Type := Eval cbn in get_formats PDCCH_Config__ext_list.
Definition PDCCH_Config__ext_Format_list : PDCCH_Config__ext_Format_Type :=
  (PDCCH_Config__ext0__Format, (PDCCH_Config__ext1__Format, unit__Format)).

Definition PDCCH_Config__list_type : Set := (seq_type PDCCH_Config__root_list) * (seq_ext_type PDCCH_Config__ext_list).
Definition PDCCH_Config__list_cond (z : PDCCH_Config__list_type) : Prop :=
        (seq_cond PDCCH_Config__root_list (fst z)) /\ (seq_ext_cond PDCCH_Config__ext_list (snd z)).
Definition PDCCH_Config__list_format : T_Format PDCCH_Config__list_type PDCCH_Config__list_cond :=
 (* Eval compute in *) seq_ext_format PDCCH_Config__root_list PDCCH_Config__root_Format_list PDCCH_Config__ext_list PDCCH_Config__ext_Format_list.

Opaque PDCCH_Config__list_format.
Definition PDCCH_Config__F1 (z : PDCCH_Config__Type) : PDCCH_Config__list_type :=
  (((PDCCH_Config__controlResourceSetToAddModList z, (PDCCH_Config__controlResourceSetToReleaseList z, (PDCCH_Config__searchSpacesToAddModList z, (PDCCH_Config__searchSpacesToReleaseList z, (PDCCH_Config__downlinkPreemption z, (PDCCH_Config__tpc_PUSCH z, (PDCCH_Config__tpc_PUCCH z, (PDCCH_Config__tpc_SRS z, tt))))))))), (
(PDCCH_Config__ext0 z, (PDCCH_Config__ext1 z, tt)))).
Definition PDCCH_Config__F2 (y : PDCCH_Config__list_type) : PDCCH_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, (i1, _)))=>
    make__PDCCH_Config__Type j0 j1 j2 j3 j4 j5 j6 j7 i0 i1
  end.
Definition PDCCH_Config__helper1 : (forall a : PDCCH_Config__Type, PDCCH_Config__cond a -> PDCCH_Config__list_cond (PDCCH_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDCCH_Config__helper2 : (forall a : PDCCH_Config__Type, PDCCH_Config__F2 (PDCCH_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDCCH_Config__helper3 : (forall b : PDCCH_Config__list_type, PDCCH_Config__list_cond b -> PDCCH_Config__cond (PDCCH_Config__F2 b) /\ PDCCH_Config__F1 (PDCCH_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDCCH_Config__cond, PDCCH_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDCCH_Config__Format : T_Format PDCCH_Config__Type PDCCH_Config__cond :=
 proj2_format PDCCH_Config__cond PDCCH_Config__list_format  PDCCH_Config__F1 PDCCH_Config__F2 PDCCH_Config__helper1 PDCCH_Config__helper2 PDCCH_Config__helper3.

Opaque PDCCH_Config__cond PDCCH_Config__Format.

