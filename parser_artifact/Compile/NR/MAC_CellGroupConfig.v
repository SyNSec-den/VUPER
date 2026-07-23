Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.DRX_Config.
Definition MAC_CellGroupConfig__drx_Config__Type := SetupRelease__Type DRX_Config__Type.
Definition MAC_CellGroupConfig__drx_Config__cond := SetupRelease__cond _ DRX_Config__cond.
Definition MAC_CellGroupConfig__drx_Config__Format : T_Format MAC_CellGroupConfig__drx_Config__Type MAC_CellGroupConfig__drx_Config__cond := SetupRelease__Format _ _ DRX_Config__Format.
Opaque MAC_CellGroupConfig__drx_Config__cond MAC_CellGroupConfig__drx_Config__Format.

Require Import NR.SchedulingRequestConfig.

Opaque SchedulingRequestConfig__cond SchedulingRequestConfig__Format.

Require Import NR.BSR_Config.

Opaque BSR_Config__cond BSR_Config__Format.

Require Import NR.TAG_Config.

Opaque TAG_Config__cond TAG_Config__Format.

Require Import NR.SetupRelease.
Require Import NR.PHR_Config.
Definition MAC_CellGroupConfig__phr_Config__Type := SetupRelease__Type PHR_Config__Type.
Definition MAC_CellGroupConfig__phr_Config__cond := SetupRelease__cond _ PHR_Config__cond.
Definition MAC_CellGroupConfig__phr_Config__Format : T_Format MAC_CellGroupConfig__phr_Config__Type MAC_CellGroupConfig__phr_Config__cond := SetupRelease__Format _ _ PHR_Config__Format.
Opaque MAC_CellGroupConfig__phr_Config__cond MAC_CellGroupConfig__phr_Config__Format.

Require Import NR.SetupRelease.
Require Import NR.DataInactivityTimer.
Definition MAC_CellGroupConfig__ext0O__dataInactivityTimer__Type := SetupRelease__Type DataInactivityTimer__Type.
Definition MAC_CellGroupConfig__ext0O__dataInactivityTimer__cond := SetupRelease__cond _ DataInactivityTimer__cond.
Definition MAC_CellGroupConfig__ext0O__dataInactivityTimer__Format : T_Format MAC_CellGroupConfig__ext0O__dataInactivityTimer__Type MAC_CellGroupConfig__ext0O__dataInactivityTimer__cond := SetupRelease__Format _ _ DataInactivityTimer__Format.
Opaque MAC_CellGroupConfig__ext0O__dataInactivityTimer__cond MAC_CellGroupConfig__ext0O__dataInactivityTimer__Format.

Record MAC_CellGroupConfig__ext0O__Type : Set :=
  make__MAC_CellGroupConfig__ext0O__Type {
    MAC_CellGroupConfig__ext0O__csi_Mask : option bool ;
    MAC_CellGroupConfig__ext0O__dataInactivityTimer : option MAC_CellGroupConfig__ext0O__dataInactivityTimer__Type ;
}.
Definition MAC_CellGroupConfig__ext0O__list := (
 Opt bool (fun _ => True) ::
 Opt MAC_CellGroupConfig__ext0O__dataInactivityTimer__Type MAC_CellGroupConfig__ext0O__dataInactivityTimer__cond ::
 nil).
Definition MAC_CellGroupConfig__ext0O__cond z := 
  opt_cond (fun _ => True) (MAC_CellGroupConfig__ext0O__csi_Mask z) /\
  opt_cond MAC_CellGroupConfig__ext0O__dataInactivityTimer__cond (MAC_CellGroupConfig__ext0O__dataInactivityTimer z) /\
  True.

Definition MAC_CellGroupConfig__ext0__Type := MAC_CellGroupConfig__ext0O__Type.
Definition MAC_CellGroupConfig__ext0__cond := MAC_CellGroupConfig__ext0O__cond.

Inductive MAC_CellGroupConfig__ext1O__usePreBSR_r16__Type : Set :=
 | MAC_CellGroupConfig__ext1O__usePreBSR_r16__true
.
Definition MAC_CellGroupConfig__ext1O__usePreBSR_r16__cond := (fun (_ : MAC_CellGroupConfig__ext1O__usePreBSR_r16__Type) => True).
Lemma MAC_CellGroupConfig__ext1O__usePreBSR_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_CellGroupConfig__ext1O__usePreBSR_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_CellGroupConfig__ext1O__usePreBSR_r16__nat__helper.

Definition MAC_CellGroupConfig__ext1O__usePreBSR_r16__F1 t :=
  match t with
  | MAC_CellGroupConfig__ext1O__usePreBSR_r16__true => 0
  end.
Definition MAC_CellGroupConfig__ext1O__usePreBSR_r16__F2 n :=
  match n with
  | 0 => MAC_CellGroupConfig__ext1O__usePreBSR_r16__true
  | _ => MAC_CellGroupConfig__ext1O__usePreBSR_r16__true
  end.
Lemma MAC_CellGroupConfig__ext1O__usePreBSR_r16__F1F2 : forall x : MAC_CellGroupConfig__ext1O__usePreBSR_r16__Type, (MAC_CellGroupConfig__ext1O__usePreBSR_r16__F1 x <= 0) /\ MAC_CellGroupConfig__ext1O__usePreBSR_r16__F2 (MAC_CellGroupConfig__ext1O__usePreBSR_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_CellGroupConfig__ext1O__usePreBSR_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_CellGroupConfig__ext1O__usePreBSR_r16__F1 (MAC_CellGroupConfig__ext1O__usePreBSR_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Inductive MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Type : Set :=
 | MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__enabled
.
Definition MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__cond := (fun (_ : MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Type) => True).
Lemma MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__nat__helper.

Definition MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F1 t :=
  match t with
  | MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__enabled => 0
  end.
Definition MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F2 n :=
  match n with
  | 0 => MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__enabled
  | _ => MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__enabled
  end.
Lemma MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F1F2 : forall x : MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Type, (MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F1 x <= 0) /\ MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F2 (MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F1 (MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Require Import NR.SetupRelease.
Require Import NR.DRX_ConfigSecondaryGroup_r16.
Definition MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__Type := SetupRelease__Type DRX_ConfigSecondaryGroup_r16__Type.
Definition MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__cond := SetupRelease__cond _ DRX_ConfigSecondaryGroup_r16__cond.
Definition MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__Format : T_Format MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__Type MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__cond := SetupRelease__Format _ _ DRX_ConfigSecondaryGroup_r16__Format.
Opaque MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__cond MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__Format.

Record MAC_CellGroupConfig__ext1O__Type : Set :=
  make__MAC_CellGroupConfig__ext1O__Type {
    MAC_CellGroupConfig__ext1O__usePreBSR_r16 : option MAC_CellGroupConfig__ext1O__usePreBSR_r16__Type ;
    MAC_CellGroupConfig__ext1O__schedulingRequestID_LBT_SCell_r16 : option SchedulingRequestId__Type ;
    MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16 : option MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Type ;
    MAC_CellGroupConfig__ext1O__schedulingRequestID_BFR_SCell_r16 : option SchedulingRequestId__Type ;
    MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16 : option MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__Type ;
}.
Definition MAC_CellGroupConfig__ext1O__list := (
 Opt MAC_CellGroupConfig__ext1O__usePreBSR_r16__Type MAC_CellGroupConfig__ext1O__usePreBSR_r16__cond ::
 Opt SchedulingRequestId__Type SchedulingRequestId__cond ::
 Opt MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Type MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__cond ::
 Opt SchedulingRequestId__Type SchedulingRequestId__cond ::
 Opt MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__Type MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__cond ::
 nil).
Definition MAC_CellGroupConfig__ext1O__cond z := 
  opt_cond MAC_CellGroupConfig__ext1O__usePreBSR_r16__cond (MAC_CellGroupConfig__ext1O__usePreBSR_r16 z) /\
  opt_cond SchedulingRequestId__cond (MAC_CellGroupConfig__ext1O__schedulingRequestID_LBT_SCell_r16 z) /\
  opt_cond MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__cond (MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16 z) /\
  opt_cond SchedulingRequestId__cond (MAC_CellGroupConfig__ext1O__schedulingRequestID_BFR_SCell_r16 z) /\
  opt_cond MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__cond (MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16 z) /\
  True.

Definition MAC_CellGroupConfig__ext1__Type := MAC_CellGroupConfig__ext1O__Type.
Definition MAC_CellGroupConfig__ext1__cond := MAC_CellGroupConfig__ext1O__cond.

Inductive MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Type : Set :=
 | MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__true
.
Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__cond := (fun (_ : MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Type) => True).
Lemma MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__nat__helper.

Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F1 t :=
  match t with
  | MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__true => 0
  end.
Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F2 n :=
  match n with
  | 0 => MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__true
  | _ => MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__true
  end.
Lemma MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F1F2 : forall x : MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Type, (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F1 x <= 0) /\ MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F2 (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F1 (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Type : Set :=
 | MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__true
.
Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__cond := (fun (_ : MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Type) => True).
Lemma MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__nat__helper.

Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F1 t :=
  match t with
  | MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__true => 0
  end.
Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F2 n :=
  match n with
  | 0 => MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__true
  | _ => MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__true
  end.
Lemma MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F1F2 : forall x : MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Type, (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F1 x <= 0) /\ MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F2 (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F1 (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F2 y) = y. enum_solve H y. Qed.

Record MAC_CellGroupConfig__ext2O__Type : Set :=
  make__MAC_CellGroupConfig__ext2O__Type {
    MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16 : option MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Type ;
    MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16 : option MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Type ;
}.
Definition MAC_CellGroupConfig__ext2O__list := (
 Opt MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Type MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__cond ::
 Opt MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Type MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__cond ::
 nil).
Definition MAC_CellGroupConfig__ext2O__cond z := 
  opt_cond MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__cond (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16 z) /\
  opt_cond MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__cond (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16 z) /\
  True.

Definition MAC_CellGroupConfig__ext2__Type := MAC_CellGroupConfig__ext2O__Type.
Definition MAC_CellGroupConfig__ext2__cond := MAC_CellGroupConfig__ext2O__cond.

Inductive MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Type : Set :=
 | MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__enabled
.
Definition MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__cond := (fun (_ : MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Type) => True).
Lemma MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__nat__helper.

Definition MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F1 t :=
  match t with
  | MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__enabled => 0
  end.
Definition MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F2 n :=
  match n with
  | 0 => MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__enabled
  | _ => MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__enabled
  end.
Lemma MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F1F2 : forall x : MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Type, (MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F1 x <= 0) /\ MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F2 (MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F1 (MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.DRX_ConfigSL_r17.
Definition MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__Type := SetupRelease__Type DRX_ConfigSL_r17__Type.
Definition MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__cond := SetupRelease__cond _ DRX_ConfigSL_r17__cond.
Definition MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__Format : T_Format MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__Type MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__cond := SetupRelease__Format _ _ DRX_ConfigSL_r17__Format.
Opaque MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__cond MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.DRX_ConfigExt_v1700.
Definition MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__Type := SetupRelease__Type DRX_ConfigExt_v1700__Type.
Definition MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__cond := SetupRelease__cond _ DRX_ConfigExt_v1700__cond.
Definition MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__Format : T_Format MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__Type MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__cond := SetupRelease__Format _ _ DRX_ConfigExt_v1700__Format.
Opaque MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__cond MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__Format.

Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Require Import NR.SchedulingRequestConfig_v1700.

Opaque SchedulingRequestConfig_v1700__cond SchedulingRequestConfig_v1700__Format.

Require Import NR.SetupRelease.
Require Import NR.TAR_Config_r17.
Definition MAC_CellGroupConfig__ext3O__tar_Config_r17__Type := SetupRelease__Type TAR_Config_r17__Type.
Definition MAC_CellGroupConfig__ext3O__tar_Config_r17__cond := SetupRelease__cond _ TAR_Config_r17__cond.
Definition MAC_CellGroupConfig__ext3O__tar_Config_r17__Format : T_Format MAC_CellGroupConfig__ext3O__tar_Config_r17__Type MAC_CellGroupConfig__ext3O__tar_Config_r17__cond := SetupRelease__Format _ _ TAR_Config_r17__Format.
Opaque MAC_CellGroupConfig__ext3O__tar_Config_r17__cond MAC_CellGroupConfig__ext3O__tar_Config_r17__Format.

Require Import NR.MBS_RNTI_SpecificConfig_r17.

Opaque MBS_RNTI_SpecificConfig_r17__cond MBS_RNTI_SpecificConfig_r17__Format.

Definition MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__Type := list MBS_RNTI_SpecificConfig_r17__Type.

Lemma MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__helper1 : (0 <= 1 <= maxG_RNTI_r17)%Z. unfold maxG_RNTI_r17.
 lia. Qed.
Lemma MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxG_RNTI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxG_RNTI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__cond (z : MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxG_RNTI_r17)%Z /\ (list_and MBS_RNTI_SpecificConfig_r17__cond z) .

Require Import NR.MBS_RNTI_SpecificConfigId_r17.

Opaque MBS_RNTI_SpecificConfigId_r17__cond MBS_RNTI_SpecificConfigId_r17__Format.

Definition MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__Type := list MBS_RNTI_SpecificConfigId_r17__Type.

Lemma MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__helper1 : (0 <= 1 <= maxG_RNTI_r17)%Z. unfold maxG_RNTI_r17.
 lia. Qed.
Lemma MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxG_RNTI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxG_RNTI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__cond (z : MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxG_RNTI_r17)%Z /\ (list_and MBS_RNTI_SpecificConfigId_r17__cond z) .

Require Import NR.MBS_RNTI_SpecificConfig_r17.

Opaque MBS_RNTI_SpecificConfig_r17__cond MBS_RNTI_SpecificConfig_r17__Format.

Definition MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__Type := list MBS_RNTI_SpecificConfig_r17__Type.

Lemma MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__helper1 : (0 <= 1 <= maxG_CS_RNTI_r17)%Z. unfold maxG_CS_RNTI_r17.
 lia. Qed.
Lemma MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxG_CS_RNTI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxG_CS_RNTI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__cond (z : MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxG_CS_RNTI_r17)%Z /\ (list_and MBS_RNTI_SpecificConfig_r17__cond z) .

Require Import NR.MBS_RNTI_SpecificConfigId_r17.

Opaque MBS_RNTI_SpecificConfigId_r17__cond MBS_RNTI_SpecificConfigId_r17__Format.

Definition MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__Type := list MBS_RNTI_SpecificConfigId_r17__Type.

Lemma MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__helper1 : (0 <= 1 <= maxG_CS_RNTI_r17)%Z. unfold maxG_CS_RNTI_r17.
 lia. Qed.
Lemma MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxG_CS_RNTI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxG_CS_RNTI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__cond (z : MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxG_CS_RNTI_r17)%Z /\ (list_and MBS_RNTI_SpecificConfigId_r17__cond z) .

Record MAC_CellGroupConfig__ext3O__Type : Set :=
  make__MAC_CellGroupConfig__ext3O__Type {
    MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17 : option MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Type ;
    MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17 : option MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__Type ;
    MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700 : option MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__Type ;
    MAC_CellGroupConfig__ext3O__schedulingRequestID_BFR_r17 : option SchedulingRequestId__Type ;
    MAC_CellGroupConfig__ext3O__schedulingRequestID_BFR2_r17 : option SchedulingRequestId__Type ;
    MAC_CellGroupConfig__ext3O__schedulingRequestConfig_v1700 : option SchedulingRequestConfig_v1700__Type ;
    MAC_CellGroupConfig__ext3O__tar_Config_r17 : option MAC_CellGroupConfig__ext3O__tar_Config_r17__Type ;
    MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17 : option MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__Type ;
    MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17 : option MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__Type ;
    MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17 : option MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__Type ;
    MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17 : option MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__Type ;
    MAC_CellGroupConfig__ext3O__allowCSI_SRS_Tx_MulticastDRX_Active_r17 : option bool ;
}.
Definition MAC_CellGroupConfig__ext3O__list := (
 Opt MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Type MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__cond ::
 Opt MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__Type MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__cond ::
 Opt MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__Type MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__cond ::
 Opt SchedulingRequestId__Type SchedulingRequestId__cond ::
 Opt SchedulingRequestId__Type SchedulingRequestId__cond ::
 Opt SchedulingRequestConfig_v1700__Type SchedulingRequestConfig_v1700__cond ::
 Opt MAC_CellGroupConfig__ext3O__tar_Config_r17__Type MAC_CellGroupConfig__ext3O__tar_Config_r17__cond ::
 Opt MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__Type MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__cond ::
 Opt MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__Type MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__cond ::
 Opt MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__Type MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__cond ::
 Opt MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__Type MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__cond ::
 Opt bool (fun _ => True) ::
 nil).
Definition MAC_CellGroupConfig__ext3O__cond z := 
  opt_cond MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__cond (MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17 z) /\
  opt_cond MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__cond (MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17 z) /\
  opt_cond MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__cond (MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700 z) /\
  opt_cond SchedulingRequestId__cond (MAC_CellGroupConfig__ext3O__schedulingRequestID_BFR_r17 z) /\
  opt_cond SchedulingRequestId__cond (MAC_CellGroupConfig__ext3O__schedulingRequestID_BFR2_r17 z) /\
  opt_cond SchedulingRequestConfig_v1700__cond (MAC_CellGroupConfig__ext3O__schedulingRequestConfig_v1700 z) /\
  opt_cond MAC_CellGroupConfig__ext3O__tar_Config_r17__cond (MAC_CellGroupConfig__ext3O__tar_Config_r17 z) /\
  opt_cond MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__cond (MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17 z) /\
  opt_cond MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__cond (MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17 z) /\
  opt_cond MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__cond (MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17 z) /\
  opt_cond MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__cond (MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17 z) /\
  opt_cond (fun _ => True) (MAC_CellGroupConfig__ext3O__allowCSI_SRS_Tx_MulticastDRX_Active_r17 z) /\
  True.

Definition MAC_CellGroupConfig__ext3__Type := MAC_CellGroupConfig__ext3O__Type.
Definition MAC_CellGroupConfig__ext3__cond := MAC_CellGroupConfig__ext3O__cond.

Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Inductive MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Type : Set :=
 | MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__enabled
.
Definition MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__cond := (fun (_ : MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Type) => True).
Lemma MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__nat__helper.

Definition MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F1 t :=
  match t with
  | MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__enabled => 0
  end.
Definition MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F2 n :=
  match n with
  | 0 => MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__enabled
  | _ => MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__enabled
  end.
Lemma MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F1F2 : forall x : MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Type, (MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F1 x <= 0) /\ MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F2 (MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F1 (MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F2 y) = y. enum_solve H y. Qed.

Record MAC_CellGroupConfig__ext4O__Type : Set :=
  make__MAC_CellGroupConfig__ext4O__Type {
    MAC_CellGroupConfig__ext4O__schedulingRequestID_PosMG_Request_r17 : option SchedulingRequestId__Type ;
    MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17 : option MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Type ;
}.
Definition MAC_CellGroupConfig__ext4O__list := (
 Opt SchedulingRequestId__Type SchedulingRequestId__cond ::
 Opt MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Type MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__cond ::
 nil).
Definition MAC_CellGroupConfig__ext4O__cond z := 
  opt_cond SchedulingRequestId__cond (MAC_CellGroupConfig__ext4O__schedulingRequestID_PosMG_Request_r17 z) /\
  opt_cond MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__cond (MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17 z) /\
  True.

Definition MAC_CellGroupConfig__ext4__Type := MAC_CellGroupConfig__ext4O__Type.
Definition MAC_CellGroupConfig__ext4__cond := MAC_CellGroupConfig__ext4O__cond.

Record MAC_CellGroupConfig__Type : Set :=
  make__MAC_CellGroupConfig__Type {
    MAC_CellGroupConfig__drx_Config : option MAC_CellGroupConfig__drx_Config__Type ;
    MAC_CellGroupConfig__schedulingRequestConfig : option SchedulingRequestConfig__Type ;
    MAC_CellGroupConfig__bsr_Config : option BSR_Config__Type ;
    MAC_CellGroupConfig__tag_Config : option TAG_Config__Type ;
    MAC_CellGroupConfig__phr_Config : option MAC_CellGroupConfig__phr_Config__Type ;
    MAC_CellGroupConfig__skipUplinkTxDynamic : bool ;
    MAC_CellGroupConfig__ext0 : option MAC_CellGroupConfig__ext0__Type ;
    MAC_CellGroupConfig__ext1 : option MAC_CellGroupConfig__ext1__Type ;
    MAC_CellGroupConfig__ext2 : option MAC_CellGroupConfig__ext2__Type ;
    MAC_CellGroupConfig__ext3 : option MAC_CellGroupConfig__ext3__Type ;
    MAC_CellGroupConfig__ext4 : option MAC_CellGroupConfig__ext4__Type ;
}.
Definition MAC_CellGroupConfig__root_list : list seq_elem := (
 Opt MAC_CellGroupConfig__drx_Config__Type MAC_CellGroupConfig__drx_Config__cond ::
 Opt SchedulingRequestConfig__Type SchedulingRequestConfig__cond ::
 Opt BSR_Config__Type BSR_Config__cond ::
 Opt TAG_Config__Type TAG_Config__cond ::
 Opt MAC_CellGroupConfig__phr_Config__Type MAC_CellGroupConfig__phr_Config__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition MAC_CellGroupConfig__ext_list : list typ := (
  typ_cons MAC_CellGroupConfig__ext0__Type MAC_CellGroupConfig__ext0__cond ::
  typ_cons MAC_CellGroupConfig__ext1__Type MAC_CellGroupConfig__ext1__cond ::
  typ_cons MAC_CellGroupConfig__ext2__Type MAC_CellGroupConfig__ext2__cond ::
  typ_cons MAC_CellGroupConfig__ext3__Type MAC_CellGroupConfig__ext3__cond ::
  typ_cons MAC_CellGroupConfig__ext4__Type MAC_CellGroupConfig__ext4__cond ::
  nil).
Definition MAC_CellGroupConfig__cond (z : MAC_CellGroupConfig__Type) := 
(  opt_cond MAC_CellGroupConfig__drx_Config__cond (MAC_CellGroupConfig__drx_Config z) /\
  opt_cond SchedulingRequestConfig__cond (MAC_CellGroupConfig__schedulingRequestConfig z) /\
  opt_cond BSR_Config__cond (MAC_CellGroupConfig__bsr_Config z) /\
  opt_cond TAG_Config__cond (MAC_CellGroupConfig__tag_Config z) /\
  opt_cond MAC_CellGroupConfig__phr_Config__cond (MAC_CellGroupConfig__phr_Config z) /\
  (fun _ => True) (MAC_CellGroupConfig__skipUplinkTxDynamic z) /\
  True) /\ 
(  opt_cond MAC_CellGroupConfig__ext0__cond (MAC_CellGroupConfig__ext0 z) /\
  opt_cond MAC_CellGroupConfig__ext1__cond (MAC_CellGroupConfig__ext1 z) /\
  opt_cond MAC_CellGroupConfig__ext2__cond (MAC_CellGroupConfig__ext2 z) /\
  opt_cond MAC_CellGroupConfig__ext3__cond (MAC_CellGroupConfig__ext3 z) /\
  opt_cond MAC_CellGroupConfig__ext4__cond (MAC_CellGroupConfig__ext4 z) /\
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
Opaque MAC_CellGroupConfig__drx_Config__cond MAC_CellGroupConfig__drx_Config__Format.

Opaque MAC_CellGroupConfig__phr_Config__cond MAC_CellGroupConfig__phr_Config__Format.

Opaque MAC_CellGroupConfig__ext0O__dataInactivityTimer__cond MAC_CellGroupConfig__ext0O__dataInactivityTimer__Format.


Definition MAC_CellGroupConfig__ext0O__Format_Type := Eval cbn in seq_format_prod MAC_CellGroupConfig__ext0O__list.
Definition MAC_CellGroupConfig__ext0O__Format_list : MAC_CellGroupConfig__ext0O__Format_Type :=
  (bool__Format, (MAC_CellGroupConfig__ext0O__dataInactivityTimer__Format, unit_format)).
Definition MAC_CellGroupConfig__ext0O__list__Format := (*Eval compute in *) seq_format MAC_CellGroupConfig__ext0O__list MAC_CellGroupConfig__ext0O__Format_list.
Definition MAC_CellGroupConfig__ext0O__F1 z :=
  (MAC_CellGroupConfig__ext0O__csi_Mask z, (MAC_CellGroupConfig__ext0O__dataInactivityTimer z, tt)).
Definition MAC_CellGroupConfig__ext0O__F2 (y : seq_type MAC_CellGroupConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MAC_CellGroupConfig__ext0O__Type i0 i1
  end.
Lemma MAC_CellGroupConfig__ext0O__F1F2_cond (z : MAC_CellGroupConfig__ext0O__Type)
  : MAC_CellGroupConfig__ext0O__cond z ->
  (seq_cond MAC_CellGroupConfig__ext0O__list (MAC_CellGroupConfig__ext0O__F1 z)).
intro H. unfold MAC_CellGroupConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext0O__F1F2_cond2 (z : MAC_CellGroupConfig__ext0O__Type)
 : MAC_CellGroupConfig__ext0O__F2 (MAC_CellGroupConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext0O__F2F1_cond (y : seq_type MAC_CellGroupConfig__ext0O__list)
  : seq_cond MAC_CellGroupConfig__ext0O__list y ->
 (MAC_CellGroupConfig__ext0O__cond (MAC_CellGroupConfig__ext0O__F2 y)) /\  MAC_CellGroupConfig__ext0O__F1 (MAC_CellGroupConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_CellGroupConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold MAC_CellGroupConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_CellGroupConfig__ext0O__Format : T_Format MAC_CellGroupConfig__ext0O__Type MAC_CellGroupConfig__ext0O__cond :=
        proj2_format  MAC_CellGroupConfig__ext0O__cond MAC_CellGroupConfig__ext0O__list__Format
    MAC_CellGroupConfig__ext0O__F1 MAC_CellGroupConfig__ext0O__F2 MAC_CellGroupConfig__ext0O__F1F2_cond  MAC_CellGroupConfig__ext0O__F1F2_cond2 MAC_CellGroupConfig__ext0O__F2F1_cond.
Opaque MAC_CellGroupConfig__ext0O__cond MAC_CellGroupConfig__ext0O__Format.

Definition MAC_CellGroupConfig__ext0__check_all_none (b : MAC_CellGroupConfig__ext0O__Type) : bool :=
match b with 
  | make__MAC_CellGroupConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition MAC_CellGroupConfig__ext0__Format : T_Format MAC_CellGroupConfig__ext0__Type MAC_CellGroupConfig__ext0__cond :=
  restrict_add_format MAC_CellGroupConfig__ext0__check_all_none MAC_CellGroupConfig__ext0O__Format.

Opaque MAC_CellGroupConfig__ext0__cond MAC_CellGroupConfig__ext0__Format.

Definition MAC_CellGroupConfig__ext1O__usePreBSR_r16__Format : T_Format MAC_CellGroupConfig__ext1O__usePreBSR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_CellGroupConfig__ext1O__usePreBSR_r16__nat__Format MAC_CellGroupConfig__ext1O__usePreBSR_r16__F1 MAC_CellGroupConfig__ext1O__usePreBSR_r16__F2 MAC_CellGroupConfig__ext1O__usePreBSR_r16__F1F2 MAC_CellGroupConfig__ext1O__usePreBSR_r16__F2F1.

Opaque MAC_CellGroupConfig__ext1O__usePreBSR_r16__cond MAC_CellGroupConfig__ext1O__usePreBSR_r16__Format.

Definition MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Format : T_Format MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__nat__Format MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F1 MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F2 MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F1F2 MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__F2F1.

Opaque MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__cond MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Format.

Opaque MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__cond MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__Format.


Definition MAC_CellGroupConfig__ext1O__Format_Type := Eval cbn in seq_format_prod MAC_CellGroupConfig__ext1O__list.
Definition MAC_CellGroupConfig__ext1O__Format_list : MAC_CellGroupConfig__ext1O__Format_Type :=
  (MAC_CellGroupConfig__ext1O__usePreBSR_r16__Format, (SchedulingRequestId__Format, (MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16__Format, (SchedulingRequestId__Format, (MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16__Format, unit_format))))).
Definition MAC_CellGroupConfig__ext1O__list__Format := (*Eval compute in *) seq_format MAC_CellGroupConfig__ext1O__list MAC_CellGroupConfig__ext1O__Format_list.
Definition MAC_CellGroupConfig__ext1O__F1 z :=
  (MAC_CellGroupConfig__ext1O__usePreBSR_r16 z, (MAC_CellGroupConfig__ext1O__schedulingRequestID_LBT_SCell_r16 z, (MAC_CellGroupConfig__ext1O__lch_BasedPrioritization_r16 z, (MAC_CellGroupConfig__ext1O__schedulingRequestID_BFR_SCell_r16 z, (MAC_CellGroupConfig__ext1O__drx_ConfigSecondaryGroup_r16 z, tt))))).
Definition MAC_CellGroupConfig__ext1O__F2 (y : seq_type MAC_CellGroupConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__MAC_CellGroupConfig__ext1O__Type i0 i1 i2 i3 i4
  end.
Lemma MAC_CellGroupConfig__ext1O__F1F2_cond (z : MAC_CellGroupConfig__ext1O__Type)
  : MAC_CellGroupConfig__ext1O__cond z ->
  (seq_cond MAC_CellGroupConfig__ext1O__list (MAC_CellGroupConfig__ext1O__F1 z)).
intro H. unfold MAC_CellGroupConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext1O__F1F2_cond2 (z : MAC_CellGroupConfig__ext1O__Type)
 : MAC_CellGroupConfig__ext1O__F2 (MAC_CellGroupConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext1O__F2F1_cond (y : seq_type MAC_CellGroupConfig__ext1O__list)
  : seq_cond MAC_CellGroupConfig__ext1O__list y ->
 (MAC_CellGroupConfig__ext1O__cond (MAC_CellGroupConfig__ext1O__F2 y)) /\  MAC_CellGroupConfig__ext1O__F1 (MAC_CellGroupConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_CellGroupConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold MAC_CellGroupConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_CellGroupConfig__ext1O__Format : T_Format MAC_CellGroupConfig__ext1O__Type MAC_CellGroupConfig__ext1O__cond :=
        proj2_format  MAC_CellGroupConfig__ext1O__cond MAC_CellGroupConfig__ext1O__list__Format
    MAC_CellGroupConfig__ext1O__F1 MAC_CellGroupConfig__ext1O__F2 MAC_CellGroupConfig__ext1O__F1F2_cond  MAC_CellGroupConfig__ext1O__F1F2_cond2 MAC_CellGroupConfig__ext1O__F2F1_cond.
Opaque MAC_CellGroupConfig__ext1O__cond MAC_CellGroupConfig__ext1O__Format.

Definition MAC_CellGroupConfig__ext1__check_all_none (b : MAC_CellGroupConfig__ext1O__Type) : bool :=
match b with 
  | make__MAC_CellGroupConfig__ext1O__Type None None None None None  => false 
  | _ => true 
 end.
Definition MAC_CellGroupConfig__ext1__Format : T_Format MAC_CellGroupConfig__ext1__Type MAC_CellGroupConfig__ext1__cond :=
  restrict_add_format MAC_CellGroupConfig__ext1__check_all_none MAC_CellGroupConfig__ext1O__Format.

Opaque MAC_CellGroupConfig__ext1__cond MAC_CellGroupConfig__ext1__Format.

Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Format : T_Format MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__nat__Format MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F1 MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F2 MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F1F2 MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__F2F1.

Opaque MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__cond MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Format.

Definition MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Format : T_Format MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__nat__Format MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F1 MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F2 MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F1F2 MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__F2F1.

Opaque MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__cond MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Format.


Definition MAC_CellGroupConfig__ext2O__Format_Type := Eval cbn in seq_format_prod MAC_CellGroupConfig__ext2O__list.
Definition MAC_CellGroupConfig__ext2O__Format_list : MAC_CellGroupConfig__ext2O__Format_Type :=
  (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16__Format, (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16__Format, unit_format)).
Definition MAC_CellGroupConfig__ext2O__list__Format := (*Eval compute in *) seq_format MAC_CellGroupConfig__ext2O__list MAC_CellGroupConfig__ext2O__Format_list.
Definition MAC_CellGroupConfig__ext2O__F1 z :=
  (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxDynamic_r16 z, (MAC_CellGroupConfig__ext2O__enhancedSkipUplinkTxConfigured_r16 z, tt)).
Definition MAC_CellGroupConfig__ext2O__F2 (y : seq_type MAC_CellGroupConfig__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MAC_CellGroupConfig__ext2O__Type i0 i1
  end.
Lemma MAC_CellGroupConfig__ext2O__F1F2_cond (z : MAC_CellGroupConfig__ext2O__Type)
  : MAC_CellGroupConfig__ext2O__cond z ->
  (seq_cond MAC_CellGroupConfig__ext2O__list (MAC_CellGroupConfig__ext2O__F1 z)).
intro H. unfold MAC_CellGroupConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext2O__F1F2_cond2 (z : MAC_CellGroupConfig__ext2O__Type)
 : MAC_CellGroupConfig__ext2O__F2 (MAC_CellGroupConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext2O__F2F1_cond (y : seq_type MAC_CellGroupConfig__ext2O__list)
  : seq_cond MAC_CellGroupConfig__ext2O__list y ->
 (MAC_CellGroupConfig__ext2O__cond (MAC_CellGroupConfig__ext2O__F2 y)) /\  MAC_CellGroupConfig__ext2O__F1 (MAC_CellGroupConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_CellGroupConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold MAC_CellGroupConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_CellGroupConfig__ext2O__Format : T_Format MAC_CellGroupConfig__ext2O__Type MAC_CellGroupConfig__ext2O__cond :=
        proj2_format  MAC_CellGroupConfig__ext2O__cond MAC_CellGroupConfig__ext2O__list__Format
    MAC_CellGroupConfig__ext2O__F1 MAC_CellGroupConfig__ext2O__F2 MAC_CellGroupConfig__ext2O__F1F2_cond  MAC_CellGroupConfig__ext2O__F1F2_cond2 MAC_CellGroupConfig__ext2O__F2F1_cond.
Opaque MAC_CellGroupConfig__ext2O__cond MAC_CellGroupConfig__ext2O__Format.

Definition MAC_CellGroupConfig__ext2__check_all_none (b : MAC_CellGroupConfig__ext2O__Type) : bool :=
match b with 
  | make__MAC_CellGroupConfig__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition MAC_CellGroupConfig__ext2__Format : T_Format MAC_CellGroupConfig__ext2__Type MAC_CellGroupConfig__ext2__cond :=
  restrict_add_format MAC_CellGroupConfig__ext2__check_all_none MAC_CellGroupConfig__ext2O__Format.

Opaque MAC_CellGroupConfig__ext2__cond MAC_CellGroupConfig__ext2__Format.

Definition MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Format : T_Format MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__nat__Format MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F1 MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F2 MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F1F2 MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__F2F1.

Opaque MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__cond MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Format.

Opaque MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__cond MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__Format.

Opaque MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__cond MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__Format.

Opaque MAC_CellGroupConfig__ext3O__tar_Config_r17__cond MAC_CellGroupConfig__ext3O__tar_Config_r17__Format.

Definition MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__Format : T_Format MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__Type MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__cond := seq_of_format MBS_RNTI_SpecificConfig_r17__Format 1 maxG_RNTI_r17 MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__helper1 MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__helper2.

Opaque MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__cond MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__Format.

Definition MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__Format : T_Format MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__Type MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__cond := seq_of_format MBS_RNTI_SpecificConfigId_r17__Format 1 maxG_RNTI_r17 MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__helper1 MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__helper2.

Opaque MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__cond MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__Format.

Definition MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__Format : T_Format MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__Type MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__cond := seq_of_format MBS_RNTI_SpecificConfig_r17__Format 1 maxG_CS_RNTI_r17 MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__helper1 MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__helper2.

Opaque MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__cond MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__Format.

Definition MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__Format : T_Format MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__Type MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__cond := seq_of_format MBS_RNTI_SpecificConfigId_r17__Format 1 maxG_CS_RNTI_r17 MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__helper1 MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__helper2.

Opaque MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__cond MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__Format.


Definition MAC_CellGroupConfig__ext3O__Format_Type := Eval cbn in seq_format_prod MAC_CellGroupConfig__ext3O__list.
Definition MAC_CellGroupConfig__ext3O__Format_list : MAC_CellGroupConfig__ext3O__Format_Type :=
  (MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17__Format, (MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17__Format, (MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700__Format, (SchedulingRequestId__Format, (SchedulingRequestId__Format, (SchedulingRequestConfig_v1700__Format, (MAC_CellGroupConfig__ext3O__tar_Config_r17__Format, (MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17__Format, (MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17__Format, (MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17__Format, (MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17__Format, (bool__Format, unit_format)))))))))))).
Definition MAC_CellGroupConfig__ext3O__list__Format := (*Eval compute in *) seq_format MAC_CellGroupConfig__ext3O__list MAC_CellGroupConfig__ext3O__Format_list.
Definition MAC_CellGroupConfig__ext3O__F1 z :=
  (MAC_CellGroupConfig__ext3O__intraCG_Prioritization_r17 z, (MAC_CellGroupConfig__ext3O__drx_ConfigSL_r17 z, (MAC_CellGroupConfig__ext3O__drx_ConfigExt_v1700 z, (MAC_CellGroupConfig__ext3O__schedulingRequestID_BFR_r17 z, (MAC_CellGroupConfig__ext3O__schedulingRequestID_BFR2_r17 z, (MAC_CellGroupConfig__ext3O__schedulingRequestConfig_v1700 z, (MAC_CellGroupConfig__ext3O__tar_Config_r17 z, (MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToAddModList_r17 z, (MAC_CellGroupConfig__ext3O__g_RNTI_ConfigToReleaseList_r17 z, (MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToAddModList_r17 z, (MAC_CellGroupConfig__ext3O__g_CS_RNTI_ConfigToReleaseList_r17 z, (MAC_CellGroupConfig__ext3O__allowCSI_SRS_Tx_MulticastDRX_Active_r17 z, tt)))))))))))).
Definition MAC_CellGroupConfig__ext3O__F2 (y : seq_type MAC_CellGroupConfig__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, _))))))))))))=>
    make__MAC_CellGroupConfig__ext3O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  end.
Lemma MAC_CellGroupConfig__ext3O__F1F2_cond (z : MAC_CellGroupConfig__ext3O__Type)
  : MAC_CellGroupConfig__ext3O__cond z ->
  (seq_cond MAC_CellGroupConfig__ext3O__list (MAC_CellGroupConfig__ext3O__F1 z)).
intro H. unfold MAC_CellGroupConfig__ext3O__cond in H. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext3O__F1F2_cond2 (z : MAC_CellGroupConfig__ext3O__Type)
 : MAC_CellGroupConfig__ext3O__F2 (MAC_CellGroupConfig__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext3O__F2F1_cond (y : seq_type MAC_CellGroupConfig__ext3O__list)
  : seq_cond MAC_CellGroupConfig__ext3O__list y ->
 (MAC_CellGroupConfig__ext3O__cond (MAC_CellGroupConfig__ext3O__F2 y)) /\  MAC_CellGroupConfig__ext3O__F1 (MAC_CellGroupConfig__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_CellGroupConfig__ext3O__cond. simpl in *. auto.
 - simpl. unfold MAC_CellGroupConfig__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_CellGroupConfig__ext3O__Format : T_Format MAC_CellGroupConfig__ext3O__Type MAC_CellGroupConfig__ext3O__cond :=
        proj2_format  MAC_CellGroupConfig__ext3O__cond MAC_CellGroupConfig__ext3O__list__Format
    MAC_CellGroupConfig__ext3O__F1 MAC_CellGroupConfig__ext3O__F2 MAC_CellGroupConfig__ext3O__F1F2_cond  MAC_CellGroupConfig__ext3O__F1F2_cond2 MAC_CellGroupConfig__ext3O__F2F1_cond.
Opaque MAC_CellGroupConfig__ext3O__cond MAC_CellGroupConfig__ext3O__Format.

Definition MAC_CellGroupConfig__ext3__check_all_none (b : MAC_CellGroupConfig__ext3O__Type) : bool :=
match b with 
  | make__MAC_CellGroupConfig__ext3O__Type None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MAC_CellGroupConfig__ext3__Format : T_Format MAC_CellGroupConfig__ext3__Type MAC_CellGroupConfig__ext3__cond :=
  restrict_add_format MAC_CellGroupConfig__ext3__check_all_none MAC_CellGroupConfig__ext3O__Format.

Opaque MAC_CellGroupConfig__ext3__cond MAC_CellGroupConfig__ext3__Format.

Definition MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Format : T_Format MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__nat__Format MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F1 MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F2 MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F1F2 MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__F2F1.

Opaque MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__cond MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Format.


Definition MAC_CellGroupConfig__ext4O__Format_Type := Eval cbn in seq_format_prod MAC_CellGroupConfig__ext4O__list.
Definition MAC_CellGroupConfig__ext4O__Format_list : MAC_CellGroupConfig__ext4O__Format_Type :=
  (SchedulingRequestId__Format, (MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17__Format, unit_format)).
Definition MAC_CellGroupConfig__ext4O__list__Format := (*Eval compute in *) seq_format MAC_CellGroupConfig__ext4O__list MAC_CellGroupConfig__ext4O__Format_list.
Definition MAC_CellGroupConfig__ext4O__F1 z :=
  (MAC_CellGroupConfig__ext4O__schedulingRequestID_PosMG_Request_r17 z, (MAC_CellGroupConfig__ext4O__drx_LastTransmissionUL_r17 z, tt)).
Definition MAC_CellGroupConfig__ext4O__F2 (y : seq_type MAC_CellGroupConfig__ext4O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MAC_CellGroupConfig__ext4O__Type i0 i1
  end.
Lemma MAC_CellGroupConfig__ext4O__F1F2_cond (z : MAC_CellGroupConfig__ext4O__Type)
  : MAC_CellGroupConfig__ext4O__cond z ->
  (seq_cond MAC_CellGroupConfig__ext4O__list (MAC_CellGroupConfig__ext4O__F1 z)).
intro H. unfold MAC_CellGroupConfig__ext4O__cond in H. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext4O__F1F2_cond2 (z : MAC_CellGroupConfig__ext4O__Type)
 : MAC_CellGroupConfig__ext4O__F2 (MAC_CellGroupConfig__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_CellGroupConfig__ext4O__F2F1_cond (y : seq_type MAC_CellGroupConfig__ext4O__list)
  : seq_cond MAC_CellGroupConfig__ext4O__list y ->
 (MAC_CellGroupConfig__ext4O__cond (MAC_CellGroupConfig__ext4O__F2 y)) /\  MAC_CellGroupConfig__ext4O__F1 (MAC_CellGroupConfig__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_CellGroupConfig__ext4O__cond. simpl in *. auto.
 - simpl. unfold MAC_CellGroupConfig__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_CellGroupConfig__ext4O__Format : T_Format MAC_CellGroupConfig__ext4O__Type MAC_CellGroupConfig__ext4O__cond :=
        proj2_format  MAC_CellGroupConfig__ext4O__cond MAC_CellGroupConfig__ext4O__list__Format
    MAC_CellGroupConfig__ext4O__F1 MAC_CellGroupConfig__ext4O__F2 MAC_CellGroupConfig__ext4O__F1F2_cond  MAC_CellGroupConfig__ext4O__F1F2_cond2 MAC_CellGroupConfig__ext4O__F2F1_cond.
Opaque MAC_CellGroupConfig__ext4O__cond MAC_CellGroupConfig__ext4O__Format.

Definition MAC_CellGroupConfig__ext4__check_all_none (b : MAC_CellGroupConfig__ext4O__Type) : bool :=
match b with 
  | make__MAC_CellGroupConfig__ext4O__Type None None  => false 
  | _ => true 
 end.
Definition MAC_CellGroupConfig__ext4__Format : T_Format MAC_CellGroupConfig__ext4__Type MAC_CellGroupConfig__ext4__cond :=
  restrict_add_format MAC_CellGroupConfig__ext4__check_all_none MAC_CellGroupConfig__ext4O__Format.

Opaque MAC_CellGroupConfig__ext4__cond MAC_CellGroupConfig__ext4__Format.


Definition MAC_CellGroupConfig__root_Format_Type := Eval cbn in seq_format_prod MAC_CellGroupConfig__root_list.
Definition MAC_CellGroupConfig__root_Format_list : MAC_CellGroupConfig__root_Format_Type :=
  (MAC_CellGroupConfig__drx_Config__Format, (SchedulingRequestConfig__Format, (BSR_Config__Format, (TAG_Config__Format, (MAC_CellGroupConfig__phr_Config__Format, (bool__Format, unit_format)))))).

Definition MAC_CellGroupConfig__ext_Format_Type := Eval cbn in get_formats MAC_CellGroupConfig__ext_list.
Definition MAC_CellGroupConfig__ext_Format_list : MAC_CellGroupConfig__ext_Format_Type :=
  (MAC_CellGroupConfig__ext0__Format, (MAC_CellGroupConfig__ext1__Format, (MAC_CellGroupConfig__ext2__Format, (MAC_CellGroupConfig__ext3__Format, (MAC_CellGroupConfig__ext4__Format, unit__Format))))).

Definition MAC_CellGroupConfig__list_type : Set := (seq_type MAC_CellGroupConfig__root_list) * (seq_ext_type MAC_CellGroupConfig__ext_list).
Definition MAC_CellGroupConfig__list_cond (z : MAC_CellGroupConfig__list_type) : Prop :=
        (seq_cond MAC_CellGroupConfig__root_list (fst z)) /\ (seq_ext_cond MAC_CellGroupConfig__ext_list (snd z)).
Definition MAC_CellGroupConfig__list_format : T_Format MAC_CellGroupConfig__list_type MAC_CellGroupConfig__list_cond :=
 (* Eval compute in *) seq_ext_format MAC_CellGroupConfig__root_list MAC_CellGroupConfig__root_Format_list MAC_CellGroupConfig__ext_list MAC_CellGroupConfig__ext_Format_list.

Opaque MAC_CellGroupConfig__list_format.
Definition MAC_CellGroupConfig__F1 (z : MAC_CellGroupConfig__Type) : MAC_CellGroupConfig__list_type :=
  (((MAC_CellGroupConfig__drx_Config z, (MAC_CellGroupConfig__schedulingRequestConfig z, (MAC_CellGroupConfig__bsr_Config z, (MAC_CellGroupConfig__tag_Config z, (MAC_CellGroupConfig__phr_Config z, (MAC_CellGroupConfig__skipUplinkTxDynamic z, tt))))))), (
(MAC_CellGroupConfig__ext0 z, (MAC_CellGroupConfig__ext1 z, (MAC_CellGroupConfig__ext2 z, (MAC_CellGroupConfig__ext3 z, (MAC_CellGroupConfig__ext4 z, tt))))))).
Definition MAC_CellGroupConfig__F2 (y : MAC_CellGroupConfig__list_type) : MAC_CellGroupConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, (i1, (i2, (i3, (i4, _))))))=>
    make__MAC_CellGroupConfig__Type j0 j1 j2 j3 j4 j5 i0 i1 i2 i3 i4
  end.
Definition MAC_CellGroupConfig__helper1 : (forall a : MAC_CellGroupConfig__Type, MAC_CellGroupConfig__cond a -> MAC_CellGroupConfig__list_cond (MAC_CellGroupConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MAC_CellGroupConfig__helper2 : (forall a : MAC_CellGroupConfig__Type, MAC_CellGroupConfig__F2 (MAC_CellGroupConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MAC_CellGroupConfig__helper3 : (forall b : MAC_CellGroupConfig__list_type, MAC_CellGroupConfig__list_cond b -> MAC_CellGroupConfig__cond (MAC_CellGroupConfig__F2 b) /\ MAC_CellGroupConfig__F1 (MAC_CellGroupConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MAC_CellGroupConfig__cond, MAC_CellGroupConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MAC_CellGroupConfig__Format : T_Format MAC_CellGroupConfig__Type MAC_CellGroupConfig__cond :=
 proj2_format MAC_CellGroupConfig__cond MAC_CellGroupConfig__list_format  MAC_CellGroupConfig__F1 MAC_CellGroupConfig__F2 MAC_CellGroupConfig__helper1 MAC_CellGroupConfig__helper2 MAC_CellGroupConfig__helper3.

Opaque MAC_CellGroupConfig__cond MAC_CellGroupConfig__Format.

