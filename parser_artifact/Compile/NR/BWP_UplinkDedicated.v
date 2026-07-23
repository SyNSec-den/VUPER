Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.PUCCH_Config.
Definition BWP_UplinkDedicated__pucch_Config__Type := SetupRelease__Type PUCCH_Config__Type.
Definition BWP_UplinkDedicated__pucch_Config__cond := SetupRelease__cond _ PUCCH_Config__cond.
Definition BWP_UplinkDedicated__pucch_Config__Format : T_Format BWP_UplinkDedicated__pucch_Config__Type BWP_UplinkDedicated__pucch_Config__cond := SetupRelease__Format _ _ PUCCH_Config__Format.
Opaque BWP_UplinkDedicated__pucch_Config__cond BWP_UplinkDedicated__pucch_Config__Format.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_Config.
Definition BWP_UplinkDedicated__pusch_Config__Type := SetupRelease__Type PUSCH_Config__Type.
Definition BWP_UplinkDedicated__pusch_Config__cond := SetupRelease__cond _ PUSCH_Config__cond.
Definition BWP_UplinkDedicated__pusch_Config__Format : T_Format BWP_UplinkDedicated__pusch_Config__Type BWP_UplinkDedicated__pusch_Config__cond := SetupRelease__Format _ _ PUSCH_Config__Format.
Opaque BWP_UplinkDedicated__pusch_Config__cond BWP_UplinkDedicated__pusch_Config__Format.

Require Import NR.SetupRelease.
Require Import NR.ConfiguredGrantConfig.
Definition BWP_UplinkDedicated__configuredGrantConfig__Type := SetupRelease__Type ConfiguredGrantConfig__Type.
Definition BWP_UplinkDedicated__configuredGrantConfig__cond := SetupRelease__cond _ ConfiguredGrantConfig__cond.
Definition BWP_UplinkDedicated__configuredGrantConfig__Format : T_Format BWP_UplinkDedicated__configuredGrantConfig__Type BWP_UplinkDedicated__configuredGrantConfig__cond := SetupRelease__Format _ _ ConfiguredGrantConfig__Format.
Opaque BWP_UplinkDedicated__configuredGrantConfig__cond BWP_UplinkDedicated__configuredGrantConfig__Format.

Require Import NR.SetupRelease.
Require Import NR.SRS_Config.
Definition BWP_UplinkDedicated__srs_Config__Type := SetupRelease__Type SRS_Config__Type.
Definition BWP_UplinkDedicated__srs_Config__cond := SetupRelease__cond _ SRS_Config__cond.
Definition BWP_UplinkDedicated__srs_Config__Format : T_Format BWP_UplinkDedicated__srs_Config__Type BWP_UplinkDedicated__srs_Config__cond := SetupRelease__Format _ _ SRS_Config__Format.
Opaque BWP_UplinkDedicated__srs_Config__cond BWP_UplinkDedicated__srs_Config__Format.

Require Import NR.SetupRelease.
Require Import NR.BeamFailureRecoveryConfig.
Definition BWP_UplinkDedicated__beamFailureRecoveryConfig__Type := SetupRelease__Type BeamFailureRecoveryConfig__Type.
Definition BWP_UplinkDedicated__beamFailureRecoveryConfig__cond := SetupRelease__cond _ BeamFailureRecoveryConfig__cond.
Definition BWP_UplinkDedicated__beamFailureRecoveryConfig__Format : T_Format BWP_UplinkDedicated__beamFailureRecoveryConfig__Type BWP_UplinkDedicated__beamFailureRecoveryConfig__cond := SetupRelease__Format _ _ BeamFailureRecoveryConfig__Format.
Opaque BWP_UplinkDedicated__beamFailureRecoveryConfig__cond BWP_UplinkDedicated__beamFailureRecoveryConfig__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_Config.
Definition BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__Type := SetupRelease__Type PUCCH_Config__Type.
Definition BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__cond := SetupRelease__cond _ PUCCH_Config__cond.
Definition BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__Format : T_Format BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__Type BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__cond := SetupRelease__Format _ _ PUCCH_Config__Format.
Opaque BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__cond BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__Format.

Lemma BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__helper1 : (1 <= 28)%Z.  lia. Qed.
Lemma BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__helper2 : to_bit_sz (Z.to_nat (28 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (28 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__Type := Z.
Definition BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__cond := (fun z => (1 <= z <= 28)%Z).
Lemma BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__helper1 : (1 <= 28)%Z.  lia. Qed.
Lemma BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__helper2 : to_bit_sz (Z.to_nat (28 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (28 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__Type := Z.
Definition BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__cond := (fun z => (1 <= z <= 28)%Z).
Inductive BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Type : Set :=
 | BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__enabled
.
Definition BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__cond := (fun (_ : BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Type) => True).
Lemma BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__nat__helper.

Definition BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F1 t :=
  match t with
  | BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__enabled => 0
  end.
Definition BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F2 n :=
  match n with
  | 0 => BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__enabled
  | _ => BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__enabled
  end.
Lemma BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F1F2 : forall x : BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Type, (BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F1 x <= 0) /\ BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F2 (BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F1 (BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_ConfigurationList_r16.
Definition BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__Type := SetupRelease__Type PUCCH_ConfigurationList_r16__Type.
Definition BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__cond := SetupRelease__cond _ PUCCH_ConfigurationList_r16__cond.
Definition BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__Format : T_Format BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__Type BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__cond := SetupRelease__Format _ _ PUCCH_ConfigurationList_r16__Format.
Opaque BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__cond BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.LBT_FailureRecoveryConfig_r16.
Definition BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__Type := SetupRelease__Type LBT_FailureRecoveryConfig_r16__Type.
Definition BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__cond := SetupRelease__cond _ LBT_FailureRecoveryConfig_r16__cond.
Definition BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__Format : T_Format BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__Type BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__cond := SetupRelease__Format _ _ LBT_FailureRecoveryConfig_r16__Format.
Opaque BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__cond BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__Format.

Require Import NR.ConfiguredGrantConfigToAddModList_r16.

Opaque ConfiguredGrantConfigToAddModList_r16__cond ConfiguredGrantConfigToAddModList_r16__Format.

Require Import NR.ConfiguredGrantConfigToReleaseList_r16.

Opaque ConfiguredGrantConfigToReleaseList_r16__cond ConfiguredGrantConfigToReleaseList_r16__Format.

Require Import NR.ConfiguredGrantConfigType2DeactivationStateList_r16.

Opaque ConfiguredGrantConfigType2DeactivationStateList_r16__cond ConfiguredGrantConfigType2DeactivationStateList_r16__Format.

Record BWP_UplinkDedicated__ext0O__Type : Set :=
  make__BWP_UplinkDedicated__ext0O__Type {
    BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16 : option BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__Type ;
    BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16 : option Z ;
    BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16 : option Z ;
    BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16 : option BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Type ;
    BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16 : option BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__Type ;
    BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16 : option BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__Type ;
    BWP_UplinkDedicated__ext0O__configuredGrantConfigToAddModList_r16 : option ConfiguredGrantConfigToAddModList_r16__Type ;
    BWP_UplinkDedicated__ext0O__configuredGrantConfigToReleaseList_r16 : option ConfiguredGrantConfigToReleaseList_r16__Type ;
    BWP_UplinkDedicated__ext0O__configuredGrantConfigType2DeactivationStateList_r16 : option ConfiguredGrantConfigType2DeactivationStateList_r16__Type ;
}.
Definition BWP_UplinkDedicated__ext0O__list := (
 Opt BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__Type BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__cond ::
 Opt Z BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__cond ::
 Opt Z BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__cond ::
 Opt BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Type BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__cond ::
 Opt BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__Type BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__cond ::
 Opt BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__Type BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__cond ::
 Opt ConfiguredGrantConfigToAddModList_r16__Type ConfiguredGrantConfigToAddModList_r16__cond ::
 Opt ConfiguredGrantConfigToReleaseList_r16__Type ConfiguredGrantConfigToReleaseList_r16__cond ::
 Opt ConfiguredGrantConfigType2DeactivationStateList_r16__Type ConfiguredGrantConfigType2DeactivationStateList_r16__cond ::
 nil).
Definition BWP_UplinkDedicated__ext0O__cond z := 
  opt_cond BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__cond (BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16 z) /\
  opt_cond BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__cond (BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16 z) /\
  opt_cond BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__cond (BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16 z) /\
  opt_cond BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__cond (BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16 z) /\
  opt_cond BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__cond (BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16 z) /\
  opt_cond BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__cond (BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16 z) /\
  opt_cond ConfiguredGrantConfigToAddModList_r16__cond (BWP_UplinkDedicated__ext0O__configuredGrantConfigToAddModList_r16 z) /\
  opt_cond ConfiguredGrantConfigToReleaseList_r16__cond (BWP_UplinkDedicated__ext0O__configuredGrantConfigToReleaseList_r16 z) /\
  opt_cond ConfiguredGrantConfigType2DeactivationStateList_r16__cond (BWP_UplinkDedicated__ext0O__configuredGrantConfigType2DeactivationStateList_r16 z) /\
  True.

Definition BWP_UplinkDedicated__ext0__Type := BWP_UplinkDedicated__ext0O__Type.
Definition BWP_UplinkDedicated__ext0__cond := BWP_UplinkDedicated__ext0O__cond.

Require Import NR.TCI_UL_State_r17.

Opaque TCI_UL_State_r17__cond TCI_UL_State_r17__Format.

Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__Type := list TCI_UL_State_r17__Type.

Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__helper1 : (0 <= 1 <= maxUL_TCI_r17)%Z. unfold maxUL_TCI_r17.
 lia. Qed.
Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxUL_TCI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUL_TCI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__cond (z : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxUL_TCI_r17)%Z /\ (list_and TCI_UL_State_r17__cond z) .

Require Import NR.TCI_UL_State_Id_r17.

Opaque TCI_UL_State_Id_r17__cond TCI_UL_State_Id_r17__Format.

Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__Type := list TCI_UL_State_Id_r17__Type.

Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__helper1 : (0 <= 1 <= maxUL_TCI_r17)%Z. unfold maxUL_TCI_r17.
 lia. Qed.
Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxUL_TCI_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUL_TCI_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__cond (z : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxUL_TCI_r17)%Z /\ (list_and TCI_UL_State_Id_r17__cond z) .

Record BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type : Set :=
  make__BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type {
    BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17 : option BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__Type ;
    BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17 : option BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__Type ;
}.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list := (
 Opt BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__Type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__cond ::
 Opt BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__Type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__cond ::
 nil).
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond z := 
  opt_cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__cond (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17 z) /\
  opt_cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__cond (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17 z) /\
  True.

Require Import NR.ServingCellAndBWP_Id_r17.

Opaque ServingCellAndBWP_Id_r17__cond ServingCellAndBWP_Id_r17__Format.


Inductive BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type : Set :=
  | BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type -> BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type
  | BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__unifiedTCI_StateRef_r17 : ServingCellAndBWP_Id_r17__Type -> BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type
.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list : list typ := (
typ_cons BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond ::
typ_cons ServingCellAndBWP_Id_r17__Type ServingCellAndBWP_Id_r17__cond ::
 nil).
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__cond (c : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type) := 
  match c with
  | BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist t => BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond t 
  | BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__unifiedTCI_StateRef_r17 t => ServingCellAndBWP_Id_r17__cond t 
  end.

Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__len_helper1 : to_bit_sz (length BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__len_helper2 : 2 <= length2 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list.
 simpl. lia. Qed.
Require Import NR.Uplink_powerControlId_r17.

Opaque Uplink_powerControlId_r17__cond Uplink_powerControlId_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_ConfigurationList_r16.
Definition BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__Type := SetupRelease__Type PUCCH_ConfigurationList_r16__Type.
Definition BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__cond := SetupRelease__cond _ PUCCH_ConfigurationList_r16__cond.
Definition BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__Format : T_Format BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__Type BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__cond := SetupRelease__Format _ _ PUCCH_ConfigurationList_r16__Format.
Opaque BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__cond BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_ConfigurationList_r16.
Definition BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__Type := SetupRelease__Type PUCCH_ConfigurationList_r16__Type.
Definition BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__cond := SetupRelease__cond _ PUCCH_ConfigurationList_r16__cond.
Definition BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__Format : T_Format BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__Type BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__cond := SetupRelease__Format _ _ PUCCH_ConfigurationList_r16__Format.
Opaque BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__cond BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__Format.

Record BWP_UplinkDedicated__ext1O__Type : Set :=
  make__BWP_UplinkDedicated__ext1O__Type {
    BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17 : option BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type ;
    BWP_UplinkDedicated__ext1O__ul_powerControl_r17 : option Uplink_powerControlId_r17__Type ;
    BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17 : option BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__Type ;
    BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17 : option BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__Type ;
}.
Definition BWP_UplinkDedicated__ext1O__list := (
 Opt BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__cond ::
 Opt Uplink_powerControlId_r17__Type Uplink_powerControlId_r17__cond ::
 Opt BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__Type BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__cond ::
 Opt BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__Type BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__cond ::
 nil).
Definition BWP_UplinkDedicated__ext1O__cond z := 
  opt_cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__cond (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17 z) /\
  opt_cond Uplink_powerControlId_r17__cond (BWP_UplinkDedicated__ext1O__ul_powerControl_r17 z) /\
  opt_cond BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__cond (BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17 z) /\
  opt_cond BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__cond (BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17 z) /\
  True.

Definition BWP_UplinkDedicated__ext1__Type := BWP_UplinkDedicated__ext1O__Type.
Definition BWP_UplinkDedicated__ext1__cond := BWP_UplinkDedicated__ext1O__cond.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_Config.
Definition BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__Type := SetupRelease__Type PUCCH_Config__Type.
Definition BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__cond := SetupRelease__cond _ PUCCH_Config__cond.
Definition BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__Format : T_Format BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__Type BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__cond := SetupRelease__Format _ _ PUCCH_Config__Format.
Opaque BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__cond BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.PUCCH_Config.
Definition BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__Type := SetupRelease__Type PUCCH_Config__Type.
Definition BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__cond := SetupRelease__cond _ PUCCH_Config__cond.
Definition BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__Format : T_Format BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__Type BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__cond := SetupRelease__Format _ _ PUCCH_Config__Format.
Opaque BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__cond BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__Format.

Record BWP_UplinkDedicated__ext2O__Type : Set :=
  make__BWP_UplinkDedicated__ext2O__Type {
    BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17 : option BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__Type ;
    BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17 : option BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__Type ;
}.
Definition BWP_UplinkDedicated__ext2O__list := (
 Opt BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__Type BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__cond ::
 Opt BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__Type BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__cond ::
 nil).
Definition BWP_UplinkDedicated__ext2O__cond z := 
  opt_cond BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__cond (BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17 z) /\
  opt_cond BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__cond (BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17 z) /\
  True.

Definition BWP_UplinkDedicated__ext2__Type := BWP_UplinkDedicated__ext2O__Type.
Definition BWP_UplinkDedicated__ext2__cond := BWP_UplinkDedicated__ext2O__cond.

Require Import NR.PathlossReferenceRS_r17.

Opaque PathlossReferenceRS_r17__cond PathlossReferenceRS_r17__Format.

Definition BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__Type := list PathlossReferenceRS_r17__Type.

Lemma BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__helper1 : (0 <= 1 <= maxNrofPathlossReferenceRSs_r17)%Z. unfold maxNrofPathlossReferenceRSs_r17.
 lia. Qed.
Lemma BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPathlossReferenceRSs_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPathlossReferenceRSs_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__cond (z : BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPathlossReferenceRSs_r17)%Z /\ (list_and PathlossReferenceRS_r17__cond z) .

Require Import NR.PathlossReferenceRS_Id_r17.

Opaque PathlossReferenceRS_Id_r17__cond PathlossReferenceRS_Id_r17__Format.

Definition BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__Type := list PathlossReferenceRS_Id_r17__Type.

Lemma BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofPathlossReferenceRSs_r17)%Z. unfold maxNrofPathlossReferenceRSs_r17.
 lia. Qed.
Lemma BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPathlossReferenceRSs_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPathlossReferenceRSs_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__cond (z : BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPathlossReferenceRSs_r17)%Z /\ (list_and PathlossReferenceRS_Id_r17__cond z) .

Record BWP_UplinkDedicated__ext3O__Type : Set :=
  make__BWP_UplinkDedicated__ext3O__Type {
    BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17 : option BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__Type ;
    BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17 : option BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__Type ;
}.
Definition BWP_UplinkDedicated__ext3O__list := (
 Opt BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__Type BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__cond ::
 Opt BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__Type BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__cond ::
 nil).
Definition BWP_UplinkDedicated__ext3O__cond z := 
  opt_cond BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__cond (BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17 z) /\
  opt_cond BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__cond (BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17 z) /\
  True.

Definition BWP_UplinkDedicated__ext3__Type := BWP_UplinkDedicated__ext3O__Type.
Definition BWP_UplinkDedicated__ext3__cond := BWP_UplinkDedicated__ext3O__cond.

Record BWP_UplinkDedicated__Type : Set :=
  make__BWP_UplinkDedicated__Type {
    BWP_UplinkDedicated__pucch_Config : option BWP_UplinkDedicated__pucch_Config__Type ;
    BWP_UplinkDedicated__pusch_Config : option BWP_UplinkDedicated__pusch_Config__Type ;
    BWP_UplinkDedicated__configuredGrantConfig : option BWP_UplinkDedicated__configuredGrantConfig__Type ;
    BWP_UplinkDedicated__srs_Config : option BWP_UplinkDedicated__srs_Config__Type ;
    BWP_UplinkDedicated__beamFailureRecoveryConfig : option BWP_UplinkDedicated__beamFailureRecoveryConfig__Type ;
    BWP_UplinkDedicated__ext0 : option BWP_UplinkDedicated__ext0__Type ;
    BWP_UplinkDedicated__ext1 : option BWP_UplinkDedicated__ext1__Type ;
    BWP_UplinkDedicated__ext2 : option BWP_UplinkDedicated__ext2__Type ;
    BWP_UplinkDedicated__ext3 : option BWP_UplinkDedicated__ext3__Type ;
}.
Definition BWP_UplinkDedicated__root_list : list seq_elem := (
 Opt BWP_UplinkDedicated__pucch_Config__Type BWP_UplinkDedicated__pucch_Config__cond ::
 Opt BWP_UplinkDedicated__pusch_Config__Type BWP_UplinkDedicated__pusch_Config__cond ::
 Opt BWP_UplinkDedicated__configuredGrantConfig__Type BWP_UplinkDedicated__configuredGrantConfig__cond ::
 Opt BWP_UplinkDedicated__srs_Config__Type BWP_UplinkDedicated__srs_Config__cond ::
 Opt BWP_UplinkDedicated__beamFailureRecoveryConfig__Type BWP_UplinkDedicated__beamFailureRecoveryConfig__cond ::
 nil).
Definition BWP_UplinkDedicated__ext_list : list typ := (
  typ_cons BWP_UplinkDedicated__ext0__Type BWP_UplinkDedicated__ext0__cond ::
  typ_cons BWP_UplinkDedicated__ext1__Type BWP_UplinkDedicated__ext1__cond ::
  typ_cons BWP_UplinkDedicated__ext2__Type BWP_UplinkDedicated__ext2__cond ::
  typ_cons BWP_UplinkDedicated__ext3__Type BWP_UplinkDedicated__ext3__cond ::
  nil).
Definition BWP_UplinkDedicated__cond (z : BWP_UplinkDedicated__Type) := 
(  opt_cond BWP_UplinkDedicated__pucch_Config__cond (BWP_UplinkDedicated__pucch_Config z) /\
  opt_cond BWP_UplinkDedicated__pusch_Config__cond (BWP_UplinkDedicated__pusch_Config z) /\
  opt_cond BWP_UplinkDedicated__configuredGrantConfig__cond (BWP_UplinkDedicated__configuredGrantConfig z) /\
  opt_cond BWP_UplinkDedicated__srs_Config__cond (BWP_UplinkDedicated__srs_Config z) /\
  opt_cond BWP_UplinkDedicated__beamFailureRecoveryConfig__cond (BWP_UplinkDedicated__beamFailureRecoveryConfig z) /\
  True) /\ 
(  opt_cond BWP_UplinkDedicated__ext0__cond (BWP_UplinkDedicated__ext0 z) /\
  opt_cond BWP_UplinkDedicated__ext1__cond (BWP_UplinkDedicated__ext1 z) /\
  opt_cond BWP_UplinkDedicated__ext2__cond (BWP_UplinkDedicated__ext2 z) /\
  opt_cond BWP_UplinkDedicated__ext3__cond (BWP_UplinkDedicated__ext3 z) /\
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
Opaque BWP_UplinkDedicated__pucch_Config__cond BWP_UplinkDedicated__pucch_Config__Format.

Opaque BWP_UplinkDedicated__pusch_Config__cond BWP_UplinkDedicated__pusch_Config__Format.

Opaque BWP_UplinkDedicated__configuredGrantConfig__cond BWP_UplinkDedicated__configuredGrantConfig__Format.

Opaque BWP_UplinkDedicated__srs_Config__cond BWP_UplinkDedicated__srs_Config__Format.

Opaque BWP_UplinkDedicated__beamFailureRecoveryConfig__cond BWP_UplinkDedicated__beamFailureRecoveryConfig__Format.

Opaque BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__cond BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__Format.

Definition BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__Format : T_Format Z BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__cond :=
 ranged_int_format (1) (28) BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__helper1 BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__helper2.

Opaque BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__cond BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__Format.

Definition BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__Format : T_Format Z BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__cond :=
 ranged_int_format (1) (28) BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__helper1 BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__helper2.

Opaque BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__cond BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__Format.

Definition BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Format : T_Format BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__nat__Format BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F1 BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F2 BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F1F2 BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__F2F1.

Opaque BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__cond BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Format.

Opaque BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__cond BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__Format.

Opaque BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__cond BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__Format.


Definition BWP_UplinkDedicated__ext0O__Format_Type := Eval cbn in seq_format_prod BWP_UplinkDedicated__ext0O__list.
Definition BWP_UplinkDedicated__ext0O__Format_list : BWP_UplinkDedicated__ext0O__Format_Type :=
  (BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16__Format, (BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16__Format, (BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16__Format, (BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16__Format, (BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16__Format, (BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16__Format, (ConfiguredGrantConfigToAddModList_r16__Format, (ConfiguredGrantConfigToReleaseList_r16__Format, (ConfiguredGrantConfigType2DeactivationStateList_r16__Format, unit_format))))))))).
Definition BWP_UplinkDedicated__ext0O__list__Format := (*Eval compute in *) seq_format BWP_UplinkDedicated__ext0O__list BWP_UplinkDedicated__ext0O__Format_list.
Definition BWP_UplinkDedicated__ext0O__F1 z :=
  (BWP_UplinkDedicated__ext0O__sl_PUCCH_Config_r16 z, (BWP_UplinkDedicated__ext0O__cp_ExtensionC2_r16 z, (BWP_UplinkDedicated__ext0O__cp_ExtensionC3_r16 z, (BWP_UplinkDedicated__ext0O__useInterlacePUCCH_PUSCH_r16 z, (BWP_UplinkDedicated__ext0O__pucch_ConfigurationList_r16 z, (BWP_UplinkDedicated__ext0O__lbt_FailureRecoveryConfig_r16 z, (BWP_UplinkDedicated__ext0O__configuredGrantConfigToAddModList_r16 z, (BWP_UplinkDedicated__ext0O__configuredGrantConfigToReleaseList_r16 z, (BWP_UplinkDedicated__ext0O__configuredGrantConfigType2DeactivationStateList_r16 z, tt))))))))).
Definition BWP_UplinkDedicated__ext0O__F2 (y : seq_type BWP_UplinkDedicated__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _)))))))))=>
    make__BWP_UplinkDedicated__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Lemma BWP_UplinkDedicated__ext0O__F1F2_cond (z : BWP_UplinkDedicated__ext0O__Type)
  : BWP_UplinkDedicated__ext0O__cond z ->
  (seq_cond BWP_UplinkDedicated__ext0O__list (BWP_UplinkDedicated__ext0O__F1 z)).
intro H. unfold BWP_UplinkDedicated__ext0O__cond in H. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext0O__F1F2_cond2 (z : BWP_UplinkDedicated__ext0O__Type)
 : BWP_UplinkDedicated__ext0O__F2 (BWP_UplinkDedicated__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext0O__F2F1_cond (y : seq_type BWP_UplinkDedicated__ext0O__list)
  : seq_cond BWP_UplinkDedicated__ext0O__list y ->
 (BWP_UplinkDedicated__ext0O__cond (BWP_UplinkDedicated__ext0O__F2 y)) /\  BWP_UplinkDedicated__ext0O__F1 (BWP_UplinkDedicated__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_UplinkDedicated__ext0O__cond. simpl in *. auto.
 - simpl. unfold BWP_UplinkDedicated__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_UplinkDedicated__ext0O__Format : T_Format BWP_UplinkDedicated__ext0O__Type BWP_UplinkDedicated__ext0O__cond :=
        proj2_format  BWP_UplinkDedicated__ext0O__cond BWP_UplinkDedicated__ext0O__list__Format
    BWP_UplinkDedicated__ext0O__F1 BWP_UplinkDedicated__ext0O__F2 BWP_UplinkDedicated__ext0O__F1F2_cond  BWP_UplinkDedicated__ext0O__F1F2_cond2 BWP_UplinkDedicated__ext0O__F2F1_cond.
Opaque BWP_UplinkDedicated__ext0O__cond BWP_UplinkDedicated__ext0O__Format.

Definition BWP_UplinkDedicated__ext0__check_all_none (b : BWP_UplinkDedicated__ext0O__Type) : bool :=
match b with 
  | make__BWP_UplinkDedicated__ext0O__Type None None None None None None None None None  => false 
  | _ => true 
 end.
Definition BWP_UplinkDedicated__ext0__Format : T_Format BWP_UplinkDedicated__ext0__Type BWP_UplinkDedicated__ext0__cond :=
  restrict_add_format BWP_UplinkDedicated__ext0__check_all_none BWP_UplinkDedicated__ext0O__Format.

Opaque BWP_UplinkDedicated__ext0__cond BWP_UplinkDedicated__ext0__Format.

Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__Format : T_Format BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__Type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__cond := seq_of_format TCI_UL_State_r17__Format 1 maxUL_TCI_r17 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__helper1 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__helper2.

Opaque BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__Format.

Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__Format : T_Format BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__Type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__cond := seq_of_format TCI_UL_State_Id_r17__Format 1 maxUL_TCI_r17 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__helper1 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__helper2.

Opaque BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__Format.


Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Format_Type := Eval cbn in seq_format_prod BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Format_list : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Format_Type :=
  (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17__Format, (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17__Format, unit_format)).
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list__Format := (*Eval compute in *) seq_format BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Format_list.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1 z :=
  (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToAddModList_r17 z, (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__ul_TCI_ToReleaseList_r17 z, tt)).
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F2 (y : seq_type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type i0 i1
  end.
Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1F2_cond (z : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type)
  : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond z ->
  (seq_cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1 z)).
intro H. unfold BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond in H. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1F2_cond2 (z : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type)
 : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F2 (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F2F1_cond (y : seq_type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list)
  : seq_cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list y ->
 (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F2 y)) /\  BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1 (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond. simpl in *. auto.
 - simpl. unfold BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Format : T_Format BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond :=
        proj2_format  BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__list__Format
    BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F2 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1F2_cond  BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F1F2_cond2 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__F2F1_cond.
Opaque BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Format.


Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Format_Type := Eval cbn in get_formats BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Format_list : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Format_Type :=
  (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Format, (ServingCellAndBWP_Id_r17__Format, unit__Format)).
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list__Format := Eval compute in choice_format BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__len_helper1 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__len_helper2  BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Format_list.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F1 (z : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type) : (choice BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list) :=
  match z with
   | BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist t => existT _ 0 t
  | BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__unifiedTCI_StateRef_r17 t => existT _ 1 t
  end.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__g := (fun n => typ_set (get_nth_typ BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list n)).
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F2 (y : choice BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list) : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__g n -> BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type) with
    | 0 => fun (t : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist__Type) => BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__explicitlist t 
    | 1 => fun (t : ServingCellAndBWP_Id_r17__Type) => BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__unifiedTCI_StateRef_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type with end) n0
           end t0).

Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__helper2 :  forall (y : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type), BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__cond y -> choice_cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__helper3 :  forall (y : BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type), BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F2 (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__helper4 : (forall b : choice BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list, choice_cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list b -> BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__cond (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F2 b) /\ BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F1 (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F1 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F2.
Definition BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Format : T_Format BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Type BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__cond :=
  (* Eval compute in *) proj2_format BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__list__Format BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F1 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__F2 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__helper2 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__helper3 BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__helper4.
Opaque BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__cond BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Format.

Opaque BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__cond BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__Format.

Opaque BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__cond BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__Format.


Definition BWP_UplinkDedicated__ext1O__Format_Type := Eval cbn in seq_format_prod BWP_UplinkDedicated__ext1O__list.
Definition BWP_UplinkDedicated__ext1O__Format_list : BWP_UplinkDedicated__ext1O__Format_Type :=
  (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17__Format, (Uplink_powerControlId_r17__Format, (BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17__Format, (BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17__Format, unit_format)))).
Definition BWP_UplinkDedicated__ext1O__list__Format := (*Eval compute in *) seq_format BWP_UplinkDedicated__ext1O__list BWP_UplinkDedicated__ext1O__Format_list.
Definition BWP_UplinkDedicated__ext1O__F1 z :=
  (BWP_UplinkDedicated__ext1O__ul_TCI_StateList_r17 z, (BWP_UplinkDedicated__ext1O__ul_powerControl_r17 z, (BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast1_r17 z, (BWP_UplinkDedicated__ext1O__pucch_ConfigurationListMulticast2_r17 z, tt)))).
Definition BWP_UplinkDedicated__ext1O__F2 (y : seq_type BWP_UplinkDedicated__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__BWP_UplinkDedicated__ext1O__Type i0 i1 i2 i3
  end.
Lemma BWP_UplinkDedicated__ext1O__F1F2_cond (z : BWP_UplinkDedicated__ext1O__Type)
  : BWP_UplinkDedicated__ext1O__cond z ->
  (seq_cond BWP_UplinkDedicated__ext1O__list (BWP_UplinkDedicated__ext1O__F1 z)).
intro H. unfold BWP_UplinkDedicated__ext1O__cond in H. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext1O__F1F2_cond2 (z : BWP_UplinkDedicated__ext1O__Type)
 : BWP_UplinkDedicated__ext1O__F2 (BWP_UplinkDedicated__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext1O__F2F1_cond (y : seq_type BWP_UplinkDedicated__ext1O__list)
  : seq_cond BWP_UplinkDedicated__ext1O__list y ->
 (BWP_UplinkDedicated__ext1O__cond (BWP_UplinkDedicated__ext1O__F2 y)) /\  BWP_UplinkDedicated__ext1O__F1 (BWP_UplinkDedicated__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_UplinkDedicated__ext1O__cond. simpl in *. auto.
 - simpl. unfold BWP_UplinkDedicated__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_UplinkDedicated__ext1O__Format : T_Format BWP_UplinkDedicated__ext1O__Type BWP_UplinkDedicated__ext1O__cond :=
        proj2_format  BWP_UplinkDedicated__ext1O__cond BWP_UplinkDedicated__ext1O__list__Format
    BWP_UplinkDedicated__ext1O__F1 BWP_UplinkDedicated__ext1O__F2 BWP_UplinkDedicated__ext1O__F1F2_cond  BWP_UplinkDedicated__ext1O__F1F2_cond2 BWP_UplinkDedicated__ext1O__F2F1_cond.
Opaque BWP_UplinkDedicated__ext1O__cond BWP_UplinkDedicated__ext1O__Format.

Definition BWP_UplinkDedicated__ext1__check_all_none (b : BWP_UplinkDedicated__ext1O__Type) : bool :=
match b with 
  | make__BWP_UplinkDedicated__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition BWP_UplinkDedicated__ext1__Format : T_Format BWP_UplinkDedicated__ext1__Type BWP_UplinkDedicated__ext1__cond :=
  restrict_add_format BWP_UplinkDedicated__ext1__check_all_none BWP_UplinkDedicated__ext1O__Format.

Opaque BWP_UplinkDedicated__ext1__cond BWP_UplinkDedicated__ext1__Format.

Opaque BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__cond BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__Format.

Opaque BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__cond BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__Format.


Definition BWP_UplinkDedicated__ext2O__Format_Type := Eval cbn in seq_format_prod BWP_UplinkDedicated__ext2O__list.
Definition BWP_UplinkDedicated__ext2O__Format_list : BWP_UplinkDedicated__ext2O__Format_Type :=
  (BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17__Format, (BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17__Format, unit_format)).
Definition BWP_UplinkDedicated__ext2O__list__Format := (*Eval compute in *) seq_format BWP_UplinkDedicated__ext2O__list BWP_UplinkDedicated__ext2O__Format_list.
Definition BWP_UplinkDedicated__ext2O__F1 z :=
  (BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast1_r17 z, (BWP_UplinkDedicated__ext2O__pucch_ConfigMulticast2_r17 z, tt)).
Definition BWP_UplinkDedicated__ext2O__F2 (y : seq_type BWP_UplinkDedicated__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BWP_UplinkDedicated__ext2O__Type i0 i1
  end.
Lemma BWP_UplinkDedicated__ext2O__F1F2_cond (z : BWP_UplinkDedicated__ext2O__Type)
  : BWP_UplinkDedicated__ext2O__cond z ->
  (seq_cond BWP_UplinkDedicated__ext2O__list (BWP_UplinkDedicated__ext2O__F1 z)).
intro H. unfold BWP_UplinkDedicated__ext2O__cond in H. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext2O__F1F2_cond2 (z : BWP_UplinkDedicated__ext2O__Type)
 : BWP_UplinkDedicated__ext2O__F2 (BWP_UplinkDedicated__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext2O__F2F1_cond (y : seq_type BWP_UplinkDedicated__ext2O__list)
  : seq_cond BWP_UplinkDedicated__ext2O__list y ->
 (BWP_UplinkDedicated__ext2O__cond (BWP_UplinkDedicated__ext2O__F2 y)) /\  BWP_UplinkDedicated__ext2O__F1 (BWP_UplinkDedicated__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_UplinkDedicated__ext2O__cond. simpl in *. auto.
 - simpl. unfold BWP_UplinkDedicated__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_UplinkDedicated__ext2O__Format : T_Format BWP_UplinkDedicated__ext2O__Type BWP_UplinkDedicated__ext2O__cond :=
        proj2_format  BWP_UplinkDedicated__ext2O__cond BWP_UplinkDedicated__ext2O__list__Format
    BWP_UplinkDedicated__ext2O__F1 BWP_UplinkDedicated__ext2O__F2 BWP_UplinkDedicated__ext2O__F1F2_cond  BWP_UplinkDedicated__ext2O__F1F2_cond2 BWP_UplinkDedicated__ext2O__F2F1_cond.
Opaque BWP_UplinkDedicated__ext2O__cond BWP_UplinkDedicated__ext2O__Format.

Definition BWP_UplinkDedicated__ext2__check_all_none (b : BWP_UplinkDedicated__ext2O__Type) : bool :=
match b with 
  | make__BWP_UplinkDedicated__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition BWP_UplinkDedicated__ext2__Format : T_Format BWP_UplinkDedicated__ext2__Type BWP_UplinkDedicated__ext2__cond :=
  restrict_add_format BWP_UplinkDedicated__ext2__check_all_none BWP_UplinkDedicated__ext2O__Format.

Opaque BWP_UplinkDedicated__ext2__cond BWP_UplinkDedicated__ext2__Format.

Definition BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__Format : T_Format BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__Type BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__cond := seq_of_format PathlossReferenceRS_r17__Format 1 maxNrofPathlossReferenceRSs_r17 BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__helper1 BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__helper2.

Opaque BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__cond BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__Format.

Definition BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__Format : T_Format BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__Type BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__cond := seq_of_format PathlossReferenceRS_Id_r17__Format 1 maxNrofPathlossReferenceRSs_r17 BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__helper1 BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__helper2.

Opaque BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__cond BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__Format.


Definition BWP_UplinkDedicated__ext3O__Format_Type := Eval cbn in seq_format_prod BWP_UplinkDedicated__ext3O__list.
Definition BWP_UplinkDedicated__ext3O__Format_list : BWP_UplinkDedicated__ext3O__Format_Type :=
  (BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17__Format, (BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17__Format, unit_format)).
Definition BWP_UplinkDedicated__ext3O__list__Format := (*Eval compute in *) seq_format BWP_UplinkDedicated__ext3O__list BWP_UplinkDedicated__ext3O__Format_list.
Definition BWP_UplinkDedicated__ext3O__F1 z :=
  (BWP_UplinkDedicated__ext3O__pathlossReferenceRSToAddModList_r17 z, (BWP_UplinkDedicated__ext3O__pathlossReferenceRSToReleaseList_r17 z, tt)).
Definition BWP_UplinkDedicated__ext3O__F2 (y : seq_type BWP_UplinkDedicated__ext3O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BWP_UplinkDedicated__ext3O__Type i0 i1
  end.
Lemma BWP_UplinkDedicated__ext3O__F1F2_cond (z : BWP_UplinkDedicated__ext3O__Type)
  : BWP_UplinkDedicated__ext3O__cond z ->
  (seq_cond BWP_UplinkDedicated__ext3O__list (BWP_UplinkDedicated__ext3O__F1 z)).
intro H. unfold BWP_UplinkDedicated__ext3O__cond in H. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext3O__F1F2_cond2 (z : BWP_UplinkDedicated__ext3O__Type)
 : BWP_UplinkDedicated__ext3O__F2 (BWP_UplinkDedicated__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_UplinkDedicated__ext3O__F2F1_cond (y : seq_type BWP_UplinkDedicated__ext3O__list)
  : seq_cond BWP_UplinkDedicated__ext3O__list y ->
 (BWP_UplinkDedicated__ext3O__cond (BWP_UplinkDedicated__ext3O__F2 y)) /\  BWP_UplinkDedicated__ext3O__F1 (BWP_UplinkDedicated__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_UplinkDedicated__ext3O__cond. simpl in *. auto.
 - simpl. unfold BWP_UplinkDedicated__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_UplinkDedicated__ext3O__Format : T_Format BWP_UplinkDedicated__ext3O__Type BWP_UplinkDedicated__ext3O__cond :=
        proj2_format  BWP_UplinkDedicated__ext3O__cond BWP_UplinkDedicated__ext3O__list__Format
    BWP_UplinkDedicated__ext3O__F1 BWP_UplinkDedicated__ext3O__F2 BWP_UplinkDedicated__ext3O__F1F2_cond  BWP_UplinkDedicated__ext3O__F1F2_cond2 BWP_UplinkDedicated__ext3O__F2F1_cond.
Opaque BWP_UplinkDedicated__ext3O__cond BWP_UplinkDedicated__ext3O__Format.

Definition BWP_UplinkDedicated__ext3__check_all_none (b : BWP_UplinkDedicated__ext3O__Type) : bool :=
match b with 
  | make__BWP_UplinkDedicated__ext3O__Type None None  => false 
  | _ => true 
 end.
Definition BWP_UplinkDedicated__ext3__Format : T_Format BWP_UplinkDedicated__ext3__Type BWP_UplinkDedicated__ext3__cond :=
  restrict_add_format BWP_UplinkDedicated__ext3__check_all_none BWP_UplinkDedicated__ext3O__Format.

Opaque BWP_UplinkDedicated__ext3__cond BWP_UplinkDedicated__ext3__Format.


Definition BWP_UplinkDedicated__root_Format_Type := Eval cbn in seq_format_prod BWP_UplinkDedicated__root_list.
Definition BWP_UplinkDedicated__root_Format_list : BWP_UplinkDedicated__root_Format_Type :=
  (BWP_UplinkDedicated__pucch_Config__Format, (BWP_UplinkDedicated__pusch_Config__Format, (BWP_UplinkDedicated__configuredGrantConfig__Format, (BWP_UplinkDedicated__srs_Config__Format, (BWP_UplinkDedicated__beamFailureRecoveryConfig__Format, unit_format))))).

Definition BWP_UplinkDedicated__ext_Format_Type := Eval cbn in get_formats BWP_UplinkDedicated__ext_list.
Definition BWP_UplinkDedicated__ext_Format_list : BWP_UplinkDedicated__ext_Format_Type :=
  (BWP_UplinkDedicated__ext0__Format, (BWP_UplinkDedicated__ext1__Format, (BWP_UplinkDedicated__ext2__Format, (BWP_UplinkDedicated__ext3__Format, unit__Format)))).

Definition BWP_UplinkDedicated__list_type : Set := (seq_type BWP_UplinkDedicated__root_list) * (seq_ext_type BWP_UplinkDedicated__ext_list).
Definition BWP_UplinkDedicated__list_cond (z : BWP_UplinkDedicated__list_type) : Prop :=
        (seq_cond BWP_UplinkDedicated__root_list (fst z)) /\ (seq_ext_cond BWP_UplinkDedicated__ext_list (snd z)).
Definition BWP_UplinkDedicated__list_format : T_Format BWP_UplinkDedicated__list_type BWP_UplinkDedicated__list_cond :=
 (* Eval compute in *) seq_ext_format BWP_UplinkDedicated__root_list BWP_UplinkDedicated__root_Format_list BWP_UplinkDedicated__ext_list BWP_UplinkDedicated__ext_Format_list.

Opaque BWP_UplinkDedicated__list_format.
Definition BWP_UplinkDedicated__F1 (z : BWP_UplinkDedicated__Type) : BWP_UplinkDedicated__list_type :=
  (((BWP_UplinkDedicated__pucch_Config z, (BWP_UplinkDedicated__pusch_Config z, (BWP_UplinkDedicated__configuredGrantConfig z, (BWP_UplinkDedicated__srs_Config z, (BWP_UplinkDedicated__beamFailureRecoveryConfig z, tt)))))), (
(BWP_UplinkDedicated__ext0 z, (BWP_UplinkDedicated__ext1 z, (BWP_UplinkDedicated__ext2 z, (BWP_UplinkDedicated__ext3 z, tt)))))).
Definition BWP_UplinkDedicated__F2 (y : BWP_UplinkDedicated__list_type) : BWP_UplinkDedicated__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, (i1, (i2, (i3, _)))))=>
    make__BWP_UplinkDedicated__Type j0 j1 j2 j3 j4 i0 i1 i2 i3
  end.
Definition BWP_UplinkDedicated__helper1 : (forall a : BWP_UplinkDedicated__Type, BWP_UplinkDedicated__cond a -> BWP_UplinkDedicated__list_cond (BWP_UplinkDedicated__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BWP_UplinkDedicated__helper2 : (forall a : BWP_UplinkDedicated__Type, BWP_UplinkDedicated__F2 (BWP_UplinkDedicated__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BWP_UplinkDedicated__helper3 : (forall b : BWP_UplinkDedicated__list_type, BWP_UplinkDedicated__list_cond b -> BWP_UplinkDedicated__cond (BWP_UplinkDedicated__F2 b) /\ BWP_UplinkDedicated__F1 (BWP_UplinkDedicated__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BWP_UplinkDedicated__cond, BWP_UplinkDedicated__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BWP_UplinkDedicated__Format : T_Format BWP_UplinkDedicated__Type BWP_UplinkDedicated__cond :=
 proj2_format BWP_UplinkDedicated__cond BWP_UplinkDedicated__list_format  BWP_UplinkDedicated__F1 BWP_UplinkDedicated__F2 BWP_UplinkDedicated__helper1 BWP_UplinkDedicated__helper2 BWP_UplinkDedicated__helper3.

Opaque BWP_UplinkDedicated__cond BWP_UplinkDedicated__Format.

