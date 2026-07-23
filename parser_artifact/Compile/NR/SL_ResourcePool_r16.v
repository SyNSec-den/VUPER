Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SL_PSCCH_Config_r16.
Definition SL_ResourcePool_r16__sl_PSCCH_Config_r16__Type := SetupRelease__Type SL_PSCCH_Config_r16__Type.
Definition SL_ResourcePool_r16__sl_PSCCH_Config_r16__cond := SetupRelease__cond _ SL_PSCCH_Config_r16__cond.
Definition SL_ResourcePool_r16__sl_PSCCH_Config_r16__Format : T_Format SL_ResourcePool_r16__sl_PSCCH_Config_r16__Type SL_ResourcePool_r16__sl_PSCCH_Config_r16__cond := SetupRelease__Format _ _ SL_PSCCH_Config_r16__Format.
Opaque SL_ResourcePool_r16__sl_PSCCH_Config_r16__cond SL_ResourcePool_r16__sl_PSCCH_Config_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_PSSCH_Config_r16.
Definition SL_ResourcePool_r16__sl_PSSCH_Config_r16__Type := SetupRelease__Type SL_PSSCH_Config_r16__Type.
Definition SL_ResourcePool_r16__sl_PSSCH_Config_r16__cond := SetupRelease__cond _ SL_PSSCH_Config_r16__cond.
Definition SL_ResourcePool_r16__sl_PSSCH_Config_r16__Format : T_Format SL_ResourcePool_r16__sl_PSSCH_Config_r16__Type SL_ResourcePool_r16__sl_PSSCH_Config_r16__cond := SetupRelease__Format _ _ SL_PSSCH_Config_r16__Format.
Opaque SL_ResourcePool_r16__sl_PSSCH_Config_r16__cond SL_ResourcePool_r16__sl_PSSCH_Config_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_PSFCH_Config_r16.
Definition SL_ResourcePool_r16__sl_PSFCH_Config_r16__Type := SetupRelease__Type SL_PSFCH_Config_r16__Type.
Definition SL_ResourcePool_r16__sl_PSFCH_Config_r16__cond := SetupRelease__cond _ SL_PSFCH_Config_r16__cond.
Definition SL_ResourcePool_r16__sl_PSFCH_Config_r16__Format : T_Format SL_ResourcePool_r16__sl_PSFCH_Config_r16__Type SL_ResourcePool_r16__sl_PSFCH_Config_r16__cond := SetupRelease__Format _ _ SL_PSFCH_Config_r16__Format.
Opaque SL_ResourcePool_r16__sl_PSFCH_Config_r16__cond SL_ResourcePool_r16__sl_PSFCH_Config_r16__Format.

Require Import NR.SL_SyncAllowed_r16.

Opaque SL_SyncAllowed_r16__cond SL_SyncAllowed_r16__Format.

Inductive SL_ResourcePool_r16__sl_SubchannelSize_r16__Type : Set :=
 | SL_ResourcePool_r16__sl_SubchannelSize_r16__n10
 | SL_ResourcePool_r16__sl_SubchannelSize_r16__n12
 | SL_ResourcePool_r16__sl_SubchannelSize_r16__n15
 | SL_ResourcePool_r16__sl_SubchannelSize_r16__n20
 | SL_ResourcePool_r16__sl_SubchannelSize_r16__n25
 | SL_ResourcePool_r16__sl_SubchannelSize_r16__n50
 | SL_ResourcePool_r16__sl_SubchannelSize_r16__n75
 | SL_ResourcePool_r16__sl_SubchannelSize_r16__n100
.
Definition SL_ResourcePool_r16__sl_SubchannelSize_r16__cond := (fun (_ : SL_ResourcePool_r16__sl_SubchannelSize_r16__Type) => True).
Lemma SL_ResourcePool_r16__sl_SubchannelSize_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ResourcePool_r16__sl_SubchannelSize_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_ResourcePool_r16__sl_SubchannelSize_r16__nat__helper.

Definition SL_ResourcePool_r16__sl_SubchannelSize_r16__F1 t :=
  match t with
  | SL_ResourcePool_r16__sl_SubchannelSize_r16__n10 => 0
  | SL_ResourcePool_r16__sl_SubchannelSize_r16__n12 => 1
  | SL_ResourcePool_r16__sl_SubchannelSize_r16__n15 => 2
  | SL_ResourcePool_r16__sl_SubchannelSize_r16__n20 => 3
  | SL_ResourcePool_r16__sl_SubchannelSize_r16__n25 => 4
  | SL_ResourcePool_r16__sl_SubchannelSize_r16__n50 => 5
  | SL_ResourcePool_r16__sl_SubchannelSize_r16__n75 => 6
  | SL_ResourcePool_r16__sl_SubchannelSize_r16__n100 => 7
  end.
Definition SL_ResourcePool_r16__sl_SubchannelSize_r16__F2 n :=
  match n with
  | 0 => SL_ResourcePool_r16__sl_SubchannelSize_r16__n10
  | 1 => SL_ResourcePool_r16__sl_SubchannelSize_r16__n12
  | 2 => SL_ResourcePool_r16__sl_SubchannelSize_r16__n15
  | 3 => SL_ResourcePool_r16__sl_SubchannelSize_r16__n20
  | 4 => SL_ResourcePool_r16__sl_SubchannelSize_r16__n25
  | 5 => SL_ResourcePool_r16__sl_SubchannelSize_r16__n50
  | 6 => SL_ResourcePool_r16__sl_SubchannelSize_r16__n75
  | 7 => SL_ResourcePool_r16__sl_SubchannelSize_r16__n100
  | _ => SL_ResourcePool_r16__sl_SubchannelSize_r16__n10
  end.
Lemma SL_ResourcePool_r16__sl_SubchannelSize_r16__F1F2 : forall x : SL_ResourcePool_r16__sl_SubchannelSize_r16__Type, (SL_ResourcePool_r16__sl_SubchannelSize_r16__F1 x <= 7) /\ SL_ResourcePool_r16__sl_SubchannelSize_r16__F2 (SL_ResourcePool_r16__sl_SubchannelSize_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ResourcePool_r16__sl_SubchannelSize_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_ResourcePool_r16__sl_SubchannelSize_r16__F1 (SL_ResourcePool_r16__sl_SubchannelSize_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_ResourcePool_r16__dummy__helper1 : (10 <= 160)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__dummy__helper2 : to_bit_sz (Z.to_nat (160 - 10)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (160 - 10))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__dummy__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__dummy__Type := Z.
Definition SL_ResourcePool_r16__dummy__cond := (fun z => (10 <= z <= 160)%Z).
Lemma SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__helper1 : (0 <= 265)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__helper2 : to_bit_sz (Z.to_nat (265 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (265 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__Type := Z.
Definition SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__cond := (fun z => (0 <= z <= 265)%Z).
Lemma SL_ResourcePool_r16__sl_NumSubchannel_r16__helper1 : (1 <= 27)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__sl_NumSubchannel_r16__helper2 : to_bit_sz (Z.to_nat (27 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (27 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__sl_NumSubchannel_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__sl_NumSubchannel_r16__Type := Z.
Definition SL_ResourcePool_r16__sl_NumSubchannel_r16__cond := (fun z => (1 <= z <= 27)%Z).
Inductive SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Type : Set :=
 | SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam256
 | SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam64LowSE
 | SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam256_qam64LowSE
.
Definition SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__cond := (fun (_ : SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Type) => True).
Lemma SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__nat__helper.

Definition SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F1 t :=
  match t with
  | SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam256 => 0
  | SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam64LowSE => 1
  | SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam256_qam64LowSE => 2
  end.
Definition SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F2 n :=
  match n with
  | 0 => SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam256
  | 1 => SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam64LowSE
  | 2 => SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam256_qam64LowSE
  | _ => SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__qam256
  end.
Lemma SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F1F2 : forall x : SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Type, (SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F1 x <= 2) /\ SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F2 (SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F2F1 : forall (y : nat) (H : y <= 2), SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F1 (SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__helper1 : (0 <= 45)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__helper2 : to_bit_sz (Z.to_nat (45 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (45 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__Type := Z.
Definition SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__cond := (fun z => (0 <= z <= 45)%Z).
Inductive SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Type : Set :=
 | SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__ms100
 | SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__slot100
.
Definition SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__cond := (fun (_ : SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Type) => True).
Lemma SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__nat__helper.

Definition SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F1 t :=
  match t with
  | SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__ms100 => 0
  | SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__slot100 => 1
  end.
Definition SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F2 n :=
  match n with
  | 0 => SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__ms100
  | 1 => SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__slot100
  | _ => SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__ms100
  end.
Lemma SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F1F2 : forall x : SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Type, (SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F1 x <= 1) /\ SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F2 (SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F1 (SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Type : Set :=
 | SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__ms1000
 | SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__slot1000
.
Definition SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__cond := (fun (_ : SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Type) => True).
Lemma SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__nat__helper.

Definition SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F1 t :=
  match t with
  | SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__ms1000 => 0
  | SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__slot1000 => 1
  end.
Definition SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F2 n :=
  match n with
  | 0 => SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__ms1000
  | 1 => SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__slot1000
  | _ => SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__ms1000
  end.
Lemma SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F1F2 : forall x : SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Type, (SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F1 x <= 1) /\ SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F2 (SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F1 (SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_PTRS_Config_r16.

Opaque SL_PTRS_Config_r16__cond SL_PTRS_Config_r16__Format.

Require Import NR.SL_UE_SelectedConfigRP_r16.

Opaque SL_UE_SelectedConfigRP_r16__cond SL_UE_SelectedConfigRP_r16__Format.

Require Import NR.TDD_UL_DL_ConfigCommon.

Opaque TDD_UL_DL_ConfigCommon__cond TDD_UL_DL_ConfigCommon__Format.

Lemma SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__Type := Z.
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__cond := (fun z => (0 <= z <= 15)%Z).
Record SL_ResourcePool_r16__sl_RxParametersNcell_r16__Type : Set :=
  make__SL_ResourcePool_r16__sl_RxParametersNcell_r16__Type {
    SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_TDD_Configuration_r16 : option TDD_UL_DL_ConfigCommon__Type ;
    SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16 : Z ;
}.
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__list := (
 Opt TDD_UL_DL_ConfigCommon__Type TDD_UL_DL_ConfigCommon__cond ::
 Nor Z SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__cond ::
 nil).
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond z := 
  opt_cond TDD_UL_DL_ConfigCommon__cond (SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_TDD_Configuration_r16 z) /\
  SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__cond (SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16 z) /\
  True.

Require Import NR.SL_ZoneConfigMCR_r16.

Opaque SL_ZoneConfigMCR_r16__cond SL_ZoneConfigMCR_r16__Format.

Definition SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__Type := list SL_ZoneConfigMCR_r16__Type.

Definition SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__cond (z : SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__Type) := (list_and SL_ZoneConfigMCR_r16__cond z) /\ (length z = Z.to_nat 16).

Require Import NR.FilterCoefficient.

Opaque FilterCoefficient__cond FilterCoefficient__Format.

Lemma SL_ResourcePool_r16__sl_RB_Number_r16__helper1 : (10 <= 275)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__sl_RB_Number_r16__helper2 : to_bit_sz (Z.to_nat (275 - 10)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (275 - 10))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__sl_RB_Number_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__sl_RB_Number_r16__Type := Z.
Definition SL_ResourcePool_r16__sl_RB_Number_r16__cond := (fun z => (10 <= z <= 275)%Z).
Inductive SL_ResourcePool_r16__sl_PreemptionEnable_r16__Type : Set :=
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__enabled
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl1
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl2
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl3
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl4
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl5
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl6
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl7
 | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl8
.
Definition SL_ResourcePool_r16__sl_PreemptionEnable_r16__cond := (fun (_ : SL_ResourcePool_r16__sl_PreemptionEnable_r16__Type) => True).
Lemma SL_ResourcePool_r16__sl_PreemptionEnable_r16__nat__helper : to_bit_sz 8 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ResourcePool_r16__sl_PreemptionEnable_r16__nat__Format : T_Format nat (fun z => (z <= 8)) :=
  nat_enum_format 8 SL_ResourcePool_r16__sl_PreemptionEnable_r16__nat__helper.

Definition SL_ResourcePool_r16__sl_PreemptionEnable_r16__F1 t :=
  match t with
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__enabled => 0
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl1 => 1
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl2 => 2
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl3 => 3
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl4 => 4
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl5 => 5
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl6 => 6
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl7 => 7
  | SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl8 => 8
  end.
Definition SL_ResourcePool_r16__sl_PreemptionEnable_r16__F2 n :=
  match n with
  | 0 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__enabled
  | 1 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl1
  | 2 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl2
  | 3 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl3
  | 4 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl4
  | 5 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl5
  | 6 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl6
  | 7 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl7
  | 8 => SL_ResourcePool_r16__sl_PreemptionEnable_r16__pl8
  | _ => SL_ResourcePool_r16__sl_PreemptionEnable_r16__enabled
  end.
Lemma SL_ResourcePool_r16__sl_PreemptionEnable_r16__F1F2 : forall x : SL_ResourcePool_r16__sl_PreemptionEnable_r16__Type, (SL_ResourcePool_r16__sl_PreemptionEnable_r16__F1 x <= 8) /\ SL_ResourcePool_r16__sl_PreemptionEnable_r16__F2 (SL_ResourcePool_r16__sl_PreemptionEnable_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ResourcePool_r16__sl_PreemptionEnable_r16__F2F1 : forall (y : nat) (H : y <= 8), SL_ResourcePool_r16__sl_PreemptionEnable_r16__F1 (SL_ResourcePool_r16__sl_PreemptionEnable_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__helper1 : (1 <= 9)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__helper2 : to_bit_sz (Z.to_nat (9 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__Type := Z.
Definition SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__cond := (fun z => (1 <= z <= 9)%Z).
Lemma SL_ResourcePool_r16__sl_PriorityThreshold_r16__helper1 : (1 <= 9)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__sl_PriorityThreshold_r16__helper2 : to_bit_sz (Z.to_nat (9 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__sl_PriorityThreshold_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__sl_PriorityThreshold_r16__Type := Z.
Definition SL_ResourcePool_r16__sl_PriorityThreshold_r16__cond := (fun z => (1 <= z <= 9)%Z).
Inductive SL_ResourcePool_r16__sl_X_Overhead_r16__Type : Set :=
 | SL_ResourcePool_r16__sl_X_Overhead_r16__n0
 | SL_ResourcePool_r16__sl_X_Overhead_r16__n3
 | SL_ResourcePool_r16__sl_X_Overhead_r16__n6
 | SL_ResourcePool_r16__sl_X_Overhead_r16__n9
.
Definition SL_ResourcePool_r16__sl_X_Overhead_r16__cond := (fun (_ : SL_ResourcePool_r16__sl_X_Overhead_r16__Type) => True).
Lemma SL_ResourcePool_r16__sl_X_Overhead_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_ResourcePool_r16__sl_X_Overhead_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SL_ResourcePool_r16__sl_X_Overhead_r16__nat__helper.

Definition SL_ResourcePool_r16__sl_X_Overhead_r16__F1 t :=
  match t with
  | SL_ResourcePool_r16__sl_X_Overhead_r16__n0 => 0
  | SL_ResourcePool_r16__sl_X_Overhead_r16__n3 => 1
  | SL_ResourcePool_r16__sl_X_Overhead_r16__n6 => 2
  | SL_ResourcePool_r16__sl_X_Overhead_r16__n9 => 3
  end.
Definition SL_ResourcePool_r16__sl_X_Overhead_r16__F2 n :=
  match n with
  | 0 => SL_ResourcePool_r16__sl_X_Overhead_r16__n0
  | 1 => SL_ResourcePool_r16__sl_X_Overhead_r16__n3
  | 2 => SL_ResourcePool_r16__sl_X_Overhead_r16__n6
  | 3 => SL_ResourcePool_r16__sl_X_Overhead_r16__n9
  | _ => SL_ResourcePool_r16__sl_X_Overhead_r16__n0
  end.
Lemma SL_ResourcePool_r16__sl_X_Overhead_r16__F1F2 : forall x : SL_ResourcePool_r16__sl_X_Overhead_r16__Type, (SL_ResourcePool_r16__sl_X_Overhead_r16__F1 x <= 3) /\ SL_ResourcePool_r16__sl_X_Overhead_r16__F2 (SL_ResourcePool_r16__sl_X_Overhead_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_ResourcePool_r16__sl_X_Overhead_r16__F2F1 : forall (y : nat) (H : y <= 3), SL_ResourcePool_r16__sl_X_Overhead_r16__F1 (SL_ResourcePool_r16__sl_X_Overhead_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_PowerControl_r16.

Opaque SL_PowerControl_r16__cond SL_PowerControl_r16__Format.

Require Import NR.SL_TxPercentageList_r16.

Opaque SL_TxPercentageList_r16__cond SL_TxPercentageList_r16__Format.

Require Import NR.SL_MinMaxMCS_List_r16.

Opaque SL_MinMaxMCS_List_r16__cond SL_MinMaxMCS_List_r16__Format.

Lemma SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__helper1 : (0 <= 10 <= 160)%Z.  lia. Qed.
Lemma SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__helper2 : to_bit_sz (Z.to_nat (160 - 10)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (160 - 10))%Z). { apply Zorder.Zle_minus_le_0. apply SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__Type := bit_string.
Definition SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__cond := (fun z : bit_string => (10 <= Z.of_nat (fst z) <= 160)%Z /\ bit_string_len_prop (fst z) (snd z)).
Record SL_ResourcePool_r16__ext0O__Type : Set :=
  make__SL_ResourcePool_r16__ext0O__Type {
    SL_ResourcePool_r16__ext0O__sl_TimeResource_r16 : option SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__Type ;
}.
Definition SL_ResourcePool_r16__ext0O__list := (
 Opt SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__Type SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__cond ::
 nil).
Definition SL_ResourcePool_r16__ext0O__cond z := 
  opt_cond SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__cond (SL_ResourcePool_r16__ext0O__sl_TimeResource_r16 z) /\
  True.

Definition SL_ResourcePool_r16__ext0__Type := SL_ResourcePool_r16__ext0O__Type.
Definition SL_ResourcePool_r16__ext0__cond := SL_ResourcePool_r16__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.SL_PBPS_CPS_Config_r17.
Definition SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__Type := SetupRelease__Type SL_PBPS_CPS_Config_r17__Type.
Definition SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__cond := SetupRelease__cond _ SL_PBPS_CPS_Config_r17__cond.
Definition SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__Format : T_Format SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__Type SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__cond := SetupRelease__Format _ _ SL_PBPS_CPS_Config_r17__Format.
Opaque SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__cond SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_InterUE_CoordinationConfig_r17.
Definition SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__Type := SetupRelease__Type SL_InterUE_CoordinationConfig_r17__Type.
Definition SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__cond := SetupRelease__cond _ SL_InterUE_CoordinationConfig_r17__cond.
Definition SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__Format : T_Format SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__Type SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__cond := SetupRelease__Format _ _ SL_InterUE_CoordinationConfig_r17__Format.
Opaque SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__cond SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__Format.

Record SL_ResourcePool_r16__ext1O__Type : Set :=
  make__SL_ResourcePool_r16__ext1O__Type {
    SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17 : option SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__Type ;
    SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17 : option SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__Type ;
}.
Definition SL_ResourcePool_r16__ext1O__list := (
 Opt SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__Type SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__cond ::
 Opt SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__Type SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__cond ::
 nil).
Definition SL_ResourcePool_r16__ext1O__cond z := 
  opt_cond SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__cond (SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17 z) /\
  opt_cond SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__cond (SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17 z) /\
  True.

Definition SL_ResourcePool_r16__ext1__Type := SL_ResourcePool_r16__ext1O__Type.
Definition SL_ResourcePool_r16__ext1__cond := SL_ResourcePool_r16__ext1O__cond.

Record SL_ResourcePool_r16__Type : Set :=
  make__SL_ResourcePool_r16__Type {
    SL_ResourcePool_r16__sl_PSCCH_Config_r16 : option SL_ResourcePool_r16__sl_PSCCH_Config_r16__Type ;
    SL_ResourcePool_r16__sl_PSSCH_Config_r16 : option SL_ResourcePool_r16__sl_PSSCH_Config_r16__Type ;
    SL_ResourcePool_r16__sl_PSFCH_Config_r16 : option SL_ResourcePool_r16__sl_PSFCH_Config_r16__Type ;
    SL_ResourcePool_r16__sl_SyncAllowed_r16 : option SL_SyncAllowed_r16__Type ;
    SL_ResourcePool_r16__sl_SubchannelSize_r16 : option SL_ResourcePool_r16__sl_SubchannelSize_r16__Type ;
    SL_ResourcePool_r16__dummy : option Z ;
    SL_ResourcePool_r16__sl_StartRB_Subchannel_r16 : option Z ;
    SL_ResourcePool_r16__sl_NumSubchannel_r16 : option Z ;
    SL_ResourcePool_r16__sl_Additional_MCS_Table_r16 : option SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Type ;
    SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16 : option Z ;
    SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16 : option SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Type ;
    SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16 : option SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Type ;
    SL_ResourcePool_r16__sl_PTRS_Config_r16 : option SL_PTRS_Config_r16__Type ;
    SL_ResourcePool_r16__sl_UE_SelectedConfigRP_r16 : option SL_UE_SelectedConfigRP_r16__Type ;
    SL_ResourcePool_r16__sl_RxParametersNcell_r16 : option SL_ResourcePool_r16__sl_RxParametersNcell_r16__Type ;
    SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16 : option SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__Type ;
    SL_ResourcePool_r16__sl_FilterCoefficient_r16 : option FilterCoefficient__Type ;
    SL_ResourcePool_r16__sl_RB_Number_r16 : option Z ;
    SL_ResourcePool_r16__sl_PreemptionEnable_r16 : option SL_ResourcePool_r16__sl_PreemptionEnable_r16__Type ;
    SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16 : option Z ;
    SL_ResourcePool_r16__sl_PriorityThreshold_r16 : option Z ;
    SL_ResourcePool_r16__sl_X_Overhead_r16 : option SL_ResourcePool_r16__sl_X_Overhead_r16__Type ;
    SL_ResourcePool_r16__sl_PowerControl_r16 : option SL_PowerControl_r16__Type ;
    SL_ResourcePool_r16__sl_TxPercentageList_r16 : option SL_TxPercentageList_r16__Type ;
    SL_ResourcePool_r16__sl_MinMaxMCS_List_r16 : option SL_MinMaxMCS_List_r16__Type ;
    SL_ResourcePool_r16__ext0 : option SL_ResourcePool_r16__ext0__Type ;
    SL_ResourcePool_r16__ext1 : option SL_ResourcePool_r16__ext1__Type ;
}.
Definition SL_ResourcePool_r16__root_list : list seq_elem := (
 Opt SL_ResourcePool_r16__sl_PSCCH_Config_r16__Type SL_ResourcePool_r16__sl_PSCCH_Config_r16__cond ::
 Opt SL_ResourcePool_r16__sl_PSSCH_Config_r16__Type SL_ResourcePool_r16__sl_PSSCH_Config_r16__cond ::
 Opt SL_ResourcePool_r16__sl_PSFCH_Config_r16__Type SL_ResourcePool_r16__sl_PSFCH_Config_r16__cond ::
 Opt SL_SyncAllowed_r16__Type SL_SyncAllowed_r16__cond ::
 Opt SL_ResourcePool_r16__sl_SubchannelSize_r16__Type SL_ResourcePool_r16__sl_SubchannelSize_r16__cond ::
 Opt Z SL_ResourcePool_r16__dummy__cond ::
 Opt Z SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__cond ::
 Opt Z SL_ResourcePool_r16__sl_NumSubchannel_r16__cond ::
 Opt SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Type SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__cond ::
 Opt Z SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__cond ::
 Opt SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Type SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__cond ::
 Opt SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Type SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__cond ::
 Opt SL_PTRS_Config_r16__Type SL_PTRS_Config_r16__cond ::
 Opt SL_UE_SelectedConfigRP_r16__Type SL_UE_SelectedConfigRP_r16__cond ::
 Opt SL_ResourcePool_r16__sl_RxParametersNcell_r16__Type SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond ::
 Opt SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__Type SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__cond ::
 Opt FilterCoefficient__Type FilterCoefficient__cond ::
 Opt Z SL_ResourcePool_r16__sl_RB_Number_r16__cond ::
 Opt SL_ResourcePool_r16__sl_PreemptionEnable_r16__Type SL_ResourcePool_r16__sl_PreemptionEnable_r16__cond ::
 Opt Z SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__cond ::
 Opt Z SL_ResourcePool_r16__sl_PriorityThreshold_r16__cond ::
 Opt SL_ResourcePool_r16__sl_X_Overhead_r16__Type SL_ResourcePool_r16__sl_X_Overhead_r16__cond ::
 Opt SL_PowerControl_r16__Type SL_PowerControl_r16__cond ::
 Opt SL_TxPercentageList_r16__Type SL_TxPercentageList_r16__cond ::
 Opt SL_MinMaxMCS_List_r16__Type SL_MinMaxMCS_List_r16__cond ::
 nil).
Definition SL_ResourcePool_r16__ext_list : list typ := (
  typ_cons SL_ResourcePool_r16__ext0__Type SL_ResourcePool_r16__ext0__cond ::
  typ_cons SL_ResourcePool_r16__ext1__Type SL_ResourcePool_r16__ext1__cond ::
  nil).
Definition SL_ResourcePool_r16__cond (z : SL_ResourcePool_r16__Type) := 
(  opt_cond SL_ResourcePool_r16__sl_PSCCH_Config_r16__cond (SL_ResourcePool_r16__sl_PSCCH_Config_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_PSSCH_Config_r16__cond (SL_ResourcePool_r16__sl_PSSCH_Config_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_PSFCH_Config_r16__cond (SL_ResourcePool_r16__sl_PSFCH_Config_r16 z) /\
  opt_cond SL_SyncAllowed_r16__cond (SL_ResourcePool_r16__sl_SyncAllowed_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_SubchannelSize_r16__cond (SL_ResourcePool_r16__sl_SubchannelSize_r16 z) /\
  opt_cond SL_ResourcePool_r16__dummy__cond (SL_ResourcePool_r16__dummy z) /\
  opt_cond SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__cond (SL_ResourcePool_r16__sl_StartRB_Subchannel_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_NumSubchannel_r16__cond (SL_ResourcePool_r16__sl_NumSubchannel_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__cond (SL_ResourcePool_r16__sl_Additional_MCS_Table_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__cond (SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__cond (SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__cond (SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16 z) /\
  opt_cond SL_PTRS_Config_r16__cond (SL_ResourcePool_r16__sl_PTRS_Config_r16 z) /\
  opt_cond SL_UE_SelectedConfigRP_r16__cond (SL_ResourcePool_r16__sl_UE_SelectedConfigRP_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond (SL_ResourcePool_r16__sl_RxParametersNcell_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__cond (SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16 z) /\
  opt_cond FilterCoefficient__cond (SL_ResourcePool_r16__sl_FilterCoefficient_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_RB_Number_r16__cond (SL_ResourcePool_r16__sl_RB_Number_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_PreemptionEnable_r16__cond (SL_ResourcePool_r16__sl_PreemptionEnable_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__cond (SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_PriorityThreshold_r16__cond (SL_ResourcePool_r16__sl_PriorityThreshold_r16 z) /\
  opt_cond SL_ResourcePool_r16__sl_X_Overhead_r16__cond (SL_ResourcePool_r16__sl_X_Overhead_r16 z) /\
  opt_cond SL_PowerControl_r16__cond (SL_ResourcePool_r16__sl_PowerControl_r16 z) /\
  opt_cond SL_TxPercentageList_r16__cond (SL_ResourcePool_r16__sl_TxPercentageList_r16 z) /\
  opt_cond SL_MinMaxMCS_List_r16__cond (SL_ResourcePool_r16__sl_MinMaxMCS_List_r16 z) /\
  True) /\ 
(  opt_cond SL_ResourcePool_r16__ext0__cond (SL_ResourcePool_r16__ext0 z) /\
  opt_cond SL_ResourcePool_r16__ext1__cond (SL_ResourcePool_r16__ext1 z) /\
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
Opaque SL_ResourcePool_r16__sl_PSCCH_Config_r16__cond SL_ResourcePool_r16__sl_PSCCH_Config_r16__Format.

Opaque SL_ResourcePool_r16__sl_PSSCH_Config_r16__cond SL_ResourcePool_r16__sl_PSSCH_Config_r16__Format.

Opaque SL_ResourcePool_r16__sl_PSFCH_Config_r16__cond SL_ResourcePool_r16__sl_PSFCH_Config_r16__Format.

Definition SL_ResourcePool_r16__sl_SubchannelSize_r16__Format : T_Format SL_ResourcePool_r16__sl_SubchannelSize_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ResourcePool_r16__sl_SubchannelSize_r16__nat__Format SL_ResourcePool_r16__sl_SubchannelSize_r16__F1 SL_ResourcePool_r16__sl_SubchannelSize_r16__F2 SL_ResourcePool_r16__sl_SubchannelSize_r16__F1F2 SL_ResourcePool_r16__sl_SubchannelSize_r16__F2F1.

Opaque SL_ResourcePool_r16__sl_SubchannelSize_r16__cond SL_ResourcePool_r16__sl_SubchannelSize_r16__Format.

Definition SL_ResourcePool_r16__dummy__Format : T_Format Z SL_ResourcePool_r16__dummy__cond :=
 ranged_int_format (10) (160) SL_ResourcePool_r16__dummy__helper1 SL_ResourcePool_r16__dummy__helper2.

Opaque SL_ResourcePool_r16__dummy__cond SL_ResourcePool_r16__dummy__Format.

Definition SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__Format : T_Format Z SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__cond :=
 ranged_int_format (0) (265) SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__helper1 SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__helper2.

Opaque SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__cond SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__Format.

Definition SL_ResourcePool_r16__sl_NumSubchannel_r16__Format : T_Format Z SL_ResourcePool_r16__sl_NumSubchannel_r16__cond :=
 ranged_int_format (1) (27) SL_ResourcePool_r16__sl_NumSubchannel_r16__helper1 SL_ResourcePool_r16__sl_NumSubchannel_r16__helper2.

Opaque SL_ResourcePool_r16__sl_NumSubchannel_r16__cond SL_ResourcePool_r16__sl_NumSubchannel_r16__Format.

Definition SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Format : T_Format SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__nat__Format SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F1 SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F2 SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F1F2 SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__F2F1.

Opaque SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__cond SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Format.

Definition SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__Format : T_Format Z SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__cond :=
 ranged_int_format (0) (45) SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__helper1 SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__helper2.

Opaque SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__cond SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__Format.

Definition SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Format : T_Format SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__nat__Format SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F1 SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F2 SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F1F2 SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__F2F1.

Opaque SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__cond SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Format.

Definition SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Format : T_Format SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__nat__Format SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F1 SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F2 SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F1F2 SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__F2F1.

Opaque SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__cond SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Format.

Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__Format : T_Format Z SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__cond :=
 ranged_int_format (0) (15) SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__helper1 SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__helper2.

Opaque SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__cond SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__Format.


Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__Format_Type := Eval cbn in seq_format_prod SL_ResourcePool_r16__sl_RxParametersNcell_r16__list.
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__Format_list : SL_ResourcePool_r16__sl_RxParametersNcell_r16__Format_Type :=
  (TDD_UL_DL_ConfigCommon__Format, (SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16__Format, unit_format)).
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__list__Format := (*Eval compute in *) seq_format SL_ResourcePool_r16__sl_RxParametersNcell_r16__list SL_ResourcePool_r16__sl_RxParametersNcell_r16__Format_list.
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1 z :=
  (SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_TDD_Configuration_r16 z, (SL_ResourcePool_r16__sl_RxParametersNcell_r16__sl_SyncConfigIndex_r16 z, tt)).
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__F2 (y : seq_type SL_ResourcePool_r16__sl_RxParametersNcell_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SL_ResourcePool_r16__sl_RxParametersNcell_r16__Type i0 i1
  end.
Lemma SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1F2_cond (z : SL_ResourcePool_r16__sl_RxParametersNcell_r16__Type)
  : SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond z ->
  (seq_cond SL_ResourcePool_r16__sl_RxParametersNcell_r16__list (SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1 z)).
intro H. unfold SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond in H. simpl. auto. Qed.
Lemma SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1F2_cond2 (z : SL_ResourcePool_r16__sl_RxParametersNcell_r16__Type)
 : SL_ResourcePool_r16__sl_RxParametersNcell_r16__F2 (SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_ResourcePool_r16__sl_RxParametersNcell_r16__F2F1_cond (y : seq_type SL_ResourcePool_r16__sl_RxParametersNcell_r16__list)
  : seq_cond SL_ResourcePool_r16__sl_RxParametersNcell_r16__list y ->
 (SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond (SL_ResourcePool_r16__sl_RxParametersNcell_r16__F2 y)) /\  SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1 (SL_ResourcePool_r16__sl_RxParametersNcell_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond. simpl in *. auto.
 - simpl. unfold SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_ResourcePool_r16__sl_RxParametersNcell_r16__Format : T_Format SL_ResourcePool_r16__sl_RxParametersNcell_r16__Type SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond :=
        proj2_format  SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond SL_ResourcePool_r16__sl_RxParametersNcell_r16__list__Format
    SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1 SL_ResourcePool_r16__sl_RxParametersNcell_r16__F2 SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1F2_cond  SL_ResourcePool_r16__sl_RxParametersNcell_r16__F1F2_cond2 SL_ResourcePool_r16__sl_RxParametersNcell_r16__F2F1_cond.
Opaque SL_ResourcePool_r16__sl_RxParametersNcell_r16__cond SL_ResourcePool_r16__sl_RxParametersNcell_r16__Format.

Definition SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__Format : T_Format SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__Type SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__cond := seq_of_fixed_format SL_ZoneConfigMCR_r16__Format 16.

Opaque SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__cond SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__Format.

Definition SL_ResourcePool_r16__sl_RB_Number_r16__Format : T_Format Z SL_ResourcePool_r16__sl_RB_Number_r16__cond :=
 ranged_int_format (10) (275) SL_ResourcePool_r16__sl_RB_Number_r16__helper1 SL_ResourcePool_r16__sl_RB_Number_r16__helper2.

Opaque SL_ResourcePool_r16__sl_RB_Number_r16__cond SL_ResourcePool_r16__sl_RB_Number_r16__Format.

Definition SL_ResourcePool_r16__sl_PreemptionEnable_r16__Format : T_Format SL_ResourcePool_r16__sl_PreemptionEnable_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ResourcePool_r16__sl_PreemptionEnable_r16__nat__Format SL_ResourcePool_r16__sl_PreemptionEnable_r16__F1 SL_ResourcePool_r16__sl_PreemptionEnable_r16__F2 SL_ResourcePool_r16__sl_PreemptionEnable_r16__F1F2 SL_ResourcePool_r16__sl_PreemptionEnable_r16__F2F1.

Opaque SL_ResourcePool_r16__sl_PreemptionEnable_r16__cond SL_ResourcePool_r16__sl_PreemptionEnable_r16__Format.

Definition SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__Format : T_Format Z SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__cond :=
 ranged_int_format (1) (9) SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__helper1 SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__helper2.

Opaque SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__cond SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__Format.

Definition SL_ResourcePool_r16__sl_PriorityThreshold_r16__Format : T_Format Z SL_ResourcePool_r16__sl_PriorityThreshold_r16__cond :=
 ranged_int_format (1) (9) SL_ResourcePool_r16__sl_PriorityThreshold_r16__helper1 SL_ResourcePool_r16__sl_PriorityThreshold_r16__helper2.

Opaque SL_ResourcePool_r16__sl_PriorityThreshold_r16__cond SL_ResourcePool_r16__sl_PriorityThreshold_r16__Format.

Definition SL_ResourcePool_r16__sl_X_Overhead_r16__Format : T_Format SL_ResourcePool_r16__sl_X_Overhead_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_ResourcePool_r16__sl_X_Overhead_r16__nat__Format SL_ResourcePool_r16__sl_X_Overhead_r16__F1 SL_ResourcePool_r16__sl_X_Overhead_r16__F2 SL_ResourcePool_r16__sl_X_Overhead_r16__F1F2 SL_ResourcePool_r16__sl_X_Overhead_r16__F2F1.

Opaque SL_ResourcePool_r16__sl_X_Overhead_r16__cond SL_ResourcePool_r16__sl_X_Overhead_r16__Format.

Definition SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__Format : T_Format SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__Type SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__cond := (* Eval compute in *) bit_string_ranged_format 10 160 SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__helper1 SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__helper2.
Opaque SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__cond SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__Format.


Definition SL_ResourcePool_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SL_ResourcePool_r16__ext0O__list.
Definition SL_ResourcePool_r16__ext0O__Format_list : SL_ResourcePool_r16__ext0O__Format_Type :=
  (SL_ResourcePool_r16__ext0O__sl_TimeResource_r16__Format, unit_format).
Definition SL_ResourcePool_r16__ext0O__list__Format := (*Eval compute in *) seq_format SL_ResourcePool_r16__ext0O__list SL_ResourcePool_r16__ext0O__Format_list.
Definition SL_ResourcePool_r16__ext0O__F1 z :=
  (SL_ResourcePool_r16__ext0O__sl_TimeResource_r16 z, tt).
Definition SL_ResourcePool_r16__ext0O__F2 (y : seq_type SL_ResourcePool_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SL_ResourcePool_r16__ext0O__Type i0
  end.
Lemma SL_ResourcePool_r16__ext0O__F1F2_cond (z : SL_ResourcePool_r16__ext0O__Type)
  : SL_ResourcePool_r16__ext0O__cond z ->
  (seq_cond SL_ResourcePool_r16__ext0O__list (SL_ResourcePool_r16__ext0O__F1 z)).
intro H. unfold SL_ResourcePool_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SL_ResourcePool_r16__ext0O__F1F2_cond2 (z : SL_ResourcePool_r16__ext0O__Type)
 : SL_ResourcePool_r16__ext0O__F2 (SL_ResourcePool_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_ResourcePool_r16__ext0O__F2F1_cond (y : seq_type SL_ResourcePool_r16__ext0O__list)
  : seq_cond SL_ResourcePool_r16__ext0O__list y ->
 (SL_ResourcePool_r16__ext0O__cond (SL_ResourcePool_r16__ext0O__F2 y)) /\  SL_ResourcePool_r16__ext0O__F1 (SL_ResourcePool_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_ResourcePool_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SL_ResourcePool_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_ResourcePool_r16__ext0O__Format : T_Format SL_ResourcePool_r16__ext0O__Type SL_ResourcePool_r16__ext0O__cond :=
        proj2_format  SL_ResourcePool_r16__ext0O__cond SL_ResourcePool_r16__ext0O__list__Format
    SL_ResourcePool_r16__ext0O__F1 SL_ResourcePool_r16__ext0O__F2 SL_ResourcePool_r16__ext0O__F1F2_cond  SL_ResourcePool_r16__ext0O__F1F2_cond2 SL_ResourcePool_r16__ext0O__F2F1_cond.
Opaque SL_ResourcePool_r16__ext0O__cond SL_ResourcePool_r16__ext0O__Format.

Definition SL_ResourcePool_r16__ext0__check_all_none (b : SL_ResourcePool_r16__ext0O__Type) : bool :=
match b with 
  | make__SL_ResourcePool_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SL_ResourcePool_r16__ext0__Format : T_Format SL_ResourcePool_r16__ext0__Type SL_ResourcePool_r16__ext0__cond :=
  restrict_add_format SL_ResourcePool_r16__ext0__check_all_none SL_ResourcePool_r16__ext0O__Format.

Opaque SL_ResourcePool_r16__ext0__cond SL_ResourcePool_r16__ext0__Format.

Opaque SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__cond SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__Format.

Opaque SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__cond SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__Format.


Definition SL_ResourcePool_r16__ext1O__Format_Type := Eval cbn in seq_format_prod SL_ResourcePool_r16__ext1O__list.
Definition SL_ResourcePool_r16__ext1O__Format_list : SL_ResourcePool_r16__ext1O__Format_Type :=
  (SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17__Format, (SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17__Format, unit_format)).
Definition SL_ResourcePool_r16__ext1O__list__Format := (*Eval compute in *) seq_format SL_ResourcePool_r16__ext1O__list SL_ResourcePool_r16__ext1O__Format_list.
Definition SL_ResourcePool_r16__ext1O__F1 z :=
  (SL_ResourcePool_r16__ext1O__sl_PBPS_CPS_Config_r17 z, (SL_ResourcePool_r16__ext1O__sl_InterUE_CoordinationConfig_r17 z, tt)).
Definition SL_ResourcePool_r16__ext1O__F2 (y : seq_type SL_ResourcePool_r16__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SL_ResourcePool_r16__ext1O__Type i0 i1
  end.
Lemma SL_ResourcePool_r16__ext1O__F1F2_cond (z : SL_ResourcePool_r16__ext1O__Type)
  : SL_ResourcePool_r16__ext1O__cond z ->
  (seq_cond SL_ResourcePool_r16__ext1O__list (SL_ResourcePool_r16__ext1O__F1 z)).
intro H. unfold SL_ResourcePool_r16__ext1O__cond in H. simpl. auto. Qed.
Lemma SL_ResourcePool_r16__ext1O__F1F2_cond2 (z : SL_ResourcePool_r16__ext1O__Type)
 : SL_ResourcePool_r16__ext1O__F2 (SL_ResourcePool_r16__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_ResourcePool_r16__ext1O__F2F1_cond (y : seq_type SL_ResourcePool_r16__ext1O__list)
  : seq_cond SL_ResourcePool_r16__ext1O__list y ->
 (SL_ResourcePool_r16__ext1O__cond (SL_ResourcePool_r16__ext1O__F2 y)) /\  SL_ResourcePool_r16__ext1O__F1 (SL_ResourcePool_r16__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_ResourcePool_r16__ext1O__cond. simpl in *. auto.
 - simpl. unfold SL_ResourcePool_r16__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_ResourcePool_r16__ext1O__Format : T_Format SL_ResourcePool_r16__ext1O__Type SL_ResourcePool_r16__ext1O__cond :=
        proj2_format  SL_ResourcePool_r16__ext1O__cond SL_ResourcePool_r16__ext1O__list__Format
    SL_ResourcePool_r16__ext1O__F1 SL_ResourcePool_r16__ext1O__F2 SL_ResourcePool_r16__ext1O__F1F2_cond  SL_ResourcePool_r16__ext1O__F1F2_cond2 SL_ResourcePool_r16__ext1O__F2F1_cond.
Opaque SL_ResourcePool_r16__ext1O__cond SL_ResourcePool_r16__ext1O__Format.

Definition SL_ResourcePool_r16__ext1__check_all_none (b : SL_ResourcePool_r16__ext1O__Type) : bool :=
match b with 
  | make__SL_ResourcePool_r16__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition SL_ResourcePool_r16__ext1__Format : T_Format SL_ResourcePool_r16__ext1__Type SL_ResourcePool_r16__ext1__cond :=
  restrict_add_format SL_ResourcePool_r16__ext1__check_all_none SL_ResourcePool_r16__ext1O__Format.

Opaque SL_ResourcePool_r16__ext1__cond SL_ResourcePool_r16__ext1__Format.


Definition SL_ResourcePool_r16__root_Format_Type := Eval cbn in seq_format_prod SL_ResourcePool_r16__root_list.
Definition SL_ResourcePool_r16__root_Format_list : SL_ResourcePool_r16__root_Format_Type :=
  (SL_ResourcePool_r16__sl_PSCCH_Config_r16__Format, (SL_ResourcePool_r16__sl_PSSCH_Config_r16__Format, (SL_ResourcePool_r16__sl_PSFCH_Config_r16__Format, (SL_SyncAllowed_r16__Format, (SL_ResourcePool_r16__sl_SubchannelSize_r16__Format, (SL_ResourcePool_r16__dummy__Format, (SL_ResourcePool_r16__sl_StartRB_Subchannel_r16__Format, (SL_ResourcePool_r16__sl_NumSubchannel_r16__Format, (SL_ResourcePool_r16__sl_Additional_MCS_Table_r16__Format, (SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16__Format, (SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16__Format, (SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16__Format, (SL_PTRS_Config_r16__Format, (SL_UE_SelectedConfigRP_r16__Format, (SL_ResourcePool_r16__sl_RxParametersNcell_r16__Format, (SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16__Format, (FilterCoefficient__Format, (SL_ResourcePool_r16__sl_RB_Number_r16__Format, (SL_ResourcePool_r16__sl_PreemptionEnable_r16__Format, (SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16__Format, (SL_ResourcePool_r16__sl_PriorityThreshold_r16__Format, (SL_ResourcePool_r16__sl_X_Overhead_r16__Format, (SL_PowerControl_r16__Format, (SL_TxPercentageList_r16__Format, (SL_MinMaxMCS_List_r16__Format, unit_format))))))))))))))))))))))))).

Definition SL_ResourcePool_r16__ext_Format_Type := Eval cbn in get_formats SL_ResourcePool_r16__ext_list.
Definition SL_ResourcePool_r16__ext_Format_list : SL_ResourcePool_r16__ext_Format_Type :=
  (SL_ResourcePool_r16__ext0__Format, (SL_ResourcePool_r16__ext1__Format, unit__Format)).

Definition SL_ResourcePool_r16__list_type : Set := (seq_type SL_ResourcePool_r16__root_list) * (seq_ext_type SL_ResourcePool_r16__ext_list).
Definition SL_ResourcePool_r16__list_cond (z : SL_ResourcePool_r16__list_type) : Prop :=
        (seq_cond SL_ResourcePool_r16__root_list (fst z)) /\ (seq_ext_cond SL_ResourcePool_r16__ext_list (snd z)).
Definition SL_ResourcePool_r16__list_format : T_Format SL_ResourcePool_r16__list_type SL_ResourcePool_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_ResourcePool_r16__root_list SL_ResourcePool_r16__root_Format_list SL_ResourcePool_r16__ext_list SL_ResourcePool_r16__ext_Format_list.

Opaque SL_ResourcePool_r16__list_format.
Definition SL_ResourcePool_r16__F1 (z : SL_ResourcePool_r16__Type) : SL_ResourcePool_r16__list_type :=
  (((SL_ResourcePool_r16__sl_PSCCH_Config_r16 z, (SL_ResourcePool_r16__sl_PSSCH_Config_r16 z, (SL_ResourcePool_r16__sl_PSFCH_Config_r16 z, (SL_ResourcePool_r16__sl_SyncAllowed_r16 z, (SL_ResourcePool_r16__sl_SubchannelSize_r16 z, (SL_ResourcePool_r16__dummy z, (SL_ResourcePool_r16__sl_StartRB_Subchannel_r16 z, (SL_ResourcePool_r16__sl_NumSubchannel_r16 z, (SL_ResourcePool_r16__sl_Additional_MCS_Table_r16 z, (SL_ResourcePool_r16__sl_ThreshS_RSSI_CBR_r16 z, (SL_ResourcePool_r16__sl_TimeWindowSizeCBR_r16 z, (SL_ResourcePool_r16__sl_TimeWindowSizeCR_r16 z, (SL_ResourcePool_r16__sl_PTRS_Config_r16 z, (SL_ResourcePool_r16__sl_UE_SelectedConfigRP_r16 z, (SL_ResourcePool_r16__sl_RxParametersNcell_r16 z, (SL_ResourcePool_r16__sl_ZoneConfigMCR_List_r16 z, (SL_ResourcePool_r16__sl_FilterCoefficient_r16 z, (SL_ResourcePool_r16__sl_RB_Number_r16 z, (SL_ResourcePool_r16__sl_PreemptionEnable_r16 z, (SL_ResourcePool_r16__sl_PriorityThreshold_UL_URLLC_r16 z, (SL_ResourcePool_r16__sl_PriorityThreshold_r16 z, (SL_ResourcePool_r16__sl_X_Overhead_r16 z, (SL_ResourcePool_r16__sl_PowerControl_r16 z, (SL_ResourcePool_r16__sl_TxPercentageList_r16 z, (SL_ResourcePool_r16__sl_MinMaxMCS_List_r16 z, tt)))))))))))))))))))))))))), (
(SL_ResourcePool_r16__ext0 z, (SL_ResourcePool_r16__ext1 z, tt)))).
Definition SL_ResourcePool_r16__F2 (y : SL_ResourcePool_r16__list_type) : SL_ResourcePool_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, (j18, (j19, (j20, (j21, (j22, (j23, (j24, _))))))))))))))))))))))))), (i0, (i1, _)))=>
    make__SL_ResourcePool_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j22 j23 j24 i0 i1
  end.
Definition SL_ResourcePool_r16__helper1 : (forall a : SL_ResourcePool_r16__Type, SL_ResourcePool_r16__cond a -> SL_ResourcePool_r16__list_cond (SL_ResourcePool_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_ResourcePool_r16__helper2 : (forall a : SL_ResourcePool_r16__Type, SL_ResourcePool_r16__F2 (SL_ResourcePool_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_ResourcePool_r16__helper3 : (forall b : SL_ResourcePool_r16__list_type, SL_ResourcePool_r16__list_cond b -> SL_ResourcePool_r16__cond (SL_ResourcePool_r16__F2 b) /\ SL_ResourcePool_r16__F1 (SL_ResourcePool_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_ResourcePool_r16__cond, SL_ResourcePool_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_ResourcePool_r16__Format : T_Format SL_ResourcePool_r16__Type SL_ResourcePool_r16__cond :=
 proj2_format SL_ResourcePool_r16__cond SL_ResourcePool_r16__list_format  SL_ResourcePool_r16__F1 SL_ResourcePool_r16__F2 SL_ResourcePool_r16__helper1 SL_ResourcePool_r16__helper2 SL_ResourcePool_r16__helper3.

Opaque SL_ResourcePool_r16__cond SL_ResourcePool_r16__Format.

