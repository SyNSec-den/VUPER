Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Type : Set :=
 | UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__supported
.
Definition UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__cond := (fun (_ : UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Type) => True).
Lemma UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__nat__helper.

Definition UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__supported
  | _ => UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__supported
  end.
Lemma UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F1F2 : forall x : UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Type, (UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F2 (UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F1 (UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.HighSpeedParameters_v1700.

Opaque HighSpeedParameters_v1700__cond HighSpeedParameters_v1700__Format.

Require Import NR.PowSav_Parameters_v1700.

Opaque PowSav_Parameters_v1700__cond PowSav_Parameters_v1700__Format.

Require Import NR.MAC_Parameters_v1700.

Opaque MAC_Parameters_v1700__cond MAC_Parameters_v1700__Format.

Require Import NR.IMS_Parameters_v1700.

Opaque IMS_Parameters_v1700__cond IMS_Parameters_v1700__Format.

Require Import NR.MeasAndMobParameters_v1700.

Opaque MeasAndMobParameters_v1700__cond MeasAndMobParameters_v1700__Format.

Require Import NR.AppLayerMeasParameters_r17.

Opaque AppLayerMeasParameters_r17__cond AppLayerMeasParameters_r17__Format.

Require Import NR.RedCapParameters_r17.

Opaque RedCapParameters_r17__cond RedCapParameters_r17__Format.

Inductive UE_NR_Capability_v1700__ra_SDT_r17__Type : Set :=
 | UE_NR_Capability_v1700__ra_SDT_r17__supported
.
Definition UE_NR_Capability_v1700__ra_SDT_r17__cond := (fun (_ : UE_NR_Capability_v1700__ra_SDT_r17__Type) => True).
Lemma UE_NR_Capability_v1700__ra_SDT_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__ra_SDT_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__ra_SDT_r17__nat__helper.

Definition UE_NR_Capability_v1700__ra_SDT_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__ra_SDT_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__ra_SDT_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__ra_SDT_r17__supported
  | _ => UE_NR_Capability_v1700__ra_SDT_r17__supported
  end.
Lemma UE_NR_Capability_v1700__ra_SDT_r17__F1F2 : forall x : UE_NR_Capability_v1700__ra_SDT_r17__Type, (UE_NR_Capability_v1700__ra_SDT_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__ra_SDT_r17__F2 (UE_NR_Capability_v1700__ra_SDT_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__ra_SDT_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__ra_SDT_r17__F1 (UE_NR_Capability_v1700__ra_SDT_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1700__srb_SDT_r17__Type : Set :=
 | UE_NR_Capability_v1700__srb_SDT_r17__supported
.
Definition UE_NR_Capability_v1700__srb_SDT_r17__cond := (fun (_ : UE_NR_Capability_v1700__srb_SDT_r17__Type) => True).
Lemma UE_NR_Capability_v1700__srb_SDT_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__srb_SDT_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__srb_SDT_r17__nat__helper.

Definition UE_NR_Capability_v1700__srb_SDT_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__srb_SDT_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__srb_SDT_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__srb_SDT_r17__supported
  | _ => UE_NR_Capability_v1700__srb_SDT_r17__supported
  end.
Lemma UE_NR_Capability_v1700__srb_SDT_r17__F1F2 : forall x : UE_NR_Capability_v1700__srb_SDT_r17__Type, (UE_NR_Capability_v1700__srb_SDT_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__srb_SDT_r17__F2 (UE_NR_Capability_v1700__srb_SDT_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__srb_SDT_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__srb_SDT_r17__F1 (UE_NR_Capability_v1700__srb_SDT_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Type : Set :=
 | UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__supported
.
Definition UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__cond := (fun (_ : UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Type) => True).
Lemma UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__nat__helper.

Definition UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__supported
  | _ => UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__supported
  end.
Lemma UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F1F2 : forall x : UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Type, (UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F2 (UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F1 (UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Type : Set :=
 | UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__supported
.
Definition UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__cond := (fun (_ : UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Type) => True).
Lemma UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__nat__helper.

Definition UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__supported
  | _ => UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__supported
  end.
Lemma UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F1F2 : forall x : UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Type, (UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F2 (UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F1 (UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.NRDC_Parameters_v1700.

Opaque NRDC_Parameters_v1700__cond NRDC_Parameters_v1700__Format.

Require Import NR.BAP_Parameters_v1700.

Opaque BAP_Parameters_v1700__cond BAP_Parameters_v1700__Format.

Inductive UE_NR_Capability_v1700__musim_GapPreference_r17__Type : Set :=
 | UE_NR_Capability_v1700__musim_GapPreference_r17__supported
.
Definition UE_NR_Capability_v1700__musim_GapPreference_r17__cond := (fun (_ : UE_NR_Capability_v1700__musim_GapPreference_r17__Type) => True).
Lemma UE_NR_Capability_v1700__musim_GapPreference_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__musim_GapPreference_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__musim_GapPreference_r17__nat__helper.

Definition UE_NR_Capability_v1700__musim_GapPreference_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__musim_GapPreference_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__musim_GapPreference_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__musim_GapPreference_r17__supported
  | _ => UE_NR_Capability_v1700__musim_GapPreference_r17__supported
  end.
Lemma UE_NR_Capability_v1700__musim_GapPreference_r17__F1F2 : forall x : UE_NR_Capability_v1700__musim_GapPreference_r17__Type, (UE_NR_Capability_v1700__musim_GapPreference_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__musim_GapPreference_r17__F2 (UE_NR_Capability_v1700__musim_GapPreference_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__musim_GapPreference_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__musim_GapPreference_r17__F1 (UE_NR_Capability_v1700__musim_GapPreference_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1700__musimLeaveConnected_r17__Type : Set :=
 | UE_NR_Capability_v1700__musimLeaveConnected_r17__supported
.
Definition UE_NR_Capability_v1700__musimLeaveConnected_r17__cond := (fun (_ : UE_NR_Capability_v1700__musimLeaveConnected_r17__Type) => True).
Lemma UE_NR_Capability_v1700__musimLeaveConnected_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__musimLeaveConnected_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__musimLeaveConnected_r17__nat__helper.

Definition UE_NR_Capability_v1700__musimLeaveConnected_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__musimLeaveConnected_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__musimLeaveConnected_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__musimLeaveConnected_r17__supported
  | _ => UE_NR_Capability_v1700__musimLeaveConnected_r17__supported
  end.
Lemma UE_NR_Capability_v1700__musimLeaveConnected_r17__F1F2 : forall x : UE_NR_Capability_v1700__musimLeaveConnected_r17__Type, (UE_NR_Capability_v1700__musimLeaveConnected_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__musimLeaveConnected_r17__F2 (UE_NR_Capability_v1700__musimLeaveConnected_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__musimLeaveConnected_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__musimLeaveConnected_r17__F1 (UE_NR_Capability_v1700__musimLeaveConnected_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MBS_Parameters_r17.

Opaque MBS_Parameters_r17__cond MBS_Parameters_r17__Format.

Inductive UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Type : Set :=
 | UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__supported
.
Definition UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__cond := (fun (_ : UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Type) => True).
Lemma UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__nat__helper.

Definition UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__supported
  | _ => UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__supported
  end.
Lemma UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F1F2 : forall x : UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Type, (UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F2 (UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F1 (UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Type : Set :=
 | UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__gso
 | UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__ngso
.
Definition UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__cond := (fun (_ : UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Type) => True).
Lemma UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__nat__helper.

Definition UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__gso => 0
  | UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__ngso => 1
  end.
Definition UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__gso
  | 1 => UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__ngso
  | _ => UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__gso
  end.
Lemma UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F1F2 : forall x : UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Type, (UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F1 x <= 1) /\ UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F2 (UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F2F1 : forall (y : nat) (H : y <= 1), UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F1 (UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Type : Set :=
 | UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__supported
.
Definition UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__cond := (fun (_ : UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Type) => True).
Lemma UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__nat__helper.

Definition UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F1 t :=
  match t with
  | UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__supported => 0
  end.
Definition UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__supported
  | _ => UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__supported
  end.
Lemma UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F1F2 : forall x : UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Type, (UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F1 x <= 0) /\ UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F2 (UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F1 (UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UE_RadioPagingInfo_r17.

Opaque UE_RadioPagingInfo_r17__cond UE_RadioPagingInfo_r17__Format.

Definition UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__Type := bit_string_fixed.
Definition UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.NTN_Parameters_r17.

Opaque NTN_Parameters_r17__cond NTN_Parameters_r17__Format.

Record UE_NR_Capability_v1700__nonCriticalExtension__Type : Set := make__UE_NR_Capability_v1700__nonCriticalExtension__Type {}.
Definition UE_NR_Capability_v1700__nonCriticalExtension__cond (z : UE_NR_Capability_v1700__nonCriticalExtension__Type) := True.
Record UE_NR_Capability_v1700__Type : Set :=
  make__UE_NR_Capability_v1700__Type {
    UE_NR_Capability_v1700__inactiveStatePO_Determination_r17 : option UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Type ;
    UE_NR_Capability_v1700__highSpeedParameters_v1700 : option HighSpeedParameters_v1700__Type ;
    UE_NR_Capability_v1700__powSav_Parameters_v1700 : option PowSav_Parameters_v1700__Type ;
    UE_NR_Capability_v1700__mac_Parameters_v1700 : option MAC_Parameters_v1700__Type ;
    UE_NR_Capability_v1700__ims_Parameters_v1700 : option IMS_Parameters_v1700__Type ;
    UE_NR_Capability_v1700__measAndMobParameters_v1700 : MeasAndMobParameters_v1700__Type ;
    UE_NR_Capability_v1700__appLayerMeasParameters_r17 : option AppLayerMeasParameters_r17__Type ;
    UE_NR_Capability_v1700__redCapParameters_r17 : option RedCapParameters_r17__Type ;
    UE_NR_Capability_v1700__ra_SDT_r17 : option UE_NR_Capability_v1700__ra_SDT_r17__Type ;
    UE_NR_Capability_v1700__srb_SDT_r17 : option UE_NR_Capability_v1700__srb_SDT_r17__Type ;
    UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17 : option UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Type ;
    UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17 : option UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Type ;
    UE_NR_Capability_v1700__nrdc_Parameters_v1700 : option NRDC_Parameters_v1700__Type ;
    UE_NR_Capability_v1700__bap_Parameters_v1700 : option BAP_Parameters_v1700__Type ;
    UE_NR_Capability_v1700__musim_GapPreference_r17 : option UE_NR_Capability_v1700__musim_GapPreference_r17__Type ;
    UE_NR_Capability_v1700__musimLeaveConnected_r17 : option UE_NR_Capability_v1700__musimLeaveConnected_r17__Type ;
    UE_NR_Capability_v1700__mbs_Parameters_r17 : MBS_Parameters_r17__Type ;
    UE_NR_Capability_v1700__nonTerrestrialNetwork_r17 : option UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Type ;
    UE_NR_Capability_v1700__ntn_ScenarioSupport_r17 : option UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Type ;
    UE_NR_Capability_v1700__sliceInfoforCellReselection_r17 : option UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Type ;
    UE_NR_Capability_v1700__ue_RadioPagingInfo_r17 : option UE_RadioPagingInfo_r17__Type ;
    UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17 : option UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__Type ;
    UE_NR_Capability_v1700__ntn_Parameters_r17 : option NTN_Parameters_r17__Type ;
    UE_NR_Capability_v1700__nonCriticalExtension : option UE_NR_Capability_v1700__nonCriticalExtension__Type ;
}.
Definition UE_NR_Capability_v1700__list := (
 Opt UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Type UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__cond ::
 Opt HighSpeedParameters_v1700__Type HighSpeedParameters_v1700__cond ::
 Opt PowSav_Parameters_v1700__Type PowSav_Parameters_v1700__cond ::
 Opt MAC_Parameters_v1700__Type MAC_Parameters_v1700__cond ::
 Opt IMS_Parameters_v1700__Type IMS_Parameters_v1700__cond ::
 Nor MeasAndMobParameters_v1700__Type MeasAndMobParameters_v1700__cond ::
 Opt AppLayerMeasParameters_r17__Type AppLayerMeasParameters_r17__cond ::
 Opt RedCapParameters_r17__Type RedCapParameters_r17__cond ::
 Opt UE_NR_Capability_v1700__ra_SDT_r17__Type UE_NR_Capability_v1700__ra_SDT_r17__cond ::
 Opt UE_NR_Capability_v1700__srb_SDT_r17__Type UE_NR_Capability_v1700__srb_SDT_r17__cond ::
 Opt UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Type UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__cond ::
 Opt UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Type UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__cond ::
 Opt NRDC_Parameters_v1700__Type NRDC_Parameters_v1700__cond ::
 Opt BAP_Parameters_v1700__Type BAP_Parameters_v1700__cond ::
 Opt UE_NR_Capability_v1700__musim_GapPreference_r17__Type UE_NR_Capability_v1700__musim_GapPreference_r17__cond ::
 Opt UE_NR_Capability_v1700__musimLeaveConnected_r17__Type UE_NR_Capability_v1700__musimLeaveConnected_r17__cond ::
 Nor MBS_Parameters_r17__Type MBS_Parameters_r17__cond ::
 Opt UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Type UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__cond ::
 Opt UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Type UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__cond ::
 Opt UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Type UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__cond ::
 Opt UE_RadioPagingInfo_r17__Type UE_RadioPagingInfo_r17__cond ::
 Opt UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__Type UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__cond ::
 Opt NTN_Parameters_r17__Type NTN_Parameters_r17__cond ::
 Opt UE_NR_Capability_v1700__nonCriticalExtension__Type UE_NR_Capability_v1700__nonCriticalExtension__cond ::
 nil).
Definition UE_NR_Capability_v1700__cond z := 
  opt_cond UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__cond (UE_NR_Capability_v1700__inactiveStatePO_Determination_r17 z) /\
  opt_cond HighSpeedParameters_v1700__cond (UE_NR_Capability_v1700__highSpeedParameters_v1700 z) /\
  opt_cond PowSav_Parameters_v1700__cond (UE_NR_Capability_v1700__powSav_Parameters_v1700 z) /\
  opt_cond MAC_Parameters_v1700__cond (UE_NR_Capability_v1700__mac_Parameters_v1700 z) /\
  opt_cond IMS_Parameters_v1700__cond (UE_NR_Capability_v1700__ims_Parameters_v1700 z) /\
  MeasAndMobParameters_v1700__cond (UE_NR_Capability_v1700__measAndMobParameters_v1700 z) /\
  opt_cond AppLayerMeasParameters_r17__cond (UE_NR_Capability_v1700__appLayerMeasParameters_r17 z) /\
  opt_cond RedCapParameters_r17__cond (UE_NR_Capability_v1700__redCapParameters_r17 z) /\
  opt_cond UE_NR_Capability_v1700__ra_SDT_r17__cond (UE_NR_Capability_v1700__ra_SDT_r17 z) /\
  opt_cond UE_NR_Capability_v1700__srb_SDT_r17__cond (UE_NR_Capability_v1700__srb_SDT_r17 z) /\
  opt_cond UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__cond (UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17 z) /\
  opt_cond UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__cond (UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17 z) /\
  opt_cond NRDC_Parameters_v1700__cond (UE_NR_Capability_v1700__nrdc_Parameters_v1700 z) /\
  opt_cond BAP_Parameters_v1700__cond (UE_NR_Capability_v1700__bap_Parameters_v1700 z) /\
  opt_cond UE_NR_Capability_v1700__musim_GapPreference_r17__cond (UE_NR_Capability_v1700__musim_GapPreference_r17 z) /\
  opt_cond UE_NR_Capability_v1700__musimLeaveConnected_r17__cond (UE_NR_Capability_v1700__musimLeaveConnected_r17 z) /\
  MBS_Parameters_r17__cond (UE_NR_Capability_v1700__mbs_Parameters_r17 z) /\
  opt_cond UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__cond (UE_NR_Capability_v1700__nonTerrestrialNetwork_r17 z) /\
  opt_cond UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__cond (UE_NR_Capability_v1700__ntn_ScenarioSupport_r17 z) /\
  opt_cond UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__cond (UE_NR_Capability_v1700__sliceInfoforCellReselection_r17 z) /\
  opt_cond UE_RadioPagingInfo_r17__cond (UE_NR_Capability_v1700__ue_RadioPagingInfo_r17 z) /\
  opt_cond UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__cond (UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17 z) /\
  opt_cond NTN_Parameters_r17__cond (UE_NR_Capability_v1700__ntn_Parameters_r17 z) /\
  opt_cond UE_NR_Capability_v1700__nonCriticalExtension__cond (UE_NR_Capability_v1700__nonCriticalExtension z) /\
  True.


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
Definition UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Format : T_Format UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__nat__Format UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F1 UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F2 UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F1F2 UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__F2F1.

Opaque UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__cond UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Format.

Definition UE_NR_Capability_v1700__ra_SDT_r17__Format : T_Format UE_NR_Capability_v1700__ra_SDT_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__ra_SDT_r17__nat__Format UE_NR_Capability_v1700__ra_SDT_r17__F1 UE_NR_Capability_v1700__ra_SDT_r17__F2 UE_NR_Capability_v1700__ra_SDT_r17__F1F2 UE_NR_Capability_v1700__ra_SDT_r17__F2F1.

Opaque UE_NR_Capability_v1700__ra_SDT_r17__cond UE_NR_Capability_v1700__ra_SDT_r17__Format.

Definition UE_NR_Capability_v1700__srb_SDT_r17__Format : T_Format UE_NR_Capability_v1700__srb_SDT_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__srb_SDT_r17__nat__Format UE_NR_Capability_v1700__srb_SDT_r17__F1 UE_NR_Capability_v1700__srb_SDT_r17__F2 UE_NR_Capability_v1700__srb_SDT_r17__F1F2 UE_NR_Capability_v1700__srb_SDT_r17__F2F1.

Opaque UE_NR_Capability_v1700__srb_SDT_r17__cond UE_NR_Capability_v1700__srb_SDT_r17__Format.

Definition UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Format : T_Format UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__nat__Format UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F1 UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F2 UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F1F2 UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__F2F1.

Opaque UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__cond UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Format.

Definition UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Format : T_Format UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__nat__Format UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F1 UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F2 UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F1F2 UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__F2F1.

Opaque UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__cond UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Format.

Definition UE_NR_Capability_v1700__musim_GapPreference_r17__Format : T_Format UE_NR_Capability_v1700__musim_GapPreference_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__musim_GapPreference_r17__nat__Format UE_NR_Capability_v1700__musim_GapPreference_r17__F1 UE_NR_Capability_v1700__musim_GapPreference_r17__F2 UE_NR_Capability_v1700__musim_GapPreference_r17__F1F2 UE_NR_Capability_v1700__musim_GapPreference_r17__F2F1.

Opaque UE_NR_Capability_v1700__musim_GapPreference_r17__cond UE_NR_Capability_v1700__musim_GapPreference_r17__Format.

Definition UE_NR_Capability_v1700__musimLeaveConnected_r17__Format : T_Format UE_NR_Capability_v1700__musimLeaveConnected_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__musimLeaveConnected_r17__nat__Format UE_NR_Capability_v1700__musimLeaveConnected_r17__F1 UE_NR_Capability_v1700__musimLeaveConnected_r17__F2 UE_NR_Capability_v1700__musimLeaveConnected_r17__F1F2 UE_NR_Capability_v1700__musimLeaveConnected_r17__F2F1.

Opaque UE_NR_Capability_v1700__musimLeaveConnected_r17__cond UE_NR_Capability_v1700__musimLeaveConnected_r17__Format.

Definition UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Format : T_Format UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__nat__Format UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F1 UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F2 UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F1F2 UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__F2F1.

Opaque UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__cond UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Format.

Definition UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Format : T_Format UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__nat__Format UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F1 UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F2 UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F1F2 UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__F2F1.

Opaque UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__cond UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Format.

Definition UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Format : T_Format UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__nat__Format UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F1 UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F2 UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F1F2 UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__F2F1.

Opaque UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__cond UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Format.

Definition UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__Format : T_Format UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__Type UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__cond UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__Format.

Definition UE_NR_Capability_v1700__nonCriticalExtension__helper : forall a : UE_NR_Capability_v1700__nonCriticalExtension__Type, True -> True /\ make__UE_NR_Capability_v1700__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition UE_NR_Capability_v1700__nonCriticalExtension__Format : T_Format UE_NR_Capability_v1700__nonCriticalExtension__Type UE_NR_Capability_v1700__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UE_NR_Capability_v1700__nonCriticalExtension__Type)
    UE_NR_Capability_v1700__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque UE_NR_Capability_v1700__nonCriticalExtension__cond UE_NR_Capability_v1700__nonCriticalExtension__Format.


Definition UE_NR_Capability_v1700__Format_Type := Eval cbn in seq_format_prod UE_NR_Capability_v1700__list.
Definition UE_NR_Capability_v1700__Format_list : UE_NR_Capability_v1700__Format_Type :=
  (UE_NR_Capability_v1700__inactiveStatePO_Determination_r17__Format, (HighSpeedParameters_v1700__Format, (PowSav_Parameters_v1700__Format, (MAC_Parameters_v1700__Format, (IMS_Parameters_v1700__Format, (MeasAndMobParameters_v1700__Format, (AppLayerMeasParameters_r17__Format, (RedCapParameters_r17__Format, (UE_NR_Capability_v1700__ra_SDT_r17__Format, (UE_NR_Capability_v1700__srb_SDT_r17__Format, (UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17__Format, (UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17__Format, (NRDC_Parameters_v1700__Format, (BAP_Parameters_v1700__Format, (UE_NR_Capability_v1700__musim_GapPreference_r17__Format, (UE_NR_Capability_v1700__musimLeaveConnected_r17__Format, (MBS_Parameters_r17__Format, (UE_NR_Capability_v1700__nonTerrestrialNetwork_r17__Format, (UE_NR_Capability_v1700__ntn_ScenarioSupport_r17__Format, (UE_NR_Capability_v1700__sliceInfoforCellReselection_r17__Format, (UE_RadioPagingInfo_r17__Format, (UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17__Format, (NTN_Parameters_r17__Format, (UE_NR_Capability_v1700__nonCriticalExtension__Format, unit_format)))))))))))))))))))))))).
Definition UE_NR_Capability_v1700__list__Format := (*Eval compute in *) seq_format UE_NR_Capability_v1700__list UE_NR_Capability_v1700__Format_list.
Definition UE_NR_Capability_v1700__F1 z :=
  (UE_NR_Capability_v1700__inactiveStatePO_Determination_r17 z, (UE_NR_Capability_v1700__highSpeedParameters_v1700 z, (UE_NR_Capability_v1700__powSav_Parameters_v1700 z, (UE_NR_Capability_v1700__mac_Parameters_v1700 z, (UE_NR_Capability_v1700__ims_Parameters_v1700 z, (UE_NR_Capability_v1700__measAndMobParameters_v1700 z, (UE_NR_Capability_v1700__appLayerMeasParameters_r17 z, (UE_NR_Capability_v1700__redCapParameters_r17 z, (UE_NR_Capability_v1700__ra_SDT_r17 z, (UE_NR_Capability_v1700__srb_SDT_r17 z, (UE_NR_Capability_v1700__gNB_SideRTT_BasedPDC_r17 z, (UE_NR_Capability_v1700__bh_RLF_DetectionRecovery_Indication_r17 z, (UE_NR_Capability_v1700__nrdc_Parameters_v1700 z, (UE_NR_Capability_v1700__bap_Parameters_v1700 z, (UE_NR_Capability_v1700__musim_GapPreference_r17 z, (UE_NR_Capability_v1700__musimLeaveConnected_r17 z, (UE_NR_Capability_v1700__mbs_Parameters_r17 z, (UE_NR_Capability_v1700__nonTerrestrialNetwork_r17 z, (UE_NR_Capability_v1700__ntn_ScenarioSupport_r17 z, (UE_NR_Capability_v1700__sliceInfoforCellReselection_r17 z, (UE_NR_Capability_v1700__ue_RadioPagingInfo_r17 z, (UE_NR_Capability_v1700__ul_GapFR2_Pattern_r17 z, (UE_NR_Capability_v1700__ntn_Parameters_r17 z, (UE_NR_Capability_v1700__nonCriticalExtension z, tt)))))))))))))))))))))))).
Definition UE_NR_Capability_v1700__F2 (y : seq_type UE_NR_Capability_v1700__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, _))))))))))))))))))))))))=>
    make__UE_NR_Capability_v1700__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23
  end.
Lemma UE_NR_Capability_v1700__F1F2_cond (z : UE_NR_Capability_v1700__Type)
  : UE_NR_Capability_v1700__cond z ->
  (seq_cond UE_NR_Capability_v1700__list (UE_NR_Capability_v1700__F1 z)).
intro H. unfold UE_NR_Capability_v1700__cond in H. simpl. auto. Qed.
Lemma UE_NR_Capability_v1700__F1F2_cond2 (z : UE_NR_Capability_v1700__Type)
 : UE_NR_Capability_v1700__F2 (UE_NR_Capability_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_NR_Capability_v1700__F2F1_cond (y : seq_type UE_NR_Capability_v1700__list)
  : seq_cond UE_NR_Capability_v1700__list y ->
 (UE_NR_Capability_v1700__cond (UE_NR_Capability_v1700__F2 y)) /\  UE_NR_Capability_v1700__F1 (UE_NR_Capability_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_NR_Capability_v1700__cond. simpl in *. auto.
 - simpl. unfold UE_NR_Capability_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_NR_Capability_v1700__Format : T_Format UE_NR_Capability_v1700__Type UE_NR_Capability_v1700__cond :=
        proj2_format  UE_NR_Capability_v1700__cond UE_NR_Capability_v1700__list__Format
    UE_NR_Capability_v1700__F1 UE_NR_Capability_v1700__F2 UE_NR_Capability_v1700__F1F2_cond  UE_NR_Capability_v1700__F1F2_cond2 UE_NR_Capability_v1700__F2F1_cond.
Opaque UE_NR_Capability_v1700__cond UE_NR_Capability_v1700__Format.

