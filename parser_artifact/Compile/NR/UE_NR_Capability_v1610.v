Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UE_NR_Capability_v1610__inDeviceCoexInd_r16__Type : Set :=
 | UE_NR_Capability_v1610__inDeviceCoexInd_r16__supported
.
Definition UE_NR_Capability_v1610__inDeviceCoexInd_r16__cond := (fun (_ : UE_NR_Capability_v1610__inDeviceCoexInd_r16__Type) => True).
Lemma UE_NR_Capability_v1610__inDeviceCoexInd_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__inDeviceCoexInd_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__inDeviceCoexInd_r16__nat__helper.

Definition UE_NR_Capability_v1610__inDeviceCoexInd_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__inDeviceCoexInd_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__inDeviceCoexInd_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__inDeviceCoexInd_r16__supported
  | _ => UE_NR_Capability_v1610__inDeviceCoexInd_r16__supported
  end.
Lemma UE_NR_Capability_v1610__inDeviceCoexInd_r16__F1F2 : forall x : UE_NR_Capability_v1610__inDeviceCoexInd_r16__Type, (UE_NR_Capability_v1610__inDeviceCoexInd_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__inDeviceCoexInd_r16__F2 (UE_NR_Capability_v1610__inDeviceCoexInd_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__inDeviceCoexInd_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__inDeviceCoexInd_r16__F1 (UE_NR_Capability_v1610__inDeviceCoexInd_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Type : Set :=
 | UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__supported
.
Definition UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__cond := (fun (_ : UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Type) => True).
Lemma UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__nat__helper.

Definition UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__supported
  | _ => UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__supported
  end.
Lemma UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F1F2 : forall x : UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Type, (UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F2 (UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F1 (UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.NRDC_Parameters_v1610.

Opaque NRDC_Parameters_v1610__cond NRDC_Parameters_v1610__Format.

Require Import NR.PowSav_Parameters_r16.

Opaque PowSav_Parameters_r16__cond PowSav_Parameters_r16__Format.

Require Import NR.UE_NR_CapabilityAddFRX_Mode_v1610.

Opaque UE_NR_CapabilityAddFRX_Mode_v1610__cond UE_NR_CapabilityAddFRX_Mode_v1610__Format.

Require Import NR.UE_NR_CapabilityAddFRX_Mode_v1610.

Opaque UE_NR_CapabilityAddFRX_Mode_v1610__cond UE_NR_CapabilityAddFRX_Mode_v1610__Format.

Inductive UE_NR_Capability_v1610__bh_RLF_Indication_r16__Type : Set :=
 | UE_NR_Capability_v1610__bh_RLF_Indication_r16__supported
.
Definition UE_NR_Capability_v1610__bh_RLF_Indication_r16__cond := (fun (_ : UE_NR_Capability_v1610__bh_RLF_Indication_r16__Type) => True).
Lemma UE_NR_Capability_v1610__bh_RLF_Indication_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__bh_RLF_Indication_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__bh_RLF_Indication_r16__nat__helper.

Definition UE_NR_Capability_v1610__bh_RLF_Indication_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__bh_RLF_Indication_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__bh_RLF_Indication_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__bh_RLF_Indication_r16__supported
  | _ => UE_NR_Capability_v1610__bh_RLF_Indication_r16__supported
  end.
Lemma UE_NR_Capability_v1610__bh_RLF_Indication_r16__F1F2 : forall x : UE_NR_Capability_v1610__bh_RLF_Indication_r16__Type, (UE_NR_Capability_v1610__bh_RLF_Indication_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__bh_RLF_Indication_r16__F2 (UE_NR_Capability_v1610__bh_RLF_Indication_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__bh_RLF_Indication_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__bh_RLF_Indication_r16__F1 (UE_NR_Capability_v1610__bh_RLF_Indication_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Type : Set :=
 | UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__supported
.
Definition UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__cond := (fun (_ : UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Type) => True).
Lemma UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__nat__helper.

Definition UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__supported
  | _ => UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__supported
  end.
Lemma UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F1F2 : forall x : UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Type, (UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F2 (UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F1 (UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.BAP_Parameters_r16.

Opaque BAP_Parameters_r16__cond BAP_Parameters_r16__Format.

Inductive UE_NR_Capability_v1610__referenceTimeProvision_r16__Type : Set :=
 | UE_NR_Capability_v1610__referenceTimeProvision_r16__supported
.
Definition UE_NR_Capability_v1610__referenceTimeProvision_r16__cond := (fun (_ : UE_NR_Capability_v1610__referenceTimeProvision_r16__Type) => True).
Lemma UE_NR_Capability_v1610__referenceTimeProvision_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__referenceTimeProvision_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__referenceTimeProvision_r16__nat__helper.

Definition UE_NR_Capability_v1610__referenceTimeProvision_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__referenceTimeProvision_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__referenceTimeProvision_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__referenceTimeProvision_r16__supported
  | _ => UE_NR_Capability_v1610__referenceTimeProvision_r16__supported
  end.
Lemma UE_NR_Capability_v1610__referenceTimeProvision_r16__F1F2 : forall x : UE_NR_Capability_v1610__referenceTimeProvision_r16__Type, (UE_NR_Capability_v1610__referenceTimeProvision_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__referenceTimeProvision_r16__F2 (UE_NR_Capability_v1610__referenceTimeProvision_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__referenceTimeProvision_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__referenceTimeProvision_r16__F1 (UE_NR_Capability_v1610__referenceTimeProvision_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SidelinkParameters_r16.

Opaque SidelinkParameters_r16__cond SidelinkParameters_r16__Format.

Require Import NR.HighSpeedParameters_r16.

Opaque HighSpeedParameters_r16__cond HighSpeedParameters_r16__Format.

Require Import NR.MAC_Parameters_v1610.

Opaque MAC_Parameters_v1610__cond MAC_Parameters_v1610__Format.

Inductive UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Type : Set :=
 | UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__supported
.
Definition UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__cond := (fun (_ : UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Type) => True).
Lemma UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__nat__helper.

Definition UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__supported
  | _ => UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__supported
  end.
Lemma UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F1F2 : forall x : UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Type, (UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F2 (UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F1 (UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Type : Set :=
 | UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__supported
.
Definition UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__cond := (fun (_ : UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Type) => True).
Lemma UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__nat__helper.

Definition UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__supported
  | _ => UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__supported
  end.
Lemma UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F1F2 : forall x : UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Type, (UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F2 (UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F1 (UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Type : Set :=
 | UE_NR_Capability_v1610__resumeWithStoredSCG_r16__supported
.
Definition UE_NR_Capability_v1610__resumeWithStoredSCG_r16__cond := (fun (_ : UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Type) => True).
Lemma UE_NR_Capability_v1610__resumeWithStoredSCG_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__resumeWithStoredSCG_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__resumeWithStoredSCG_r16__nat__helper.

Definition UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__resumeWithStoredSCG_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__resumeWithStoredSCG_r16__supported
  | _ => UE_NR_Capability_v1610__resumeWithStoredSCG_r16__supported
  end.
Lemma UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F1F2 : forall x : UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Type, (UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F2 (UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F1 (UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Type : Set :=
 | UE_NR_Capability_v1610__resumeWithSCG_Config_r16__supported
.
Definition UE_NR_Capability_v1610__resumeWithSCG_Config_r16__cond := (fun (_ : UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Type) => True).
Lemma UE_NR_Capability_v1610__resumeWithSCG_Config_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__resumeWithSCG_Config_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__resumeWithSCG_Config_r16__nat__helper.

Definition UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__resumeWithSCG_Config_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__resumeWithSCG_Config_r16__supported
  | _ => UE_NR_Capability_v1610__resumeWithSCG_Config_r16__supported
  end.
Lemma UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F1F2 : forall x : UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Type, (UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F2 (UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F1 (UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UE_BasedPerfMeas_Parameters_r16.

Opaque UE_BasedPerfMeas_Parameters_r16__cond UE_BasedPerfMeas_Parameters_r16__Format.

Require Import NR.SON_Parameters_r16.

Opaque SON_Parameters_r16__cond SON_Parameters_r16__Format.

Inductive UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Type : Set :=
 | UE_NR_Capability_v1610__onDemandSIB_Connected_r16__supported
.
Definition UE_NR_Capability_v1610__onDemandSIB_Connected_r16__cond := (fun (_ : UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Type) => True).
Lemma UE_NR_Capability_v1610__onDemandSIB_Connected_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v1610__onDemandSIB_Connected_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v1610__onDemandSIB_Connected_r16__nat__helper.

Definition UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F1 t :=
  match t with
  | UE_NR_Capability_v1610__onDemandSIB_Connected_r16__supported => 0
  end.
Definition UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v1610__onDemandSIB_Connected_r16__supported
  | _ => UE_NR_Capability_v1610__onDemandSIB_Connected_r16__supported
  end.
Lemma UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F1F2 : forall x : UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Type, (UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F1 x <= 0) /\ UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F2 (UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F1 (UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UE_NR_Capability_v1640.

Opaque UE_NR_Capability_v1640__cond UE_NR_Capability_v1640__Format.

Record UE_NR_Capability_v1610__Type : Set :=
  make__UE_NR_Capability_v1610__Type {
    UE_NR_Capability_v1610__inDeviceCoexInd_r16 : option UE_NR_Capability_v1610__inDeviceCoexInd_r16__Type ;
    UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16 : option UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Type ;
    UE_NR_Capability_v1610__nrdc_Parameters_v1610 : option NRDC_Parameters_v1610__Type ;
    UE_NR_Capability_v1610__powSav_Parameters_r16 : option PowSav_Parameters_r16__Type ;
    UE_NR_Capability_v1610__fr1_Add_UE_NR_Capabilities_v1610 : option UE_NR_CapabilityAddFRX_Mode_v1610__Type ;
    UE_NR_Capability_v1610__fr2_Add_UE_NR_Capabilities_v1610 : option UE_NR_CapabilityAddFRX_Mode_v1610__Type ;
    UE_NR_Capability_v1610__bh_RLF_Indication_r16 : option UE_NR_Capability_v1610__bh_RLF_Indication_r16__Type ;
    UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16 : option UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Type ;
    UE_NR_Capability_v1610__bap_Parameters_r16 : option BAP_Parameters_r16__Type ;
    UE_NR_Capability_v1610__referenceTimeProvision_r16 : option UE_NR_Capability_v1610__referenceTimeProvision_r16__Type ;
    UE_NR_Capability_v1610__sidelinkParameters_r16 : option SidelinkParameters_r16__Type ;
    UE_NR_Capability_v1610__highSpeedParameters_r16 : option HighSpeedParameters_r16__Type ;
    UE_NR_Capability_v1610__mac_Parameters_v1610 : option MAC_Parameters_v1610__Type ;
    UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16 : option UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Type ;
    UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16 : option UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Type ;
    UE_NR_Capability_v1610__resumeWithStoredSCG_r16 : option UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Type ;
    UE_NR_Capability_v1610__resumeWithSCG_Config_r16 : option UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Type ;
    UE_NR_Capability_v1610__ue_BasedPerfMeas_Parameters_r16 : option UE_BasedPerfMeas_Parameters_r16__Type ;
    UE_NR_Capability_v1610__son_Parameters_r16 : option SON_Parameters_r16__Type ;
    UE_NR_Capability_v1610__onDemandSIB_Connected_r16 : option UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Type ;
    UE_NR_Capability_v1610__nonCriticalExtension : option UE_NR_Capability_v1640__Type ;
}.
Definition UE_NR_Capability_v1610__list := (
 Opt UE_NR_Capability_v1610__inDeviceCoexInd_r16__Type UE_NR_Capability_v1610__inDeviceCoexInd_r16__cond ::
 Opt UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Type UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__cond ::
 Opt NRDC_Parameters_v1610__Type NRDC_Parameters_v1610__cond ::
 Opt PowSav_Parameters_r16__Type PowSav_Parameters_r16__cond ::
 Opt UE_NR_CapabilityAddFRX_Mode_v1610__Type UE_NR_CapabilityAddFRX_Mode_v1610__cond ::
 Opt UE_NR_CapabilityAddFRX_Mode_v1610__Type UE_NR_CapabilityAddFRX_Mode_v1610__cond ::
 Opt UE_NR_Capability_v1610__bh_RLF_Indication_r16__Type UE_NR_Capability_v1610__bh_RLF_Indication_r16__cond ::
 Opt UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Type UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__cond ::
 Opt BAP_Parameters_r16__Type BAP_Parameters_r16__cond ::
 Opt UE_NR_Capability_v1610__referenceTimeProvision_r16__Type UE_NR_Capability_v1610__referenceTimeProvision_r16__cond ::
 Opt SidelinkParameters_r16__Type SidelinkParameters_r16__cond ::
 Opt HighSpeedParameters_r16__Type HighSpeedParameters_r16__cond ::
 Opt MAC_Parameters_v1610__Type MAC_Parameters_v1610__cond ::
 Opt UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Type UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__cond ::
 Opt UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Type UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__cond ::
 Opt UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Type UE_NR_Capability_v1610__resumeWithStoredSCG_r16__cond ::
 Opt UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Type UE_NR_Capability_v1610__resumeWithSCG_Config_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__Type UE_BasedPerfMeas_Parameters_r16__cond ::
 Opt SON_Parameters_r16__Type SON_Parameters_r16__cond ::
 Opt UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Type UE_NR_Capability_v1610__onDemandSIB_Connected_r16__cond ::
 Opt UE_NR_Capability_v1640__Type UE_NR_Capability_v1640__cond ::
 nil).
Definition UE_NR_Capability_v1610__cond z := 
  opt_cond UE_NR_Capability_v1610__inDeviceCoexInd_r16__cond (UE_NR_Capability_v1610__inDeviceCoexInd_r16 z) /\
  opt_cond UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__cond (UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16 z) /\
  opt_cond NRDC_Parameters_v1610__cond (UE_NR_Capability_v1610__nrdc_Parameters_v1610 z) /\
  opt_cond PowSav_Parameters_r16__cond (UE_NR_Capability_v1610__powSav_Parameters_r16 z) /\
  opt_cond UE_NR_CapabilityAddFRX_Mode_v1610__cond (UE_NR_Capability_v1610__fr1_Add_UE_NR_Capabilities_v1610 z) /\
  opt_cond UE_NR_CapabilityAddFRX_Mode_v1610__cond (UE_NR_Capability_v1610__fr2_Add_UE_NR_Capabilities_v1610 z) /\
  opt_cond UE_NR_Capability_v1610__bh_RLF_Indication_r16__cond (UE_NR_Capability_v1610__bh_RLF_Indication_r16 z) /\
  opt_cond UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__cond (UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16 z) /\
  opt_cond BAP_Parameters_r16__cond (UE_NR_Capability_v1610__bap_Parameters_r16 z) /\
  opt_cond UE_NR_Capability_v1610__referenceTimeProvision_r16__cond (UE_NR_Capability_v1610__referenceTimeProvision_r16 z) /\
  opt_cond SidelinkParameters_r16__cond (UE_NR_Capability_v1610__sidelinkParameters_r16 z) /\
  opt_cond HighSpeedParameters_r16__cond (UE_NR_Capability_v1610__highSpeedParameters_r16 z) /\
  opt_cond MAC_Parameters_v1610__cond (UE_NR_Capability_v1610__mac_Parameters_v1610 z) /\
  opt_cond UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__cond (UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16 z) /\
  opt_cond UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__cond (UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16 z) /\
  opt_cond UE_NR_Capability_v1610__resumeWithStoredSCG_r16__cond (UE_NR_Capability_v1610__resumeWithStoredSCG_r16 z) /\
  opt_cond UE_NR_Capability_v1610__resumeWithSCG_Config_r16__cond (UE_NR_Capability_v1610__resumeWithSCG_Config_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__cond (UE_NR_Capability_v1610__ue_BasedPerfMeas_Parameters_r16 z) /\
  opt_cond SON_Parameters_r16__cond (UE_NR_Capability_v1610__son_Parameters_r16 z) /\
  opt_cond UE_NR_Capability_v1610__onDemandSIB_Connected_r16__cond (UE_NR_Capability_v1610__onDemandSIB_Connected_r16 z) /\
  opt_cond UE_NR_Capability_v1640__cond (UE_NR_Capability_v1610__nonCriticalExtension z) /\
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
Definition UE_NR_Capability_v1610__inDeviceCoexInd_r16__Format : T_Format UE_NR_Capability_v1610__inDeviceCoexInd_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__inDeviceCoexInd_r16__nat__Format UE_NR_Capability_v1610__inDeviceCoexInd_r16__F1 UE_NR_Capability_v1610__inDeviceCoexInd_r16__F2 UE_NR_Capability_v1610__inDeviceCoexInd_r16__F1F2 UE_NR_Capability_v1610__inDeviceCoexInd_r16__F2F1.

Opaque UE_NR_Capability_v1610__inDeviceCoexInd_r16__cond UE_NR_Capability_v1610__inDeviceCoexInd_r16__Format.

Definition UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Format : T_Format UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__nat__Format UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F1 UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F2 UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F1F2 UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__F2F1.

Opaque UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__cond UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Format.

Definition UE_NR_Capability_v1610__bh_RLF_Indication_r16__Format : T_Format UE_NR_Capability_v1610__bh_RLF_Indication_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__bh_RLF_Indication_r16__nat__Format UE_NR_Capability_v1610__bh_RLF_Indication_r16__F1 UE_NR_Capability_v1610__bh_RLF_Indication_r16__F2 UE_NR_Capability_v1610__bh_RLF_Indication_r16__F1F2 UE_NR_Capability_v1610__bh_RLF_Indication_r16__F2F1.

Opaque UE_NR_Capability_v1610__bh_RLF_Indication_r16__cond UE_NR_Capability_v1610__bh_RLF_Indication_r16__Format.

Definition UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Format : T_Format UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__nat__Format UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F1 UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F2 UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F1F2 UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__F2F1.

Opaque UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__cond UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Format.

Definition UE_NR_Capability_v1610__referenceTimeProvision_r16__Format : T_Format UE_NR_Capability_v1610__referenceTimeProvision_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__referenceTimeProvision_r16__nat__Format UE_NR_Capability_v1610__referenceTimeProvision_r16__F1 UE_NR_Capability_v1610__referenceTimeProvision_r16__F2 UE_NR_Capability_v1610__referenceTimeProvision_r16__F1F2 UE_NR_Capability_v1610__referenceTimeProvision_r16__F2F1.

Opaque UE_NR_Capability_v1610__referenceTimeProvision_r16__cond UE_NR_Capability_v1610__referenceTimeProvision_r16__Format.

Definition UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Format : T_Format UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__nat__Format UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F1 UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F2 UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F1F2 UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__F2F1.

Opaque UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__cond UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Format.

Definition UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Format : T_Format UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__nat__Format UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F1 UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F2 UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F1F2 UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__F2F1.

Opaque UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__cond UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Format.

Definition UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Format : T_Format UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__resumeWithStoredSCG_r16__nat__Format UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F1 UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F2 UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F1F2 UE_NR_Capability_v1610__resumeWithStoredSCG_r16__F2F1.

Opaque UE_NR_Capability_v1610__resumeWithStoredSCG_r16__cond UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Format.

Definition UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Format : T_Format UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__resumeWithSCG_Config_r16__nat__Format UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F1 UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F2 UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F1F2 UE_NR_Capability_v1610__resumeWithSCG_Config_r16__F2F1.

Opaque UE_NR_Capability_v1610__resumeWithSCG_Config_r16__cond UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Format.

Definition UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Format : T_Format UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v1610__onDemandSIB_Connected_r16__nat__Format UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F1 UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F2 UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F1F2 UE_NR_Capability_v1610__onDemandSIB_Connected_r16__F2F1.

Opaque UE_NR_Capability_v1610__onDemandSIB_Connected_r16__cond UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Format.


Definition UE_NR_Capability_v1610__Format_Type := Eval cbn in seq_format_prod UE_NR_Capability_v1610__list.
Definition UE_NR_Capability_v1610__Format_list : UE_NR_Capability_v1610__Format_Type :=
  (UE_NR_Capability_v1610__inDeviceCoexInd_r16__Format, (UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16__Format, (NRDC_Parameters_v1610__Format, (PowSav_Parameters_r16__Format, (UE_NR_CapabilityAddFRX_Mode_v1610__Format, (UE_NR_CapabilityAddFRX_Mode_v1610__Format, (UE_NR_Capability_v1610__bh_RLF_Indication_r16__Format, (UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16__Format, (BAP_Parameters_r16__Format, (UE_NR_Capability_v1610__referenceTimeProvision_r16__Format, (SidelinkParameters_r16__Format, (HighSpeedParameters_r16__Format, (MAC_Parameters_v1610__Format, (UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16__Format, (UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16__Format, (UE_NR_Capability_v1610__resumeWithStoredSCG_r16__Format, (UE_NR_Capability_v1610__resumeWithSCG_Config_r16__Format, (UE_BasedPerfMeas_Parameters_r16__Format, (SON_Parameters_r16__Format, (UE_NR_Capability_v1610__onDemandSIB_Connected_r16__Format, (UE_NR_Capability_v1640__Format, unit_format))))))))))))))))))))).
Definition UE_NR_Capability_v1610__list__Format := (*Eval compute in *) seq_format UE_NR_Capability_v1610__list UE_NR_Capability_v1610__Format_list.
Definition UE_NR_Capability_v1610__F1 z :=
  (UE_NR_Capability_v1610__inDeviceCoexInd_r16 z, (UE_NR_Capability_v1610__dl_DedicatedMessageSegmentation_r16 z, (UE_NR_Capability_v1610__nrdc_Parameters_v1610 z, (UE_NR_Capability_v1610__powSav_Parameters_r16 z, (UE_NR_Capability_v1610__fr1_Add_UE_NR_Capabilities_v1610 z, (UE_NR_Capability_v1610__fr2_Add_UE_NR_Capabilities_v1610 z, (UE_NR_Capability_v1610__bh_RLF_Indication_r16 z, (UE_NR_Capability_v1610__directSN_AdditionFirstRRC_IAB_r16 z, (UE_NR_Capability_v1610__bap_Parameters_r16 z, (UE_NR_Capability_v1610__referenceTimeProvision_r16 z, (UE_NR_Capability_v1610__sidelinkParameters_r16 z, (UE_NR_Capability_v1610__highSpeedParameters_r16 z, (UE_NR_Capability_v1610__mac_Parameters_v1610 z, (UE_NR_Capability_v1610__mcgRLF_RecoveryViaSCG_r16 z, (UE_NR_Capability_v1610__resumeWithStoredMCG_SCells_r16 z, (UE_NR_Capability_v1610__resumeWithStoredSCG_r16 z, (UE_NR_Capability_v1610__resumeWithSCG_Config_r16 z, (UE_NR_Capability_v1610__ue_BasedPerfMeas_Parameters_r16 z, (UE_NR_Capability_v1610__son_Parameters_r16 z, (UE_NR_Capability_v1610__onDemandSIB_Connected_r16 z, (UE_NR_Capability_v1610__nonCriticalExtension z, tt))))))))))))))))))))).
Definition UE_NR_Capability_v1610__F2 (y : seq_type UE_NR_Capability_v1610__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, _)))))))))))))))))))))=>
    make__UE_NR_Capability_v1610__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20
  end.
Lemma UE_NR_Capability_v1610__F1F2_cond (z : UE_NR_Capability_v1610__Type)
  : UE_NR_Capability_v1610__cond z ->
  (seq_cond UE_NR_Capability_v1610__list (UE_NR_Capability_v1610__F1 z)).
intro H. unfold UE_NR_Capability_v1610__cond in H. simpl. auto. Qed.
Lemma UE_NR_Capability_v1610__F1F2_cond2 (z : UE_NR_Capability_v1610__Type)
 : UE_NR_Capability_v1610__F2 (UE_NR_Capability_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_NR_Capability_v1610__F2F1_cond (y : seq_type UE_NR_Capability_v1610__list)
  : seq_cond UE_NR_Capability_v1610__list y ->
 (UE_NR_Capability_v1610__cond (UE_NR_Capability_v1610__F2 y)) /\  UE_NR_Capability_v1610__F1 (UE_NR_Capability_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_NR_Capability_v1610__cond. simpl in *. auto.
 - simpl. unfold UE_NR_Capability_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_NR_Capability_v1610__Format : T_Format UE_NR_Capability_v1610__Type UE_NR_Capability_v1610__cond :=
        proj2_format  UE_NR_Capability_v1610__cond UE_NR_Capability_v1610__list__Format
    UE_NR_Capability_v1610__F1 UE_NR_Capability_v1610__F2 UE_NR_Capability_v1610__F1F2_cond  UE_NR_Capability_v1610__F1F2_cond2 UE_NR_Capability_v1610__F2F1_cond.
Opaque UE_NR_Capability_v1610__cond UE_NR_Capability_v1610__Format.

