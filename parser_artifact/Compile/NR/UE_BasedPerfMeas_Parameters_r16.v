Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Type, (UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F2 (UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F1 (UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Type, (UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F2 (UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F1 (UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Type, (UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F2 (UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F1 (UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Type, (UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F2 (UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F1 (UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Type, (UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F2 (UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F1 (UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Type, (UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F2 (UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F1 (UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Type, (UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F2 (UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F1 (UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Type, (UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F2 (UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F1 (UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Type, (UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F2 (UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F1 (UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Type, (UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F2 (UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F1 (UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Type, (UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F2 (UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F1 (UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Type, (UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F2 (UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F1 (UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Type, (UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F2 (UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F1 (UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F2 y) = y. enum_solve H y. Qed.

Inductive UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Type : Set :=
 | UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__supported
.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__cond := (fun (_ : UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Type) => True).
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__nat__helper.

Definition UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F1 t :=
  match t with
  | UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__supported => 0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F2 n :=
  match n with
  | 0 => UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__supported
  | _ => UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__supported
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F1F2 : forall x : UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Type, (UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F1 x <= 0) /\ UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F2 (UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F1 x) = x. imp_solve. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F2F1 : forall (y : nat) (H : y <= 0), UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F1 (UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F2 y) = y. enum_solve H y. Qed.

Record UE_BasedPerfMeas_Parameters_r16__ext0O__Type : Set :=
  make__UE_BasedPerfMeas_Parameters_r16__ext0O__Type {
    UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17 : option UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Type ;
    UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17 : option UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Type ;
    UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17 : option UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Type ;
    UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17 : option UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Type ;
}.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__list := (
 Opt UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Type UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Type UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Type UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Type UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__cond ::
 nil).
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__cond z := 
  opt_cond UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__cond (UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__cond (UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__cond (UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__cond (UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17 z) /\
  True.

Definition UE_BasedPerfMeas_Parameters_r16__ext0__Type := UE_BasedPerfMeas_Parameters_r16__ext0O__Type.
Definition UE_BasedPerfMeas_Parameters_r16__ext0__cond := UE_BasedPerfMeas_Parameters_r16__ext0O__cond.

Record UE_BasedPerfMeas_Parameters_r16__Type : Set :=
  make__UE_BasedPerfMeas_Parameters_r16__Type {
    UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16 : option UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16 : option UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16 : option UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16 : option UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16 : option UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16 : option UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16 : option UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16 : option UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16 : option UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16 : option UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Type ;
    UE_BasedPerfMeas_Parameters_r16__ext0 : option UE_BasedPerfMeas_Parameters_r16__ext0__Type ;
}.
Definition UE_BasedPerfMeas_Parameters_r16__root_list : list seq_elem := (
 Opt UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Type UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Type UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Type UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Type UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Type UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Type UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Type UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Type UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Type UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__cond ::
 Opt UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Type UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__cond ::
 nil).
Definition UE_BasedPerfMeas_Parameters_r16__ext_list : list typ := (
  typ_cons UE_BasedPerfMeas_Parameters_r16__ext0__Type UE_BasedPerfMeas_Parameters_r16__ext0__cond ::
  nil).
Definition UE_BasedPerfMeas_Parameters_r16__cond (z : UE_BasedPerfMeas_Parameters_r16__Type) := 
(  opt_cond UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__cond (UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__cond (UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__cond (UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__cond (UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__cond (UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__cond (UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__cond (UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__cond (UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__cond (UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16 z) /\
  opt_cond UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__cond (UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16 z) /\
  True) /\ 
(  opt_cond UE_BasedPerfMeas_Parameters_r16__ext0__cond (UE_BasedPerfMeas_Parameters_r16__ext0 z) /\
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
Definition UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F1 UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F2 UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__cond UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F1 UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F2 UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__cond UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F1 UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F2 UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__cond UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F1 UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F2 UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__cond UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F1 UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F2 UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__cond UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F1 UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F2 UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__cond UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F1 UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F2 UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__cond UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F1 UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F2 UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__cond UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F1 UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F2 UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__cond UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__nat__Format UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F1 UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F2 UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F1F2 UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__cond UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Format.

Definition UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Format : T_Format UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__nat__Format UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F1 UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F2 UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F1F2 UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__cond UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Format.

Definition UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Format : T_Format UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__nat__Format UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F1 UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F2 UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F1F2 UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__cond UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Format.

Definition UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Format : T_Format UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__nat__Format UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F1 UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F2 UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F1F2 UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__cond UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Format.

Definition UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Format : T_Format UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__nat__Format UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F1 UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F2 UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F1F2 UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__F2F1.

Opaque UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__cond UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Format.


Definition UE_BasedPerfMeas_Parameters_r16__ext0O__Format_Type := Eval cbn in seq_format_prod UE_BasedPerfMeas_Parameters_r16__ext0O__list.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__Format_list : UE_BasedPerfMeas_Parameters_r16__ext0O__Format_Type :=
  (UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17__Format, (UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17__Format, (UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17__Format, (UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17__Format, unit_format)))).
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__list__Format := (*Eval compute in *) seq_format UE_BasedPerfMeas_Parameters_r16__ext0O__list UE_BasedPerfMeas_Parameters_r16__ext0O__Format_list.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__F1 z :=
  (UE_BasedPerfMeas_Parameters_r16__ext0O__sigBasedLogMDT_OverrideProtect_r17 z, (UE_BasedPerfMeas_Parameters_r16__ext0O__multipleCEF_Report_r17 z, (UE_BasedPerfMeas_Parameters_r16__ext0O__excessPacketDelay_r17 z, (UE_BasedPerfMeas_Parameters_r16__ext0O__earlyMeasLog_r17 z, tt)))).
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__F2 (y : seq_type UE_BasedPerfMeas_Parameters_r16__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__UE_BasedPerfMeas_Parameters_r16__ext0O__Type i0 i1 i2 i3
  end.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__F1F2_cond (z : UE_BasedPerfMeas_Parameters_r16__ext0O__Type)
  : UE_BasedPerfMeas_Parameters_r16__ext0O__cond z ->
  (seq_cond UE_BasedPerfMeas_Parameters_r16__ext0O__list (UE_BasedPerfMeas_Parameters_r16__ext0O__F1 z)).
intro H. unfold UE_BasedPerfMeas_Parameters_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__F1F2_cond2 (z : UE_BasedPerfMeas_Parameters_r16__ext0O__Type)
 : UE_BasedPerfMeas_Parameters_r16__ext0O__F2 (UE_BasedPerfMeas_Parameters_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_BasedPerfMeas_Parameters_r16__ext0O__F2F1_cond (y : seq_type UE_BasedPerfMeas_Parameters_r16__ext0O__list)
  : seq_cond UE_BasedPerfMeas_Parameters_r16__ext0O__list y ->
 (UE_BasedPerfMeas_Parameters_r16__ext0O__cond (UE_BasedPerfMeas_Parameters_r16__ext0O__F2 y)) /\  UE_BasedPerfMeas_Parameters_r16__ext0O__F1 (UE_BasedPerfMeas_Parameters_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_BasedPerfMeas_Parameters_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold UE_BasedPerfMeas_Parameters_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_BasedPerfMeas_Parameters_r16__ext0O__Format : T_Format UE_BasedPerfMeas_Parameters_r16__ext0O__Type UE_BasedPerfMeas_Parameters_r16__ext0O__cond :=
        proj2_format  UE_BasedPerfMeas_Parameters_r16__ext0O__cond UE_BasedPerfMeas_Parameters_r16__ext0O__list__Format
    UE_BasedPerfMeas_Parameters_r16__ext0O__F1 UE_BasedPerfMeas_Parameters_r16__ext0O__F2 UE_BasedPerfMeas_Parameters_r16__ext0O__F1F2_cond  UE_BasedPerfMeas_Parameters_r16__ext0O__F1F2_cond2 UE_BasedPerfMeas_Parameters_r16__ext0O__F2F1_cond.
Opaque UE_BasedPerfMeas_Parameters_r16__ext0O__cond UE_BasedPerfMeas_Parameters_r16__ext0O__Format.

Definition UE_BasedPerfMeas_Parameters_r16__ext0__check_all_none (b : UE_BasedPerfMeas_Parameters_r16__ext0O__Type) : bool :=
match b with 
  | make__UE_BasedPerfMeas_Parameters_r16__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition UE_BasedPerfMeas_Parameters_r16__ext0__Format : T_Format UE_BasedPerfMeas_Parameters_r16__ext0__Type UE_BasedPerfMeas_Parameters_r16__ext0__cond :=
  restrict_add_format UE_BasedPerfMeas_Parameters_r16__ext0__check_all_none UE_BasedPerfMeas_Parameters_r16__ext0O__Format.

Opaque UE_BasedPerfMeas_Parameters_r16__ext0__cond UE_BasedPerfMeas_Parameters_r16__ext0__Format.


Definition UE_BasedPerfMeas_Parameters_r16__root_Format_Type := Eval cbn in seq_format_prod UE_BasedPerfMeas_Parameters_r16__root_list.
Definition UE_BasedPerfMeas_Parameters_r16__root_Format_list : UE_BasedPerfMeas_Parameters_r16__root_Format_Type :=
  (UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16__Format, (UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16__Format, (UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16__Format, (UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16__Format, (UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16__Format, (UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16__Format, (UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16__Format, (UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16__Format, (UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16__Format, (UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16__Format, unit_format)))))))))).

Definition UE_BasedPerfMeas_Parameters_r16__ext_Format_Type := Eval cbn in get_formats UE_BasedPerfMeas_Parameters_r16__ext_list.
Definition UE_BasedPerfMeas_Parameters_r16__ext_Format_list : UE_BasedPerfMeas_Parameters_r16__ext_Format_Type :=
  (UE_BasedPerfMeas_Parameters_r16__ext0__Format, unit__Format).

Definition UE_BasedPerfMeas_Parameters_r16__list_type : Set := (seq_type UE_BasedPerfMeas_Parameters_r16__root_list) * (seq_ext_type UE_BasedPerfMeas_Parameters_r16__ext_list).
Definition UE_BasedPerfMeas_Parameters_r16__list_cond (z : UE_BasedPerfMeas_Parameters_r16__list_type) : Prop :=
        (seq_cond UE_BasedPerfMeas_Parameters_r16__root_list (fst z)) /\ (seq_ext_cond UE_BasedPerfMeas_Parameters_r16__ext_list (snd z)).
Definition UE_BasedPerfMeas_Parameters_r16__list_format : T_Format UE_BasedPerfMeas_Parameters_r16__list_type UE_BasedPerfMeas_Parameters_r16__list_cond :=
 (* Eval compute in *) seq_ext_format UE_BasedPerfMeas_Parameters_r16__root_list UE_BasedPerfMeas_Parameters_r16__root_Format_list UE_BasedPerfMeas_Parameters_r16__ext_list UE_BasedPerfMeas_Parameters_r16__ext_Format_list.

Opaque UE_BasedPerfMeas_Parameters_r16__list_format.
Definition UE_BasedPerfMeas_Parameters_r16__F1 (z : UE_BasedPerfMeas_Parameters_r16__Type) : UE_BasedPerfMeas_Parameters_r16__list_type :=
  (((UE_BasedPerfMeas_Parameters_r16__barometerMeasReport_r16 z, (UE_BasedPerfMeas_Parameters_r16__immMeasBT_r16 z, (UE_BasedPerfMeas_Parameters_r16__immMeasWLAN_r16 z, (UE_BasedPerfMeas_Parameters_r16__loggedMeasBT_r16 z, (UE_BasedPerfMeas_Parameters_r16__loggedMeasurements_r16 z, (UE_BasedPerfMeas_Parameters_r16__loggedMeasWLAN_r16 z, (UE_BasedPerfMeas_Parameters_r16__orientationMeasReport_r16 z, (UE_BasedPerfMeas_Parameters_r16__speedMeasReport_r16 z, (UE_BasedPerfMeas_Parameters_r16__gnss_Location_r16 z, (UE_BasedPerfMeas_Parameters_r16__ulPDCP_Delay_r16 z, tt))))))))))), (
(UE_BasedPerfMeas_Parameters_r16__ext0 z, tt))).
Definition UE_BasedPerfMeas_Parameters_r16__F2 (y : UE_BasedPerfMeas_Parameters_r16__list_type) : UE_BasedPerfMeas_Parameters_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, _)))))))))), (i0, _))=>
    make__UE_BasedPerfMeas_Parameters_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i0
  end.
Definition UE_BasedPerfMeas_Parameters_r16__helper1 : (forall a : UE_BasedPerfMeas_Parameters_r16__Type, UE_BasedPerfMeas_Parameters_r16__cond a -> UE_BasedPerfMeas_Parameters_r16__list_cond (UE_BasedPerfMeas_Parameters_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition UE_BasedPerfMeas_Parameters_r16__helper2 : (forall a : UE_BasedPerfMeas_Parameters_r16__Type, UE_BasedPerfMeas_Parameters_r16__F2 (UE_BasedPerfMeas_Parameters_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition UE_BasedPerfMeas_Parameters_r16__helper3 : (forall b : UE_BasedPerfMeas_Parameters_r16__list_type, UE_BasedPerfMeas_Parameters_r16__list_cond b -> UE_BasedPerfMeas_Parameters_r16__cond (UE_BasedPerfMeas_Parameters_r16__F2 b) /\ UE_BasedPerfMeas_Parameters_r16__F1 (UE_BasedPerfMeas_Parameters_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold UE_BasedPerfMeas_Parameters_r16__cond, UE_BasedPerfMeas_Parameters_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition UE_BasedPerfMeas_Parameters_r16__Format : T_Format UE_BasedPerfMeas_Parameters_r16__Type UE_BasedPerfMeas_Parameters_r16__cond :=
 proj2_format UE_BasedPerfMeas_Parameters_r16__cond UE_BasedPerfMeas_Parameters_r16__list_format  UE_BasedPerfMeas_Parameters_r16__F1 UE_BasedPerfMeas_Parameters_r16__F2 UE_BasedPerfMeas_Parameters_r16__helper1 UE_BasedPerfMeas_Parameters_r16__helper2 UE_BasedPerfMeas_Parameters_r16__helper3.

Opaque UE_BasedPerfMeas_Parameters_r16__cond UE_BasedPerfMeas_Parameters_r16__Format.

