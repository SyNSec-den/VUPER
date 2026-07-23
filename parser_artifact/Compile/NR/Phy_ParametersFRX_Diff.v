Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive Phy_ParametersFRX_Diff__dynamicSFI__Type : Set :=
 | Phy_ParametersFRX_Diff__dynamicSFI__supported
.
Definition Phy_ParametersFRX_Diff__dynamicSFI__cond := (fun (_ : Phy_ParametersFRX_Diff__dynamicSFI__Type) => True).
Lemma Phy_ParametersFRX_Diff__dynamicSFI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__dynamicSFI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__dynamicSFI__nat__helper.

Definition Phy_ParametersFRX_Diff__dynamicSFI__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__dynamicSFI__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__dynamicSFI__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__dynamicSFI__supported
  | _ => Phy_ParametersFRX_Diff__dynamicSFI__supported
  end.
Lemma Phy_ParametersFRX_Diff__dynamicSFI__F1F2 : forall x : Phy_ParametersFRX_Diff__dynamicSFI__Type, (Phy_ParametersFRX_Diff__dynamicSFI__F1 x <= 0) /\ Phy_ParametersFRX_Diff__dynamicSFI__F2 (Phy_ParametersFRX_Diff__dynamicSFI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__dynamicSFI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__dynamicSFI__F1 (Phy_ParametersFRX_Diff__dynamicSFI__F2 y) = y. enum_solve H y. Qed.

Definition Phy_ParametersFRX_Diff__dummy1__Type := bit_string_fixed.
Definition Phy_ParametersFRX_Diff__dummy1__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Definition Phy_ParametersFRX_Diff__twoFL_DMRS__Type := bit_string_fixed.
Definition Phy_ParametersFRX_Diff__twoFL_DMRS__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Definition Phy_ParametersFRX_Diff__dummy2__Type := bit_string_fixed.
Definition Phy_ParametersFRX_Diff__dummy2__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Definition Phy_ParametersFRX_Diff__dummy3__Type := bit_string_fixed.
Definition Phy_ParametersFRX_Diff__dummy3__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Inductive Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Type : Set :=
 | Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__type1
 | Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__type1And2
.
Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__cond := (fun (_ : Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Type) => True).
Lemma Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__nat__helper.

Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__type1 => 0
  | Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__type1And2 => 1
  end.
Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__type1
  | 1 => Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__type1And2
  | _ => Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__type1
  end.
Lemma Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F1F2 : forall x : Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Type, (Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F1 x <= 1) /\ Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F2 (Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F2F1 : forall (y : nat) (H : y <= 1), Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F1 (Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Type : Set :=
 | Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__type1
 | Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__type1And2
.
Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__cond := (fun (_ : Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Type) => True).
Lemma Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__nat__helper.

Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__type1 => 0
  | Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__type1And2 => 1
  end.
Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__type1
  | 1 => Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__type1And2
  | _ => Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__type1
  end.
Lemma Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F1F2 : forall x : Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Type, (Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F1 x <= 1) /\ Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F2 (Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F2F1 : forall (y : nat) (H : y <= 1), Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F1 (Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__semiOpenLoopCSI__Type : Set :=
 | Phy_ParametersFRX_Diff__semiOpenLoopCSI__supported
.
Definition Phy_ParametersFRX_Diff__semiOpenLoopCSI__cond := (fun (_ : Phy_ParametersFRX_Diff__semiOpenLoopCSI__Type) => True).
Lemma Phy_ParametersFRX_Diff__semiOpenLoopCSI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__semiOpenLoopCSI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__semiOpenLoopCSI__nat__helper.

Definition Phy_ParametersFRX_Diff__semiOpenLoopCSI__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__semiOpenLoopCSI__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__semiOpenLoopCSI__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__semiOpenLoopCSI__supported
  | _ => Phy_ParametersFRX_Diff__semiOpenLoopCSI__supported
  end.
Lemma Phy_ParametersFRX_Diff__semiOpenLoopCSI__F1F2 : forall x : Phy_ParametersFRX_Diff__semiOpenLoopCSI__Type, (Phy_ParametersFRX_Diff__semiOpenLoopCSI__F1 x <= 0) /\ Phy_ParametersFRX_Diff__semiOpenLoopCSI__F2 (Phy_ParametersFRX_Diff__semiOpenLoopCSI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__semiOpenLoopCSI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__semiOpenLoopCSI__F1 (Phy_ParametersFRX_Diff__semiOpenLoopCSI__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Type : Set :=
 | Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__supported
.
Definition Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__cond := (fun (_ : Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Type) => True).
Lemma Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__nat__helper.

Definition Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__supported
  | _ => Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__supported
  end.
Lemma Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F1F2 : forall x : Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Type, (Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F1 x <= 0) /\ Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F2 (Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F1 (Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Type : Set :=
 | Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__supported
.
Definition Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__cond := (fun (_ : Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Type) => True).
Lemma Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__nat__helper.

Definition Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__supported
  | _ => Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__supported
  end.
Lemma Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F1F2 : forall x : Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Type, (Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F1 x <= 0) /\ Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F2 (Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F1 (Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F2 y) = y. enum_solve H y. Qed.

Definition Phy_ParametersFRX_Diff__onePortsPTRS__Type := bit_string_fixed.
Definition Phy_ParametersFRX_Diff__onePortsPTRS__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Inductive Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Type : Set :=
 | Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__supported
.
Definition Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__cond := (fun (_ : Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Type) => True).
Lemma Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__nat__helper.

Definition Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__supported
  | _ => Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__supported
  end.
Lemma Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F1F2 : forall x : Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Type, (Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 x <= 0) /\ Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F2 (Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 (Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__pucch_F2_WithFH__Type : Set :=
 | Phy_ParametersFRX_Diff__pucch_F2_WithFH__supported
.
Definition Phy_ParametersFRX_Diff__pucch_F2_WithFH__cond := (fun (_ : Phy_ParametersFRX_Diff__pucch_F2_WithFH__Type) => True).
Lemma Phy_ParametersFRX_Diff__pucch_F2_WithFH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__pucch_F2_WithFH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__pucch_F2_WithFH__nat__helper.

Definition Phy_ParametersFRX_Diff__pucch_F2_WithFH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__pucch_F2_WithFH__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__pucch_F2_WithFH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__pucch_F2_WithFH__supported
  | _ => Phy_ParametersFRX_Diff__pucch_F2_WithFH__supported
  end.
Lemma Phy_ParametersFRX_Diff__pucch_F2_WithFH__F1F2 : forall x : Phy_ParametersFRX_Diff__pucch_F2_WithFH__Type, (Phy_ParametersFRX_Diff__pucch_F2_WithFH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__pucch_F2_WithFH__F2 (Phy_ParametersFRX_Diff__pucch_F2_WithFH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__pucch_F2_WithFH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__pucch_F2_WithFH__F1 (Phy_ParametersFRX_Diff__pucch_F2_WithFH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__pucch_F3_WithFH__Type : Set :=
 | Phy_ParametersFRX_Diff__pucch_F3_WithFH__supported
.
Definition Phy_ParametersFRX_Diff__pucch_F3_WithFH__cond := (fun (_ : Phy_ParametersFRX_Diff__pucch_F3_WithFH__Type) => True).
Lemma Phy_ParametersFRX_Diff__pucch_F3_WithFH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__pucch_F3_WithFH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__pucch_F3_WithFH__nat__helper.

Definition Phy_ParametersFRX_Diff__pucch_F3_WithFH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__pucch_F3_WithFH__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__pucch_F3_WithFH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__pucch_F3_WithFH__supported
  | _ => Phy_ParametersFRX_Diff__pucch_F3_WithFH__supported
  end.
Lemma Phy_ParametersFRX_Diff__pucch_F3_WithFH__F1F2 : forall x : Phy_ParametersFRX_Diff__pucch_F3_WithFH__Type, (Phy_ParametersFRX_Diff__pucch_F3_WithFH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__pucch_F3_WithFH__F2 (Phy_ParametersFRX_Diff__pucch_F3_WithFH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__pucch_F3_WithFH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__pucch_F3_WithFH__F1 (Phy_ParametersFRX_Diff__pucch_F3_WithFH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__pucch_F4_WithFH__Type : Set :=
 | Phy_ParametersFRX_Diff__pucch_F4_WithFH__supported
.
Definition Phy_ParametersFRX_Diff__pucch_F4_WithFH__cond := (fun (_ : Phy_ParametersFRX_Diff__pucch_F4_WithFH__Type) => True).
Lemma Phy_ParametersFRX_Diff__pucch_F4_WithFH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__pucch_F4_WithFH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__pucch_F4_WithFH__nat__helper.

Definition Phy_ParametersFRX_Diff__pucch_F4_WithFH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__pucch_F4_WithFH__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__pucch_F4_WithFH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__pucch_F4_WithFH__supported
  | _ => Phy_ParametersFRX_Diff__pucch_F4_WithFH__supported
  end.
Lemma Phy_ParametersFRX_Diff__pucch_F4_WithFH__F1F2 : forall x : Phy_ParametersFRX_Diff__pucch_F4_WithFH__Type, (Phy_ParametersFRX_Diff__pucch_F4_WithFH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__pucch_F4_WithFH__F2 (Phy_ParametersFRX_Diff__pucch_F4_WithFH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__pucch_F4_WithFH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__pucch_F4_WithFH__F1 (Phy_ParametersFRX_Diff__pucch_F4_WithFH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Type : Set :=
 | Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__notSupported
.
Definition Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__cond := (fun (_ : Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Type) => True).
Lemma Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__nat__helper.

Definition Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__notSupported => 0
  end.
Definition Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__notSupported
  | _ => Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__notSupported
  end.
Lemma Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F1F2 : forall x : Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Type, (Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F2 (Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F1 (Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Type : Set :=
 | Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__notSupported
.
Definition Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__cond := (fun (_ : Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Type) => True).
Lemma Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__nat__helper.

Definition Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__notSupported => 0
  end.
Definition Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__notSupported
  | _ => Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__notSupported
  end.
Lemma Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F1F2 : forall x : Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Type, (Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F2 (Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F1 (Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Type : Set :=
 | Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__supported
.
Definition Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__cond := (fun (_ : Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Type) => True).
Lemma Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__nat__helper.

Definition Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__supported
  | _ => Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__supported
  end.
Lemma Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F1F2 : forall x : Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Type, (Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F1 x <= 0) /\ Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F2 (Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F1 (Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Type : Set :=
 | Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__supported
.
Definition Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__cond := (fun (_ : Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Type) => True).
Lemma Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__nat__helper.

Definition Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__supported
  | _ => Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__supported
  end.
Lemma Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F1F2 : forall x : Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Type, (Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F1 x <= 0) /\ Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F2 (Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F1 (Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Type : Set :=
 | Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__supported
.
Definition Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__cond := (fun (_ : Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Type) => True).
Lemma Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__nat__helper.

Definition Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__supported
  | _ => Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__supported
  end.
Lemma Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F1F2 : forall x : Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Type, (Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F1 x <= 0) /\ Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F2 (Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F1 (Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Type : Set :=
 | Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__supported
.
Definition Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__cond := (fun (_ : Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Type) => True).
Lemma Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__nat__helper.

Definition Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__supported
  | _ => Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__supported
  end.
Lemma Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F1F2 : forall x : Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Type, (Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F1 x <= 0) /\ Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F2 (Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F1 (Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Type : Set :=
 | Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__supported
.
Definition Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__cond := (fun (_ : Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Type) => True).
Lemma Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__nat__helper.

Definition Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__supported
  | _ => Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__supported
  end.
Lemma Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F1F2 : forall x : Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Type, (Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F2 (Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F1 (Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__pusch_LBRM__Type : Set :=
 | Phy_ParametersFRX_Diff__pusch_LBRM__supported
.
Definition Phy_ParametersFRX_Diff__pusch_LBRM__cond := (fun (_ : Phy_ParametersFRX_Diff__pusch_LBRM__Type) => True).
Lemma Phy_ParametersFRX_Diff__pusch_LBRM__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__pusch_LBRM__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__pusch_LBRM__nat__helper.

Definition Phy_ParametersFRX_Diff__pusch_LBRM__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__pusch_LBRM__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__pusch_LBRM__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__pusch_LBRM__supported
  | _ => Phy_ParametersFRX_Diff__pusch_LBRM__supported
  end.
Lemma Phy_ParametersFRX_Diff__pusch_LBRM__F1F2 : forall x : Phy_ParametersFRX_Diff__pusch_LBRM__Type, (Phy_ParametersFRX_Diff__pusch_LBRM__F1 x <= 0) /\ Phy_ParametersFRX_Diff__pusch_LBRM__F2 (Phy_ParametersFRX_Diff__pusch_LBRM__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__pusch_LBRM__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__pusch_LBRM__F1 (Phy_ParametersFRX_Diff__pusch_LBRM__F2 y) = y. enum_solve H y. Qed.

Lemma Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__helper1 : (4 <= 16)%Z.  lia. Qed.
Lemma Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__helper2 : to_bit_sz (Z.to_nat (16 - 4)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 4))%Z). { apply Zorder.Zle_minus_le_0. apply Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__Type := Z.
Definition Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__cond := (fun z => (4 <= z <= 16)%Z).
Inductive Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Type : Set :=
 | Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__supported
.
Definition Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__cond := (fun (_ : Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Type) => True).
Lemma Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__nat__helper.

Definition Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__supported
  | _ => Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__supported
  end.
Lemma Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F1F2 : forall x : Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Type, (Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F1 x <= 0) /\ Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F2 (Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F1 (Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Type : Set :=
 | Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__supported
.
Definition Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__cond := (fun (_ : Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Type) => True).
Lemma Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__nat__helper.

Definition Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__supported
  | _ => Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__supported
  end.
Lemma Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F1F2 : forall x : Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Type, (Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F1 x <= 0) /\ Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F2 (Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F1 (Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Type : Set :=
 | Phy_ParametersFRX_Diff__tpc_SRS_RNTI__supported
.
Definition Phy_ParametersFRX_Diff__tpc_SRS_RNTI__cond := (fun (_ : Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Type) => True).
Lemma Phy_ParametersFRX_Diff__tpc_SRS_RNTI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__tpc_SRS_RNTI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__tpc_SRS_RNTI__nat__helper.

Definition Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__tpc_SRS_RNTI__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__tpc_SRS_RNTI__supported
  | _ => Phy_ParametersFRX_Diff__tpc_SRS_RNTI__supported
  end.
Lemma Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F1F2 : forall x : Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Type, (Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F1 x <= 0) /\ Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F2 (Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F1 (Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__absoluteTPC_Command__Type : Set :=
 | Phy_ParametersFRX_Diff__absoluteTPC_Command__supported
.
Definition Phy_ParametersFRX_Diff__absoluteTPC_Command__cond := (fun (_ : Phy_ParametersFRX_Diff__absoluteTPC_Command__Type) => True).
Lemma Phy_ParametersFRX_Diff__absoluteTPC_Command__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__absoluteTPC_Command__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__absoluteTPC_Command__nat__helper.

Definition Phy_ParametersFRX_Diff__absoluteTPC_Command__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__absoluteTPC_Command__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__absoluteTPC_Command__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__absoluteTPC_Command__supported
  | _ => Phy_ParametersFRX_Diff__absoluteTPC_Command__supported
  end.
Lemma Phy_ParametersFRX_Diff__absoluteTPC_Command__F1F2 : forall x : Phy_ParametersFRX_Diff__absoluteTPC_Command__Type, (Phy_ParametersFRX_Diff__absoluteTPC_Command__F1 x <= 0) /\ Phy_ParametersFRX_Diff__absoluteTPC_Command__F2 (Phy_ParametersFRX_Diff__absoluteTPC_Command__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__absoluteTPC_Command__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__absoluteTPC_Command__F1 (Phy_ParametersFRX_Diff__absoluteTPC_Command__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Type : Set :=
 | Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__supported
.
Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__cond := (fun (_ : Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Type) => True).
Lemma Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__nat__helper.

Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__supported
  | _ => Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__supported
  end.
Lemma Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F1F2 : forall x : Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Type, (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F2 (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F1 (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Type : Set :=
 | Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__supported
.
Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__cond := (fun (_ : Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Type) => True).
Lemma Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__nat__helper.

Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__supported
  | _ => Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__supported
  end.
Lemma Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F1F2 : forall x : Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Type, (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F2 (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F1 (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Type : Set :=
 | Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__supported
.
Definition Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__cond := (fun (_ : Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Type) => True).
Lemma Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__nat__helper.

Definition Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__supported
  | _ => Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__supported
  end.
Lemma Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F1F2 : forall x : Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Type, (Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F1 x <= 0) /\ Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F2 (Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F1 (Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Type : Set :=
 | Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__supported
.
Definition Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__cond := (fun (_ : Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Type) => True).
Lemma Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__nat__helper.

Definition Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__supported
  | _ => Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__supported
  end.
Lemma Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F1F2 : forall x : Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Type, (Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F1 x <= 0) /\ Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F2 (Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F1 (Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Type : Set :=
 | Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__supported
.
Definition Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__cond := (fun (_ : Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Type) => True).
Lemma Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__nat__helper.

Definition Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__supported
  | _ => Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__supported
  end.
Lemma Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F1F2 : forall x : Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Type, (Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F1 x <= 0) /\ Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F2 (Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F1 (Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__sp_CSI_RS__Type : Set :=
 | Phy_ParametersFRX_Diff__sp_CSI_RS__supported
.
Definition Phy_ParametersFRX_Diff__sp_CSI_RS__cond := (fun (_ : Phy_ParametersFRX_Diff__sp_CSI_RS__Type) => True).
Lemma Phy_ParametersFRX_Diff__sp_CSI_RS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__sp_CSI_RS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__sp_CSI_RS__nat__helper.

Definition Phy_ParametersFRX_Diff__sp_CSI_RS__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__sp_CSI_RS__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__sp_CSI_RS__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__sp_CSI_RS__supported
  | _ => Phy_ParametersFRX_Diff__sp_CSI_RS__supported
  end.
Lemma Phy_ParametersFRX_Diff__sp_CSI_RS__F1F2 : forall x : Phy_ParametersFRX_Diff__sp_CSI_RS__Type, (Phy_ParametersFRX_Diff__sp_CSI_RS__F1 x <= 0) /\ Phy_ParametersFRX_Diff__sp_CSI_RS__F2 (Phy_ParametersFRX_Diff__sp_CSI_RS__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__sp_CSI_RS__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__sp_CSI_RS__F1 (Phy_ParametersFRX_Diff__sp_CSI_RS__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__sp_CSI_IM__Type : Set :=
 | Phy_ParametersFRX_Diff__sp_CSI_IM__supported
.
Definition Phy_ParametersFRX_Diff__sp_CSI_IM__cond := (fun (_ : Phy_ParametersFRX_Diff__sp_CSI_IM__Type) => True).
Lemma Phy_ParametersFRX_Diff__sp_CSI_IM__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__sp_CSI_IM__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__sp_CSI_IM__nat__helper.

Definition Phy_ParametersFRX_Diff__sp_CSI_IM__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__sp_CSI_IM__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__sp_CSI_IM__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__sp_CSI_IM__supported
  | _ => Phy_ParametersFRX_Diff__sp_CSI_IM__supported
  end.
Lemma Phy_ParametersFRX_Diff__sp_CSI_IM__F1F2 : forall x : Phy_ParametersFRX_Diff__sp_CSI_IM__Type, (Phy_ParametersFRX_Diff__sp_CSI_IM__F1 x <= 0) /\ Phy_ParametersFRX_Diff__sp_CSI_IM__F2 (Phy_ParametersFRX_Diff__sp_CSI_IM__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__sp_CSI_IM__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__sp_CSI_IM__F1 (Phy_ParametersFRX_Diff__sp_CSI_IM__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Type : Set :=
 | Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__supported
.
Definition Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__cond := (fun (_ : Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Type) => True).
Lemma Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__nat__helper.

Definition Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__supported
  | _ => Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__supported
  end.
Lemma Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F1F2 : forall x : Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Type, (Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F1 x <= 0) /\ Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F2 (Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F1 (Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__multipleCORESET__Type : Set :=
 | Phy_ParametersFRX_Diff__multipleCORESET__supported
.
Definition Phy_ParametersFRX_Diff__multipleCORESET__cond := (fun (_ : Phy_ParametersFRX_Diff__multipleCORESET__Type) => True).
Lemma Phy_ParametersFRX_Diff__multipleCORESET__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__multipleCORESET__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__multipleCORESET__nat__helper.

Definition Phy_ParametersFRX_Diff__multipleCORESET__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__multipleCORESET__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__multipleCORESET__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__multipleCORESET__supported
  | _ => Phy_ParametersFRX_Diff__multipleCORESET__supported
  end.
Lemma Phy_ParametersFRX_Diff__multipleCORESET__F1F2 : forall x : Phy_ParametersFRX_Diff__multipleCORESET__Type, (Phy_ParametersFRX_Diff__multipleCORESET__F1 x <= 0) /\ Phy_ParametersFRX_Diff__multipleCORESET__F2 (Phy_ParametersFRX_Diff__multipleCORESET__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__multipleCORESET__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__multipleCORESET__F1 (Phy_ParametersFRX_Diff__multipleCORESET__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CSI_RS_IM_ReceptionForFeedback.

Opaque CSI_RS_IM_ReceptionForFeedback__cond CSI_RS_IM_ReceptionForFeedback__Format.

Require Import NR.CSI_RS_ProcFrameworkForSRS.

Opaque CSI_RS_ProcFrameworkForSRS__cond CSI_RS_ProcFrameworkForSRS__Format.

Require Import NR.CSI_ReportFramework.

Opaque CSI_ReportFramework__cond CSI_ReportFramework__Format.

Inductive Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Type, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F2 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F1 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Type, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F2 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F1 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Type {
    Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol : option Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Type ;
    Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol : option Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Type ;
}.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list := (
 Opt Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Type Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Type Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond z := 
  opt_cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__cond (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__cond (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol z) /\
  True.

Inductive Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Type, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F2 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F1 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Type, (Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F2 (Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F1 (Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type, (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2 (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type, (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2 (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Type, (Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F2 (Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F1 (Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Type, (Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F2 (Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F1 (Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Type, (Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F2 (Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F1 (Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Type, (Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F2 (Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F1 (Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Type, (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F2 (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F1 (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Type, (Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F2 (Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F1 (Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Type : Set :=
 | Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__supported
.
Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__cond := (fun (_ : Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__nat__helper.

Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__supported
  | _ => Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F1F2 : forall x : Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Type, (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F2 (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F1 (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFRX_Diff__ext0O__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext0O__Type {
    Phy_ParametersFRX_Diff__ext0O__csi_RS_IM_ReceptionForFeedback : option CSI_RS_IM_ReceptionForFeedback__Type ;
    Phy_ParametersFRX_Diff__ext0O__csi_RS_ProcFrameworkForSRS : option CSI_RS_ProcFrameworkForSRS__Type ;
    Phy_ParametersFRX_Diff__ext0O__csi_ReportFramework : option CSI_ReportFramework__Type ;
    Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot : option Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Type ;
    Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH : option Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Type ;
    Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap : option Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Type ;
    Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA : option Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type ;
    Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB : option Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type ;
    Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset : option Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Type ;
    Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt : option Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Type ;
    Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt : option Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Type ;
    Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt : option Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Type ;
    Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL : option Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Type ;
    Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL : option Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Type ;
    Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL : option Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Type ;
}.
Definition Phy_ParametersFRX_Diff__ext0O__list := (
 Opt CSI_RS_IM_ReceptionForFeedback__Type CSI_RS_IM_ReceptionForFeedback__cond ::
 Opt CSI_RS_ProcFrameworkForSRS__Type CSI_RS_ProcFrameworkForSRS__cond ::
 Opt CSI_ReportFramework__Type CSI_ReportFramework__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Type Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Type Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Type Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Type Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Type Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Type Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Type Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Type Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Type Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__cond ::
 Opt Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Type Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext0O__cond z := 
  opt_cond CSI_RS_IM_ReceptionForFeedback__cond (Phy_ParametersFRX_Diff__ext0O__csi_RS_IM_ReceptionForFeedback z) /\
  opt_cond CSI_RS_ProcFrameworkForSRS__cond (Phy_ParametersFRX_Diff__ext0O__csi_RS_ProcFrameworkForSRS z) /\
  opt_cond CSI_ReportFramework__cond (Phy_ParametersFRX_Diff__ext0O__csi_ReportFramework z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__cond (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__cond (Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__cond (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__cond (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__cond (Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__cond (Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__cond (Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__cond (Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__cond (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__cond (Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL z) /\
  opt_cond Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__cond (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL z) /\
  True.

Definition Phy_ParametersFRX_Diff__ext0__Type := Phy_ParametersFRX_Diff__ext0O__Type.
Definition Phy_ParametersFRX_Diff__ext0__cond := Phy_ParametersFRX_Diff__ext0O__cond.

Lemma Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__Type := Z.
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__cond := (fun z => (1 <= z <= 15)%Z).
Lemma Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__Type := Z.
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__cond := (fun z => (1 <= z <= 15)%Z).
Record Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Type {
    Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE : Z ;
    Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE : Z ;
}.
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list := (
 Nor Z Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__cond ::
 Nor Z Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond z := 
  Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__cond (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE z) /\
  Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__cond (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE z) /\
  True.

Inductive Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Type : Set :=
 | Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__supported
.
Definition Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__cond := (fun (_ : Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__nat__helper.

Definition Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__supported
  | _ => Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F1F2 : forall x : Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Type, (Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F2 (Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F1 (Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFRX_Diff__ext1O__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext1O__Type {
    Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC : option Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Type ;
    Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol : option Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Type ;
}.
Definition Phy_ParametersFRX_Diff__ext1O__list := (
 Opt Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Type Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond ::
 Opt Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Type Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext1O__cond z := 
  opt_cond Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC z) /\
  opt_cond Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__cond (Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol z) /\
  True.

Definition Phy_ParametersFRX_Diff__ext1__Type := Phy_ParametersFRX_Diff__ext1O__Type.
Definition Phy_ParametersFRX_Diff__ext1__cond := Phy_ParametersFRX_Diff__ext1O__cond.

Inductive Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Type, (Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F2 (Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F1 (Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Type, (Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F2 (Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F1 (Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Type, (Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F2 (Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F1 (Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Type, (Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F2 (Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F1 (Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Type, (Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F2 (Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F1 (Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Type, (Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F2 (Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F1 (Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Type, (Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F2 (Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F1 (Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Type, (Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F2 (Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F1 (Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n2
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n4
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n8
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n12
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n16
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n32
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n64
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n128
.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n2 => 0
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n4 => 1
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n8 => 2
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n12 => 3
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n16 => 4
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n32 => 5
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n64 => 6
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n128 => 7
  end.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n2
  | 1 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n4
  | 2 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n8
  | 3 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n12
  | 4 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n16
  | 5 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n32
  | 6 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n64
  | 7 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n128
  | _ => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__n2
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Type, (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F1 x <= 7) /\ Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F2 (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F2F1 : forall (y : nat) (H : y <= 7), Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F1 (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n2
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n4
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n8
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n12
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n16
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n32
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n40
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n48
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n64
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n72
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n80
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n96
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n128
 | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n256
.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__nat__helper : to_bit_sz 13 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__nat__Format : T_Format nat (fun z => (z <= 13)) :=
  nat_enum_format 13 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n2 => 0
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n4 => 1
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n8 => 2
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n12 => 3
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n16 => 4
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n32 => 5
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n40 => 6
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n48 => 7
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n64 => 8
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n72 => 9
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n80 => 10
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n96 => 11
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n128 => 12
  | Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n256 => 13
  end.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n2
  | 1 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n4
  | 2 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n8
  | 3 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n12
  | 4 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n16
  | 5 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n32
  | 6 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n40
  | 7 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n48
  | 8 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n64
  | 9 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n72
  | 10 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n80
  | 11 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n96
  | 12 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n128
  | 13 => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n256
  | _ => Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__n2
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Type, (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F1 x <= 13) /\ Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F2 (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F2F1 : forall (y : nat) (H : y <= 13), Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F1 (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Type {
    Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16 : option Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16 : option Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Type ;
}.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list := (
 Opt Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Type Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Type Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond z := 
  opt_cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__cond (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__cond (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16 z) /\
  True.

Require Import NR.CSI_ReportFrameworkExt_r16.

Opaque CSI_ReportFrameworkExt_r16__cond CSI_ReportFrameworkExt_r16__Format.

Record Phy_ParametersFRX_Diff__ext2O__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext2O__Type {
    Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16 : option Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16 : option Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16 : option Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16 : option Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16 : option Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16 : option Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16 : option Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16 : option Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16 : option Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Type ;
    Phy_ParametersFRX_Diff__ext2O__csi_ReportFrameworkExt_r16 : option CSI_ReportFrameworkExt_r16__Type ;
}.
Definition Phy_ParametersFRX_Diff__ext2O__list := (
 Opt Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Type Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Type Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Type Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Type Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Type Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Type Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Type Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Type Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__cond ::
 Opt Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Type Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond ::
 Opt CSI_ReportFrameworkExt_r16__Type CSI_ReportFrameworkExt_r16__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext2O__cond z := 
  opt_cond Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__cond (Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__cond (Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__cond (Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__cond (Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__cond (Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__cond (Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__cond (Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__cond (Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16 z) /\
  opt_cond CSI_ReportFrameworkExt_r16__cond (Phy_ParametersFRX_Diff__ext2O__csi_ReportFrameworkExt_r16 z) /\
  True.

Definition Phy_ParametersFRX_Diff__ext2__Type := Phy_ParametersFRX_Diff__ext2O__Type.
Definition Phy_ParametersFRX_Diff__ext2__cond := Phy_ParametersFRX_Diff__ext2O__cond.

Inductive Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Type, (Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F2 (Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F1 (Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFRX_Diff__ext3O__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext3O__Type {
    Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16 : option Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Type ;
}.
Definition Phy_ParametersFRX_Diff__ext3O__list := (
 Opt Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Type Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext3O__cond z := 
  opt_cond Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__cond (Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16 z) /\
  True.

Definition Phy_ParametersFRX_Diff__ext3__Type := Phy_ParametersFRX_Diff__ext3O__Type.
Definition Phy_ParametersFRX_Diff__ext3__cond := Phy_ParametersFRX_Diff__ext3O__cond.

Inductive Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Type : Set :=
 | Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__supported
.
Definition Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__cond := (fun (_ : Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__nat__helper.

Definition Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__supported
  | _ => Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F1F2 : forall x : Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Type, (Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F2 (Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F1 (Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFRX_Diff__ext4O__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext4O__Type {
    Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16 : option Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Type ;
}.
Definition Phy_ParametersFRX_Diff__ext4O__list := (
 Opt Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Type Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext4O__cond z := 
  opt_cond Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__cond (Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16 z) /\
  True.

Definition Phy_ParametersFRX_Diff__ext4__Type := Phy_ParametersFRX_Diff__ext4O__Type.
Definition Phy_ParametersFRX_Diff__ext4__cond := Phy_ParametersFRX_Diff__ext4O__cond.

Inductive Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Type : Set :=
 | Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__supported
.
Definition Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__cond := (fun (_ : Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Type) => True).
Lemma Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__nat__helper.

Definition Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F1 t :=
  match t with
  | Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__supported => 0
  end.
Definition Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__supported
  | _ => Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__supported
  end.
Lemma Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F1F2 : forall x : Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Type, (Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F1 x <= 0) /\ Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F2 (Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F1 (Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFRX_Diff__ext5O__Type : Set :=
  make__Phy_ParametersFRX_Diff__ext5O__Type {
    Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17 : option Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Type ;
}.
Definition Phy_ParametersFRX_Diff__ext5O__list := (
 Opt Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Type Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext5O__cond z := 
  opt_cond Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__cond (Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17 z) /\
  True.

Definition Phy_ParametersFRX_Diff__ext5__Type := Phy_ParametersFRX_Diff__ext5O__Type.
Definition Phy_ParametersFRX_Diff__ext5__cond := Phy_ParametersFRX_Diff__ext5O__cond.

Record Phy_ParametersFRX_Diff__Type : Set :=
  make__Phy_ParametersFRX_Diff__Type {
    Phy_ParametersFRX_Diff__dynamicSFI : option Phy_ParametersFRX_Diff__dynamicSFI__Type ;
    Phy_ParametersFRX_Diff__dummy1 : option Phy_ParametersFRX_Diff__dummy1__Type ;
    Phy_ParametersFRX_Diff__twoFL_DMRS : option Phy_ParametersFRX_Diff__twoFL_DMRS__Type ;
    Phy_ParametersFRX_Diff__dummy2 : option Phy_ParametersFRX_Diff__dummy2__Type ;
    Phy_ParametersFRX_Diff__dummy3 : option Phy_ParametersFRX_Diff__dummy3__Type ;
    Phy_ParametersFRX_Diff__supportedDMRS_TypeDL : option Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Type ;
    Phy_ParametersFRX_Diff__supportedDMRS_TypeUL : option Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Type ;
    Phy_ParametersFRX_Diff__semiOpenLoopCSI : option Phy_ParametersFRX_Diff__semiOpenLoopCSI__Type ;
    Phy_ParametersFRX_Diff__csi_ReportWithoutPMI : option Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Type ;
    Phy_ParametersFRX_Diff__csi_ReportWithoutCQI : option Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Type ;
    Phy_ParametersFRX_Diff__onePortsPTRS : option Phy_ParametersFRX_Diff__onePortsPTRS__Type ;
    Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols : option Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Type ;
    Phy_ParametersFRX_Diff__pucch_F2_WithFH : option Phy_ParametersFRX_Diff__pucch_F2_WithFH__Type ;
    Phy_ParametersFRX_Diff__pucch_F3_WithFH : option Phy_ParametersFRX_Diff__pucch_F3_WithFH__Type ;
    Phy_ParametersFRX_Diff__pucch_F4_WithFH : option Phy_ParametersFRX_Diff__pucch_F4_WithFH__Type ;
    Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH : option Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Type ;
    Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH : option Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Type ;
    Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot : option Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Type ;
    Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation : option Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Type ;
    Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat : option Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Type ;
    Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot : option Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Type ;
    Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH : option Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Type ;
    Phy_ParametersFRX_Diff__pusch_LBRM : option Phy_ParametersFRX_Diff__pusch_LBRM__Type ;
    Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA : option Z ;
    Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI : option Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Type ;
    Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI : option Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Type ;
    Phy_ParametersFRX_Diff__tpc_SRS_RNTI : option Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Type ;
    Phy_ParametersFRX_Diff__absoluteTPC_Command : option Phy_ParametersFRX_Diff__absoluteTPC_Command__Type ;
    Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH : option Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Type ;
    Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH : option Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Type ;
    Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK : option Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Type ;
    Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK : option Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Type ;
    Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL : option Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Type ;
    Phy_ParametersFRX_Diff__sp_CSI_RS : option Phy_ParametersFRX_Diff__sp_CSI_RS__Type ;
    Phy_ParametersFRX_Diff__sp_CSI_IM : option Phy_ParametersFRX_Diff__sp_CSI_IM__Type ;
    Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot : option Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Type ;
    Phy_ParametersFRX_Diff__multipleCORESET : option Phy_ParametersFRX_Diff__multipleCORESET__Type ;
    Phy_ParametersFRX_Diff__ext0 : option Phy_ParametersFRX_Diff__ext0__Type ;
    Phy_ParametersFRX_Diff__ext1 : option Phy_ParametersFRX_Diff__ext1__Type ;
    Phy_ParametersFRX_Diff__ext2 : option Phy_ParametersFRX_Diff__ext2__Type ;
    Phy_ParametersFRX_Diff__ext3 : option Phy_ParametersFRX_Diff__ext3__Type ;
    Phy_ParametersFRX_Diff__ext4 : option Phy_ParametersFRX_Diff__ext4__Type ;
    Phy_ParametersFRX_Diff__ext5 : option Phy_ParametersFRX_Diff__ext5__Type ;
}.
Definition Phy_ParametersFRX_Diff__root_list : list seq_elem := (
 Opt Phy_ParametersFRX_Diff__dynamicSFI__Type Phy_ParametersFRX_Diff__dynamicSFI__cond ::
 Opt Phy_ParametersFRX_Diff__dummy1__Type Phy_ParametersFRX_Diff__dummy1__cond ::
 Opt Phy_ParametersFRX_Diff__twoFL_DMRS__Type Phy_ParametersFRX_Diff__twoFL_DMRS__cond ::
 Opt Phy_ParametersFRX_Diff__dummy2__Type Phy_ParametersFRX_Diff__dummy2__cond ::
 Opt Phy_ParametersFRX_Diff__dummy3__Type Phy_ParametersFRX_Diff__dummy3__cond ::
 Opt Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Type Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__cond ::
 Opt Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Type Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__cond ::
 Opt Phy_ParametersFRX_Diff__semiOpenLoopCSI__Type Phy_ParametersFRX_Diff__semiOpenLoopCSI__cond ::
 Opt Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Type Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__cond ::
 Opt Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Type Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__cond ::
 Opt Phy_ParametersFRX_Diff__onePortsPTRS__Type Phy_ParametersFRX_Diff__onePortsPTRS__cond ::
 Opt Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Type Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__cond ::
 Opt Phy_ParametersFRX_Diff__pucch_F2_WithFH__Type Phy_ParametersFRX_Diff__pucch_F2_WithFH__cond ::
 Opt Phy_ParametersFRX_Diff__pucch_F3_WithFH__Type Phy_ParametersFRX_Diff__pucch_F3_WithFH__cond ::
 Opt Phy_ParametersFRX_Diff__pucch_F4_WithFH__Type Phy_ParametersFRX_Diff__pucch_F4_WithFH__cond ::
 Opt Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Type Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__cond ::
 Opt Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Type Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__cond ::
 Opt Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Type Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__cond ::
 Opt Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Type Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__cond ::
 Opt Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Type Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__cond ::
 Opt Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Type Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__cond ::
 Opt Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Type Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__cond ::
 Opt Phy_ParametersFRX_Diff__pusch_LBRM__Type Phy_ParametersFRX_Diff__pusch_LBRM__cond ::
 Opt Z Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__cond ::
 Opt Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Type Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__cond ::
 Opt Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Type Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__cond ::
 Opt Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Type Phy_ParametersFRX_Diff__tpc_SRS_RNTI__cond ::
 Opt Phy_ParametersFRX_Diff__absoluteTPC_Command__Type Phy_ParametersFRX_Diff__absoluteTPC_Command__cond ::
 Opt Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Type Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__cond ::
 Opt Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Type Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__cond ::
 Opt Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Type Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__cond ::
 Opt Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Type Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__cond ::
 Opt Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Type Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__cond ::
 Opt Phy_ParametersFRX_Diff__sp_CSI_RS__Type Phy_ParametersFRX_Diff__sp_CSI_RS__cond ::
 Opt Phy_ParametersFRX_Diff__sp_CSI_IM__Type Phy_ParametersFRX_Diff__sp_CSI_IM__cond ::
 Opt Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Type Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__cond ::
 Opt Phy_ParametersFRX_Diff__multipleCORESET__Type Phy_ParametersFRX_Diff__multipleCORESET__cond ::
 nil).
Definition Phy_ParametersFRX_Diff__ext_list : list typ := (
  typ_cons Phy_ParametersFRX_Diff__ext0__Type Phy_ParametersFRX_Diff__ext0__cond ::
  typ_cons Phy_ParametersFRX_Diff__ext1__Type Phy_ParametersFRX_Diff__ext1__cond ::
  typ_cons Phy_ParametersFRX_Diff__ext2__Type Phy_ParametersFRX_Diff__ext2__cond ::
  typ_cons Phy_ParametersFRX_Diff__ext3__Type Phy_ParametersFRX_Diff__ext3__cond ::
  typ_cons Phy_ParametersFRX_Diff__ext4__Type Phy_ParametersFRX_Diff__ext4__cond ::
  typ_cons Phy_ParametersFRX_Diff__ext5__Type Phy_ParametersFRX_Diff__ext5__cond ::
  nil).
Definition Phy_ParametersFRX_Diff__cond (z : Phy_ParametersFRX_Diff__Type) := 
(  opt_cond Phy_ParametersFRX_Diff__dynamicSFI__cond (Phy_ParametersFRX_Diff__dynamicSFI z) /\
  opt_cond Phy_ParametersFRX_Diff__dummy1__cond (Phy_ParametersFRX_Diff__dummy1 z) /\
  opt_cond Phy_ParametersFRX_Diff__twoFL_DMRS__cond (Phy_ParametersFRX_Diff__twoFL_DMRS z) /\
  opt_cond Phy_ParametersFRX_Diff__dummy2__cond (Phy_ParametersFRX_Diff__dummy2 z) /\
  opt_cond Phy_ParametersFRX_Diff__dummy3__cond (Phy_ParametersFRX_Diff__dummy3 z) /\
  opt_cond Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__cond (Phy_ParametersFRX_Diff__supportedDMRS_TypeDL z) /\
  opt_cond Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__cond (Phy_ParametersFRX_Diff__supportedDMRS_TypeUL z) /\
  opt_cond Phy_ParametersFRX_Diff__semiOpenLoopCSI__cond (Phy_ParametersFRX_Diff__semiOpenLoopCSI z) /\
  opt_cond Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__cond (Phy_ParametersFRX_Diff__csi_ReportWithoutPMI z) /\
  opt_cond Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__cond (Phy_ParametersFRX_Diff__csi_ReportWithoutCQI z) /\
  opt_cond Phy_ParametersFRX_Diff__onePortsPTRS__cond (Phy_ParametersFRX_Diff__onePortsPTRS z) /\
  opt_cond Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__cond (Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols z) /\
  opt_cond Phy_ParametersFRX_Diff__pucch_F2_WithFH__cond (Phy_ParametersFRX_Diff__pucch_F2_WithFH z) /\
  opt_cond Phy_ParametersFRX_Diff__pucch_F3_WithFH__cond (Phy_ParametersFRX_Diff__pucch_F3_WithFH z) /\
  opt_cond Phy_ParametersFRX_Diff__pucch_F4_WithFH__cond (Phy_ParametersFRX_Diff__pucch_F4_WithFH z) /\
  opt_cond Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__cond (Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH z) /\
  opt_cond Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__cond (Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH z) /\
  opt_cond Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__cond (Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot z) /\
  opt_cond Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__cond (Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation z) /\
  opt_cond Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__cond (Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat z) /\
  opt_cond Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__cond (Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot z) /\
  opt_cond Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__cond (Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH z) /\
  opt_cond Phy_ParametersFRX_Diff__pusch_LBRM__cond (Phy_ParametersFRX_Diff__pusch_LBRM z) /\
  opt_cond Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__cond (Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA z) /\
  opt_cond Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__cond (Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI z) /\
  opt_cond Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__cond (Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI z) /\
  opt_cond Phy_ParametersFRX_Diff__tpc_SRS_RNTI__cond (Phy_ParametersFRX_Diff__tpc_SRS_RNTI z) /\
  opt_cond Phy_ParametersFRX_Diff__absoluteTPC_Command__cond (Phy_ParametersFRX_Diff__absoluteTPC_Command z) /\
  opt_cond Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__cond (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH z) /\
  opt_cond Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__cond (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH z) /\
  opt_cond Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__cond (Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK z) /\
  opt_cond Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__cond (Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK z) /\
  opt_cond Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__cond (Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL z) /\
  opt_cond Phy_ParametersFRX_Diff__sp_CSI_RS__cond (Phy_ParametersFRX_Diff__sp_CSI_RS z) /\
  opt_cond Phy_ParametersFRX_Diff__sp_CSI_IM__cond (Phy_ParametersFRX_Diff__sp_CSI_IM z) /\
  opt_cond Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__cond (Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot z) /\
  opt_cond Phy_ParametersFRX_Diff__multipleCORESET__cond (Phy_ParametersFRX_Diff__multipleCORESET z) /\
  True) /\ 
(  opt_cond Phy_ParametersFRX_Diff__ext0__cond (Phy_ParametersFRX_Diff__ext0 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext1__cond (Phy_ParametersFRX_Diff__ext1 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext2__cond (Phy_ParametersFRX_Diff__ext2 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext3__cond (Phy_ParametersFRX_Diff__ext3 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext4__cond (Phy_ParametersFRX_Diff__ext4 z) /\
  opt_cond Phy_ParametersFRX_Diff__ext5__cond (Phy_ParametersFRX_Diff__ext5 z) /\
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
Definition Phy_ParametersFRX_Diff__dynamicSFI__Format : T_Format Phy_ParametersFRX_Diff__dynamicSFI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__dynamicSFI__nat__Format Phy_ParametersFRX_Diff__dynamicSFI__F1 Phy_ParametersFRX_Diff__dynamicSFI__F2 Phy_ParametersFRX_Diff__dynamicSFI__F1F2 Phy_ParametersFRX_Diff__dynamicSFI__F2F1.

Opaque Phy_ParametersFRX_Diff__dynamicSFI__cond Phy_ParametersFRX_Diff__dynamicSFI__Format.

Definition Phy_ParametersFRX_Diff__dummy1__Format : T_Format Phy_ParametersFRX_Diff__dummy1__Type Phy_ParametersFRX_Diff__dummy1__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque Phy_ParametersFRX_Diff__dummy1__cond Phy_ParametersFRX_Diff__dummy1__Format.

Definition Phy_ParametersFRX_Diff__twoFL_DMRS__Format : T_Format Phy_ParametersFRX_Diff__twoFL_DMRS__Type Phy_ParametersFRX_Diff__twoFL_DMRS__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque Phy_ParametersFRX_Diff__twoFL_DMRS__cond Phy_ParametersFRX_Diff__twoFL_DMRS__Format.

Definition Phy_ParametersFRX_Diff__dummy2__Format : T_Format Phy_ParametersFRX_Diff__dummy2__Type Phy_ParametersFRX_Diff__dummy2__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque Phy_ParametersFRX_Diff__dummy2__cond Phy_ParametersFRX_Diff__dummy2__Format.

Definition Phy_ParametersFRX_Diff__dummy3__Format : T_Format Phy_ParametersFRX_Diff__dummy3__Type Phy_ParametersFRX_Diff__dummy3__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque Phy_ParametersFRX_Diff__dummy3__cond Phy_ParametersFRX_Diff__dummy3__Format.

Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Format : T_Format Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__nat__Format Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F1 Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F2 Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F1F2 Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__F2F1.

Opaque Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__cond Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Format.

Definition Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Format : T_Format Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__nat__Format Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F1 Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F2 Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F1F2 Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__F2F1.

Opaque Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__cond Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Format.

Definition Phy_ParametersFRX_Diff__semiOpenLoopCSI__Format : T_Format Phy_ParametersFRX_Diff__semiOpenLoopCSI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__semiOpenLoopCSI__nat__Format Phy_ParametersFRX_Diff__semiOpenLoopCSI__F1 Phy_ParametersFRX_Diff__semiOpenLoopCSI__F2 Phy_ParametersFRX_Diff__semiOpenLoopCSI__F1F2 Phy_ParametersFRX_Diff__semiOpenLoopCSI__F2F1.

Opaque Phy_ParametersFRX_Diff__semiOpenLoopCSI__cond Phy_ParametersFRX_Diff__semiOpenLoopCSI__Format.

Definition Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Format : T_Format Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__nat__Format Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F1 Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F2 Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F1F2 Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__F2F1.

Opaque Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__cond Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Format.

Definition Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Format : T_Format Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__nat__Format Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F1 Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F2 Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F1F2 Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__F2F1.

Opaque Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__cond Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Format.

Definition Phy_ParametersFRX_Diff__onePortsPTRS__Format : T_Format Phy_ParametersFRX_Diff__onePortsPTRS__Type Phy_ParametersFRX_Diff__onePortsPTRS__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque Phy_ParametersFRX_Diff__onePortsPTRS__cond Phy_ParametersFRX_Diff__onePortsPTRS__Format.

Definition Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Format : T_Format Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__nat__Format Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F1 Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F2 Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F1F2 Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__F2F1.

Opaque Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__cond Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Format.

Definition Phy_ParametersFRX_Diff__pucch_F2_WithFH__Format : T_Format Phy_ParametersFRX_Diff__pucch_F2_WithFH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__pucch_F2_WithFH__nat__Format Phy_ParametersFRX_Diff__pucch_F2_WithFH__F1 Phy_ParametersFRX_Diff__pucch_F2_WithFH__F2 Phy_ParametersFRX_Diff__pucch_F2_WithFH__F1F2 Phy_ParametersFRX_Diff__pucch_F2_WithFH__F2F1.

Opaque Phy_ParametersFRX_Diff__pucch_F2_WithFH__cond Phy_ParametersFRX_Diff__pucch_F2_WithFH__Format.

Definition Phy_ParametersFRX_Diff__pucch_F3_WithFH__Format : T_Format Phy_ParametersFRX_Diff__pucch_F3_WithFH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__pucch_F3_WithFH__nat__Format Phy_ParametersFRX_Diff__pucch_F3_WithFH__F1 Phy_ParametersFRX_Diff__pucch_F3_WithFH__F2 Phy_ParametersFRX_Diff__pucch_F3_WithFH__F1F2 Phy_ParametersFRX_Diff__pucch_F3_WithFH__F2F1.

Opaque Phy_ParametersFRX_Diff__pucch_F3_WithFH__cond Phy_ParametersFRX_Diff__pucch_F3_WithFH__Format.

Definition Phy_ParametersFRX_Diff__pucch_F4_WithFH__Format : T_Format Phy_ParametersFRX_Diff__pucch_F4_WithFH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__pucch_F4_WithFH__nat__Format Phy_ParametersFRX_Diff__pucch_F4_WithFH__F1 Phy_ParametersFRX_Diff__pucch_F4_WithFH__F2 Phy_ParametersFRX_Diff__pucch_F4_WithFH__F1F2 Phy_ParametersFRX_Diff__pucch_F4_WithFH__F2F1.

Opaque Phy_ParametersFRX_Diff__pucch_F4_WithFH__cond Phy_ParametersFRX_Diff__pucch_F4_WithFH__Format.

Definition Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Format : T_Format Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__nat__Format Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F1 Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F2 Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F1F2 Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__F2F1.

Opaque Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__cond Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Format.

Definition Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Format : T_Format Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__nat__Format Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F1 Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F2 Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F1F2 Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__F2F1.

Opaque Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__cond Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Format.

Definition Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Format : T_Format Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__nat__Format Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F1 Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F2 Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F1F2 Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__F2F1.

Opaque Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__cond Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Format.

Definition Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Format : T_Format Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__nat__Format Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F1 Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F2 Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F1F2 Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__F2F1.

Opaque Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__cond Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Format.

Definition Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Format : T_Format Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__nat__Format Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F1 Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F2 Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F1F2 Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__F2F1.

Opaque Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__cond Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Format.

Definition Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Format : T_Format Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__nat__Format Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F1 Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F2 Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F1F2 Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__F2F1.

Opaque Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__cond Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Format.

Definition Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Format : T_Format Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__nat__Format Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F1 Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F2 Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F1F2 Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__F2F1.

Opaque Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__cond Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Format.

Definition Phy_ParametersFRX_Diff__pusch_LBRM__Format : T_Format Phy_ParametersFRX_Diff__pusch_LBRM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__pusch_LBRM__nat__Format Phy_ParametersFRX_Diff__pusch_LBRM__F1 Phy_ParametersFRX_Diff__pusch_LBRM__F2 Phy_ParametersFRX_Diff__pusch_LBRM__F1F2 Phy_ParametersFRX_Diff__pusch_LBRM__F2F1.

Opaque Phy_ParametersFRX_Diff__pusch_LBRM__cond Phy_ParametersFRX_Diff__pusch_LBRM__Format.

Definition Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__Format : T_Format Z Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__cond :=
 ranged_int_format (4) (16) Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__helper1 Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__helper2.

Opaque Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__cond Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__Format.

Definition Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Format : T_Format Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__nat__Format Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F1 Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F2 Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F1F2 Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__F2F1.

Opaque Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__cond Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Format.

Definition Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Format : T_Format Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__nat__Format Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F1 Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F2 Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F1F2 Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__F2F1.

Opaque Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__cond Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Format.

Definition Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Format : T_Format Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__tpc_SRS_RNTI__nat__Format Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F1 Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F2 Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F1F2 Phy_ParametersFRX_Diff__tpc_SRS_RNTI__F2F1.

Opaque Phy_ParametersFRX_Diff__tpc_SRS_RNTI__cond Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Format.

Definition Phy_ParametersFRX_Diff__absoluteTPC_Command__Format : T_Format Phy_ParametersFRX_Diff__absoluteTPC_Command__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__absoluteTPC_Command__nat__Format Phy_ParametersFRX_Diff__absoluteTPC_Command__F1 Phy_ParametersFRX_Diff__absoluteTPC_Command__F2 Phy_ParametersFRX_Diff__absoluteTPC_Command__F1F2 Phy_ParametersFRX_Diff__absoluteTPC_Command__F2F1.

Opaque Phy_ParametersFRX_Diff__absoluteTPC_Command__cond Phy_ParametersFRX_Diff__absoluteTPC_Command__Format.

Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Format : T_Format Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__nat__Format Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F1 Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F2 Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F1F2 Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__F2F1.

Opaque Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__cond Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Format.

Definition Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Format : T_Format Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__nat__Format Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F1 Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F2 Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F1F2 Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__F2F1.

Opaque Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__cond Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Format.

Definition Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Format : T_Format Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__nat__Format Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F1 Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F2 Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F1F2 Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__F2F1.

Opaque Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__cond Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Format.

Definition Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Format : T_Format Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__nat__Format Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F1 Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F2 Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F1F2 Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__F2F1.

Opaque Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__cond Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Format.

Definition Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Format : T_Format Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__nat__Format Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F1 Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F2 Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F1F2 Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__F2F1.

Opaque Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__cond Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Format.

Definition Phy_ParametersFRX_Diff__sp_CSI_RS__Format : T_Format Phy_ParametersFRX_Diff__sp_CSI_RS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__sp_CSI_RS__nat__Format Phy_ParametersFRX_Diff__sp_CSI_RS__F1 Phy_ParametersFRX_Diff__sp_CSI_RS__F2 Phy_ParametersFRX_Diff__sp_CSI_RS__F1F2 Phy_ParametersFRX_Diff__sp_CSI_RS__F2F1.

Opaque Phy_ParametersFRX_Diff__sp_CSI_RS__cond Phy_ParametersFRX_Diff__sp_CSI_RS__Format.

Definition Phy_ParametersFRX_Diff__sp_CSI_IM__Format : T_Format Phy_ParametersFRX_Diff__sp_CSI_IM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__sp_CSI_IM__nat__Format Phy_ParametersFRX_Diff__sp_CSI_IM__F1 Phy_ParametersFRX_Diff__sp_CSI_IM__F2 Phy_ParametersFRX_Diff__sp_CSI_IM__F1F2 Phy_ParametersFRX_Diff__sp_CSI_IM__F2F1.

Opaque Phy_ParametersFRX_Diff__sp_CSI_IM__cond Phy_ParametersFRX_Diff__sp_CSI_IM__Format.

Definition Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Format : T_Format Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__nat__Format Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F1 Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F2 Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F1F2 Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__F2F1.

Opaque Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__cond Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Format.

Definition Phy_ParametersFRX_Diff__multipleCORESET__Format : T_Format Phy_ParametersFRX_Diff__multipleCORESET__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__multipleCORESET__nat__Format Phy_ParametersFRX_Diff__multipleCORESET__F1 Phy_ParametersFRX_Diff__multipleCORESET__F2 Phy_ParametersFRX_Diff__multipleCORESET__F1F2 Phy_ParametersFRX_Diff__multipleCORESET__F2F1.

Opaque Phy_ParametersFRX_Diff__multipleCORESET__cond Phy_ParametersFRX_Diff__multipleCORESET__Format.

Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Format : T_Format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__nat__Format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F1 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F2 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F1F2 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Format.

Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Format : T_Format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__nat__Format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F1 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F2 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F1F2 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Format.


Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Format_list : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Format_Type :=
  (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol__Format, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol__Format, unit_format)).
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Format_list.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1 z :=
  (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__sameSymbol z, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__diffSymbol z, tt)).
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F2 (y : seq_type Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Type i0 i1
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1F2_cond (z : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Type)
  : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Type)
 : Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F2 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list)
  : seq_cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list y ->
 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F2 y)) /\  Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1 (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Format : T_Format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Type Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__list__Format
    Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F2 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1F2_cond  Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F1F2_cond2 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Format.

Definition Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Format : T_Format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__nat__Format Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F1 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F2 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F1F2 Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__cond Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Format.

Definition Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Format : T_Format Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__nat__Format Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F1 Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F2 Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F1F2 Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__cond Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Format.

Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Format : T_Format Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__nat__Format Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1 Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2 Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F1F2 Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__cond Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Format.

Definition Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Format : T_Format Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__nat__Format Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1 Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2 Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F1F2 Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__cond Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Format.

Definition Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Format : T_Format Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__nat__Format Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F1 Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F2 Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F1F2 Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__cond Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Format.

Definition Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Format : T_Format Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__nat__Format Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F1 Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F2 Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F1F2 Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__cond Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Format.

Definition Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Format : T_Format Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__nat__Format Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F1 Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F2 Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F1F2 Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__cond Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Format.

Definition Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Format : T_Format Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__nat__Format Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F1 Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F2 Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F1F2 Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__cond Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Format.

Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Format : T_Format Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__nat__Format Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F1 Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F2 Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F1F2 Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__cond Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Format.

Definition Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Format : T_Format Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__nat__Format Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F1 Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F2 Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F1F2 Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__cond Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Format.

Definition Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Format : T_Format Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__nat__Format Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F1 Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F2 Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F1F2 Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__F2F1.

Opaque Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__cond Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Format.


Definition Phy_ParametersFRX_Diff__ext0O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext0O__list.
Definition Phy_ParametersFRX_Diff__ext0O__Format_list : Phy_ParametersFRX_Diff__ext0O__Format_Type :=
  (CSI_RS_IM_ReceptionForFeedback__Format, (CSI_RS_ProcFrameworkForSRS__Format, (CSI_ReportFramework__Format, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot__Format, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH__Format, (Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap__Format, (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA__Format, (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB__Format, (Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset__Format, (Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt__Format, (Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt__Format, (Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt__Format, (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL__Format, (Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL__Format, (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL__Format, unit_format))))))))))))))).
Definition Phy_ParametersFRX_Diff__ext0O__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext0O__list Phy_ParametersFRX_Diff__ext0O__Format_list.
Definition Phy_ParametersFRX_Diff__ext0O__F1 z :=
  (Phy_ParametersFRX_Diff__ext0O__csi_RS_IM_ReceptionForFeedback z, (Phy_ParametersFRX_Diff__ext0O__csi_RS_ProcFrameworkForSRS z, (Phy_ParametersFRX_Diff__ext0O__csi_ReportFramework z, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot z, (Phy_ParametersFRX_Diff__ext0O__mux_SR_HARQ_ACK_PUCCH z, (Phy_ParametersFRX_Diff__ext0O__mux_MultipleGroupCtrlCH_Overlap z, (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeA z, (Phy_ParametersFRX_Diff__ext0O__dl_SchedulingOffset_PDSCH_TypeB z, (Phy_ParametersFRX_Diff__ext0O__ul_SchedulingOffset z, (Phy_ParametersFRX_Diff__ext0O__dl_64QAM_MCS_TableAlt z, (Phy_ParametersFRX_Diff__ext0O__ul_64QAM_MCS_TableAlt z, (Phy_ParametersFRX_Diff__ext0O__cqi_TableAlt z, (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_TwoAdditionalDMRS_UL z, (Phy_ParametersFRX_Diff__ext0O__twoFL_DMRS_TwoAdditionalDMRS_UL z, (Phy_ParametersFRX_Diff__ext0O__oneFL_DMRS_ThreeAdditionalDMRS_UL z, tt))))))))))))))).
Definition Phy_ParametersFRX_Diff__ext0O__F2 (y : seq_type Phy_ParametersFRX_Diff__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, _)))))))))))))))=>
    make__Phy_ParametersFRX_Diff__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14
  end.
Lemma Phy_ParametersFRX_Diff__ext0O__F1F2_cond (z : Phy_ParametersFRX_Diff__ext0O__Type)
  : Phy_ParametersFRX_Diff__ext0O__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext0O__list (Phy_ParametersFRX_Diff__ext0O__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext0O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext0O__Type)
 : Phy_ParametersFRX_Diff__ext0O__F2 (Phy_ParametersFRX_Diff__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext0O__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext0O__list)
  : seq_cond Phy_ParametersFRX_Diff__ext0O__list y ->
 (Phy_ParametersFRX_Diff__ext0O__cond (Phy_ParametersFRX_Diff__ext0O__F2 y)) /\  Phy_ParametersFRX_Diff__ext0O__F1 (Phy_ParametersFRX_Diff__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext0O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext0O__Format : T_Format Phy_ParametersFRX_Diff__ext0O__Type Phy_ParametersFRX_Diff__ext0O__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext0O__cond Phy_ParametersFRX_Diff__ext0O__list__Format
    Phy_ParametersFRX_Diff__ext0O__F1 Phy_ParametersFRX_Diff__ext0O__F2 Phy_ParametersFRX_Diff__ext0O__F1F2_cond  Phy_ParametersFRX_Diff__ext0O__F1F2_cond2 Phy_ParametersFRX_Diff__ext0O__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext0O__cond Phy_ParametersFRX_Diff__ext0O__Format.

Definition Phy_ParametersFRX_Diff__ext0__check_all_none (b : Phy_ParametersFRX_Diff__ext0O__Type) : bool :=
match b with 
  | make__Phy_ParametersFRX_Diff__ext0O__Type None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersFRX_Diff__ext0__Format : T_Format Phy_ParametersFRX_Diff__ext0__Type Phy_ParametersFRX_Diff__ext0__cond :=
  restrict_add_format Phy_ParametersFRX_Diff__ext0__check_all_none Phy_ParametersFRX_Diff__ext0O__Format.

Opaque Phy_ParametersFRX_Diff__ext0__cond Phy_ParametersFRX_Diff__ext0__Format.

Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__Format : T_Format Z Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__cond :=
 ranged_int_format (1) (15) Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__helper1 Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__helper2.

Opaque Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__cond Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__Format.

Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__Format : T_Format Z Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__cond :=
 ranged_int_format (1) (15) Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__helper1 Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__helper2.

Opaque Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__cond Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__Format.


Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list.
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Format_list : Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Format_Type :=
  (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE__Format, (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE__Format, unit_format)).
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Format_list.
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1 z :=
  (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionMCG_UE z, (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__pdcch_BlindDetectionSCG_UE z, tt)).
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F2 (y : seq_type Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Type i0 i1
  end.
Lemma Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1F2_cond (z : Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Type)
  : Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Type)
 : Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F2 (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list)
  : seq_cond Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list y ->
 (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F2 y)) /\  Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1 (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Format : T_Format Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Type Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__list__Format
    Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1 Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F2 Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1F2_cond  Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F1F2_cond2 Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__cond Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Format.

Definition Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Format : T_Format Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__nat__Format Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F1 Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F2 Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F1F2 Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__F2F1.

Opaque Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__cond Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Format.


Definition Phy_ParametersFRX_Diff__ext1O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext1O__list.
Definition Phy_ParametersFRX_Diff__ext1O__Format_list : Phy_ParametersFRX_Diff__ext1O__Format_Type :=
  (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC__Format, (Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol__Format, unit_format)).
Definition Phy_ParametersFRX_Diff__ext1O__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext1O__list Phy_ParametersFRX_Diff__ext1O__Format_list.
Definition Phy_ParametersFRX_Diff__ext1O__F1 z :=
  (Phy_ParametersFRX_Diff__ext1O__pdcch_BlindDetectionNRDC z, (Phy_ParametersFRX_Diff__ext1O__mux_HARQ_ACK_PUSCH_DiffSymbol z, tt)).
Definition Phy_ParametersFRX_Diff__ext1O__F2 (y : seq_type Phy_ParametersFRX_Diff__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersFRX_Diff__ext1O__Type i0 i1
  end.
Lemma Phy_ParametersFRX_Diff__ext1O__F1F2_cond (z : Phy_ParametersFRX_Diff__ext1O__Type)
  : Phy_ParametersFRX_Diff__ext1O__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext1O__list (Phy_ParametersFRX_Diff__ext1O__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext1O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext1O__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext1O__Type)
 : Phy_ParametersFRX_Diff__ext1O__F2 (Phy_ParametersFRX_Diff__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext1O__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext1O__list)
  : seq_cond Phy_ParametersFRX_Diff__ext1O__list y ->
 (Phy_ParametersFRX_Diff__ext1O__cond (Phy_ParametersFRX_Diff__ext1O__F2 y)) /\  Phy_ParametersFRX_Diff__ext1O__F1 (Phy_ParametersFRX_Diff__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext1O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext1O__Format : T_Format Phy_ParametersFRX_Diff__ext1O__Type Phy_ParametersFRX_Diff__ext1O__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext1O__cond Phy_ParametersFRX_Diff__ext1O__list__Format
    Phy_ParametersFRX_Diff__ext1O__F1 Phy_ParametersFRX_Diff__ext1O__F2 Phy_ParametersFRX_Diff__ext1O__F1F2_cond  Phy_ParametersFRX_Diff__ext1O__F1F2_cond2 Phy_ParametersFRX_Diff__ext1O__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext1O__cond Phy_ParametersFRX_Diff__ext1O__Format.

Definition Phy_ParametersFRX_Diff__ext1__check_all_none (b : Phy_ParametersFRX_Diff__ext1O__Type) : bool :=
match b with 
  | make__Phy_ParametersFRX_Diff__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersFRX_Diff__ext1__Format : T_Format Phy_ParametersFRX_Diff__ext1__Type Phy_ParametersFRX_Diff__ext1__cond :=
  restrict_add_format Phy_ParametersFRX_Diff__ext1__check_all_none Phy_ParametersFRX_Diff__ext1O__Format.

Opaque Phy_ParametersFRX_Diff__ext1__cond Phy_ParametersFRX_Diff__ext1__Format.

Definition Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F1 Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F2 Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__cond Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F1 Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F2 Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__cond Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F1 Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F2 Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__cond Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F1 Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F2 Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__cond Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F1 Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F2 Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__cond Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F1 Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F2 Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__cond Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F1 Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F2 Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__cond Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F1 Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F2 Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__cond Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F1 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F2 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Format.

Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__nat__Format Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F1 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F2 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F1F2 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Format.


Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Format_list : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Format_Type :=
  (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16__Format, (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16__Format, unit_format)).
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Format_list.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1 z :=
  (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResWithinSlotAcrossCC_OneFR_r16 z, (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__maxNumberResAcrossCC_OneFR_r16 z, tt)).
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F2 (y : seq_type Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Type i0 i1
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1F2_cond (z : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Type)
  : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Type)
 : Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F2 (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list)
  : seq_cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list y ->
 (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F2 y)) /\  Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1 (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Format : T_Format Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Type Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__list__Format
    Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F2 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1F2_cond  Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F1F2_cond2 Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__cond Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Format.


Definition Phy_ParametersFRX_Diff__ext2O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext2O__list.
Definition Phy_ParametersFRX_Diff__ext2O__Format_list : Phy_ParametersFRX_Diff__ext2O__Format_Type :=
  (Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16__Format, (Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16__Format, (Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16__Format, (Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16__Format, (Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16__Format, (Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16__Format, (Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16__Format, (Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16__Format, (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16__Format, (CSI_ReportFrameworkExt_r16__Format, unit_format)))))))))).
Definition Phy_ParametersFRX_Diff__ext2O__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext2O__list Phy_ParametersFRX_Diff__ext2O__Format_list.
Definition Phy_ParametersFRX_Diff__ext2O__F1 z :=
  (Phy_ParametersFRX_Diff__ext2O__type1_HARQ_ACK_Codebook_r16 z, (Phy_ParametersFRX_Diff__ext2O__enhancedPowerControl_r16 z, (Phy_ParametersFRX_Diff__ext2O__simultaneousTCI_ActMultipleCC_r16 z, (Phy_ParametersFRX_Diff__ext2O__simultaneousSpatialRelationMultipleCC_r16 z, (Phy_ParametersFRX_Diff__ext2O__cli_RSSI_FDM_DL_r16 z, (Phy_ParametersFRX_Diff__ext2O__cli_SRS_RSRP_FDM_DL_r16 z, (Phy_ParametersFRX_Diff__ext2O__maxLayersMIMO_Adaptation_r16 z, (Phy_ParametersFRX_Diff__ext2O__aggregationFactorSPS_DL_r16 z, (Phy_ParametersFRX_Diff__ext2O__maxTotalResourcesForOneFreqRange_r16 z, (Phy_ParametersFRX_Diff__ext2O__csi_ReportFrameworkExt_r16 z, tt)))))))))).
Definition Phy_ParametersFRX_Diff__ext2O__F2 (y : seq_type Phy_ParametersFRX_Diff__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__Phy_ParametersFRX_Diff__ext2O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma Phy_ParametersFRX_Diff__ext2O__F1F2_cond (z : Phy_ParametersFRX_Diff__ext2O__Type)
  : Phy_ParametersFRX_Diff__ext2O__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext2O__list (Phy_ParametersFRX_Diff__ext2O__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext2O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext2O__Type)
 : Phy_ParametersFRX_Diff__ext2O__F2 (Phy_ParametersFRX_Diff__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext2O__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext2O__list)
  : seq_cond Phy_ParametersFRX_Diff__ext2O__list y ->
 (Phy_ParametersFRX_Diff__ext2O__cond (Phy_ParametersFRX_Diff__ext2O__F2 y)) /\  Phy_ParametersFRX_Diff__ext2O__F1 (Phy_ParametersFRX_Diff__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext2O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext2O__Format : T_Format Phy_ParametersFRX_Diff__ext2O__Type Phy_ParametersFRX_Diff__ext2O__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext2O__cond Phy_ParametersFRX_Diff__ext2O__list__Format
    Phy_ParametersFRX_Diff__ext2O__F1 Phy_ParametersFRX_Diff__ext2O__F2 Phy_ParametersFRX_Diff__ext2O__F1F2_cond  Phy_ParametersFRX_Diff__ext2O__F1F2_cond2 Phy_ParametersFRX_Diff__ext2O__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext2O__cond Phy_ParametersFRX_Diff__ext2O__Format.

Definition Phy_ParametersFRX_Diff__ext2__check_all_none (b : Phy_ParametersFRX_Diff__ext2O__Type) : bool :=
match b with 
  | make__Phy_ParametersFRX_Diff__ext2O__Type None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersFRX_Diff__ext2__Format : T_Format Phy_ParametersFRX_Diff__ext2__Type Phy_ParametersFRX_Diff__ext2__cond :=
  restrict_add_format Phy_ParametersFRX_Diff__ext2__check_all_none Phy_ParametersFRX_Diff__ext2O__Format.

Opaque Phy_ParametersFRX_Diff__ext2__cond Phy_ParametersFRX_Diff__ext2__Format.

Definition Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Format : T_Format Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__nat__Format Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F1 Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F2 Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F1F2 Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__cond Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Format.


Definition Phy_ParametersFRX_Diff__ext3O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext3O__list.
Definition Phy_ParametersFRX_Diff__ext3O__Format_list : Phy_ParametersFRX_Diff__ext3O__Format_Type :=
  (Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16__Format, unit_format).
Definition Phy_ParametersFRX_Diff__ext3O__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext3O__list Phy_ParametersFRX_Diff__ext3O__Format_list.
Definition Phy_ParametersFRX_Diff__ext3O__F1 z :=
  (Phy_ParametersFRX_Diff__ext3O__twoTCI_Act_servingCellInCC_List_r16 z, tt).
Definition Phy_ParametersFRX_Diff__ext3O__F2 (y : seq_type Phy_ParametersFRX_Diff__ext3O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersFRX_Diff__ext3O__Type i0
  end.
Lemma Phy_ParametersFRX_Diff__ext3O__F1F2_cond (z : Phy_ParametersFRX_Diff__ext3O__Type)
  : Phy_ParametersFRX_Diff__ext3O__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext3O__list (Phy_ParametersFRX_Diff__ext3O__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext3O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext3O__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext3O__Type)
 : Phy_ParametersFRX_Diff__ext3O__F2 (Phy_ParametersFRX_Diff__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext3O__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext3O__list)
  : seq_cond Phy_ParametersFRX_Diff__ext3O__list y ->
 (Phy_ParametersFRX_Diff__ext3O__cond (Phy_ParametersFRX_Diff__ext3O__F2 y)) /\  Phy_ParametersFRX_Diff__ext3O__F1 (Phy_ParametersFRX_Diff__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext3O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext3O__Format : T_Format Phy_ParametersFRX_Diff__ext3O__Type Phy_ParametersFRX_Diff__ext3O__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext3O__cond Phy_ParametersFRX_Diff__ext3O__list__Format
    Phy_ParametersFRX_Diff__ext3O__F1 Phy_ParametersFRX_Diff__ext3O__F2 Phy_ParametersFRX_Diff__ext3O__F1F2_cond  Phy_ParametersFRX_Diff__ext3O__F1F2_cond2 Phy_ParametersFRX_Diff__ext3O__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext3O__cond Phy_ParametersFRX_Diff__ext3O__Format.

Definition Phy_ParametersFRX_Diff__ext3__check_all_none (b : Phy_ParametersFRX_Diff__ext3O__Type) : bool :=
match b with 
  | make__Phy_ParametersFRX_Diff__ext3O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersFRX_Diff__ext3__Format : T_Format Phy_ParametersFRX_Diff__ext3__Type Phy_ParametersFRX_Diff__ext3__cond :=
  restrict_add_format Phy_ParametersFRX_Diff__ext3__check_all_none Phy_ParametersFRX_Diff__ext3O__Format.

Opaque Phy_ParametersFRX_Diff__ext3__cond Phy_ParametersFRX_Diff__ext3__Format.

Definition Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Format : T_Format Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__nat__Format Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F1 Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F2 Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F1F2 Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__F2F1.

Opaque Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__cond Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Format.


Definition Phy_ParametersFRX_Diff__ext4O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext4O__list.
Definition Phy_ParametersFRX_Diff__ext4O__Format_list : Phy_ParametersFRX_Diff__ext4O__Format_Type :=
  (Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16__Format, unit_format).
Definition Phy_ParametersFRX_Diff__ext4O__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext4O__list Phy_ParametersFRX_Diff__ext4O__Format_list.
Definition Phy_ParametersFRX_Diff__ext4O__F1 z :=
  (Phy_ParametersFRX_Diff__ext4O__cri_RI_CQI_WithoutNon_PMI_PortInd_r16 z, tt).
Definition Phy_ParametersFRX_Diff__ext4O__F2 (y : seq_type Phy_ParametersFRX_Diff__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersFRX_Diff__ext4O__Type i0
  end.
Lemma Phy_ParametersFRX_Diff__ext4O__F1F2_cond (z : Phy_ParametersFRX_Diff__ext4O__Type)
  : Phy_ParametersFRX_Diff__ext4O__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext4O__list (Phy_ParametersFRX_Diff__ext4O__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext4O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext4O__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext4O__Type)
 : Phy_ParametersFRX_Diff__ext4O__F2 (Phy_ParametersFRX_Diff__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext4O__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext4O__list)
  : seq_cond Phy_ParametersFRX_Diff__ext4O__list y ->
 (Phy_ParametersFRX_Diff__ext4O__cond (Phy_ParametersFRX_Diff__ext4O__F2 y)) /\  Phy_ParametersFRX_Diff__ext4O__F1 (Phy_ParametersFRX_Diff__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext4O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext4O__Format : T_Format Phy_ParametersFRX_Diff__ext4O__Type Phy_ParametersFRX_Diff__ext4O__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext4O__cond Phy_ParametersFRX_Diff__ext4O__list__Format
    Phy_ParametersFRX_Diff__ext4O__F1 Phy_ParametersFRX_Diff__ext4O__F2 Phy_ParametersFRX_Diff__ext4O__F1F2_cond  Phy_ParametersFRX_Diff__ext4O__F1F2_cond2 Phy_ParametersFRX_Diff__ext4O__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext4O__cond Phy_ParametersFRX_Diff__ext4O__Format.

Definition Phy_ParametersFRX_Diff__ext4__check_all_none (b : Phy_ParametersFRX_Diff__ext4O__Type) : bool :=
match b with 
  | make__Phy_ParametersFRX_Diff__ext4O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersFRX_Diff__ext4__Format : T_Format Phy_ParametersFRX_Diff__ext4__Type Phy_ParametersFRX_Diff__ext4__cond :=
  restrict_add_format Phy_ParametersFRX_Diff__ext4__check_all_none Phy_ParametersFRX_Diff__ext4O__Format.

Opaque Phy_ParametersFRX_Diff__ext4__cond Phy_ParametersFRX_Diff__ext4__Format.

Definition Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Format : T_Format Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__nat__Format Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F1 Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F2 Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F1F2 Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__F2F1.

Opaque Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__cond Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Format.


Definition Phy_ParametersFRX_Diff__ext5O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__ext5O__list.
Definition Phy_ParametersFRX_Diff__ext5O__Format_list : Phy_ParametersFRX_Diff__ext5O__Format_Type :=
  (Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17__Format, unit_format).
Definition Phy_ParametersFRX_Diff__ext5O__list__Format := (*Eval compute in *) seq_format Phy_ParametersFRX_Diff__ext5O__list Phy_ParametersFRX_Diff__ext5O__Format_list.
Definition Phy_ParametersFRX_Diff__ext5O__F1 z :=
  (Phy_ParametersFRX_Diff__ext5O__cqi_4_BitsSubbandTN_NonSharedSpectrumChAccess_r17 z, tt).
Definition Phy_ParametersFRX_Diff__ext5O__F2 (y : seq_type Phy_ParametersFRX_Diff__ext5O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersFRX_Diff__ext5O__Type i0
  end.
Lemma Phy_ParametersFRX_Diff__ext5O__F1F2_cond (z : Phy_ParametersFRX_Diff__ext5O__Type)
  : Phy_ParametersFRX_Diff__ext5O__cond z ->
  (seq_cond Phy_ParametersFRX_Diff__ext5O__list (Phy_ParametersFRX_Diff__ext5O__F1 z)).
intro H. unfold Phy_ParametersFRX_Diff__ext5O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext5O__F1F2_cond2 (z : Phy_ParametersFRX_Diff__ext5O__Type)
 : Phy_ParametersFRX_Diff__ext5O__F2 (Phy_ParametersFRX_Diff__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFRX_Diff__ext5O__F2F1_cond (y : seq_type Phy_ParametersFRX_Diff__ext5O__list)
  : seq_cond Phy_ParametersFRX_Diff__ext5O__list y ->
 (Phy_ParametersFRX_Diff__ext5O__cond (Phy_ParametersFRX_Diff__ext5O__F2 y)) /\  Phy_ParametersFRX_Diff__ext5O__F1 (Phy_ParametersFRX_Diff__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFRX_Diff__ext5O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFRX_Diff__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFRX_Diff__ext5O__Format : T_Format Phy_ParametersFRX_Diff__ext5O__Type Phy_ParametersFRX_Diff__ext5O__cond :=
        proj2_format  Phy_ParametersFRX_Diff__ext5O__cond Phy_ParametersFRX_Diff__ext5O__list__Format
    Phy_ParametersFRX_Diff__ext5O__F1 Phy_ParametersFRX_Diff__ext5O__F2 Phy_ParametersFRX_Diff__ext5O__F1F2_cond  Phy_ParametersFRX_Diff__ext5O__F1F2_cond2 Phy_ParametersFRX_Diff__ext5O__F2F1_cond.
Opaque Phy_ParametersFRX_Diff__ext5O__cond Phy_ParametersFRX_Diff__ext5O__Format.

Definition Phy_ParametersFRX_Diff__ext5__check_all_none (b : Phy_ParametersFRX_Diff__ext5O__Type) : bool :=
match b with 
  | make__Phy_ParametersFRX_Diff__ext5O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersFRX_Diff__ext5__Format : T_Format Phy_ParametersFRX_Diff__ext5__Type Phy_ParametersFRX_Diff__ext5__cond :=
  restrict_add_format Phy_ParametersFRX_Diff__ext5__check_all_none Phy_ParametersFRX_Diff__ext5O__Format.

Opaque Phy_ParametersFRX_Diff__ext5__cond Phy_ParametersFRX_Diff__ext5__Format.


Definition Phy_ParametersFRX_Diff__root_Format_Type := Eval cbn in seq_format_prod Phy_ParametersFRX_Diff__root_list.
Definition Phy_ParametersFRX_Diff__root_Format_list : Phy_ParametersFRX_Diff__root_Format_Type :=
  (Phy_ParametersFRX_Diff__dynamicSFI__Format, (Phy_ParametersFRX_Diff__dummy1__Format, (Phy_ParametersFRX_Diff__twoFL_DMRS__Format, (Phy_ParametersFRX_Diff__dummy2__Format, (Phy_ParametersFRX_Diff__dummy3__Format, (Phy_ParametersFRX_Diff__supportedDMRS_TypeDL__Format, (Phy_ParametersFRX_Diff__supportedDMRS_TypeUL__Format, (Phy_ParametersFRX_Diff__semiOpenLoopCSI__Format, (Phy_ParametersFRX_Diff__csi_ReportWithoutPMI__Format, (Phy_ParametersFRX_Diff__csi_ReportWithoutCQI__Format, (Phy_ParametersFRX_Diff__onePortsPTRS__Format, (Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols__Format, (Phy_ParametersFRX_Diff__pucch_F2_WithFH__Format, (Phy_ParametersFRX_Diff__pucch_F3_WithFH__Format, (Phy_ParametersFRX_Diff__pucch_F4_WithFH__Format, (Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH__Format, (Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH__Format, (Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot__Format, (Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation__Format, (Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat__Format, (Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot__Format, (Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH__Format, (Phy_ParametersFRX_Diff__pusch_LBRM__Format, (Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA__Format, (Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI__Format, (Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI__Format, (Phy_ParametersFRX_Diff__tpc_SRS_RNTI__Format, (Phy_ParametersFRX_Diff__absoluteTPC_Command__Format, (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH__Format, (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH__Format, (Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK__Format, (Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK__Format, (Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL__Format, (Phy_ParametersFRX_Diff__sp_CSI_RS__Format, (Phy_ParametersFRX_Diff__sp_CSI_IM__Format, (Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot__Format, (Phy_ParametersFRX_Diff__multipleCORESET__Format, unit_format))))))))))))))))))))))))))))))))))))).

Definition Phy_ParametersFRX_Diff__ext_Format_Type := Eval cbn in get_formats Phy_ParametersFRX_Diff__ext_list.
Definition Phy_ParametersFRX_Diff__ext_Format_list : Phy_ParametersFRX_Diff__ext_Format_Type :=
  (Phy_ParametersFRX_Diff__ext0__Format, (Phy_ParametersFRX_Diff__ext1__Format, (Phy_ParametersFRX_Diff__ext2__Format, (Phy_ParametersFRX_Diff__ext3__Format, (Phy_ParametersFRX_Diff__ext4__Format, (Phy_ParametersFRX_Diff__ext5__Format, unit__Format)))))).

Definition Phy_ParametersFRX_Diff__list_type : Set := (seq_type Phy_ParametersFRX_Diff__root_list) * (seq_ext_type Phy_ParametersFRX_Diff__ext_list).
Definition Phy_ParametersFRX_Diff__list_cond (z : Phy_ParametersFRX_Diff__list_type) : Prop :=
        (seq_cond Phy_ParametersFRX_Diff__root_list (fst z)) /\ (seq_ext_cond Phy_ParametersFRX_Diff__ext_list (snd z)).
Definition Phy_ParametersFRX_Diff__list_format : T_Format Phy_ParametersFRX_Diff__list_type Phy_ParametersFRX_Diff__list_cond :=
 (* Eval compute in *) seq_ext_format Phy_ParametersFRX_Diff__root_list Phy_ParametersFRX_Diff__root_Format_list Phy_ParametersFRX_Diff__ext_list Phy_ParametersFRX_Diff__ext_Format_list.

Opaque Phy_ParametersFRX_Diff__list_format.
Definition Phy_ParametersFRX_Diff__F1 (z : Phy_ParametersFRX_Diff__Type) : Phy_ParametersFRX_Diff__list_type :=
  (((Phy_ParametersFRX_Diff__dynamicSFI z, (Phy_ParametersFRX_Diff__dummy1 z, (Phy_ParametersFRX_Diff__twoFL_DMRS z, (Phy_ParametersFRX_Diff__dummy2 z, (Phy_ParametersFRX_Diff__dummy3 z, (Phy_ParametersFRX_Diff__supportedDMRS_TypeDL z, (Phy_ParametersFRX_Diff__supportedDMRS_TypeUL z, (Phy_ParametersFRX_Diff__semiOpenLoopCSI z, (Phy_ParametersFRX_Diff__csi_ReportWithoutPMI z, (Phy_ParametersFRX_Diff__csi_ReportWithoutCQI z, (Phy_ParametersFRX_Diff__onePortsPTRS z, (Phy_ParametersFRX_Diff__twoPUCCH_F0_2_ConsecSymbols z, (Phy_ParametersFRX_Diff__pucch_F2_WithFH z, (Phy_ParametersFRX_Diff__pucch_F3_WithFH z, (Phy_ParametersFRX_Diff__pucch_F4_WithFH z, (Phy_ParametersFRX_Diff__pucch_F0_2WithoutFH z, (Phy_ParametersFRX_Diff__pucch_F1_3_4WithoutFH z, (Phy_ParametersFRX_Diff__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot z, (Phy_ParametersFRX_Diff__uci_CodeBlockSegmentation z, (Phy_ParametersFRX_Diff__onePUCCH_LongAndShortFormat z, (Phy_ParametersFRX_Diff__twoPUCCH_AnyOthersInSlot z, (Phy_ParametersFRX_Diff__intraSlotFreqHopping_PUSCH z, (Phy_ParametersFRX_Diff__pusch_LBRM z, (Phy_ParametersFRX_Diff__pdcch_BlindDetectionCA z, (Phy_ParametersFRX_Diff__tpc_PUSCH_RNTI z, (Phy_ParametersFRX_Diff__tpc_PUCCH_RNTI z, (Phy_ParametersFRX_Diff__tpc_SRS_RNTI z, (Phy_ParametersFRX_Diff__absoluteTPC_Command z, (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUSCH z, (Phy_ParametersFRX_Diff__twoDifferentTPC_Loop_PUCCH z, (Phy_ParametersFRX_Diff__pusch_HalfPi_BPSK z, (Phy_ParametersFRX_Diff__pucch_F3_4_HalfPi_BPSK z, (Phy_ParametersFRX_Diff__almostContiguousCP_OFDM_UL z, (Phy_ParametersFRX_Diff__sp_CSI_RS z, (Phy_ParametersFRX_Diff__sp_CSI_IM z, (Phy_ParametersFRX_Diff__tdd_MultiDL_UL_SwitchPerSlot z, (Phy_ParametersFRX_Diff__multipleCORESET z, tt)))))))))))))))))))))))))))))))))))))), (
(Phy_ParametersFRX_Diff__ext0 z, (Phy_ParametersFRX_Diff__ext1 z, (Phy_ParametersFRX_Diff__ext2 z, (Phy_ParametersFRX_Diff__ext3 z, (Phy_ParametersFRX_Diff__ext4 z, (Phy_ParametersFRX_Diff__ext5 z, tt)))))))).
Definition Phy_ParametersFRX_Diff__F2 (y : Phy_ParametersFRX_Diff__list_type) : Phy_ParametersFRX_Diff__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, (j18, (j19, (j20, (j21, (j22, (j23, (j24, (j25, (j26, (j27, (j28, (j29, (j30, (j31, (j32, (j33, (j34, (j35, (j36, _))))))))))))))))))))))))))))))))))))), (i0, (i1, (i2, (i3, (i4, (i5, _)))))))=>
    make__Phy_ParametersFRX_Diff__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j22 j23 j24 j25 j26 j27 j28 j29 j30 j31 j32 j33 j34 j35 j36 i0 i1 i2 i3 i4 i5
  end.
Definition Phy_ParametersFRX_Diff__helper1 : (forall a : Phy_ParametersFRX_Diff__Type, Phy_ParametersFRX_Diff__cond a -> Phy_ParametersFRX_Diff__list_cond (Phy_ParametersFRX_Diff__F1 a)).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersFRX_Diff__helper2 : (forall a : Phy_ParametersFRX_Diff__Type, Phy_ParametersFRX_Diff__F2 (Phy_ParametersFRX_Diff__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersFRX_Diff__helper3 : (forall b : Phy_ParametersFRX_Diff__list_type, Phy_ParametersFRX_Diff__list_cond b -> Phy_ParametersFRX_Diff__cond (Phy_ParametersFRX_Diff__F2 b) /\ Phy_ParametersFRX_Diff__F1 (Phy_ParametersFRX_Diff__F2 b) = b).
                     intros. destruct b as [y y1]. unfold Phy_ParametersFRX_Diff__cond, Phy_ParametersFRX_Diff__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition Phy_ParametersFRX_Diff__Format : T_Format Phy_ParametersFRX_Diff__Type Phy_ParametersFRX_Diff__cond :=
 proj2_format Phy_ParametersFRX_Diff__cond Phy_ParametersFRX_Diff__list_format  Phy_ParametersFRX_Diff__F1 Phy_ParametersFRX_Diff__F2 Phy_ParametersFRX_Diff__helper1 Phy_ParametersFRX_Diff__helper2 Phy_ParametersFRX_Diff__helper3.

Opaque Phy_ParametersFRX_Diff__cond Phy_ParametersFRX_Diff__Format.

