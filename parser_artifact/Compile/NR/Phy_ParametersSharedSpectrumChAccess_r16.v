Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Type : Set :=
  make__Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Type {
    Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Type ;
}.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list := (
 Opt Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__cond ::
 nil).
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond z := 
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16 z) /\
  True.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Type : Set :=
 | Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__supported
.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__cond := (fun (_ : Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Type) => True).
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__nat__helper.

Definition Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F1 t :=
  match t with
  | Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__supported => 0
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__supported
  | _ => Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__supported
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F1F2 : forall x : Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Type, (Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F1 x <= 0) /\ Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersSharedSpectrumChAccess_r16__Type : Set :=
  make__Phy_ParametersSharedSpectrumChAccess_r16__Type {
    Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Type ;
    Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16 : option Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Type ;
}.
Definition Phy_ParametersSharedSpectrumChAccess_r16__root_list : list seq_elem := (
 Opt Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__cond ::
 Opt Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__cond ::
 nil).
Definition Phy_ParametersSharedSpectrumChAccess_r16__ext_list : list typ := (
  nil).
Definition Phy_ParametersSharedSpectrumChAccess_r16__cond (z : Phy_ParametersSharedSpectrumChAccess_r16__Type) := 
(  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16 z) /\
  opt_cond Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16 z) /\
  True) /\ 
(  True).


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
Definition Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Format.


Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Format_Type := Eval cbn in seq_format_prod Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Format_list : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Format_Type :=
  (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16__Format, unit_format)).
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list__Format := (*Eval compute in *) seq_format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Format_list.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1 z :=
  (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__sameSymbol_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__diffSymbol_r16 z, tt)).
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F2 (y : seq_type Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Type i0 i1
  end.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1F2_cond (z : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Type)
  : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond z ->
  (seq_cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1 z)).
intro H. unfold Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1F2_cond2 (z : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Type)
 : Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F2F1_cond (y : seq_type Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list)
  : seq_cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list y ->
 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F2 y)) /\  Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond :=
        proj2_format  Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__list__Format
    Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1F2_cond  Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F1F2_cond2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__F2F1_cond.
Opaque Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__nat__Format Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F1F2 Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__F2F1.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Format.


Definition Phy_ParametersSharedSpectrumChAccess_r16__root_Format_Type := Eval cbn in seq_format_prod Phy_ParametersSharedSpectrumChAccess_r16__root_list.
Definition Phy_ParametersSharedSpectrumChAccess_r16__root_Format_list : Phy_ParametersSharedSpectrumChAccess_r16__root_Format_Type :=
  (Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16__Format, (Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16__Format, unit_format))))))))))))))))).

Definition Phy_ParametersSharedSpectrumChAccess_r16__ext_Format_Type := Eval cbn in get_formats Phy_ParametersSharedSpectrumChAccess_r16__ext_list.
Definition Phy_ParametersSharedSpectrumChAccess_r16__ext_Format_list : Phy_ParametersSharedSpectrumChAccess_r16__ext_Format_Type :=
  unit__Format.

Definition Phy_ParametersSharedSpectrumChAccess_r16__list_type : Set := (seq_type Phy_ParametersSharedSpectrumChAccess_r16__root_list) * (seq_ext_type Phy_ParametersSharedSpectrumChAccess_r16__ext_list).
Definition Phy_ParametersSharedSpectrumChAccess_r16__list_cond (z : Phy_ParametersSharedSpectrumChAccess_r16__list_type) : Prop :=
        (seq_cond Phy_ParametersSharedSpectrumChAccess_r16__root_list (fst z)) /\ (seq_ext_cond Phy_ParametersSharedSpectrumChAccess_r16__ext_list (snd z)).
Definition Phy_ParametersSharedSpectrumChAccess_r16__list_format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__list_type Phy_ParametersSharedSpectrumChAccess_r16__list_cond :=
 (* Eval compute in *) seq_ext_format Phy_ParametersSharedSpectrumChAccess_r16__root_list Phy_ParametersSharedSpectrumChAccess_r16__root_Format_list Phy_ParametersSharedSpectrumChAccess_r16__ext_list Phy_ParametersSharedSpectrumChAccess_r16__ext_Format_list.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__list_format.
Definition Phy_ParametersSharedSpectrumChAccess_r16__F1 (z : Phy_ParametersSharedSpectrumChAccess_r16__Type) : Phy_ParametersSharedSpectrumChAccess_r16__list_type :=
  (((Phy_ParametersSharedSpectrumChAccess_r16__ss_SINR_Meas_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUCCH_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__sp_CSI_ReportPUSCH_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__dynamicSFI_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_OncePerSlot_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_PUCCH_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__mux_SR_HARQ_ACK_CSI_PUCCH_MultiPerSlot_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__mux_HARQ_ACK_PUSCH_DiffSymbol_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__pucch_Repetition_F1_3_4_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__type1_PUSCH_RepetitionMultiSlots_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__type2_PUSCH_RepetitionMultiSlots_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__pusch_RepetitionMultiSlots_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__pdsch_RepetitionMultiSlots_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__downlinkSPS_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType1_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__configuredUL_GrantType2_r16 z, (Phy_ParametersSharedSpectrumChAccess_r16__pre_EmptIndication_DL_r16 z, tt)))))))))))))))))), (
tt)).
Definition Phy_ParametersSharedSpectrumChAccess_r16__F2 (y : Phy_ParametersSharedSpectrumChAccess_r16__list_type) : Phy_ParametersSharedSpectrumChAccess_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, _))))))))))))))))), _)=>
    make__Phy_ParametersSharedSpectrumChAccess_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16
  end.
Definition Phy_ParametersSharedSpectrumChAccess_r16__helper1 : (forall a : Phy_ParametersSharedSpectrumChAccess_r16__Type, Phy_ParametersSharedSpectrumChAccess_r16__cond a -> Phy_ParametersSharedSpectrumChAccess_r16__list_cond (Phy_ParametersSharedSpectrumChAccess_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__helper2 : (forall a : Phy_ParametersSharedSpectrumChAccess_r16__Type, Phy_ParametersSharedSpectrumChAccess_r16__F2 (Phy_ParametersSharedSpectrumChAccess_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__helper3 : (forall b : Phy_ParametersSharedSpectrumChAccess_r16__list_type, Phy_ParametersSharedSpectrumChAccess_r16__list_cond b -> Phy_ParametersSharedSpectrumChAccess_r16__cond (Phy_ParametersSharedSpectrumChAccess_r16__F2 b) /\ Phy_ParametersSharedSpectrumChAccess_r16__F1 (Phy_ParametersSharedSpectrumChAccess_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold Phy_ParametersSharedSpectrumChAccess_r16__cond, Phy_ParametersSharedSpectrumChAccess_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition Phy_ParametersSharedSpectrumChAccess_r16__Format : T_Format Phy_ParametersSharedSpectrumChAccess_r16__Type Phy_ParametersSharedSpectrumChAccess_r16__cond :=
 proj2_format Phy_ParametersSharedSpectrumChAccess_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__list_format  Phy_ParametersSharedSpectrumChAccess_r16__F1 Phy_ParametersSharedSpectrumChAccess_r16__F2 Phy_ParametersSharedSpectrumChAccess_r16__helper1 Phy_ParametersSharedSpectrumChAccess_r16__helper2 Phy_ParametersSharedSpectrumChAccess_r16__helper3.

Opaque Phy_ParametersSharedSpectrumChAccess_r16__cond Phy_ParametersSharedSpectrumChAccess_r16__Format.

