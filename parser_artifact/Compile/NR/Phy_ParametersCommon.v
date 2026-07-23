Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive Phy_ParametersCommon__csi_RS_CFRA_ForHO__Type : Set :=
 | Phy_ParametersCommon__csi_RS_CFRA_ForHO__supported
.
Definition Phy_ParametersCommon__csi_RS_CFRA_ForHO__cond := (fun (_ : Phy_ParametersCommon__csi_RS_CFRA_ForHO__Type) => True).
Lemma Phy_ParametersCommon__csi_RS_CFRA_ForHO__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__csi_RS_CFRA_ForHO__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__csi_RS_CFRA_ForHO__nat__helper.

Definition Phy_ParametersCommon__csi_RS_CFRA_ForHO__F1 t :=
  match t with
  | Phy_ParametersCommon__csi_RS_CFRA_ForHO__supported => 0
  end.
Definition Phy_ParametersCommon__csi_RS_CFRA_ForHO__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__csi_RS_CFRA_ForHO__supported
  | _ => Phy_ParametersCommon__csi_RS_CFRA_ForHO__supported
  end.
Lemma Phy_ParametersCommon__csi_RS_CFRA_ForHO__F1F2 : forall x : Phy_ParametersCommon__csi_RS_CFRA_ForHO__Type, (Phy_ParametersCommon__csi_RS_CFRA_ForHO__F1 x <= 0) /\ Phy_ParametersCommon__csi_RS_CFRA_ForHO__F2 (Phy_ParametersCommon__csi_RS_CFRA_ForHO__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__csi_RS_CFRA_ForHO__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__csi_RS_CFRA_ForHO__F1 (Phy_ParametersCommon__csi_RS_CFRA_ForHO__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__dynamicPRB_BundlingDL__Type : Set :=
 | Phy_ParametersCommon__dynamicPRB_BundlingDL__supported
.
Definition Phy_ParametersCommon__dynamicPRB_BundlingDL__cond := (fun (_ : Phy_ParametersCommon__dynamicPRB_BundlingDL__Type) => True).
Lemma Phy_ParametersCommon__dynamicPRB_BundlingDL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__dynamicPRB_BundlingDL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__dynamicPRB_BundlingDL__nat__helper.

Definition Phy_ParametersCommon__dynamicPRB_BundlingDL__F1 t :=
  match t with
  | Phy_ParametersCommon__dynamicPRB_BundlingDL__supported => 0
  end.
Definition Phy_ParametersCommon__dynamicPRB_BundlingDL__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__dynamicPRB_BundlingDL__supported
  | _ => Phy_ParametersCommon__dynamicPRB_BundlingDL__supported
  end.
Lemma Phy_ParametersCommon__dynamicPRB_BundlingDL__F1F2 : forall x : Phy_ParametersCommon__dynamicPRB_BundlingDL__Type, (Phy_ParametersCommon__dynamicPRB_BundlingDL__F1 x <= 0) /\ Phy_ParametersCommon__dynamicPRB_BundlingDL__F2 (Phy_ParametersCommon__dynamicPRB_BundlingDL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__dynamicPRB_BundlingDL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__dynamicPRB_BundlingDL__F1 (Phy_ParametersCommon__dynamicPRB_BundlingDL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__sp_CSI_ReportPUCCH__Type : Set :=
 | Phy_ParametersCommon__sp_CSI_ReportPUCCH__supported
.
Definition Phy_ParametersCommon__sp_CSI_ReportPUCCH__cond := (fun (_ : Phy_ParametersCommon__sp_CSI_ReportPUCCH__Type) => True).
Lemma Phy_ParametersCommon__sp_CSI_ReportPUCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__sp_CSI_ReportPUCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__sp_CSI_ReportPUCCH__nat__helper.

Definition Phy_ParametersCommon__sp_CSI_ReportPUCCH__F1 t :=
  match t with
  | Phy_ParametersCommon__sp_CSI_ReportPUCCH__supported => 0
  end.
Definition Phy_ParametersCommon__sp_CSI_ReportPUCCH__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__sp_CSI_ReportPUCCH__supported
  | _ => Phy_ParametersCommon__sp_CSI_ReportPUCCH__supported
  end.
Lemma Phy_ParametersCommon__sp_CSI_ReportPUCCH__F1F2 : forall x : Phy_ParametersCommon__sp_CSI_ReportPUCCH__Type, (Phy_ParametersCommon__sp_CSI_ReportPUCCH__F1 x <= 0) /\ Phy_ParametersCommon__sp_CSI_ReportPUCCH__F2 (Phy_ParametersCommon__sp_CSI_ReportPUCCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__sp_CSI_ReportPUCCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__sp_CSI_ReportPUCCH__F1 (Phy_ParametersCommon__sp_CSI_ReportPUCCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__sp_CSI_ReportPUSCH__Type : Set :=
 | Phy_ParametersCommon__sp_CSI_ReportPUSCH__supported
.
Definition Phy_ParametersCommon__sp_CSI_ReportPUSCH__cond := (fun (_ : Phy_ParametersCommon__sp_CSI_ReportPUSCH__Type) => True).
Lemma Phy_ParametersCommon__sp_CSI_ReportPUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__sp_CSI_ReportPUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__sp_CSI_ReportPUSCH__nat__helper.

Definition Phy_ParametersCommon__sp_CSI_ReportPUSCH__F1 t :=
  match t with
  | Phy_ParametersCommon__sp_CSI_ReportPUSCH__supported => 0
  end.
Definition Phy_ParametersCommon__sp_CSI_ReportPUSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__sp_CSI_ReportPUSCH__supported
  | _ => Phy_ParametersCommon__sp_CSI_ReportPUSCH__supported
  end.
Lemma Phy_ParametersCommon__sp_CSI_ReportPUSCH__F1F2 : forall x : Phy_ParametersCommon__sp_CSI_ReportPUSCH__Type, (Phy_ParametersCommon__sp_CSI_ReportPUSCH__F1 x <= 0) /\ Phy_ParametersCommon__sp_CSI_ReportPUSCH__F2 (Phy_ParametersCommon__sp_CSI_ReportPUSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__sp_CSI_ReportPUSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__sp_CSI_ReportPUSCH__F1 (Phy_ParametersCommon__sp_CSI_ReportPUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Type : Set :=
 | Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__supported
.
Definition Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__cond := (fun (_ : Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Type) => True).
Lemma Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__nat__helper.

Definition Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F1 t :=
  match t with
  | Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__supported => 0
  end.
Definition Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__supported
  | _ => Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__supported
  end.
Lemma Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F1F2 : forall x : Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Type, (Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F1 x <= 0) /\ Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F2 (Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F1 (Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Type : Set :=
 | Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__supported
.
Definition Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__cond := (fun (_ : Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Type) => True).
Lemma Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__nat__helper.

Definition Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F1 t :=
  match t with
  | Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__supported => 0
  end.
Definition Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__supported
  | _ => Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__supported
  end.
Lemma Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F1F2 : forall x : Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Type, (Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F1 x <= 0) /\ Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F2 (Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F1 (Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__precoderGranularityCORESET__Type : Set :=
 | Phy_ParametersCommon__precoderGranularityCORESET__supported
.
Definition Phy_ParametersCommon__precoderGranularityCORESET__cond := (fun (_ : Phy_ParametersCommon__precoderGranularityCORESET__Type) => True).
Lemma Phy_ParametersCommon__precoderGranularityCORESET__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__precoderGranularityCORESET__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__precoderGranularityCORESET__nat__helper.

Definition Phy_ParametersCommon__precoderGranularityCORESET__F1 t :=
  match t with
  | Phy_ParametersCommon__precoderGranularityCORESET__supported => 0
  end.
Definition Phy_ParametersCommon__precoderGranularityCORESET__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__precoderGranularityCORESET__supported
  | _ => Phy_ParametersCommon__precoderGranularityCORESET__supported
  end.
Lemma Phy_ParametersCommon__precoderGranularityCORESET__F1F2 : forall x : Phy_ParametersCommon__precoderGranularityCORESET__Type, (Phy_ParametersCommon__precoderGranularityCORESET__F1 x <= 0) /\ Phy_ParametersCommon__precoderGranularityCORESET__F2 (Phy_ParametersCommon__precoderGranularityCORESET__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__precoderGranularityCORESET__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__precoderGranularityCORESET__F1 (Phy_ParametersCommon__precoderGranularityCORESET__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Type : Set :=
 | Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__supported
.
Definition Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__cond := (fun (_ : Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Type) => True).
Lemma Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__nat__helper.

Definition Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F1 t :=
  match t with
  | Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__supported => 0
  end.
Definition Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__supported
  | _ => Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__supported
  end.
Lemma Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F1F2 : forall x : Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Type, (Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F1 x <= 0) /\ Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F2 (Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F1 (Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Type : Set :=
 | Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__supported
.
Definition Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__cond := (fun (_ : Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Type) => True).
Lemma Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__nat__helper.

Definition Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F1 t :=
  match t with
  | Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__supported => 0
  end.
Definition Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__supported
  | _ => Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__supported
  end.
Lemma Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F1F2 : forall x : Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Type, (Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F1 x <= 0) /\ Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F2 (Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F1 (Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__spatialBundlingHARQ_ACK__Type : Set :=
 | Phy_ParametersCommon__spatialBundlingHARQ_ACK__supported
.
Definition Phy_ParametersCommon__spatialBundlingHARQ_ACK__cond := (fun (_ : Phy_ParametersCommon__spatialBundlingHARQ_ACK__Type) => True).
Lemma Phy_ParametersCommon__spatialBundlingHARQ_ACK__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__spatialBundlingHARQ_ACK__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__spatialBundlingHARQ_ACK__nat__helper.

Definition Phy_ParametersCommon__spatialBundlingHARQ_ACK__F1 t :=
  match t with
  | Phy_ParametersCommon__spatialBundlingHARQ_ACK__supported => 0
  end.
Definition Phy_ParametersCommon__spatialBundlingHARQ_ACK__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__spatialBundlingHARQ_ACK__supported
  | _ => Phy_ParametersCommon__spatialBundlingHARQ_ACK__supported
  end.
Lemma Phy_ParametersCommon__spatialBundlingHARQ_ACK__F1F2 : forall x : Phy_ParametersCommon__spatialBundlingHARQ_ACK__Type, (Phy_ParametersCommon__spatialBundlingHARQ_ACK__F1 x <= 0) /\ Phy_ParametersCommon__spatialBundlingHARQ_ACK__F2 (Phy_ParametersCommon__spatialBundlingHARQ_ACK__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__spatialBundlingHARQ_ACK__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__spatialBundlingHARQ_ACK__F1 (Phy_ParametersCommon__spatialBundlingHARQ_ACK__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Type : Set :=
 | Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__supported
.
Definition Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__cond := (fun (_ : Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Type) => True).
Lemma Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__nat__helper.

Definition Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F1 t :=
  match t with
  | Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__supported => 0
  end.
Definition Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__supported
  | _ => Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__supported
  end.
Lemma Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F1F2 : forall x : Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Type, (Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F1 x <= 0) /\ Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F2 (Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F1 (Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__pucch_Repetition_F1_3_4__Type : Set :=
 | Phy_ParametersCommon__pucch_Repetition_F1_3_4__supported
.
Definition Phy_ParametersCommon__pucch_Repetition_F1_3_4__cond := (fun (_ : Phy_ParametersCommon__pucch_Repetition_F1_3_4__Type) => True).
Lemma Phy_ParametersCommon__pucch_Repetition_F1_3_4__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__pucch_Repetition_F1_3_4__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__pucch_Repetition_F1_3_4__nat__helper.

Definition Phy_ParametersCommon__pucch_Repetition_F1_3_4__F1 t :=
  match t with
  | Phy_ParametersCommon__pucch_Repetition_F1_3_4__supported => 0
  end.
Definition Phy_ParametersCommon__pucch_Repetition_F1_3_4__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__pucch_Repetition_F1_3_4__supported
  | _ => Phy_ParametersCommon__pucch_Repetition_F1_3_4__supported
  end.
Lemma Phy_ParametersCommon__pucch_Repetition_F1_3_4__F1F2 : forall x : Phy_ParametersCommon__pucch_Repetition_F1_3_4__Type, (Phy_ParametersCommon__pucch_Repetition_F1_3_4__F1 x <= 0) /\ Phy_ParametersCommon__pucch_Repetition_F1_3_4__F2 (Phy_ParametersCommon__pucch_Repetition_F1_3_4__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__pucch_Repetition_F1_3_4__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__pucch_Repetition_F1_3_4__F1 (Phy_ParametersCommon__pucch_Repetition_F1_3_4__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ra_Type0_PUSCH__Type : Set :=
 | Phy_ParametersCommon__ra_Type0_PUSCH__supported
.
Definition Phy_ParametersCommon__ra_Type0_PUSCH__cond := (fun (_ : Phy_ParametersCommon__ra_Type0_PUSCH__Type) => True).
Lemma Phy_ParametersCommon__ra_Type0_PUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ra_Type0_PUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ra_Type0_PUSCH__nat__helper.

Definition Phy_ParametersCommon__ra_Type0_PUSCH__F1 t :=
  match t with
  | Phy_ParametersCommon__ra_Type0_PUSCH__supported => 0
  end.
Definition Phy_ParametersCommon__ra_Type0_PUSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ra_Type0_PUSCH__supported
  | _ => Phy_ParametersCommon__ra_Type0_PUSCH__supported
  end.
Lemma Phy_ParametersCommon__ra_Type0_PUSCH__F1F2 : forall x : Phy_ParametersCommon__ra_Type0_PUSCH__Type, (Phy_ParametersCommon__ra_Type0_PUSCH__F1 x <= 0) /\ Phy_ParametersCommon__ra_Type0_PUSCH__F2 (Phy_ParametersCommon__ra_Type0_PUSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ra_Type0_PUSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ra_Type0_PUSCH__F1 (Phy_ParametersCommon__ra_Type0_PUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Type : Set :=
 | Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__supported
.
Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__cond := (fun (_ : Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Type) => True).
Lemma Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__nat__helper.

Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F1 t :=
  match t with
  | Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__supported => 0
  end.
Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__supported
  | _ => Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__supported
  end.
Lemma Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F1F2 : forall x : Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Type, (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F1 x <= 0) /\ Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F2 (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F1 (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Type : Set :=
 | Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__supported
.
Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__cond := (fun (_ : Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Type) => True).
Lemma Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__nat__helper.

Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F1 t :=
  match t with
  | Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__supported => 0
  end.
Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__supported
  | _ => Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__supported
  end.
Lemma Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F1F2 : forall x : Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Type, (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F1 x <= 0) /\ Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F2 (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F1 (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__pdsch_MappingTypeA__Type : Set :=
 | Phy_ParametersCommon__pdsch_MappingTypeA__supported
.
Definition Phy_ParametersCommon__pdsch_MappingTypeA__cond := (fun (_ : Phy_ParametersCommon__pdsch_MappingTypeA__Type) => True).
Lemma Phy_ParametersCommon__pdsch_MappingTypeA__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__pdsch_MappingTypeA__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__pdsch_MappingTypeA__nat__helper.

Definition Phy_ParametersCommon__pdsch_MappingTypeA__F1 t :=
  match t with
  | Phy_ParametersCommon__pdsch_MappingTypeA__supported => 0
  end.
Definition Phy_ParametersCommon__pdsch_MappingTypeA__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__pdsch_MappingTypeA__supported
  | _ => Phy_ParametersCommon__pdsch_MappingTypeA__supported
  end.
Lemma Phy_ParametersCommon__pdsch_MappingTypeA__F1F2 : forall x : Phy_ParametersCommon__pdsch_MappingTypeA__Type, (Phy_ParametersCommon__pdsch_MappingTypeA__F1 x <= 0) /\ Phy_ParametersCommon__pdsch_MappingTypeA__F2 (Phy_ParametersCommon__pdsch_MappingTypeA__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__pdsch_MappingTypeA__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__pdsch_MappingTypeA__F1 (Phy_ParametersCommon__pdsch_MappingTypeA__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__pdsch_MappingTypeB__Type : Set :=
 | Phy_ParametersCommon__pdsch_MappingTypeB__supported
.
Definition Phy_ParametersCommon__pdsch_MappingTypeB__cond := (fun (_ : Phy_ParametersCommon__pdsch_MappingTypeB__Type) => True).
Lemma Phy_ParametersCommon__pdsch_MappingTypeB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__pdsch_MappingTypeB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__pdsch_MappingTypeB__nat__helper.

Definition Phy_ParametersCommon__pdsch_MappingTypeB__F1 t :=
  match t with
  | Phy_ParametersCommon__pdsch_MappingTypeB__supported => 0
  end.
Definition Phy_ParametersCommon__pdsch_MappingTypeB__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__pdsch_MappingTypeB__supported
  | _ => Phy_ParametersCommon__pdsch_MappingTypeB__supported
  end.
Lemma Phy_ParametersCommon__pdsch_MappingTypeB__F1F2 : forall x : Phy_ParametersCommon__pdsch_MappingTypeB__Type, (Phy_ParametersCommon__pdsch_MappingTypeB__F1 x <= 0) /\ Phy_ParametersCommon__pdsch_MappingTypeB__F2 (Phy_ParametersCommon__pdsch_MappingTypeB__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__pdsch_MappingTypeB__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__pdsch_MappingTypeB__F1 (Phy_ParametersCommon__pdsch_MappingTypeB__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Type : Set :=
 | Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__supported
.
Definition Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__cond := (fun (_ : Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Type) => True).
Lemma Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__nat__helper.

Definition Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F1 t :=
  match t with
  | Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__supported => 0
  end.
Definition Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__supported
  | _ => Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__supported
  end.
Lemma Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F1F2 : forall x : Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Type, (Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F1 x <= 0) /\ Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F2 (Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F1 (Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Type : Set :=
 | Phy_ParametersCommon__interSlotFreqHopping_PUSCH__supported
.
Definition Phy_ParametersCommon__interSlotFreqHopping_PUSCH__cond := (fun (_ : Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Type) => True).
Lemma Phy_ParametersCommon__interSlotFreqHopping_PUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__interSlotFreqHopping_PUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__interSlotFreqHopping_PUSCH__nat__helper.

Definition Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F1 t :=
  match t with
  | Phy_ParametersCommon__interSlotFreqHopping_PUSCH__supported => 0
  end.
Definition Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__interSlotFreqHopping_PUSCH__supported
  | _ => Phy_ParametersCommon__interSlotFreqHopping_PUSCH__supported
  end.
Lemma Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F1F2 : forall x : Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Type, (Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F1 x <= 0) /\ Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F2 (Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F1 (Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Type : Set :=
 | Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__supported
.
Definition Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__cond := (fun (_ : Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Type) => True).
Lemma Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__nat__helper.

Definition Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F1 t :=
  match t with
  | Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__supported => 0
  end.
Definition Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__supported
  | _ => Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__supported
  end.
Lemma Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F1F2 : forall x : Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Type, (Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F1 x <= 0) /\ Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F2 (Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F1 (Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Type : Set :=
 | Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__supported
.
Definition Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__cond := (fun (_ : Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Type) => True).
Lemma Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__nat__helper.

Definition Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F1 t :=
  match t with
  | Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__supported => 0
  end.
Definition Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__supported
  | _ => Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__supported
  end.
Lemma Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F1F2 : forall x : Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Type, (Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F1 x <= 0) /\ Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F2 (Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F1 (Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__pusch_RepetitionMultiSlots__Type : Set :=
 | Phy_ParametersCommon__pusch_RepetitionMultiSlots__supported
.
Definition Phy_ParametersCommon__pusch_RepetitionMultiSlots__cond := (fun (_ : Phy_ParametersCommon__pusch_RepetitionMultiSlots__Type) => True).
Lemma Phy_ParametersCommon__pusch_RepetitionMultiSlots__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__pusch_RepetitionMultiSlots__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__pusch_RepetitionMultiSlots__nat__helper.

Definition Phy_ParametersCommon__pusch_RepetitionMultiSlots__F1 t :=
  match t with
  | Phy_ParametersCommon__pusch_RepetitionMultiSlots__supported => 0
  end.
Definition Phy_ParametersCommon__pusch_RepetitionMultiSlots__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__pusch_RepetitionMultiSlots__supported
  | _ => Phy_ParametersCommon__pusch_RepetitionMultiSlots__supported
  end.
Lemma Phy_ParametersCommon__pusch_RepetitionMultiSlots__F1F2 : forall x : Phy_ParametersCommon__pusch_RepetitionMultiSlots__Type, (Phy_ParametersCommon__pusch_RepetitionMultiSlots__F1 x <= 0) /\ Phy_ParametersCommon__pusch_RepetitionMultiSlots__F2 (Phy_ParametersCommon__pusch_RepetitionMultiSlots__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__pusch_RepetitionMultiSlots__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__pusch_RepetitionMultiSlots__F1 (Phy_ParametersCommon__pusch_RepetitionMultiSlots__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Type : Set :=
 | Phy_ParametersCommon__pdsch_RepetitionMultiSlots__supported
.
Definition Phy_ParametersCommon__pdsch_RepetitionMultiSlots__cond := (fun (_ : Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Type) => True).
Lemma Phy_ParametersCommon__pdsch_RepetitionMultiSlots__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__pdsch_RepetitionMultiSlots__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__pdsch_RepetitionMultiSlots__nat__helper.

Definition Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F1 t :=
  match t with
  | Phy_ParametersCommon__pdsch_RepetitionMultiSlots__supported => 0
  end.
Definition Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__pdsch_RepetitionMultiSlots__supported
  | _ => Phy_ParametersCommon__pdsch_RepetitionMultiSlots__supported
  end.
Lemma Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F1F2 : forall x : Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Type, (Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F1 x <= 0) /\ Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F2 (Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F1 (Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__downlinkSPS__Type : Set :=
 | Phy_ParametersCommon__downlinkSPS__supported
.
Definition Phy_ParametersCommon__downlinkSPS__cond := (fun (_ : Phy_ParametersCommon__downlinkSPS__Type) => True).
Lemma Phy_ParametersCommon__downlinkSPS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__downlinkSPS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__downlinkSPS__nat__helper.

Definition Phy_ParametersCommon__downlinkSPS__F1 t :=
  match t with
  | Phy_ParametersCommon__downlinkSPS__supported => 0
  end.
Definition Phy_ParametersCommon__downlinkSPS__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__downlinkSPS__supported
  | _ => Phy_ParametersCommon__downlinkSPS__supported
  end.
Lemma Phy_ParametersCommon__downlinkSPS__F1F2 : forall x : Phy_ParametersCommon__downlinkSPS__Type, (Phy_ParametersCommon__downlinkSPS__F1 x <= 0) /\ Phy_ParametersCommon__downlinkSPS__F2 (Phy_ParametersCommon__downlinkSPS__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__downlinkSPS__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__downlinkSPS__F1 (Phy_ParametersCommon__downlinkSPS__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__configuredUL_GrantType1__Type : Set :=
 | Phy_ParametersCommon__configuredUL_GrantType1__supported
.
Definition Phy_ParametersCommon__configuredUL_GrantType1__cond := (fun (_ : Phy_ParametersCommon__configuredUL_GrantType1__Type) => True).
Lemma Phy_ParametersCommon__configuredUL_GrantType1__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__configuredUL_GrantType1__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__configuredUL_GrantType1__nat__helper.

Definition Phy_ParametersCommon__configuredUL_GrantType1__F1 t :=
  match t with
  | Phy_ParametersCommon__configuredUL_GrantType1__supported => 0
  end.
Definition Phy_ParametersCommon__configuredUL_GrantType1__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__configuredUL_GrantType1__supported
  | _ => Phy_ParametersCommon__configuredUL_GrantType1__supported
  end.
Lemma Phy_ParametersCommon__configuredUL_GrantType1__F1F2 : forall x : Phy_ParametersCommon__configuredUL_GrantType1__Type, (Phy_ParametersCommon__configuredUL_GrantType1__F1 x <= 0) /\ Phy_ParametersCommon__configuredUL_GrantType1__F2 (Phy_ParametersCommon__configuredUL_GrantType1__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__configuredUL_GrantType1__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__configuredUL_GrantType1__F1 (Phy_ParametersCommon__configuredUL_GrantType1__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__configuredUL_GrantType2__Type : Set :=
 | Phy_ParametersCommon__configuredUL_GrantType2__supported
.
Definition Phy_ParametersCommon__configuredUL_GrantType2__cond := (fun (_ : Phy_ParametersCommon__configuredUL_GrantType2__Type) => True).
Lemma Phy_ParametersCommon__configuredUL_GrantType2__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__configuredUL_GrantType2__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__configuredUL_GrantType2__nat__helper.

Definition Phy_ParametersCommon__configuredUL_GrantType2__F1 t :=
  match t with
  | Phy_ParametersCommon__configuredUL_GrantType2__supported => 0
  end.
Definition Phy_ParametersCommon__configuredUL_GrantType2__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__configuredUL_GrantType2__supported
  | _ => Phy_ParametersCommon__configuredUL_GrantType2__supported
  end.
Lemma Phy_ParametersCommon__configuredUL_GrantType2__F1F2 : forall x : Phy_ParametersCommon__configuredUL_GrantType2__Type, (Phy_ParametersCommon__configuredUL_GrantType2__F1 x <= 0) /\ Phy_ParametersCommon__configuredUL_GrantType2__F2 (Phy_ParametersCommon__configuredUL_GrantType2__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__configuredUL_GrantType2__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__configuredUL_GrantType2__F1 (Phy_ParametersCommon__configuredUL_GrantType2__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__pre_EmptIndication_DL__Type : Set :=
 | Phy_ParametersCommon__pre_EmptIndication_DL__supported
.
Definition Phy_ParametersCommon__pre_EmptIndication_DL__cond := (fun (_ : Phy_ParametersCommon__pre_EmptIndication_DL__Type) => True).
Lemma Phy_ParametersCommon__pre_EmptIndication_DL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__pre_EmptIndication_DL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__pre_EmptIndication_DL__nat__helper.

Definition Phy_ParametersCommon__pre_EmptIndication_DL__F1 t :=
  match t with
  | Phy_ParametersCommon__pre_EmptIndication_DL__supported => 0
  end.
Definition Phy_ParametersCommon__pre_EmptIndication_DL__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__pre_EmptIndication_DL__supported
  | _ => Phy_ParametersCommon__pre_EmptIndication_DL__supported
  end.
Lemma Phy_ParametersCommon__pre_EmptIndication_DL__F1F2 : forall x : Phy_ParametersCommon__pre_EmptIndication_DL__Type, (Phy_ParametersCommon__pre_EmptIndication_DL__F1 x <= 0) /\ Phy_ParametersCommon__pre_EmptIndication_DL__F2 (Phy_ParametersCommon__pre_EmptIndication_DL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__pre_EmptIndication_DL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__pre_EmptIndication_DL__F1 (Phy_ParametersCommon__pre_EmptIndication_DL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__cbg_TransIndication_DL__Type : Set :=
 | Phy_ParametersCommon__cbg_TransIndication_DL__supported
.
Definition Phy_ParametersCommon__cbg_TransIndication_DL__cond := (fun (_ : Phy_ParametersCommon__cbg_TransIndication_DL__Type) => True).
Lemma Phy_ParametersCommon__cbg_TransIndication_DL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__cbg_TransIndication_DL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__cbg_TransIndication_DL__nat__helper.

Definition Phy_ParametersCommon__cbg_TransIndication_DL__F1 t :=
  match t with
  | Phy_ParametersCommon__cbg_TransIndication_DL__supported => 0
  end.
Definition Phy_ParametersCommon__cbg_TransIndication_DL__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__cbg_TransIndication_DL__supported
  | _ => Phy_ParametersCommon__cbg_TransIndication_DL__supported
  end.
Lemma Phy_ParametersCommon__cbg_TransIndication_DL__F1F2 : forall x : Phy_ParametersCommon__cbg_TransIndication_DL__Type, (Phy_ParametersCommon__cbg_TransIndication_DL__F1 x <= 0) /\ Phy_ParametersCommon__cbg_TransIndication_DL__F2 (Phy_ParametersCommon__cbg_TransIndication_DL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__cbg_TransIndication_DL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__cbg_TransIndication_DL__F1 (Phy_ParametersCommon__cbg_TransIndication_DL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__cbg_TransIndication_UL__Type : Set :=
 | Phy_ParametersCommon__cbg_TransIndication_UL__supported
.
Definition Phy_ParametersCommon__cbg_TransIndication_UL__cond := (fun (_ : Phy_ParametersCommon__cbg_TransIndication_UL__Type) => True).
Lemma Phy_ParametersCommon__cbg_TransIndication_UL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__cbg_TransIndication_UL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__cbg_TransIndication_UL__nat__helper.

Definition Phy_ParametersCommon__cbg_TransIndication_UL__F1 t :=
  match t with
  | Phy_ParametersCommon__cbg_TransIndication_UL__supported => 0
  end.
Definition Phy_ParametersCommon__cbg_TransIndication_UL__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__cbg_TransIndication_UL__supported
  | _ => Phy_ParametersCommon__cbg_TransIndication_UL__supported
  end.
Lemma Phy_ParametersCommon__cbg_TransIndication_UL__F1F2 : forall x : Phy_ParametersCommon__cbg_TransIndication_UL__Type, (Phy_ParametersCommon__cbg_TransIndication_UL__F1 x <= 0) /\ Phy_ParametersCommon__cbg_TransIndication_UL__F2 (Phy_ParametersCommon__cbg_TransIndication_UL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__cbg_TransIndication_UL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__cbg_TransIndication_UL__F1 (Phy_ParametersCommon__cbg_TransIndication_UL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__cbg_FlushIndication_DL__Type : Set :=
 | Phy_ParametersCommon__cbg_FlushIndication_DL__supported
.
Definition Phy_ParametersCommon__cbg_FlushIndication_DL__cond := (fun (_ : Phy_ParametersCommon__cbg_FlushIndication_DL__Type) => True).
Lemma Phy_ParametersCommon__cbg_FlushIndication_DL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__cbg_FlushIndication_DL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__cbg_FlushIndication_DL__nat__helper.

Definition Phy_ParametersCommon__cbg_FlushIndication_DL__F1 t :=
  match t with
  | Phy_ParametersCommon__cbg_FlushIndication_DL__supported => 0
  end.
Definition Phy_ParametersCommon__cbg_FlushIndication_DL__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__cbg_FlushIndication_DL__supported
  | _ => Phy_ParametersCommon__cbg_FlushIndication_DL__supported
  end.
Lemma Phy_ParametersCommon__cbg_FlushIndication_DL__F1F2 : forall x : Phy_ParametersCommon__cbg_FlushIndication_DL__Type, (Phy_ParametersCommon__cbg_FlushIndication_DL__F1 x <= 0) /\ Phy_ParametersCommon__cbg_FlushIndication_DL__F2 (Phy_ParametersCommon__cbg_FlushIndication_DL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__cbg_FlushIndication_DL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__cbg_FlushIndication_DL__F1 (Phy_ParametersCommon__cbg_FlushIndication_DL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Type : Set :=
 | Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__supported
.
Definition Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__cond := (fun (_ : Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Type) => True).
Lemma Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__nat__helper.

Definition Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F1 t :=
  match t with
  | Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__supported => 0
  end.
Definition Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__supported
  | _ => Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__supported
  end.
Lemma Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F1F2 : forall x : Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Type, (Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F1 x <= 0) /\ Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F2 (Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F1 (Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Type : Set :=
 | Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__supported
.
Definition Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__cond := (fun (_ : Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Type) => True).
Lemma Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__nat__helper.

Definition Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F1 t :=
  match t with
  | Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__supported => 0
  end.
Definition Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__supported
  | _ => Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__supported
  end.
Lemma Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F1F2 : forall x : Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Type, (Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F1 x <= 0) /\ Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F2 (Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F1 (Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__rateMatchingResrcSetDynamic__Type : Set :=
 | Phy_ParametersCommon__rateMatchingResrcSetDynamic__supported
.
Definition Phy_ParametersCommon__rateMatchingResrcSetDynamic__cond := (fun (_ : Phy_ParametersCommon__rateMatchingResrcSetDynamic__Type) => True).
Lemma Phy_ParametersCommon__rateMatchingResrcSetDynamic__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__rateMatchingResrcSetDynamic__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__rateMatchingResrcSetDynamic__nat__helper.

Definition Phy_ParametersCommon__rateMatchingResrcSetDynamic__F1 t :=
  match t with
  | Phy_ParametersCommon__rateMatchingResrcSetDynamic__supported => 0
  end.
Definition Phy_ParametersCommon__rateMatchingResrcSetDynamic__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__rateMatchingResrcSetDynamic__supported
  | _ => Phy_ParametersCommon__rateMatchingResrcSetDynamic__supported
  end.
Lemma Phy_ParametersCommon__rateMatchingResrcSetDynamic__F1F2 : forall x : Phy_ParametersCommon__rateMatchingResrcSetDynamic__Type, (Phy_ParametersCommon__rateMatchingResrcSetDynamic__F1 x <= 0) /\ Phy_ParametersCommon__rateMatchingResrcSetDynamic__F2 (Phy_ParametersCommon__rateMatchingResrcSetDynamic__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__rateMatchingResrcSetDynamic__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__rateMatchingResrcSetDynamic__F1 (Phy_ParametersCommon__rateMatchingResrcSetDynamic__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__bwp_SwitchingDelay__Type : Set :=
 | Phy_ParametersCommon__bwp_SwitchingDelay__type1
 | Phy_ParametersCommon__bwp_SwitchingDelay__type2
.
Definition Phy_ParametersCommon__bwp_SwitchingDelay__cond := (fun (_ : Phy_ParametersCommon__bwp_SwitchingDelay__Type) => True).
Lemma Phy_ParametersCommon__bwp_SwitchingDelay__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__bwp_SwitchingDelay__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 Phy_ParametersCommon__bwp_SwitchingDelay__nat__helper.

Definition Phy_ParametersCommon__bwp_SwitchingDelay__F1 t :=
  match t with
  | Phy_ParametersCommon__bwp_SwitchingDelay__type1 => 0
  | Phy_ParametersCommon__bwp_SwitchingDelay__type2 => 1
  end.
Definition Phy_ParametersCommon__bwp_SwitchingDelay__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__bwp_SwitchingDelay__type1
  | 1 => Phy_ParametersCommon__bwp_SwitchingDelay__type2
  | _ => Phy_ParametersCommon__bwp_SwitchingDelay__type1
  end.
Lemma Phy_ParametersCommon__bwp_SwitchingDelay__F1F2 : forall x : Phy_ParametersCommon__bwp_SwitchingDelay__Type, (Phy_ParametersCommon__bwp_SwitchingDelay__F1 x <= 1) /\ Phy_ParametersCommon__bwp_SwitchingDelay__F2 (Phy_ParametersCommon__bwp_SwitchingDelay__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__bwp_SwitchingDelay__F2F1 : forall (y : nat) (H : y <= 1), Phy_ParametersCommon__bwp_SwitchingDelay__F1 (Phy_ParametersCommon__bwp_SwitchingDelay__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext0O__dummy__Type : Set :=
 | Phy_ParametersCommon__ext0O__dummy__supported
.
Definition Phy_ParametersCommon__ext0O__dummy__cond := (fun (_ : Phy_ParametersCommon__ext0O__dummy__Type) => True).
Lemma Phy_ParametersCommon__ext0O__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext0O__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext0O__dummy__nat__helper.

Definition Phy_ParametersCommon__ext0O__dummy__F1 t :=
  match t with
  | Phy_ParametersCommon__ext0O__dummy__supported => 0
  end.
Definition Phy_ParametersCommon__ext0O__dummy__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext0O__dummy__supported
  | _ => Phy_ParametersCommon__ext0O__dummy__supported
  end.
Lemma Phy_ParametersCommon__ext0O__dummy__F1F2 : forall x : Phy_ParametersCommon__ext0O__dummy__Type, (Phy_ParametersCommon__ext0O__dummy__F1 x <= 0) /\ Phy_ParametersCommon__ext0O__dummy__F2 (Phy_ParametersCommon__ext0O__dummy__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext0O__dummy__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext0O__dummy__F1 (Phy_ParametersCommon__ext0O__dummy__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext0O__Type : Set :=
  make__Phy_ParametersCommon__ext0O__Type {
    Phy_ParametersCommon__ext0O__dummy : option Phy_ParametersCommon__ext0O__dummy__Type ;
}.
Definition Phy_ParametersCommon__ext0O__list := (
 Opt Phy_ParametersCommon__ext0O__dummy__Type Phy_ParametersCommon__ext0O__dummy__cond ::
 nil).
Definition Phy_ParametersCommon__ext0O__cond z := 
  opt_cond Phy_ParametersCommon__ext0O__dummy__cond (Phy_ParametersCommon__ext0O__dummy z) /\
  True.

Definition Phy_ParametersCommon__ext0__Type := Phy_ParametersCommon__ext0O__Type.
Definition Phy_ParametersCommon__ext0__cond := Phy_ParametersCommon__ext0O__cond.

Inductive Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Type : Set :=
 | Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__n10
.
Definition Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__cond := (fun (_ : Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Type) => True).
Lemma Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__nat__helper.

Definition Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F1 t :=
  match t with
  | Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__n10 => 0
  end.
Definition Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__n10
  | _ => Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__n10
  end.
Lemma Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F1F2 : forall x : Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Type, (Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F1 x <= 0) /\ Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F2 (Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F1 (Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Type : Set :=
 | Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__supported
.
Definition Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__cond := (fun (_ : Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Type) => True).
Lemma Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__nat__helper.

Definition Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F1 t :=
  match t with
  | Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__supported => 0
  end.
Definition Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__supported
  | _ => Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__supported
  end.
Lemma Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F1F2 : forall x : Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Type, (Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F1 x <= 0) /\ Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F2 (Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F1 (Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Type : Set :=
 | Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__supported
.
Definition Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__cond := (fun (_ : Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Type) => True).
Lemma Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__nat__helper.

Definition Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F1 t :=
  match t with
  | Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__supported => 0
  end.
Definition Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__supported
  | _ => Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__supported
  end.
Lemma Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F1F2 : forall x : Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Type, (Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F1 x <= 0) /\ Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F2 (Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F1 (Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext1O__Type : Set :=
  make__Phy_ParametersCommon__ext1O__Type {
    Phy_ParametersCommon__ext1O__maxNumberSearchSpaces : option Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Type ;
    Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic : option Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Type ;
    Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication : option Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Type ;
}.
Definition Phy_ParametersCommon__ext1O__list := (
 Opt Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Type Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__cond ::
 Opt Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Type Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__cond ::
 Opt Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Type Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__cond ::
 nil).
Definition Phy_ParametersCommon__ext1O__cond z := 
  opt_cond Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__cond (Phy_ParametersCommon__ext1O__maxNumberSearchSpaces z) /\
  opt_cond Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__cond (Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic z) /\
  opt_cond Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__cond (Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication z) /\
  True.

Definition Phy_ParametersCommon__ext1__Type := Phy_ParametersCommon__ext1O__Type.
Definition Phy_ParametersCommon__ext1__cond := Phy_ParametersCommon__ext1O__cond.

Require Import NR.CarrierAggregationVariant.

Opaque CarrierAggregationVariant__cond CarrierAggregationVariant__Format.

Record Phy_ParametersCommon__ext2O__Type : Set :=
  make__Phy_ParametersCommon__ext2O__Type {
    Phy_ParametersCommon__ext2O__spCellPlacement : option CarrierAggregationVariant__Type ;
}.
Definition Phy_ParametersCommon__ext2O__list := (
 Opt CarrierAggregationVariant__Type CarrierAggregationVariant__cond ::
 nil).
Definition Phy_ParametersCommon__ext2O__cond z := 
  opt_cond CarrierAggregationVariant__cond (Phy_ParametersCommon__ext2O__spCellPlacement z) /\
  True.

Definition Phy_ParametersCommon__ext2__Type := Phy_ParametersCommon__ext2O__Type.
Definition Phy_ParametersCommon__ext2__cond := Phy_ParametersCommon__ext2O__cond.

Inductive Phy_ParametersCommon__ext3O__twoStepRACH_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__twoStepRACH_r16__supported
.
Definition Phy_ParametersCommon__ext3O__twoStepRACH_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__twoStepRACH_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__twoStepRACH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__twoStepRACH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__twoStepRACH_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__twoStepRACH_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__twoStepRACH_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__twoStepRACH_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__twoStepRACH_r16__supported
  | _ => Phy_ParametersCommon__ext3O__twoStepRACH_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__twoStepRACH_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__twoStepRACH_r16__Type, (Phy_ParametersCommon__ext3O__twoStepRACH_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__twoStepRACH_r16__F2 (Phy_ParametersCommon__ext3O__twoStepRACH_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__twoStepRACH_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__twoStepRACH_r16__F1 (Phy_ParametersCommon__ext3O__twoStepRACH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__supported
.
Definition Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__supported
  | _ => Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Type, (Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F2 (Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F1 (Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__supported
.
Definition Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__supported
  | _ => Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Type, (Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F2 (Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F1 (Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__supported
.
Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__supported
  | _ => Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Type, (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F2 (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F1 (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__supported
.
Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__supported
  | _ => Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Type, (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F2 (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F1 (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__supported
.
Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__supported
  | _ => Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Type, (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F2 (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F1 (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__supported
.
Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__supported
  | _ => Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Type, (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F2 (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F1 (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__supported
.
Definition Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__supported
  | _ => Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Type, (Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F2 (Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F1 (Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__supported
.
Definition Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__supported
  | _ => Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Type, (Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F2 (Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F1 (Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__supported
.
Definition Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__supported
  | _ => Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Type, (Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F2 (Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F1 (Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__supported
.
Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__supported
  | _ => Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Type, (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F2 (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F1 (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__supported
.
Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__supported
  | _ => Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Type, (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F2 (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F1 (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__supported
.
Definition Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__supported
  | _ => Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Type, (Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F2 (Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F1 (Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__supported
.
Definition Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__supported
  | _ => Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Type, (Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F2 (Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F1 (Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__supported
.
Definition Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__supported
  | _ => Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Type, (Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F2 (Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F1 (Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__supported
.
Definition Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__supported
  | _ => Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Type, (Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F2 (Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F1 (Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__supported
.
Definition Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__supported
  | _ => Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Type, (Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F2 (Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F1 (Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__supported
.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__supported
  | _ => Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Type, (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F2 (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F1 (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__supported
.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__supported
  | _ => Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Type, (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F2 (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F1 (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Type : Set :=
  make__Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Type {
    Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16 : option Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Type ;
    Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16 : option Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Type ;
}.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list := (
 Opt Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Type Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Type Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond z := 
  opt_cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__cond (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__cond (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16 z) /\
  True.

Inductive Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n1
 | Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n4
 | Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n8
 | Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n16
.
Definition Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n1 => 0
  | Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n4 => 1
  | Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n8 => 2
  | Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n16 => 3
  end.
Definition Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n1
  | 1 => Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n4
  | 2 => Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n8
  | 3 => Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n16
  | _ => Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__n1
  end.
Lemma Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Type, (Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F1 x <= 3) /\ Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F2 (Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F2F1 : forall (y : nat) (H : y <= 3), Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F1 (Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__supported
.
Definition Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__supported
  | _ => Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Type, (Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F2 (Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F1 (Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__supported
.
Definition Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__supported
  | _ => Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Type, (Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F2 (Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F1 (Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CodebookVariantsList_r16.

Opaque CodebookVariantsList_r16__cond CodebookVariantsList_r16__Format.

Inductive Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__supported
.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__supported
  | _ => Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Type, (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F2 (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F1 (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__supported
.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__supported
  | _ => Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Type, (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F2 (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F1 (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Type : Set :=
  make__Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Type {
    Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16 : option Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Type ;
    Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16 : option Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Type ;
}.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list := (
 Opt Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Type Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Type Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond z := 
  opt_cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__cond (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__cond (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16 z) /\
  True.

Inductive Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__supported
.
Definition Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__supported
  | _ => Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Type, (Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F2 (Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F1 (Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__supported
.
Definition Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__supported
  | _ => Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Type, (Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F2 (Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F1 (Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n4
 | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n8
 | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n16
 | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n32
 | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n64
.
Definition Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n4 => 0
  | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n8 => 1
  | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n16 => 2
  | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n32 => 3
  | Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n64 => 4
  end.
Definition Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n4
  | 1 => Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n8
  | 2 => Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n16
  | 3 => Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n32
  | 4 => Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n64
  | _ => Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__n4
  end.
Lemma Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Type, (Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F1 x <= 4) /\ Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F2 (Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F2F1 : forall (y : nat) (H : y <= 4), Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F1 (Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__supported
.
Definition Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__supported
  | _ => Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Type, (Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F2 (Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F1 (Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n2
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n4
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n8
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n12
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n16
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n32
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n64
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n128
.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n2 => 0
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n4 => 1
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n8 => 2
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n12 => 3
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n16 => 4
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n32 => 5
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n64 => 6
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n128 => 7
  end.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n2
  | 1 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n4
  | 2 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n8
  | 3 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n12
  | 4 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n16
  | 5 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n32
  | 6 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n64
  | 7 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n128
  | _ => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__n2
  end.
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Type, (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F1 x <= 7) /\ Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F2 (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F2F1 : forall (y : nat) (H : y <= 7), Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F1 (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n2
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n4
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n8
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n12
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n16
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n32
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n40
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n48
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n64
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n72
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n80
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n96
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n128
 | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n256
.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__nat__helper : to_bit_sz 13 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__nat__Format : T_Format nat (fun z => (z <= 13)) :=
  nat_enum_format 13 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n2 => 0
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n4 => 1
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n8 => 2
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n12 => 3
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n16 => 4
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n32 => 5
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n40 => 6
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n48 => 7
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n64 => 8
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n72 => 9
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n80 => 10
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n96 => 11
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n128 => 12
  | Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n256 => 13
  end.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n2
  | 1 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n4
  | 2 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n8
  | 3 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n12
  | 4 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n16
  | 5 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n32
  | 6 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n40
  | 7 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n48
  | 8 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n64
  | 9 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n72
  | 10 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n80
  | 11 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n96
  | 12 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n128
  | 13 => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n256
  | _ => Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__n2
  end.
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Type, (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F1 x <= 13) /\ Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F2 (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F2F1 : forall (y : nat) (H : y <= 13), Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F1 (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Type : Set :=
  make__Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Type {
    Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16 : option Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Type ;
    Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16 : option Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Type ;
}.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list := (
 Opt Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Type Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Type Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond z := 
  opt_cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__cond (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__cond (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16 z) /\
  True.

Inductive Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__longAndLong
 | Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__longAndShort
 | Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__shortAndShort
.
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__longAndLong => 0
  | Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__longAndShort => 1
  | Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__shortAndShort => 2
  end.
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__longAndLong
  | 1 => Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__longAndShort
  | 2 => Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__shortAndShort
  | _ => Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__longAndLong
  end.
Lemma Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Type, (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F1 x <= 2) /\ Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F2 (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F2F1 : forall (y : nat) (H : y <= 2), Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F1 (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Type : Set :=
  make__Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Type {
    Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16 : option Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Type ;
}.
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list := (
 Opt Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Type Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond z := 
  opt_cond Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__cond (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16 z) /\
  True.

Inductive Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__supported
.
Definition Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__supported
  | _ => Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__supported
  end.
Lemma Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Type, (Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F2 (Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F1 (Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__us100
 | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__us200
.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__us100 => 0
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__us200 => 1
  end.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__us100
  | 1 => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__us200
  | _ => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__us100
  end.
Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Type, (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F1 x <= 1) /\ Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F2 (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F2F1 : forall (y : nat) (H : y <= 1), Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F1 (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Type : Set :=
 | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us200
 | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us400
 | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us800
 | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us1000
.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__cond := (fun (_ : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Type) => True).
Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__nat__helper.

Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us200 => 0
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us400 => 1
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us800 => 2
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us1000 => 3
  end.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us200
  | 1 => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us400
  | 2 => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us800
  | 3 => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us1000
  | _ => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__us200
  end.
Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F1F2 : forall x : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Type, (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F1 x <= 3) /\ Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F2 (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F2F1 : forall (y : nat) (H : y <= 3), Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F1 (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F2 y) = y. enum_solve H y. Qed.


Inductive Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type : Set :=
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16 : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Type -> Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16 : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Type -> Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type
.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list : list typ := (
typ_cons Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Type Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__cond ::
typ_cons Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Type Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__cond (c : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type) := 
  match c with
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16 t => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__cond t 
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16 t => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__cond t 
  end.

Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__len_helper1 : to_bit_sz (length Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__len_helper2 : 2 <= length2 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list.
 simpl. lia. Qed.
Record Phy_ParametersCommon__ext3O__Type : Set :=
  make__Phy_ParametersCommon__ext3O__Type {
    Phy_ParametersCommon__ext3O__twoStepRACH_r16 : option Phy_ParametersCommon__ext3O__twoStepRACH_r16__Type ;
    Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16 : option Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Type ;
    Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16 : option Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Type ;
    Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16 : option Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Type ;
    Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16 : option Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Type ;
    Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16 : option Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Type ;
    Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16 : option Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Type ;
    Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16 : option Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Type ;
    Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16 : option Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Type ;
    Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16 : option Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Type ;
    Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16 : option Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Type ;
    Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16 : option Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Type ;
    Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16 : option Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Type ;
    Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16 : option Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Type ;
    Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16 : option Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Type ;
    Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16 : option Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Type ;
    Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16 : option Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Type ;
    Phy_ParametersCommon__ext3O__crossSlotScheduling_r16 : option Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Type ;
    Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16 : option Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Type ;
    Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16 : option Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Type ;
    Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16 : option Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Type ;
    Phy_ParametersCommon__ext3O__codebookVariantsList_r16 : option CodebookVariantsList_r16__Type ;
    Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16 : option Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Type ;
    Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16 : option Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Type ;
    Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16 : option Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Type ;
    Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16 : option Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Type ;
    Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16 : option Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Type ;
    Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16 : option Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Type ;
    Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16 : option Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Type ;
    Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16 : option Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Type ;
    Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16 : option Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type ;
}.
Definition Phy_ParametersCommon__ext3O__list := (
 Opt Phy_ParametersCommon__ext3O__twoStepRACH_r16__Type Phy_ParametersCommon__ext3O__twoStepRACH_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Type Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Type Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Type Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Type Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Type Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Type Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Type Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Type Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Type Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Type Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Type Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Type Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Type Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Type Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Type Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Type Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Type Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Type Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Type Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Type Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__cond ::
 Opt CodebookVariantsList_r16__Type CodebookVariantsList_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Type Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Type Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Type Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Type Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Type Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Type Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Type Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Type Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__cond ::
 Opt Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext3O__cond z := 
  opt_cond Phy_ParametersCommon__ext3O__twoStepRACH_r16__cond (Phy_ParametersCommon__ext3O__twoStepRACH_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__cond (Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__cond (Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__cond (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__cond (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__cond (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__cond (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__cond (Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__cond (Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__cond (Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__cond (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__cond (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__cond (Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__cond (Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__cond (Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__cond (Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__cond (Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__cond (Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__cond (Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__cond (Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16 z) /\
  opt_cond CodebookVariantsList_r16__cond (Phy_ParametersCommon__ext3O__codebookVariantsList_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__cond (Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__cond (Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__cond (Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__cond (Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__cond (Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16 z) /\
  opt_cond Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__cond (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16 z) /\
  True.

Definition Phy_ParametersCommon__ext3__Type := Phy_ParametersCommon__ext3O__Type.
Definition Phy_ParametersCommon__ext3__cond := Phy_ParametersCommon__ext3O__cond.

Inductive Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Type : Set :=
 | Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__supported
.
Definition Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__cond := (fun (_ : Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Type) => True).
Lemma Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__nat__helper.

Definition Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__supported
  | _ => Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__supported
  end.
Lemma Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F1F2 : forall x : Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Type, (Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F2 (Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F1 (Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Type : Set :=
 | Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__supported
.
Definition Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__cond := (fun (_ : Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Type) => True).
Lemma Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__nat__helper.

Definition Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__supported
  | _ => Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__supported
  end.
Lemma Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F1F2 : forall x : Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Type, (Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F2 (Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F1 (Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Type : Set :=
 | Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__supported
.
Definition Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__cond := (fun (_ : Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Type) => True).
Lemma Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__nat__helper.

Definition Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__supported
  | _ => Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__supported
  end.
Lemma Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F1F2 : forall x : Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Type, (Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F2 (Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F1 (Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext4O__Type : Set :=
  make__Phy_ParametersCommon__ext4O__Type {
    Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16 : option Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Type ;
    Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16 : option Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Type ;
    Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16 : option Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Type ;
}.
Definition Phy_ParametersCommon__ext4O__list := (
 Opt Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Type Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__cond ::
 Opt Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Type Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__cond ::
 Opt Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Type Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext4O__cond z := 
  opt_cond Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__cond (Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16 z) /\
  opt_cond Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__cond (Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16 z) /\
  opt_cond Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__cond (Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16 z) /\
  True.

Definition Phy_ParametersCommon__ext4__Type := Phy_ParametersCommon__ext4O__Type.
Definition Phy_ParametersCommon__ext4__cond := Phy_ParametersCommon__ext4O__cond.

Inductive Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Type : Set :=
 | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__us100
 | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__us200
.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__cond := (fun (_ : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Type) => True).
Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__nat__helper.

Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__us100 => 0
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__us200 => 1
  end.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__us100
  | 1 => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__us200
  | _ => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__us100
  end.
Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F1F2 : forall x : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Type, (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F1 x <= 1) /\ Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F2 (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F2F1 : forall (y : nat) (H : y <= 1), Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F1 (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Type : Set :=
 | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us200
 | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us400
 | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us800
 | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us1000
.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__cond := (fun (_ : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Type) => True).
Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__nat__helper.

Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us200 => 0
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us400 => 1
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us800 => 2
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us1000 => 3
  end.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us200
  | 1 => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us400
  | 2 => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us800
  | 3 => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us1000
  | _ => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__us200
  end.
Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F1F2 : forall x : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Type, (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F1 x <= 3) /\ Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F2 (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F2F1 : forall (y : nat) (H : y <= 3), Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F1 (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F2 y) = y. enum_solve H y. Qed.


Inductive Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type : Set :=
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16 : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Type -> Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16 : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Type -> Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type
.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list : list typ := (
typ_cons Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Type Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__cond ::
typ_cons Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Type Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__cond (c : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type) := 
  match c with
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16 t => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__cond t 
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16 t => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__cond t 
  end.

Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__len_helper1 : to_bit_sz (length Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__len_helper2 : 2 <= length2 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list.
 simpl. lia. Qed.
Inductive Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Type : Set :=
 | Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__notSupported
.
Definition Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__cond := (fun (_ : Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Type) => True).
Lemma Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__nat__helper.

Definition Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__notSupported => 0
  end.
Definition Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__notSupported
  | _ => Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__notSupported
  end.
Lemma Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F1F2 : forall x : Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Type, (Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F2 (Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F1 (Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Type : Set :=
 | Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__mode2
 | Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__mode3
.
Definition Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__cond := (fun (_ : Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Type) => True).
Lemma Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__nat__helper.

Definition Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__mode2 => 0
  | Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__mode3 => 1
  end.
Definition Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__mode2
  | 1 => Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__mode3
  | _ => Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__mode2
  end.
Lemma Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F1F2 : forall x : Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Type, (Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F1 x <= 1) /\ Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F2 (Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F2F1 : forall (y : nat) (H : y <= 1), Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F1 (Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext5O__Type : Set :=
  make__Phy_ParametersCommon__ext5O__Type {
    Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16 : option Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type ;
    Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16 : option Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Type ;
    Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16 : option Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Type ;
}.
Definition Phy_ParametersCommon__ext5O__list := (
 Opt Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__cond ::
 Opt Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Type Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__cond ::
 Opt Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Type Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext5O__cond z := 
  opt_cond Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__cond (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16 z) /\
  opt_cond Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__cond (Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16 z) /\
  opt_cond Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__cond (Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16 z) /\
  True.

Definition Phy_ParametersCommon__ext5__Type := Phy_ParametersCommon__ext5O__Type.
Definition Phy_ParametersCommon__ext5__cond := Phy_ParametersCommon__ext5O__cond.

Inductive Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Type : Set :=
 | Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__supported
.
Definition Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__cond := (fun (_ : Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Type) => True).
Lemma Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__nat__helper.

Definition Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__supported
  | _ => Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__supported
  end.
Lemma Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F1F2 : forall x : Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Type, (Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F2 (Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F1 (Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Type : Set :=
 | Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__supported
.
Definition Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__cond := (fun (_ : Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Type) => True).
Lemma Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__nat__helper.

Definition Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__supported
  | _ => Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__supported
  end.
Lemma Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F1F2 : forall x : Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Type, (Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F2 (Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F1 (Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext6O__Type : Set :=
  make__Phy_ParametersCommon__ext6O__Type {
    Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16 : option Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Type ;
    Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16 : option Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Type ;
}.
Definition Phy_ParametersCommon__ext6O__list := (
 Opt Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Type Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__cond ::
 Opt Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Type Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext6O__cond z := 
  opt_cond Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__cond (Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16 z) /\
  opt_cond Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__cond (Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16 z) /\
  True.

Definition Phy_ParametersCommon__ext6__Type := Phy_ParametersCommon__ext6O__Type.
Definition Phy_ParametersCommon__ext6__cond := Phy_ParametersCommon__ext6O__cond.

Inductive Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Type : Set :=
 | Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__supported
.
Definition Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__cond := (fun (_ : Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Type) => True).
Lemma Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__nat__helper.

Definition Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F1 t :=
  match t with
  | Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__supported => 0
  end.
Definition Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__supported
  | _ => Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__supported
  end.
Lemma Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F1F2 : forall x : Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Type, (Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F1 x <= 0) /\ Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F2 (Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F1 (Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext7O__Type : Set :=
  make__Phy_ParametersCommon__ext7O__Type {
    Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16 : option Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Type ;
}.
Definition Phy_ParametersCommon__ext7O__list := (
 Opt Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Type Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__cond ::
 nil).
Definition Phy_ParametersCommon__ext7O__cond z := 
  opt_cond Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__cond (Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16 z) /\
  True.

Definition Phy_ParametersCommon__ext7__Type := Phy_ParametersCommon__ext7O__Type.
Definition Phy_ParametersCommon__ext7__cond := Phy_ParametersCommon__ext7O__cond.

Inductive Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__supported
.
Definition Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__supported
  | _ => Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Type, (Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F2 (Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F1 (Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__supported
.
Definition Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__supported
  | _ => Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Type, (Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F2 (Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F1 (Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__supported
.
Definition Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__supported
  | _ => Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Type, (Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F2 (Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F1 (Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__supported
.
Definition Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__supported
  | _ => Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Type, (Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F2 (Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F1 (Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__supported
.
Definition Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__supported
  | _ => Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Type, (Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F2 (Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F1 (Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__supported
.
Definition Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__supported
  | _ => Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Type, (Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F2 (Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F1 (Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__supported
.
Definition Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__supported
  | _ => Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Type, (Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F2 (Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F1 (Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__supported
.
Definition Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__supported
  | _ => Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Type, (Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F2 (Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F1 (Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__supported
.
Definition Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__supported
  | _ => Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Type, (Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F2 (Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F1 (Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__supported
.
Definition Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__supported
  | _ => Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Type, (Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F2 (Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F1 (Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__supported
.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__supported
  | _ => Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Type, (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F2 (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F1 (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__supported
.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__supported
  | _ => Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Type, (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F2 (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F1 (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Type : Set :=
  make__Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Type {
    Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17 : option Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Type ;
    Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17 : option Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Type ;
}.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list := (
 Opt Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Type Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Type Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__cond ::
 nil).
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond z := 
  opt_cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__cond (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__cond (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17 z) /\
  True.

Lemma Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__Type := Z.
Definition Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__cond := (fun z => (1 <= z <= 4)%Z).
Inductive Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__supported
.
Definition Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__supported
  | _ => Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Type, (Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F2 (Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F1 (Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n2
 | Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n3
 | Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n4
.
Definition Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n2 => 0
  | Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n3 => 1
  | Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n4 => 2
  end.
Definition Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n2
  | 1 => Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n3
  | 2 => Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n4
  | _ => Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__n2
  end.
Lemma Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Type, (Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F1 x <= 2) /\ Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F2 (Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F2F1 : forall (y : nat) (H : y <= 2), Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F1 (Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Type : Set :=
 | Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__supported
.
Definition Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__cond := (fun (_ : Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Type) => True).
Lemma Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__nat__helper.

Definition Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__supported
  | _ => Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__supported
  end.
Lemma Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F1F2 : forall x : Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Type, (Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F2 (Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F1 (Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext8O__Type : Set :=
  make__Phy_ParametersCommon__ext8O__Type {
    Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17 : option Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Type ;
    Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17 : option Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Type ;
    Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17 : option Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Type ;
    Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17 : option Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Type ;
    Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17 : option Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Type ;
    Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17 : option Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Type ;
    Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17 : option Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Type ;
    Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17 : option Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Type ;
    Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17 : option Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Type ;
    Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17 : option Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Type ;
    Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17 : option Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Type ;
    Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17 : option Z ;
    Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17 : option Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Type ;
    Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17 : option Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Type ;
    Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17 : option Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Type ;
}.
Definition Phy_ParametersCommon__ext8O__list := (
 Opt Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Type Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Type Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Type Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Type Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Type Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Type Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Type Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Type Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Type Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Type Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Type Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond ::
 Opt Z Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Type Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Type Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__cond ::
 Opt Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Type Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__cond ::
 nil).
Definition Phy_ParametersCommon__ext8O__cond z := 
  opt_cond Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__cond (Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__cond (Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__cond (Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__cond (Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__cond (Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__cond (Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__cond (Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__cond (Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__cond (Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__cond (Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__cond (Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__cond (Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__cond (Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17 z) /\
  opt_cond Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__cond (Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17 z) /\
  True.

Definition Phy_ParametersCommon__ext8__Type := Phy_ParametersCommon__ext8O__Type.
Definition Phy_ParametersCommon__ext8__cond := Phy_ParametersCommon__ext8O__cond.

Inductive Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Type : Set :=
 | Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__supported
.
Definition Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__cond := (fun (_ : Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Type) => True).
Lemma Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__nat__helper.

Definition Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__supported
  | _ => Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__supported
  end.
Lemma Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F1F2 : forall x : Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Type, (Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F2 (Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F1 (Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Type : Set :=
 | Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__supported
.
Definition Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__cond := (fun (_ : Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Type) => True).
Lemma Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__nat__helper.

Definition Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__supported
  | _ => Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__supported
  end.
Lemma Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F1F2 : forall x : Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Type, (Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F2 (Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F1 (Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext9O__Type : Set :=
  make__Phy_ParametersCommon__ext9O__Type {
    Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17 : option Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Type ;
    Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17 : option Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Type ;
}.
Definition Phy_ParametersCommon__ext9O__list := (
 Opt Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Type Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__cond ::
 Opt Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Type Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__cond ::
 nil).
Definition Phy_ParametersCommon__ext9O__cond z := 
  opt_cond Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__cond (Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17 z) /\
  opt_cond Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__cond (Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17 z) /\
  True.

Definition Phy_ParametersCommon__ext9__Type := Phy_ParametersCommon__ext9O__Type.
Definition Phy_ParametersCommon__ext9__cond := Phy_ParametersCommon__ext9O__cond.

Inductive Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Type : Set :=
 | Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__supported
.
Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__cond := (fun (_ : Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Type) => True).
Lemma Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__nat__helper.

Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__supported
  | _ => Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__supported
  end.
Lemma Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F1F2 : forall x : Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Type, (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F2 (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F1 (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Type : Set :=
 | Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__supported
.
Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__cond := (fun (_ : Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Type) => True).
Lemma Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__nat__helper.

Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__supported
  | _ => Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__supported
  end.
Lemma Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F1F2 : forall x : Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Type, (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F2 (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F1 (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Type : Set :=
 | Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__supported
.
Definition Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__cond := (fun (_ : Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Type) => True).
Lemma Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__nat__helper.

Definition Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__supported
  | _ => Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__supported
  end.
Lemma Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F1F2 : forall x : Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Type, (Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F2 (Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F1 (Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Type : Set :=
 | Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__supported
.
Definition Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__cond := (fun (_ : Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Type) => True).
Lemma Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__nat__helper.

Definition Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__supported
  | _ => Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__supported
  end.
Lemma Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F1F2 : forall x : Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Type, (Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F2 (Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F1 (Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Type : Set :=
 | Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__supported
.
Definition Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__cond := (fun (_ : Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Type) => True).
Lemma Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__nat__helper.

Definition Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__supported
  | _ => Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__supported
  end.
Lemma Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F1F2 : forall x : Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Type, (Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F2 (Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F1 (Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Type : Set :=
 | Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__supported
.
Definition Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__cond := (fun (_ : Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Type) => True).
Lemma Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__nat__helper.

Definition Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F1 t :=
  match t with
  | Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__supported => 0
  end.
Definition Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F2 n :=
  match n with
  | 0 => Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__supported
  | _ => Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__supported
  end.
Lemma Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F1F2 : forall x : Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Type, (Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F1 x <= 0) /\ Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F2 (Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F1 (Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersCommon__ext10O__Type : Set :=
  make__Phy_ParametersCommon__ext10O__Type {
    Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17 : option Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Type ;
    Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17 : option Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Type ;
    Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17 : option Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Type ;
    Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17 : option Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Type ;
    Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17 : option Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Type ;
    Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17 : option Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Type ;
}.
Definition Phy_ParametersCommon__ext10O__list := (
 Opt Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Type Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__cond ::
 Opt Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Type Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__cond ::
 Opt Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Type Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__cond ::
 Opt Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Type Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__cond ::
 Opt Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Type Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__cond ::
 Opt Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Type Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__cond ::
 nil).
Definition Phy_ParametersCommon__ext10O__cond z := 
  opt_cond Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__cond (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17 z) /\
  opt_cond Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__cond (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17 z) /\
  opt_cond Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__cond (Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17 z) /\
  opt_cond Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__cond (Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17 z) /\
  opt_cond Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__cond (Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17 z) /\
  opt_cond Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__cond (Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17 z) /\
  True.

Definition Phy_ParametersCommon__ext10__Type := Phy_ParametersCommon__ext10O__Type.
Definition Phy_ParametersCommon__ext10__cond := Phy_ParametersCommon__ext10O__cond.

Record Phy_ParametersCommon__Type : Set :=
  make__Phy_ParametersCommon__Type {
    Phy_ParametersCommon__csi_RS_CFRA_ForHO : option Phy_ParametersCommon__csi_RS_CFRA_ForHO__Type ;
    Phy_ParametersCommon__dynamicPRB_BundlingDL : option Phy_ParametersCommon__dynamicPRB_BundlingDL__Type ;
    Phy_ParametersCommon__sp_CSI_ReportPUCCH : option Phy_ParametersCommon__sp_CSI_ReportPUCCH__Type ;
    Phy_ParametersCommon__sp_CSI_ReportPUSCH : option Phy_ParametersCommon__sp_CSI_ReportPUSCH__Type ;
    Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt : option Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Type ;
    Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH : option Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Type ;
    Phy_ParametersCommon__precoderGranularityCORESET : option Phy_ParametersCommon__precoderGranularityCORESET__Type ;
    Phy_ParametersCommon__dynamicHARQ_ACK_Codebook : option Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Type ;
    Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook : option Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Type ;
    Phy_ParametersCommon__spatialBundlingHARQ_ACK : option Phy_ParametersCommon__spatialBundlingHARQ_ACK__Type ;
    Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI : option Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Type ;
    Phy_ParametersCommon__pucch_Repetition_F1_3_4 : option Phy_ParametersCommon__pucch_Repetition_F1_3_4__Type ;
    Phy_ParametersCommon__ra_Type0_PUSCH : option Phy_ParametersCommon__ra_Type0_PUSCH__Type ;
    Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH : option Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Type ;
    Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH : option Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Type ;
    Phy_ParametersCommon__pdsch_MappingTypeA : option Phy_ParametersCommon__pdsch_MappingTypeA__Type ;
    Phy_ParametersCommon__pdsch_MappingTypeB : option Phy_ParametersCommon__pdsch_MappingTypeB__Type ;
    Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH : option Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Type ;
    Phy_ParametersCommon__interSlotFreqHopping_PUSCH : option Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Type ;
    Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots : option Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Type ;
    Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots : option Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Type ;
    Phy_ParametersCommon__pusch_RepetitionMultiSlots : option Phy_ParametersCommon__pusch_RepetitionMultiSlots__Type ;
    Phy_ParametersCommon__pdsch_RepetitionMultiSlots : option Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Type ;
    Phy_ParametersCommon__downlinkSPS : option Phy_ParametersCommon__downlinkSPS__Type ;
    Phy_ParametersCommon__configuredUL_GrantType1 : option Phy_ParametersCommon__configuredUL_GrantType1__Type ;
    Phy_ParametersCommon__configuredUL_GrantType2 : option Phy_ParametersCommon__configuredUL_GrantType2__Type ;
    Phy_ParametersCommon__pre_EmptIndication_DL : option Phy_ParametersCommon__pre_EmptIndication_DL__Type ;
    Phy_ParametersCommon__cbg_TransIndication_DL : option Phy_ParametersCommon__cbg_TransIndication_DL__Type ;
    Phy_ParametersCommon__cbg_TransIndication_UL : option Phy_ParametersCommon__cbg_TransIndication_UL__Type ;
    Phy_ParametersCommon__cbg_FlushIndication_DL : option Phy_ParametersCommon__cbg_FlushIndication_DL__Type ;
    Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL : option Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Type ;
    Phy_ParametersCommon__rateMatchingResrcSetSemi_Static : option Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Type ;
    Phy_ParametersCommon__rateMatchingResrcSetDynamic : option Phy_ParametersCommon__rateMatchingResrcSetDynamic__Type ;
    Phy_ParametersCommon__bwp_SwitchingDelay : option Phy_ParametersCommon__bwp_SwitchingDelay__Type ;
    Phy_ParametersCommon__ext0 : option Phy_ParametersCommon__ext0__Type ;
    Phy_ParametersCommon__ext1 : option Phy_ParametersCommon__ext1__Type ;
    Phy_ParametersCommon__ext2 : option Phy_ParametersCommon__ext2__Type ;
    Phy_ParametersCommon__ext3 : option Phy_ParametersCommon__ext3__Type ;
    Phy_ParametersCommon__ext4 : option Phy_ParametersCommon__ext4__Type ;
    Phy_ParametersCommon__ext5 : option Phy_ParametersCommon__ext5__Type ;
    Phy_ParametersCommon__ext6 : option Phy_ParametersCommon__ext6__Type ;
    Phy_ParametersCommon__ext7 : option Phy_ParametersCommon__ext7__Type ;
    Phy_ParametersCommon__ext8 : option Phy_ParametersCommon__ext8__Type ;
    Phy_ParametersCommon__ext9 : option Phy_ParametersCommon__ext9__Type ;
    Phy_ParametersCommon__ext10 : option Phy_ParametersCommon__ext10__Type ;
}.
Definition Phy_ParametersCommon__root_list : list seq_elem := (
 Opt Phy_ParametersCommon__csi_RS_CFRA_ForHO__Type Phy_ParametersCommon__csi_RS_CFRA_ForHO__cond ::
 Opt Phy_ParametersCommon__dynamicPRB_BundlingDL__Type Phy_ParametersCommon__dynamicPRB_BundlingDL__cond ::
 Opt Phy_ParametersCommon__sp_CSI_ReportPUCCH__Type Phy_ParametersCommon__sp_CSI_ReportPUCCH__cond ::
 Opt Phy_ParametersCommon__sp_CSI_ReportPUSCH__Type Phy_ParametersCommon__sp_CSI_ReportPUSCH__cond ::
 Opt Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Type Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__cond ::
 Opt Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Type Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__cond ::
 Opt Phy_ParametersCommon__precoderGranularityCORESET__Type Phy_ParametersCommon__precoderGranularityCORESET__cond ::
 Opt Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Type Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__cond ::
 Opt Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Type Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__cond ::
 Opt Phy_ParametersCommon__spatialBundlingHARQ_ACK__Type Phy_ParametersCommon__spatialBundlingHARQ_ACK__cond ::
 Opt Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Type Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__cond ::
 Opt Phy_ParametersCommon__pucch_Repetition_F1_3_4__Type Phy_ParametersCommon__pucch_Repetition_F1_3_4__cond ::
 Opt Phy_ParametersCommon__ra_Type0_PUSCH__Type Phy_ParametersCommon__ra_Type0_PUSCH__cond ::
 Opt Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Type Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__cond ::
 Opt Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Type Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__cond ::
 Opt Phy_ParametersCommon__pdsch_MappingTypeA__Type Phy_ParametersCommon__pdsch_MappingTypeA__cond ::
 Opt Phy_ParametersCommon__pdsch_MappingTypeB__Type Phy_ParametersCommon__pdsch_MappingTypeB__cond ::
 Opt Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Type Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__cond ::
 Opt Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Type Phy_ParametersCommon__interSlotFreqHopping_PUSCH__cond ::
 Opt Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Type Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__cond ::
 Opt Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Type Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__cond ::
 Opt Phy_ParametersCommon__pusch_RepetitionMultiSlots__Type Phy_ParametersCommon__pusch_RepetitionMultiSlots__cond ::
 Opt Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Type Phy_ParametersCommon__pdsch_RepetitionMultiSlots__cond ::
 Opt Phy_ParametersCommon__downlinkSPS__Type Phy_ParametersCommon__downlinkSPS__cond ::
 Opt Phy_ParametersCommon__configuredUL_GrantType1__Type Phy_ParametersCommon__configuredUL_GrantType1__cond ::
 Opt Phy_ParametersCommon__configuredUL_GrantType2__Type Phy_ParametersCommon__configuredUL_GrantType2__cond ::
 Opt Phy_ParametersCommon__pre_EmptIndication_DL__Type Phy_ParametersCommon__pre_EmptIndication_DL__cond ::
 Opt Phy_ParametersCommon__cbg_TransIndication_DL__Type Phy_ParametersCommon__cbg_TransIndication_DL__cond ::
 Opt Phy_ParametersCommon__cbg_TransIndication_UL__Type Phy_ParametersCommon__cbg_TransIndication_UL__cond ::
 Opt Phy_ParametersCommon__cbg_FlushIndication_DL__Type Phy_ParametersCommon__cbg_FlushIndication_DL__cond ::
 Opt Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Type Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__cond ::
 Opt Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Type Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__cond ::
 Opt Phy_ParametersCommon__rateMatchingResrcSetDynamic__Type Phy_ParametersCommon__rateMatchingResrcSetDynamic__cond ::
 Opt Phy_ParametersCommon__bwp_SwitchingDelay__Type Phy_ParametersCommon__bwp_SwitchingDelay__cond ::
 nil).
Definition Phy_ParametersCommon__ext_list : list typ := (
  typ_cons Phy_ParametersCommon__ext0__Type Phy_ParametersCommon__ext0__cond ::
  typ_cons Phy_ParametersCommon__ext1__Type Phy_ParametersCommon__ext1__cond ::
  typ_cons Phy_ParametersCommon__ext2__Type Phy_ParametersCommon__ext2__cond ::
  typ_cons Phy_ParametersCommon__ext3__Type Phy_ParametersCommon__ext3__cond ::
  typ_cons Phy_ParametersCommon__ext4__Type Phy_ParametersCommon__ext4__cond ::
  typ_cons Phy_ParametersCommon__ext5__Type Phy_ParametersCommon__ext5__cond ::
  typ_cons Phy_ParametersCommon__ext6__Type Phy_ParametersCommon__ext6__cond ::
  typ_cons Phy_ParametersCommon__ext7__Type Phy_ParametersCommon__ext7__cond ::
  typ_cons Phy_ParametersCommon__ext8__Type Phy_ParametersCommon__ext8__cond ::
  typ_cons Phy_ParametersCommon__ext9__Type Phy_ParametersCommon__ext9__cond ::
  typ_cons Phy_ParametersCommon__ext10__Type Phy_ParametersCommon__ext10__cond ::
  nil).
Definition Phy_ParametersCommon__cond (z : Phy_ParametersCommon__Type) := 
(  opt_cond Phy_ParametersCommon__csi_RS_CFRA_ForHO__cond (Phy_ParametersCommon__csi_RS_CFRA_ForHO z) /\
  opt_cond Phy_ParametersCommon__dynamicPRB_BundlingDL__cond (Phy_ParametersCommon__dynamicPRB_BundlingDL z) /\
  opt_cond Phy_ParametersCommon__sp_CSI_ReportPUCCH__cond (Phy_ParametersCommon__sp_CSI_ReportPUCCH z) /\
  opt_cond Phy_ParametersCommon__sp_CSI_ReportPUSCH__cond (Phy_ParametersCommon__sp_CSI_ReportPUSCH z) /\
  opt_cond Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__cond (Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt z) /\
  opt_cond Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__cond (Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH z) /\
  opt_cond Phy_ParametersCommon__precoderGranularityCORESET__cond (Phy_ParametersCommon__precoderGranularityCORESET z) /\
  opt_cond Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__cond (Phy_ParametersCommon__dynamicHARQ_ACK_Codebook z) /\
  opt_cond Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__cond (Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook z) /\
  opt_cond Phy_ParametersCommon__spatialBundlingHARQ_ACK__cond (Phy_ParametersCommon__spatialBundlingHARQ_ACK z) /\
  opt_cond Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__cond (Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI z) /\
  opt_cond Phy_ParametersCommon__pucch_Repetition_F1_3_4__cond (Phy_ParametersCommon__pucch_Repetition_F1_3_4 z) /\
  opt_cond Phy_ParametersCommon__ra_Type0_PUSCH__cond (Phy_ParametersCommon__ra_Type0_PUSCH z) /\
  opt_cond Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__cond (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH z) /\
  opt_cond Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__cond (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH z) /\
  opt_cond Phy_ParametersCommon__pdsch_MappingTypeA__cond (Phy_ParametersCommon__pdsch_MappingTypeA z) /\
  opt_cond Phy_ParametersCommon__pdsch_MappingTypeB__cond (Phy_ParametersCommon__pdsch_MappingTypeB z) /\
  opt_cond Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__cond (Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH z) /\
  opt_cond Phy_ParametersCommon__interSlotFreqHopping_PUSCH__cond (Phy_ParametersCommon__interSlotFreqHopping_PUSCH z) /\
  opt_cond Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__cond (Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots z) /\
  opt_cond Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__cond (Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots z) /\
  opt_cond Phy_ParametersCommon__pusch_RepetitionMultiSlots__cond (Phy_ParametersCommon__pusch_RepetitionMultiSlots z) /\
  opt_cond Phy_ParametersCommon__pdsch_RepetitionMultiSlots__cond (Phy_ParametersCommon__pdsch_RepetitionMultiSlots z) /\
  opt_cond Phy_ParametersCommon__downlinkSPS__cond (Phy_ParametersCommon__downlinkSPS z) /\
  opt_cond Phy_ParametersCommon__configuredUL_GrantType1__cond (Phy_ParametersCommon__configuredUL_GrantType1 z) /\
  opt_cond Phy_ParametersCommon__configuredUL_GrantType2__cond (Phy_ParametersCommon__configuredUL_GrantType2 z) /\
  opt_cond Phy_ParametersCommon__pre_EmptIndication_DL__cond (Phy_ParametersCommon__pre_EmptIndication_DL z) /\
  opt_cond Phy_ParametersCommon__cbg_TransIndication_DL__cond (Phy_ParametersCommon__cbg_TransIndication_DL z) /\
  opt_cond Phy_ParametersCommon__cbg_TransIndication_UL__cond (Phy_ParametersCommon__cbg_TransIndication_UL z) /\
  opt_cond Phy_ParametersCommon__cbg_FlushIndication_DL__cond (Phy_ParametersCommon__cbg_FlushIndication_DL z) /\
  opt_cond Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__cond (Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL z) /\
  opt_cond Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__cond (Phy_ParametersCommon__rateMatchingResrcSetSemi_Static z) /\
  opt_cond Phy_ParametersCommon__rateMatchingResrcSetDynamic__cond (Phy_ParametersCommon__rateMatchingResrcSetDynamic z) /\
  opt_cond Phy_ParametersCommon__bwp_SwitchingDelay__cond (Phy_ParametersCommon__bwp_SwitchingDelay z) /\
  True) /\ 
(  opt_cond Phy_ParametersCommon__ext0__cond (Phy_ParametersCommon__ext0 z) /\
  opt_cond Phy_ParametersCommon__ext1__cond (Phy_ParametersCommon__ext1 z) /\
  opt_cond Phy_ParametersCommon__ext2__cond (Phy_ParametersCommon__ext2 z) /\
  opt_cond Phy_ParametersCommon__ext3__cond (Phy_ParametersCommon__ext3 z) /\
  opt_cond Phy_ParametersCommon__ext4__cond (Phy_ParametersCommon__ext4 z) /\
  opt_cond Phy_ParametersCommon__ext5__cond (Phy_ParametersCommon__ext5 z) /\
  opt_cond Phy_ParametersCommon__ext6__cond (Phy_ParametersCommon__ext6 z) /\
  opt_cond Phy_ParametersCommon__ext7__cond (Phy_ParametersCommon__ext7 z) /\
  opt_cond Phy_ParametersCommon__ext8__cond (Phy_ParametersCommon__ext8 z) /\
  opt_cond Phy_ParametersCommon__ext9__cond (Phy_ParametersCommon__ext9 z) /\
  opt_cond Phy_ParametersCommon__ext10__cond (Phy_ParametersCommon__ext10 z) /\
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
Definition Phy_ParametersCommon__csi_RS_CFRA_ForHO__Format : T_Format Phy_ParametersCommon__csi_RS_CFRA_ForHO__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__csi_RS_CFRA_ForHO__nat__Format Phy_ParametersCommon__csi_RS_CFRA_ForHO__F1 Phy_ParametersCommon__csi_RS_CFRA_ForHO__F2 Phy_ParametersCommon__csi_RS_CFRA_ForHO__F1F2 Phy_ParametersCommon__csi_RS_CFRA_ForHO__F2F1.

Opaque Phy_ParametersCommon__csi_RS_CFRA_ForHO__cond Phy_ParametersCommon__csi_RS_CFRA_ForHO__Format.

Definition Phy_ParametersCommon__dynamicPRB_BundlingDL__Format : T_Format Phy_ParametersCommon__dynamicPRB_BundlingDL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__dynamicPRB_BundlingDL__nat__Format Phy_ParametersCommon__dynamicPRB_BundlingDL__F1 Phy_ParametersCommon__dynamicPRB_BundlingDL__F2 Phy_ParametersCommon__dynamicPRB_BundlingDL__F1F2 Phy_ParametersCommon__dynamicPRB_BundlingDL__F2F1.

Opaque Phy_ParametersCommon__dynamicPRB_BundlingDL__cond Phy_ParametersCommon__dynamicPRB_BundlingDL__Format.

Definition Phy_ParametersCommon__sp_CSI_ReportPUCCH__Format : T_Format Phy_ParametersCommon__sp_CSI_ReportPUCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__sp_CSI_ReportPUCCH__nat__Format Phy_ParametersCommon__sp_CSI_ReportPUCCH__F1 Phy_ParametersCommon__sp_CSI_ReportPUCCH__F2 Phy_ParametersCommon__sp_CSI_ReportPUCCH__F1F2 Phy_ParametersCommon__sp_CSI_ReportPUCCH__F2F1.

Opaque Phy_ParametersCommon__sp_CSI_ReportPUCCH__cond Phy_ParametersCommon__sp_CSI_ReportPUCCH__Format.

Definition Phy_ParametersCommon__sp_CSI_ReportPUSCH__Format : T_Format Phy_ParametersCommon__sp_CSI_ReportPUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__sp_CSI_ReportPUSCH__nat__Format Phy_ParametersCommon__sp_CSI_ReportPUSCH__F1 Phy_ParametersCommon__sp_CSI_ReportPUSCH__F2 Phy_ParametersCommon__sp_CSI_ReportPUSCH__F1F2 Phy_ParametersCommon__sp_CSI_ReportPUSCH__F2F1.

Opaque Phy_ParametersCommon__sp_CSI_ReportPUSCH__cond Phy_ParametersCommon__sp_CSI_ReportPUSCH__Format.

Definition Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Format : T_Format Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__nat__Format Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F1 Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F2 Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F1F2 Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__F2F1.

Opaque Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__cond Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Format.

Definition Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Format : T_Format Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__nat__Format Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F1 Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F2 Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F1F2 Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__F2F1.

Opaque Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__cond Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Format.

Definition Phy_ParametersCommon__precoderGranularityCORESET__Format : T_Format Phy_ParametersCommon__precoderGranularityCORESET__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__precoderGranularityCORESET__nat__Format Phy_ParametersCommon__precoderGranularityCORESET__F1 Phy_ParametersCommon__precoderGranularityCORESET__F2 Phy_ParametersCommon__precoderGranularityCORESET__F1F2 Phy_ParametersCommon__precoderGranularityCORESET__F2F1.

Opaque Phy_ParametersCommon__precoderGranularityCORESET__cond Phy_ParametersCommon__precoderGranularityCORESET__Format.

Definition Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Format : T_Format Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__nat__Format Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F1 Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F2 Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F1F2 Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__F2F1.

Opaque Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__cond Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Format.

Definition Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Format : T_Format Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__nat__Format Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F1 Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F2 Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F1F2 Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__F2F1.

Opaque Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__cond Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Format.

Definition Phy_ParametersCommon__spatialBundlingHARQ_ACK__Format : T_Format Phy_ParametersCommon__spatialBundlingHARQ_ACK__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__spatialBundlingHARQ_ACK__nat__Format Phy_ParametersCommon__spatialBundlingHARQ_ACK__F1 Phy_ParametersCommon__spatialBundlingHARQ_ACK__F2 Phy_ParametersCommon__spatialBundlingHARQ_ACK__F1F2 Phy_ParametersCommon__spatialBundlingHARQ_ACK__F2F1.

Opaque Phy_ParametersCommon__spatialBundlingHARQ_ACK__cond Phy_ParametersCommon__spatialBundlingHARQ_ACK__Format.

Definition Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Format : T_Format Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__nat__Format Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F1 Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F2 Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F1F2 Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__F2F1.

Opaque Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__cond Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Format.

Definition Phy_ParametersCommon__pucch_Repetition_F1_3_4__Format : T_Format Phy_ParametersCommon__pucch_Repetition_F1_3_4__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__pucch_Repetition_F1_3_4__nat__Format Phy_ParametersCommon__pucch_Repetition_F1_3_4__F1 Phy_ParametersCommon__pucch_Repetition_F1_3_4__F2 Phy_ParametersCommon__pucch_Repetition_F1_3_4__F1F2 Phy_ParametersCommon__pucch_Repetition_F1_3_4__F2F1.

Opaque Phy_ParametersCommon__pucch_Repetition_F1_3_4__cond Phy_ParametersCommon__pucch_Repetition_F1_3_4__Format.

Definition Phy_ParametersCommon__ra_Type0_PUSCH__Format : T_Format Phy_ParametersCommon__ra_Type0_PUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ra_Type0_PUSCH__nat__Format Phy_ParametersCommon__ra_Type0_PUSCH__F1 Phy_ParametersCommon__ra_Type0_PUSCH__F2 Phy_ParametersCommon__ra_Type0_PUSCH__F1F2 Phy_ParametersCommon__ra_Type0_PUSCH__F2F1.

Opaque Phy_ParametersCommon__ra_Type0_PUSCH__cond Phy_ParametersCommon__ra_Type0_PUSCH__Format.

Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Format : T_Format Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__nat__Format Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F1 Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F2 Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F1F2 Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__F2F1.

Opaque Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__cond Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Format.

Definition Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Format : T_Format Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__nat__Format Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F1 Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F2 Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F1F2 Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__F2F1.

Opaque Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__cond Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Format.

Definition Phy_ParametersCommon__pdsch_MappingTypeA__Format : T_Format Phy_ParametersCommon__pdsch_MappingTypeA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__pdsch_MappingTypeA__nat__Format Phy_ParametersCommon__pdsch_MappingTypeA__F1 Phy_ParametersCommon__pdsch_MappingTypeA__F2 Phy_ParametersCommon__pdsch_MappingTypeA__F1F2 Phy_ParametersCommon__pdsch_MappingTypeA__F2F1.

Opaque Phy_ParametersCommon__pdsch_MappingTypeA__cond Phy_ParametersCommon__pdsch_MappingTypeA__Format.

Definition Phy_ParametersCommon__pdsch_MappingTypeB__Format : T_Format Phy_ParametersCommon__pdsch_MappingTypeB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__pdsch_MappingTypeB__nat__Format Phy_ParametersCommon__pdsch_MappingTypeB__F1 Phy_ParametersCommon__pdsch_MappingTypeB__F2 Phy_ParametersCommon__pdsch_MappingTypeB__F1F2 Phy_ParametersCommon__pdsch_MappingTypeB__F2F1.

Opaque Phy_ParametersCommon__pdsch_MappingTypeB__cond Phy_ParametersCommon__pdsch_MappingTypeB__Format.

Definition Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Format : T_Format Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__nat__Format Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F1 Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F2 Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F1F2 Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__F2F1.

Opaque Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__cond Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Format.

Definition Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Format : T_Format Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__interSlotFreqHopping_PUSCH__nat__Format Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F1 Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F2 Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F1F2 Phy_ParametersCommon__interSlotFreqHopping_PUSCH__F2F1.

Opaque Phy_ParametersCommon__interSlotFreqHopping_PUSCH__cond Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Format.

Definition Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Format : T_Format Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__nat__Format Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F1 Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F2 Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F1F2 Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__F2F1.

Opaque Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__cond Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Format.

Definition Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Format : T_Format Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__nat__Format Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F1 Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F2 Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F1F2 Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__F2F1.

Opaque Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__cond Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Format.

Definition Phy_ParametersCommon__pusch_RepetitionMultiSlots__Format : T_Format Phy_ParametersCommon__pusch_RepetitionMultiSlots__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__pusch_RepetitionMultiSlots__nat__Format Phy_ParametersCommon__pusch_RepetitionMultiSlots__F1 Phy_ParametersCommon__pusch_RepetitionMultiSlots__F2 Phy_ParametersCommon__pusch_RepetitionMultiSlots__F1F2 Phy_ParametersCommon__pusch_RepetitionMultiSlots__F2F1.

Opaque Phy_ParametersCommon__pusch_RepetitionMultiSlots__cond Phy_ParametersCommon__pusch_RepetitionMultiSlots__Format.

Definition Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Format : T_Format Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__pdsch_RepetitionMultiSlots__nat__Format Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F1 Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F2 Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F1F2 Phy_ParametersCommon__pdsch_RepetitionMultiSlots__F2F1.

Opaque Phy_ParametersCommon__pdsch_RepetitionMultiSlots__cond Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Format.

Definition Phy_ParametersCommon__downlinkSPS__Format : T_Format Phy_ParametersCommon__downlinkSPS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__downlinkSPS__nat__Format Phy_ParametersCommon__downlinkSPS__F1 Phy_ParametersCommon__downlinkSPS__F2 Phy_ParametersCommon__downlinkSPS__F1F2 Phy_ParametersCommon__downlinkSPS__F2F1.

Opaque Phy_ParametersCommon__downlinkSPS__cond Phy_ParametersCommon__downlinkSPS__Format.

Definition Phy_ParametersCommon__configuredUL_GrantType1__Format : T_Format Phy_ParametersCommon__configuredUL_GrantType1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__configuredUL_GrantType1__nat__Format Phy_ParametersCommon__configuredUL_GrantType1__F1 Phy_ParametersCommon__configuredUL_GrantType1__F2 Phy_ParametersCommon__configuredUL_GrantType1__F1F2 Phy_ParametersCommon__configuredUL_GrantType1__F2F1.

Opaque Phy_ParametersCommon__configuredUL_GrantType1__cond Phy_ParametersCommon__configuredUL_GrantType1__Format.

Definition Phy_ParametersCommon__configuredUL_GrantType2__Format : T_Format Phy_ParametersCommon__configuredUL_GrantType2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__configuredUL_GrantType2__nat__Format Phy_ParametersCommon__configuredUL_GrantType2__F1 Phy_ParametersCommon__configuredUL_GrantType2__F2 Phy_ParametersCommon__configuredUL_GrantType2__F1F2 Phy_ParametersCommon__configuredUL_GrantType2__F2F1.

Opaque Phy_ParametersCommon__configuredUL_GrantType2__cond Phy_ParametersCommon__configuredUL_GrantType2__Format.

Definition Phy_ParametersCommon__pre_EmptIndication_DL__Format : T_Format Phy_ParametersCommon__pre_EmptIndication_DL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__pre_EmptIndication_DL__nat__Format Phy_ParametersCommon__pre_EmptIndication_DL__F1 Phy_ParametersCommon__pre_EmptIndication_DL__F2 Phy_ParametersCommon__pre_EmptIndication_DL__F1F2 Phy_ParametersCommon__pre_EmptIndication_DL__F2F1.

Opaque Phy_ParametersCommon__pre_EmptIndication_DL__cond Phy_ParametersCommon__pre_EmptIndication_DL__Format.

Definition Phy_ParametersCommon__cbg_TransIndication_DL__Format : T_Format Phy_ParametersCommon__cbg_TransIndication_DL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__cbg_TransIndication_DL__nat__Format Phy_ParametersCommon__cbg_TransIndication_DL__F1 Phy_ParametersCommon__cbg_TransIndication_DL__F2 Phy_ParametersCommon__cbg_TransIndication_DL__F1F2 Phy_ParametersCommon__cbg_TransIndication_DL__F2F1.

Opaque Phy_ParametersCommon__cbg_TransIndication_DL__cond Phy_ParametersCommon__cbg_TransIndication_DL__Format.

Definition Phy_ParametersCommon__cbg_TransIndication_UL__Format : T_Format Phy_ParametersCommon__cbg_TransIndication_UL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__cbg_TransIndication_UL__nat__Format Phy_ParametersCommon__cbg_TransIndication_UL__F1 Phy_ParametersCommon__cbg_TransIndication_UL__F2 Phy_ParametersCommon__cbg_TransIndication_UL__F1F2 Phy_ParametersCommon__cbg_TransIndication_UL__F2F1.

Opaque Phy_ParametersCommon__cbg_TransIndication_UL__cond Phy_ParametersCommon__cbg_TransIndication_UL__Format.

Definition Phy_ParametersCommon__cbg_FlushIndication_DL__Format : T_Format Phy_ParametersCommon__cbg_FlushIndication_DL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__cbg_FlushIndication_DL__nat__Format Phy_ParametersCommon__cbg_FlushIndication_DL__F1 Phy_ParametersCommon__cbg_FlushIndication_DL__F2 Phy_ParametersCommon__cbg_FlushIndication_DL__F1F2 Phy_ParametersCommon__cbg_FlushIndication_DL__F2F1.

Opaque Phy_ParametersCommon__cbg_FlushIndication_DL__cond Phy_ParametersCommon__cbg_FlushIndication_DL__Format.

Definition Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Format : T_Format Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__nat__Format Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F1 Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F2 Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F1F2 Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__F2F1.

Opaque Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__cond Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Format.

Definition Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Format : T_Format Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__nat__Format Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F1 Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F2 Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F1F2 Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__F2F1.

Opaque Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__cond Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Format.

Definition Phy_ParametersCommon__rateMatchingResrcSetDynamic__Format : T_Format Phy_ParametersCommon__rateMatchingResrcSetDynamic__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__rateMatchingResrcSetDynamic__nat__Format Phy_ParametersCommon__rateMatchingResrcSetDynamic__F1 Phy_ParametersCommon__rateMatchingResrcSetDynamic__F2 Phy_ParametersCommon__rateMatchingResrcSetDynamic__F1F2 Phy_ParametersCommon__rateMatchingResrcSetDynamic__F2F1.

Opaque Phy_ParametersCommon__rateMatchingResrcSetDynamic__cond Phy_ParametersCommon__rateMatchingResrcSetDynamic__Format.

Definition Phy_ParametersCommon__bwp_SwitchingDelay__Format : T_Format Phy_ParametersCommon__bwp_SwitchingDelay__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__bwp_SwitchingDelay__nat__Format Phy_ParametersCommon__bwp_SwitchingDelay__F1 Phy_ParametersCommon__bwp_SwitchingDelay__F2 Phy_ParametersCommon__bwp_SwitchingDelay__F1F2 Phy_ParametersCommon__bwp_SwitchingDelay__F2F1.

Opaque Phy_ParametersCommon__bwp_SwitchingDelay__cond Phy_ParametersCommon__bwp_SwitchingDelay__Format.

Definition Phy_ParametersCommon__ext0O__dummy__Format : T_Format Phy_ParametersCommon__ext0O__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext0O__dummy__nat__Format Phy_ParametersCommon__ext0O__dummy__F1 Phy_ParametersCommon__ext0O__dummy__F2 Phy_ParametersCommon__ext0O__dummy__F1F2 Phy_ParametersCommon__ext0O__dummy__F2F1.

Opaque Phy_ParametersCommon__ext0O__dummy__cond Phy_ParametersCommon__ext0O__dummy__Format.


Definition Phy_ParametersCommon__ext0O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext0O__list.
Definition Phy_ParametersCommon__ext0O__Format_list : Phy_ParametersCommon__ext0O__Format_Type :=
  (Phy_ParametersCommon__ext0O__dummy__Format, unit_format).
Definition Phy_ParametersCommon__ext0O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext0O__list Phy_ParametersCommon__ext0O__Format_list.
Definition Phy_ParametersCommon__ext0O__F1 z :=
  (Phy_ParametersCommon__ext0O__dummy z, tt).
Definition Phy_ParametersCommon__ext0O__F2 (y : seq_type Phy_ParametersCommon__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersCommon__ext0O__Type i0
  end.
Lemma Phy_ParametersCommon__ext0O__F1F2_cond (z : Phy_ParametersCommon__ext0O__Type)
  : Phy_ParametersCommon__ext0O__cond z ->
  (seq_cond Phy_ParametersCommon__ext0O__list (Phy_ParametersCommon__ext0O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext0O__F1F2_cond2 (z : Phy_ParametersCommon__ext0O__Type)
 : Phy_ParametersCommon__ext0O__F2 (Phy_ParametersCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext0O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext0O__list)
  : seq_cond Phy_ParametersCommon__ext0O__list y ->
 (Phy_ParametersCommon__ext0O__cond (Phy_ParametersCommon__ext0O__F2 y)) /\  Phy_ParametersCommon__ext0O__F1 (Phy_ParametersCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext0O__Format : T_Format Phy_ParametersCommon__ext0O__Type Phy_ParametersCommon__ext0O__cond :=
        proj2_format  Phy_ParametersCommon__ext0O__cond Phy_ParametersCommon__ext0O__list__Format
    Phy_ParametersCommon__ext0O__F1 Phy_ParametersCommon__ext0O__F2 Phy_ParametersCommon__ext0O__F1F2_cond  Phy_ParametersCommon__ext0O__F1F2_cond2 Phy_ParametersCommon__ext0O__F2F1_cond.
Opaque Phy_ParametersCommon__ext0O__cond Phy_ParametersCommon__ext0O__Format.

Definition Phy_ParametersCommon__ext0__check_all_none (b : Phy_ParametersCommon__ext0O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext0O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext0__Format : T_Format Phy_ParametersCommon__ext0__Type Phy_ParametersCommon__ext0__cond :=
  restrict_add_format Phy_ParametersCommon__ext0__check_all_none Phy_ParametersCommon__ext0O__Format.

Opaque Phy_ParametersCommon__ext0__cond Phy_ParametersCommon__ext0__Format.

Definition Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Format : T_Format Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__nat__Format Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F1 Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F2 Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F1F2 Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__F2F1.

Opaque Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__cond Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Format.

Definition Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Format : T_Format Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__nat__Format Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F1 Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F2 Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F1F2 Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__F2F1.

Opaque Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__cond Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Format.

Definition Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Format : T_Format Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__nat__Format Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F1 Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F2 Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F1F2 Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__F2F1.

Opaque Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__cond Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Format.


Definition Phy_ParametersCommon__ext1O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext1O__list.
Definition Phy_ParametersCommon__ext1O__Format_list : Phy_ParametersCommon__ext1O__Format_Type :=
  (Phy_ParametersCommon__ext1O__maxNumberSearchSpaces__Format, (Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic__Format, (Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication__Format, unit_format))).
Definition Phy_ParametersCommon__ext1O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext1O__list Phy_ParametersCommon__ext1O__Format_list.
Definition Phy_ParametersCommon__ext1O__F1 z :=
  (Phy_ParametersCommon__ext1O__maxNumberSearchSpaces z, (Phy_ParametersCommon__ext1O__rateMatchingCtrlResrcSetDynamic z, (Phy_ParametersCommon__ext1O__maxLayersMIMO_Indication z, tt))).
Definition Phy_ParametersCommon__ext1O__F2 (y : seq_type Phy_ParametersCommon__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__Phy_ParametersCommon__ext1O__Type i0 i1 i2
  end.
Lemma Phy_ParametersCommon__ext1O__F1F2_cond (z : Phy_ParametersCommon__ext1O__Type)
  : Phy_ParametersCommon__ext1O__cond z ->
  (seq_cond Phy_ParametersCommon__ext1O__list (Phy_ParametersCommon__ext1O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext1O__F1F2_cond2 (z : Phy_ParametersCommon__ext1O__Type)
 : Phy_ParametersCommon__ext1O__F2 (Phy_ParametersCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext1O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext1O__list)
  : seq_cond Phy_ParametersCommon__ext1O__list y ->
 (Phy_ParametersCommon__ext1O__cond (Phy_ParametersCommon__ext1O__F2 y)) /\  Phy_ParametersCommon__ext1O__F1 (Phy_ParametersCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext1O__Format : T_Format Phy_ParametersCommon__ext1O__Type Phy_ParametersCommon__ext1O__cond :=
        proj2_format  Phy_ParametersCommon__ext1O__cond Phy_ParametersCommon__ext1O__list__Format
    Phy_ParametersCommon__ext1O__F1 Phy_ParametersCommon__ext1O__F2 Phy_ParametersCommon__ext1O__F1F2_cond  Phy_ParametersCommon__ext1O__F1F2_cond2 Phy_ParametersCommon__ext1O__F2F1_cond.
Opaque Phy_ParametersCommon__ext1O__cond Phy_ParametersCommon__ext1O__Format.

Definition Phy_ParametersCommon__ext1__check_all_none (b : Phy_ParametersCommon__ext1O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext1O__Type None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext1__Format : T_Format Phy_ParametersCommon__ext1__Type Phy_ParametersCommon__ext1__cond :=
  restrict_add_format Phy_ParametersCommon__ext1__check_all_none Phy_ParametersCommon__ext1O__Format.

Opaque Phy_ParametersCommon__ext1__cond Phy_ParametersCommon__ext1__Format.


Definition Phy_ParametersCommon__ext2O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext2O__list.
Definition Phy_ParametersCommon__ext2O__Format_list : Phy_ParametersCommon__ext2O__Format_Type :=
  (CarrierAggregationVariant__Format, unit_format).
Definition Phy_ParametersCommon__ext2O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext2O__list Phy_ParametersCommon__ext2O__Format_list.
Definition Phy_ParametersCommon__ext2O__F1 z :=
  (Phy_ParametersCommon__ext2O__spCellPlacement z, tt).
Definition Phy_ParametersCommon__ext2O__F2 (y : seq_type Phy_ParametersCommon__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersCommon__ext2O__Type i0
  end.
Lemma Phy_ParametersCommon__ext2O__F1F2_cond (z : Phy_ParametersCommon__ext2O__Type)
  : Phy_ParametersCommon__ext2O__cond z ->
  (seq_cond Phy_ParametersCommon__ext2O__list (Phy_ParametersCommon__ext2O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext2O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext2O__F1F2_cond2 (z : Phy_ParametersCommon__ext2O__Type)
 : Phy_ParametersCommon__ext2O__F2 (Phy_ParametersCommon__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext2O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext2O__list)
  : seq_cond Phy_ParametersCommon__ext2O__list y ->
 (Phy_ParametersCommon__ext2O__cond (Phy_ParametersCommon__ext2O__F2 y)) /\  Phy_ParametersCommon__ext2O__F1 (Phy_ParametersCommon__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext2O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext2O__Format : T_Format Phy_ParametersCommon__ext2O__Type Phy_ParametersCommon__ext2O__cond :=
        proj2_format  Phy_ParametersCommon__ext2O__cond Phy_ParametersCommon__ext2O__list__Format
    Phy_ParametersCommon__ext2O__F1 Phy_ParametersCommon__ext2O__F2 Phy_ParametersCommon__ext2O__F1F2_cond  Phy_ParametersCommon__ext2O__F1F2_cond2 Phy_ParametersCommon__ext2O__F2F1_cond.
Opaque Phy_ParametersCommon__ext2O__cond Phy_ParametersCommon__ext2O__Format.

Definition Phy_ParametersCommon__ext2__check_all_none (b : Phy_ParametersCommon__ext2O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext2O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext2__Format : T_Format Phy_ParametersCommon__ext2__Type Phy_ParametersCommon__ext2__cond :=
  restrict_add_format Phy_ParametersCommon__ext2__check_all_none Phy_ParametersCommon__ext2O__Format.

Opaque Phy_ParametersCommon__ext2__cond Phy_ParametersCommon__ext2__Format.

Definition Phy_ParametersCommon__ext3O__twoStepRACH_r16__Format : T_Format Phy_ParametersCommon__ext3O__twoStepRACH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__twoStepRACH_r16__nat__Format Phy_ParametersCommon__ext3O__twoStepRACH_r16__F1 Phy_ParametersCommon__ext3O__twoStepRACH_r16__F2 Phy_ParametersCommon__ext3O__twoStepRACH_r16__F1F2 Phy_ParametersCommon__ext3O__twoStepRACH_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__twoStepRACH_r16__cond Phy_ParametersCommon__ext3O__twoStepRACH_r16__Format.

Definition Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Format : T_Format Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__nat__Format Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F1 Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F2 Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F1F2 Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__cond Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Format.

Definition Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Format : T_Format Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__nat__Format Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F1 Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F2 Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F1F2 Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__cond Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Format.

Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Format : T_Format Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__nat__Format Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F1 Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F2 Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F1F2 Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__cond Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Format.

Definition Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Format : T_Format Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__nat__Format Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F1 Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F2 Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F1F2 Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__cond Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Format.

Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Format : T_Format Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__nat__Format Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F1 Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F2 Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F1F2 Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__cond Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Format.

Definition Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Format : T_Format Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__nat__Format Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F1 Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F2 Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F1F2 Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__cond Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Format.

Definition Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Format : T_Format Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__nat__Format Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F1 Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F2 Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F1F2 Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__cond Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Format.

Definition Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Format : T_Format Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__nat__Format Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F1 Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F2 Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F1F2 Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__cond Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Format.

Definition Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Format : T_Format Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__nat__Format Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F1 Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F2 Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F1F2 Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__cond Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Format.

Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Format : T_Format Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__nat__Format Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F1 Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F2 Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F1F2 Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__cond Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Format.

Definition Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Format : T_Format Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__nat__Format Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F1 Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F2 Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F1F2 Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__cond Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Format.

Definition Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Format : T_Format Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__nat__Format Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F1 Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F2 Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F1F2 Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__cond Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Format.

Definition Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Format : T_Format Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__nat__Format Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F1 Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F2 Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F1F2 Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__cond Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Format.

Definition Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Format : T_Format Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__nat__Format Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F1 Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F2 Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F1F2 Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__cond Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Format.

Definition Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Format : T_Format Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__nat__Format Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F1 Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F2 Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F1F2 Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__cond Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Format.

Definition Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Format : T_Format Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__nat__Format Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F1 Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F2 Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F1F2 Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__cond Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Format.

Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Format : T_Format Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__nat__Format Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F1 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F2 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F1F2 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Format.

Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Format : T_Format Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__nat__Format Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F1 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F2 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F1F2 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Format.


Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Format_list : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Format_Type :=
  (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16__Format, (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16__Format, unit_format)).
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Format_list.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1 z :=
  (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__non_SharedSpectrumChAccess_r16 z, (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__sharedSpectrumChAccess_r16 z, tt)).
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F2 (y : seq_type Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Type i0 i1
  end.
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1F2_cond (z : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Type)
  : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond z ->
  (seq_cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1 z)).
intro H. unfold Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1F2_cond2 (z : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Type)
 : Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F2 (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F2F1_cond (y : seq_type Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list)
  : seq_cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list y ->
 (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F2 y)) /\  Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1 (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Format : T_Format Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Type Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond :=
        proj2_format  Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__list__Format
    Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F2 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1F2_cond  Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F1F2_cond2 Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__F2F1_cond.
Opaque Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__cond Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Format.

Definition Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Format : T_Format Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__nat__Format Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F1 Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F2 Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F1F2 Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__cond Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Format.

Definition Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Format : T_Format Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__nat__Format Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F1 Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F2 Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F1F2 Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__cond Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Format.

Definition Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Format : T_Format Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__nat__Format Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F1 Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F2 Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F1F2 Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__cond Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Format.

Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Format : T_Format Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__nat__Format Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F1 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F2 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F1F2 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Format.

Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Format : T_Format Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__nat__Format Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F1 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F2 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F1F2 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Format.


Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Format_list : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Format_Type :=
  (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16__Format, (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16__Format, unit_format)).
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Format_list.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1 z :=
  (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__sharedSpectrumChAccess_r16 z, (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__non_SharedSpectrumChAccess_r16 z, tt)).
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F2 (y : seq_type Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Type i0 i1
  end.
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1F2_cond (z : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Type)
  : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond z ->
  (seq_cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1 z)).
intro H. unfold Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1F2_cond2 (z : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Type)
 : Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F2 (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F2F1_cond (y : seq_type Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list)
  : seq_cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list y ->
 (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F2 y)) /\  Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1 (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Format : T_Format Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Type Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond :=
        proj2_format  Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__list__Format
    Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F2 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1F2_cond  Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F1F2_cond2 Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__F2F1_cond.
Opaque Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__cond Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Format.

Definition Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Format : T_Format Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__nat__Format Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F1 Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F2 Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F1F2 Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__cond Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Format.

Definition Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Format : T_Format Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__nat__Format Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F1 Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F2 Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F1F2 Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__cond Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Format.

Definition Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Format : T_Format Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__nat__Format Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F1 Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F2 Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F1F2 Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__cond Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Format.

Definition Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Format : T_Format Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__nat__Format Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F1 Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F2 Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F1F2 Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__cond Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Format.

Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Format : T_Format Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__nat__Format Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F1 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F2 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F1F2 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Format.

Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Format : T_Format Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__nat__Format Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F1 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F2 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F1F2 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Format.


Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Format_list : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Format_Type :=
  (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16__Format, (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16__Format, unit_format)).
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Format_list.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1 z :=
  (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResWithinSlotAcrossCC_AcrossFR_r16 z, (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__maxNumberResAcrossCC_AcrossFR_r16 z, tt)).
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F2 (y : seq_type Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Type i0 i1
  end.
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1F2_cond (z : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Type)
  : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond z ->
  (seq_cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1 z)).
intro H. unfold Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1F2_cond2 (z : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Type)
 : Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F2 (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F2F1_cond (y : seq_type Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list)
  : seq_cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list y ->
 (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F2 y)) /\  Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1 (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Format : T_Format Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Type Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond :=
        proj2_format  Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__list__Format
    Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F2 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1F2_cond  Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F1F2_cond2 Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__F2F1_cond.
Opaque Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__cond Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Format.

Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Format : T_Format Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__nat__Format Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F1 Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F2 Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F1F2 Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__cond Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Format.


Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list.
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Format_list : Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Format_Type :=
  (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16__Format, unit_format).
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Format_list.
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1 z :=
  (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__maxNumberLongPUCCHs_r16 z, tt).
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F2 (y : seq_type Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Type i0
  end.
Lemma Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1F2_cond (z : Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Type)
  : Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond z ->
  (seq_cond Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1 z)).
intro H. unfold Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1F2_cond2 (z : Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Type)
 : Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F2 (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F2F1_cond (y : seq_type Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list)
  : seq_cond Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list y ->
 (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F2 y)) /\  Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1 (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Format : T_Format Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Type Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond :=
        proj2_format  Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__list__Format
    Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1 Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F2 Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1F2_cond  Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F1F2_cond2 Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__F2F1_cond.
Opaque Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__cond Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Format.

Definition Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Format : T_Format Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__nat__Format Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F1 Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F2 Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F1F2 Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__cond Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Format.

Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Format : T_Format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__nat__Format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F1 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F2 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F1F2 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__cond Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Format.

Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Format : T_Format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__nat__Format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F1 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F2 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F1F2 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__F2F1.

Opaque Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__cond Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Format.


Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Format_Type := Eval cbn in get_formats Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Format_list : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Format_Type :=
  (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Format, (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Format, unit__Format)).
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list__Format := Eval compute in choice_format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__len_helper1 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__len_helper2  Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Format_list.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F1 (z : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type) : (choice Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list) :=
  match z with
   | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16 t => existT _ 0 t
  | Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16 t => existT _ 1 t
  end.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__g := (fun n => typ_set (get_nth_typ Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list n)).
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F2 (y : choice Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list) : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__g n -> Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type) with
    | 0 => fun (t : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16__Type) => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type1_r16 t 
    | 1 => fun (t : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16__Type) => Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__type2_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type with end) n0
           end t0).

Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__helper2 :  forall (y : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type), Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__cond y -> choice_cond Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__helper3 :  forall (y : Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type), Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F2 (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__helper4 : (forall b : choice Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list, choice_cond Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list b -> Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__cond (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F2 b) /\ Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F1 (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F1 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F2.
Definition Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Format : T_Format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Type Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__cond :=
  (* Eval compute in *) proj2_format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__cond Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__list__Format Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F1 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__F2 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__helper2 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__helper3 Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__helper4.
Opaque Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__cond Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Format.


Definition Phy_ParametersCommon__ext3O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext3O__list.
Definition Phy_ParametersCommon__ext3O__Format_list : Phy_ParametersCommon__ext3O__Format_Type :=
  (Phy_ParametersCommon__ext3O__twoStepRACH_r16__Format, (Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16__Format, (Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16__Format, (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16__Format, (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16__Format, (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16__Format, (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16__Format, (Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16__Format, (Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16__Format, (Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16__Format, (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16__Format, (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16__Format, (Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16__Format, (Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16__Format, (Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16__Format, (Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16__Format, (Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16__Format, (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16__Format, (Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16__Format, (Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16__Format, (Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16__Format, (CodebookVariantsList_r16__Format, (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16__Format, (Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16__Format, (Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16__Format, (Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16__Format, (Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16__Format, (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16__Format, (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16__Format, (Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16__Format, (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16__Format, unit_format))))))))))))))))))))))))))))))).
Definition Phy_ParametersCommon__ext3O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext3O__list Phy_ParametersCommon__ext3O__Format_list.
Definition Phy_ParametersCommon__ext3O__F1 z :=
  (Phy_ParametersCommon__ext3O__twoStepRACH_r16 z, (Phy_ParametersCommon__ext3O__dci_Format1_2And0_2_r16 z, (Phy_ParametersCommon__ext3O__monitoringDCI_SameSearchSpace_r16 z, (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_1_r16 z, (Phy_ParametersCommon__ext3O__type2_CG_ReleaseDCI_0_2_r16 z, (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_1_r16 z, (Phy_ParametersCommon__ext3O__sps_ReleaseDCI_1_2_r16 z, (Phy_ParametersCommon__ext3O__csi_TriggerStateNon_ActiveBWP_r16 z, (Phy_ParametersCommon__ext3O__separateSMTC_InterIAB_Support_r16 z, (Phy_ParametersCommon__ext3O__separateRACH_IAB_Support_r16 z, (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatSemiStatic_IAB_r16 z, (Phy_ParametersCommon__ext3O__ul_flexibleDL_SlotFormatDynamics_IAB_r16 z, (Phy_ParametersCommon__ext3O__dft_S_OFDM_WaveformUL_IAB_r16 z, (Phy_ParametersCommon__ext3O__dci_25_AI_RNTI_Support_IAB_r16 z, (Phy_ParametersCommon__ext3O__t_DeltaReceptionSupport_IAB_r16 z, (Phy_ParametersCommon__ext3O__guardSymbolReportReception_IAB_r16 z, (Phy_ParametersCommon__ext3O__harqACK_CB_SpatialBundlingPUCCH_Group_r16 z, (Phy_ParametersCommon__ext3O__crossSlotScheduling_r16 z, (Phy_ParametersCommon__ext3O__maxNumberSRS_PosPathLossEstimateAllServingCells_r16 z, (Phy_ParametersCommon__ext3O__extendedCG_Periodicities_r16 z, (Phy_ParametersCommon__ext3O__extendedSPS_Periodicities_r16 z, (Phy_ParametersCommon__ext3O__codebookVariantsList_r16 z, (Phy_ParametersCommon__ext3O__pusch_RepetitionTypeA_r16 z, (Phy_ParametersCommon__ext3O__dci_DL_PriorityIndicator_r16 z, (Phy_ParametersCommon__ext3O__dci_UL_PriorityIndicator_r16 z, (Phy_ParametersCommon__ext3O__maxNumberPathlossRS_Update_r16 z, (Phy_ParametersCommon__ext3O__type2_HARQ_ACK_Codebook_r16 z, (Phy_ParametersCommon__ext3O__maxTotalResourcesForAcrossFreqRanges_r16 z, (Phy_ParametersCommon__ext3O__harqACK_separateMultiDCI_MultiTRP_r16 z, (Phy_ParametersCommon__ext3O__harqACK_jointMultiDCI_MultiTRP_r16 z, (Phy_ParametersCommon__ext3O__bwp_SwitchingMultiCCs_r16 z, tt))))))))))))))))))))))))))))))).
Definition Phy_ParametersCommon__ext3O__F2 (y : seq_type Phy_ParametersCommon__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, (i24, (i25, (i26, (i27, (i28, (i29, (i30, _)))))))))))))))))))))))))))))))=>
    make__Phy_ParametersCommon__ext3O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30
  end.
Lemma Phy_ParametersCommon__ext3O__F1F2_cond (z : Phy_ParametersCommon__ext3O__Type)
  : Phy_ParametersCommon__ext3O__cond z ->
  (seq_cond Phy_ParametersCommon__ext3O__list (Phy_ParametersCommon__ext3O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext3O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__F1F2_cond2 (z : Phy_ParametersCommon__ext3O__Type)
 : Phy_ParametersCommon__ext3O__F2 (Phy_ParametersCommon__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext3O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext3O__list)
  : seq_cond Phy_ParametersCommon__ext3O__list y ->
 (Phy_ParametersCommon__ext3O__cond (Phy_ParametersCommon__ext3O__F2 y)) /\  Phy_ParametersCommon__ext3O__F1 (Phy_ParametersCommon__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext3O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext3O__Format : T_Format Phy_ParametersCommon__ext3O__Type Phy_ParametersCommon__ext3O__cond :=
        proj2_format  Phy_ParametersCommon__ext3O__cond Phy_ParametersCommon__ext3O__list__Format
    Phy_ParametersCommon__ext3O__F1 Phy_ParametersCommon__ext3O__F2 Phy_ParametersCommon__ext3O__F1F2_cond  Phy_ParametersCommon__ext3O__F1F2_cond2 Phy_ParametersCommon__ext3O__F2F1_cond.
Opaque Phy_ParametersCommon__ext3O__cond Phy_ParametersCommon__ext3O__Format.

Definition Phy_ParametersCommon__ext3__check_all_none (b : Phy_ParametersCommon__ext3O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext3O__Type None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext3__Format : T_Format Phy_ParametersCommon__ext3__Type Phy_ParametersCommon__ext3__cond :=
  restrict_add_format Phy_ParametersCommon__ext3__check_all_none Phy_ParametersCommon__ext3O__Format.

Opaque Phy_ParametersCommon__ext3__cond Phy_ParametersCommon__ext3__Format.

Definition Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Format : T_Format Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__nat__Format Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F1 Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F2 Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F1F2 Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__F2F1.

Opaque Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__cond Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Format.

Definition Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Format : T_Format Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__nat__Format Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F1 Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F2 Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F1F2 Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__F2F1.

Opaque Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__cond Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Format.

Definition Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Format : T_Format Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__nat__Format Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F1 Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F2 Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F1F2 Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__F2F1.

Opaque Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__cond Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Format.


Definition Phy_ParametersCommon__ext4O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext4O__list.
Definition Phy_ParametersCommon__ext4O__Format_list : Phy_ParametersCommon__ext4O__Format_Type :=
  (Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16__Format, (Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16__Format, (Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16__Format, unit_format))).
Definition Phy_ParametersCommon__ext4O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext4O__list Phy_ParametersCommon__ext4O__Format_list.
Definition Phy_ParametersCommon__ext4O__F1 z :=
  (Phy_ParametersCommon__ext4O__targetSMTC_SCG_r16 z, (Phy_ParametersCommon__ext4O__supportRepetitionZeroOffsetRV_r16 z, (Phy_ParametersCommon__ext4O__cbg_TransInOrderPUSCH_UL_r16 z, tt))).
Definition Phy_ParametersCommon__ext4O__F2 (y : seq_type Phy_ParametersCommon__ext4O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__Phy_ParametersCommon__ext4O__Type i0 i1 i2
  end.
Lemma Phy_ParametersCommon__ext4O__F1F2_cond (z : Phy_ParametersCommon__ext4O__Type)
  : Phy_ParametersCommon__ext4O__cond z ->
  (seq_cond Phy_ParametersCommon__ext4O__list (Phy_ParametersCommon__ext4O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext4O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext4O__F1F2_cond2 (z : Phy_ParametersCommon__ext4O__Type)
 : Phy_ParametersCommon__ext4O__F2 (Phy_ParametersCommon__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext4O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext4O__list)
  : seq_cond Phy_ParametersCommon__ext4O__list y ->
 (Phy_ParametersCommon__ext4O__cond (Phy_ParametersCommon__ext4O__F2 y)) /\  Phy_ParametersCommon__ext4O__F1 (Phy_ParametersCommon__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext4O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext4O__Format : T_Format Phy_ParametersCommon__ext4O__Type Phy_ParametersCommon__ext4O__cond :=
        proj2_format  Phy_ParametersCommon__ext4O__cond Phy_ParametersCommon__ext4O__list__Format
    Phy_ParametersCommon__ext4O__F1 Phy_ParametersCommon__ext4O__F2 Phy_ParametersCommon__ext4O__F1F2_cond  Phy_ParametersCommon__ext4O__F1F2_cond2 Phy_ParametersCommon__ext4O__F2F1_cond.
Opaque Phy_ParametersCommon__ext4O__cond Phy_ParametersCommon__ext4O__Format.

Definition Phy_ParametersCommon__ext4__check_all_none (b : Phy_ParametersCommon__ext4O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext4O__Type None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext4__Format : T_Format Phy_ParametersCommon__ext4__Type Phy_ParametersCommon__ext4__cond :=
  restrict_add_format Phy_ParametersCommon__ext4__check_all_none Phy_ParametersCommon__ext4O__Format.

Opaque Phy_ParametersCommon__ext4__cond Phy_ParametersCommon__ext4__Format.

Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Format : T_Format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__nat__Format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F1 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F2 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F1F2 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__F2F1.

Opaque Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__cond Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Format.

Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Format : T_Format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__nat__Format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F1 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F2 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F1F2 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__F2F1.

Opaque Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__cond Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Format.


Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Format_Type := Eval cbn in get_formats Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Format_list : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Format_Type :=
  (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Format, (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Format, unit__Format)).
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list__Format := Eval compute in choice_format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__len_helper1 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__len_helper2  Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Format_list.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F1 (z : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type) : (choice Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list) :=
  match z with
   | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16 t => existT _ 0 t
  | Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16 t => existT _ 1 t
  end.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__g := (fun n => typ_set (get_nth_typ Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list n)).
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F2 (y : choice Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list) : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__g n -> Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type) with
    | 0 => fun (t : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16__Type) => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type1_r16 t 
    | 1 => fun (t : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16__Type) => Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__type2_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type with end) n0
           end t0).

Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__helper2 :  forall (y : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type), Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__cond y -> choice_cond Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__helper3 :  forall (y : Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type), Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F2 (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__helper4 : (forall b : choice Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list, choice_cond Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list b -> Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__cond (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F2 b) /\ Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F1 (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F1 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F2.
Definition Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Format : T_Format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Type Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__cond :=
  (* Eval compute in *) proj2_format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__cond Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__list__Format Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F1 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__F2 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__helper2 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__helper3 Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__helper4.
Opaque Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__cond Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Format.

Definition Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Format : T_Format Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__nat__Format Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F1 Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F2 Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F1F2 Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__F2F1.

Opaque Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__cond Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Format.

Definition Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Format : T_Format Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__nat__Format Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F1 Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F2 Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F1F2 Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__F2F1.

Opaque Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__cond Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Format.


Definition Phy_ParametersCommon__ext5O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext5O__list.
Definition Phy_ParametersCommon__ext5O__Format_list : Phy_ParametersCommon__ext5O__Format_Type :=
  (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16__Format, (Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16__Format, (Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16__Format, unit_format))).
Definition Phy_ParametersCommon__ext5O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext5O__list Phy_ParametersCommon__ext5O__Format_list.
Definition Phy_ParametersCommon__ext5O__F1 z :=
  (Phy_ParametersCommon__ext5O__bwp_SwitchingMultiDormancyCCs_r16 z, (Phy_ParametersCommon__ext5O__supportRetx_Diff_CoresetPool_Multi_DCI_TRP_r16 z, (Phy_ParametersCommon__ext5O__pdcch_MonitoringAnyOccasionsWithSpanGapCrossCarrierSch_r16 z, tt))).
Definition Phy_ParametersCommon__ext5O__F2 (y : seq_type Phy_ParametersCommon__ext5O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__Phy_ParametersCommon__ext5O__Type i0 i1 i2
  end.
Lemma Phy_ParametersCommon__ext5O__F1F2_cond (z : Phy_ParametersCommon__ext5O__Type)
  : Phy_ParametersCommon__ext5O__cond z ->
  (seq_cond Phy_ParametersCommon__ext5O__list (Phy_ParametersCommon__ext5O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext5O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext5O__F1F2_cond2 (z : Phy_ParametersCommon__ext5O__Type)
 : Phy_ParametersCommon__ext5O__F2 (Phy_ParametersCommon__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext5O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext5O__list)
  : seq_cond Phy_ParametersCommon__ext5O__list y ->
 (Phy_ParametersCommon__ext5O__cond (Phy_ParametersCommon__ext5O__F2 y)) /\  Phy_ParametersCommon__ext5O__F1 (Phy_ParametersCommon__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext5O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext5O__Format : T_Format Phy_ParametersCommon__ext5O__Type Phy_ParametersCommon__ext5O__cond :=
        proj2_format  Phy_ParametersCommon__ext5O__cond Phy_ParametersCommon__ext5O__list__Format
    Phy_ParametersCommon__ext5O__F1 Phy_ParametersCommon__ext5O__F2 Phy_ParametersCommon__ext5O__F1F2_cond  Phy_ParametersCommon__ext5O__F1F2_cond2 Phy_ParametersCommon__ext5O__F2F1_cond.
Opaque Phy_ParametersCommon__ext5O__cond Phy_ParametersCommon__ext5O__Format.

Definition Phy_ParametersCommon__ext5__check_all_none (b : Phy_ParametersCommon__ext5O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext5O__Type None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext5__Format : T_Format Phy_ParametersCommon__ext5__Type Phy_ParametersCommon__ext5__cond :=
  restrict_add_format Phy_ParametersCommon__ext5__check_all_none Phy_ParametersCommon__ext5O__Format.

Opaque Phy_ParametersCommon__ext5__cond Phy_ParametersCommon__ext5__Format.

Definition Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Format : T_Format Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__nat__Format Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F1 Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F2 Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F1F2 Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__F2F1.

Opaque Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__cond Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Format.

Definition Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Format : T_Format Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__nat__Format Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F1 Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F2 Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F1F2 Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__F2F1.

Opaque Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__cond Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Format.


Definition Phy_ParametersCommon__ext6O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext6O__list.
Definition Phy_ParametersCommon__ext6O__Format_list : Phy_ParametersCommon__ext6O__Format_Type :=
  (Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16__Format, (Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16__Format, unit_format)).
Definition Phy_ParametersCommon__ext6O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext6O__list Phy_ParametersCommon__ext6O__Format_list.
Definition Phy_ParametersCommon__ext6O__F1 z :=
  (Phy_ParametersCommon__ext6O__newBeamIdentifications2PortCSI_RS_r16 z, (Phy_ParametersCommon__ext6O__pathlossEstimation2PortCSI_RS_r16 z, tt)).
Definition Phy_ParametersCommon__ext6O__F2 (y : seq_type Phy_ParametersCommon__ext6O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersCommon__ext6O__Type i0 i1
  end.
Lemma Phy_ParametersCommon__ext6O__F1F2_cond (z : Phy_ParametersCommon__ext6O__Type)
  : Phy_ParametersCommon__ext6O__cond z ->
  (seq_cond Phy_ParametersCommon__ext6O__list (Phy_ParametersCommon__ext6O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext6O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext6O__F1F2_cond2 (z : Phy_ParametersCommon__ext6O__Type)
 : Phy_ParametersCommon__ext6O__F2 (Phy_ParametersCommon__ext6O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext6O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext6O__list)
  : seq_cond Phy_ParametersCommon__ext6O__list y ->
 (Phy_ParametersCommon__ext6O__cond (Phy_ParametersCommon__ext6O__F2 y)) /\  Phy_ParametersCommon__ext6O__F1 (Phy_ParametersCommon__ext6O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext6O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext6O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext6O__Format : T_Format Phy_ParametersCommon__ext6O__Type Phy_ParametersCommon__ext6O__cond :=
        proj2_format  Phy_ParametersCommon__ext6O__cond Phy_ParametersCommon__ext6O__list__Format
    Phy_ParametersCommon__ext6O__F1 Phy_ParametersCommon__ext6O__F2 Phy_ParametersCommon__ext6O__F1F2_cond  Phy_ParametersCommon__ext6O__F1F2_cond2 Phy_ParametersCommon__ext6O__F2F1_cond.
Opaque Phy_ParametersCommon__ext6O__cond Phy_ParametersCommon__ext6O__Format.

Definition Phy_ParametersCommon__ext6__check_all_none (b : Phy_ParametersCommon__ext6O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext6O__Type None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext6__Format : T_Format Phy_ParametersCommon__ext6__Type Phy_ParametersCommon__ext6__cond :=
  restrict_add_format Phy_ParametersCommon__ext6__check_all_none Phy_ParametersCommon__ext6O__Format.

Opaque Phy_ParametersCommon__ext6__cond Phy_ParametersCommon__ext6__Format.

Definition Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Format : T_Format Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__nat__Format Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F1 Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F2 Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F1F2 Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__F2F1.

Opaque Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__cond Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Format.


Definition Phy_ParametersCommon__ext7O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext7O__list.
Definition Phy_ParametersCommon__ext7O__Format_list : Phy_ParametersCommon__ext7O__Format_Type :=
  (Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16__Format, unit_format).
Definition Phy_ParametersCommon__ext7O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext7O__list Phy_ParametersCommon__ext7O__Format_list.
Definition Phy_ParametersCommon__ext7O__F1 z :=
  (Phy_ParametersCommon__ext7O__mux_HARQ_ACK_withoutPUCCH_onPUSCH_r16 z, tt).
Definition Phy_ParametersCommon__ext7O__F2 (y : seq_type Phy_ParametersCommon__ext7O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersCommon__ext7O__Type i0
  end.
Lemma Phy_ParametersCommon__ext7O__F1F2_cond (z : Phy_ParametersCommon__ext7O__Type)
  : Phy_ParametersCommon__ext7O__cond z ->
  (seq_cond Phy_ParametersCommon__ext7O__list (Phy_ParametersCommon__ext7O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext7O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext7O__F1F2_cond2 (z : Phy_ParametersCommon__ext7O__Type)
 : Phy_ParametersCommon__ext7O__F2 (Phy_ParametersCommon__ext7O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext7O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext7O__list)
  : seq_cond Phy_ParametersCommon__ext7O__list y ->
 (Phy_ParametersCommon__ext7O__cond (Phy_ParametersCommon__ext7O__F2 y)) /\  Phy_ParametersCommon__ext7O__F1 (Phy_ParametersCommon__ext7O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext7O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext7O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext7O__Format : T_Format Phy_ParametersCommon__ext7O__Type Phy_ParametersCommon__ext7O__cond :=
        proj2_format  Phy_ParametersCommon__ext7O__cond Phy_ParametersCommon__ext7O__list__Format
    Phy_ParametersCommon__ext7O__F1 Phy_ParametersCommon__ext7O__F2 Phy_ParametersCommon__ext7O__F1F2_cond  Phy_ParametersCommon__ext7O__F1F2_cond2 Phy_ParametersCommon__ext7O__F2F1_cond.
Opaque Phy_ParametersCommon__ext7O__cond Phy_ParametersCommon__ext7O__Format.

Definition Phy_ParametersCommon__ext7__check_all_none (b : Phy_ParametersCommon__ext7O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext7O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext7__Format : T_Format Phy_ParametersCommon__ext7__Type Phy_ParametersCommon__ext7__cond :=
  restrict_add_format Phy_ParametersCommon__ext7__check_all_none Phy_ParametersCommon__ext7O__Format.

Opaque Phy_ParametersCommon__ext7__cond Phy_ParametersCommon__ext7__Format.

Definition Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Format : T_Format Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__nat__Format Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F1 Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F2 Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F1F2 Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__cond Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Format.

Definition Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Format : T_Format Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__nat__Format Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F1 Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F2 Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F1F2 Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__cond Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Format.

Definition Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Format : T_Format Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__nat__Format Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F1 Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F2 Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F1F2 Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__cond Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Format.

Definition Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Format : T_Format Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__nat__Format Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F1 Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F2 Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F1F2 Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__cond Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Format.

Definition Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Format : T_Format Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__nat__Format Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F1 Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F2 Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F1F2 Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__cond Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Format.

Definition Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Format : T_Format Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__nat__Format Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F1 Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F2 Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F1F2 Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__cond Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Format.

Definition Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Format : T_Format Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__nat__Format Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F1 Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F2 Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F1F2 Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__cond Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Format.

Definition Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Format : T_Format Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__nat__Format Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F1 Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F2 Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F1F2 Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__cond Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Format.

Definition Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Format : T_Format Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__nat__Format Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F1 Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F2 Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F1F2 Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__cond Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Format.

Definition Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Format : T_Format Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__nat__Format Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F1 Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F2 Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F1F2 Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__cond Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Format.

Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Format : T_Format Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__nat__Format Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F1 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F2 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F1F2 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Format.

Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Format : T_Format Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__nat__Format Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F1 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F2 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F1F2 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Format.


Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Format_list : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Format_Type :=
  (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17__Format, (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17__Format, unit_format)).
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Format_list.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1 z :=
  (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__non_SharedSpectrumChAccess_r17 z, (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__sharedSpectrumChAccess_r17 z, tt)).
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F2 (y : seq_type Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Type i0 i1
  end.
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1F2_cond (z : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Type)
  : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond z ->
  (seq_cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1 z)).
intro H. unfold Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1F2_cond2 (z : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Type)
 : Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F2 (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F2F1_cond (y : seq_type Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list)
  : seq_cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list y ->
 (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F2 y)) /\  Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1 (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Format : T_Format Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Type Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond :=
        proj2_format  Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__list__Format
    Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F2 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1F2_cond  Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F1F2_cond2 Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__F2F1_cond.
Opaque Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__cond Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Format.

Definition Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__Format : T_Format Z Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__cond :=
 ranged_int_format (1) (4) Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__helper1 Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__helper2.

Opaque Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__cond Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__Format.

Definition Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Format : T_Format Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__nat__Format Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F1 Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F2 Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F1F2 Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__cond Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Format.

Definition Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Format : T_Format Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__nat__Format Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F1 Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F2 Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F1F2 Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__cond Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Format.

Definition Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Format : T_Format Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__nat__Format Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F1 Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F2 Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F1F2 Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__F2F1.

Opaque Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__cond Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Format.


Definition Phy_ParametersCommon__ext8O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext8O__list.
Definition Phy_ParametersCommon__ext8O__Format_list : Phy_ParametersCommon__ext8O__Format_Type :=
  (Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17__Format, (Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17__Format, (Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17__Format, (Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17__Format, (Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17__Format, (Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17__Format, (Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17__Format, (Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17__Format, (Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17__Format, (Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17__Format, (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17__Format, (Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17__Format, (Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17__Format, (Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17__Format, (Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17__Format, unit_format))))))))))))))).
Definition Phy_ParametersCommon__ext8O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext8O__list Phy_ParametersCommon__ext8O__Format_list.
Definition Phy_ParametersCommon__ext8O__F1 z :=
  (Phy_ParametersCommon__ext8O__guardSymbolReportReception_IAB_r17 z, (Phy_ParametersCommon__ext8O__restricted_IAB_DU_BeamReception_r17 z, (Phy_ParametersCommon__ext8O__recommended_IAB_MT_BeamTransmission_r17 z, (Phy_ParametersCommon__ext8O__case6_TimingAlignmentReception_IAB_r17 z, (Phy_ParametersCommon__ext8O__case7_TimingAlignmentReception_IAB_r17 z, (Phy_ParametersCommon__ext8O__dl_tx_PowerAdjustment_IAB_r17 z, (Phy_ParametersCommon__ext8O__desired_ul_tx_PowerAdjustment_r17 z, (Phy_ParametersCommon__ext8O__fdm_SoftResourceAvailability_DynamicIndication_r17 z, (Phy_ParametersCommon__ext8O__updated_T_DeltaRangeRecption_r17 z, (Phy_ParametersCommon__ext8O__slotBasedDynamicPUCCH_Rep_r17 z, (Phy_ParametersCommon__ext8O__sps_HARQ_ACK_Deferral_r17 z, (Phy_ParametersCommon__ext8O__unifiedJointTCI_commonUpdate_r17 z, (Phy_ParametersCommon__ext8O__mTRP_PDCCH_singleSpan_r17 z, (Phy_ParametersCommon__ext8O__supportedActivatedPRS_ProcessingWindow_r17 z, (Phy_ParametersCommon__ext8O__cg_TimeDomainAllocationExtension_r17 z, tt))))))))))))))).
Definition Phy_ParametersCommon__ext8O__F2 (y : seq_type Phy_ParametersCommon__ext8O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, _)))))))))))))))=>
    make__Phy_ParametersCommon__ext8O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14
  end.
Lemma Phy_ParametersCommon__ext8O__F1F2_cond (z : Phy_ParametersCommon__ext8O__Type)
  : Phy_ParametersCommon__ext8O__cond z ->
  (seq_cond Phy_ParametersCommon__ext8O__list (Phy_ParametersCommon__ext8O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext8O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext8O__F1F2_cond2 (z : Phy_ParametersCommon__ext8O__Type)
 : Phy_ParametersCommon__ext8O__F2 (Phy_ParametersCommon__ext8O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext8O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext8O__list)
  : seq_cond Phy_ParametersCommon__ext8O__list y ->
 (Phy_ParametersCommon__ext8O__cond (Phy_ParametersCommon__ext8O__F2 y)) /\  Phy_ParametersCommon__ext8O__F1 (Phy_ParametersCommon__ext8O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext8O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext8O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext8O__Format : T_Format Phy_ParametersCommon__ext8O__Type Phy_ParametersCommon__ext8O__cond :=
        proj2_format  Phy_ParametersCommon__ext8O__cond Phy_ParametersCommon__ext8O__list__Format
    Phy_ParametersCommon__ext8O__F1 Phy_ParametersCommon__ext8O__F2 Phy_ParametersCommon__ext8O__F1F2_cond  Phy_ParametersCommon__ext8O__F1F2_cond2 Phy_ParametersCommon__ext8O__F2F1_cond.
Opaque Phy_ParametersCommon__ext8O__cond Phy_ParametersCommon__ext8O__Format.

Definition Phy_ParametersCommon__ext8__check_all_none (b : Phy_ParametersCommon__ext8O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext8O__Type None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext8__Format : T_Format Phy_ParametersCommon__ext8__Type Phy_ParametersCommon__ext8__cond :=
  restrict_add_format Phy_ParametersCommon__ext8__check_all_none Phy_ParametersCommon__ext8O__Format.

Opaque Phy_ParametersCommon__ext8__cond Phy_ParametersCommon__ext8__Format.

Definition Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Format : T_Format Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__nat__Format Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F1 Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F2 Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F1F2 Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__F2F1.

Opaque Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__cond Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Format.

Definition Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Format : T_Format Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__nat__Format Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F1 Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F2 Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F1F2 Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__F2F1.

Opaque Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__cond Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Format.


Definition Phy_ParametersCommon__ext9O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext9O__list.
Definition Phy_ParametersCommon__ext9O__Format_list : Phy_ParametersCommon__ext9O__Format_Type :=
  (Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17__Format, (Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17__Format, unit_format)).
Definition Phy_ParametersCommon__ext9O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext9O__list Phy_ParametersCommon__ext9O__Format_list.
Definition Phy_ParametersCommon__ext9O__F1 z :=
  (Phy_ParametersCommon__ext9O__ta_BasedPDC_TN_NonSharedSpectrumChAccess_r17 z, (Phy_ParametersCommon__ext9O__directionalCollisionDC_IAB_r17 z, tt)).
Definition Phy_ParametersCommon__ext9O__F2 (y : seq_type Phy_ParametersCommon__ext9O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__Phy_ParametersCommon__ext9O__Type i0 i1
  end.
Lemma Phy_ParametersCommon__ext9O__F1F2_cond (z : Phy_ParametersCommon__ext9O__Type)
  : Phy_ParametersCommon__ext9O__cond z ->
  (seq_cond Phy_ParametersCommon__ext9O__list (Phy_ParametersCommon__ext9O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext9O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext9O__F1F2_cond2 (z : Phy_ParametersCommon__ext9O__Type)
 : Phy_ParametersCommon__ext9O__F2 (Phy_ParametersCommon__ext9O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext9O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext9O__list)
  : seq_cond Phy_ParametersCommon__ext9O__list y ->
 (Phy_ParametersCommon__ext9O__cond (Phy_ParametersCommon__ext9O__F2 y)) /\  Phy_ParametersCommon__ext9O__F1 (Phy_ParametersCommon__ext9O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext9O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext9O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext9O__Format : T_Format Phy_ParametersCommon__ext9O__Type Phy_ParametersCommon__ext9O__cond :=
        proj2_format  Phy_ParametersCommon__ext9O__cond Phy_ParametersCommon__ext9O__list__Format
    Phy_ParametersCommon__ext9O__F1 Phy_ParametersCommon__ext9O__F2 Phy_ParametersCommon__ext9O__F1F2_cond  Phy_ParametersCommon__ext9O__F1F2_cond2 Phy_ParametersCommon__ext9O__F2F1_cond.
Opaque Phy_ParametersCommon__ext9O__cond Phy_ParametersCommon__ext9O__Format.

Definition Phy_ParametersCommon__ext9__check_all_none (b : Phy_ParametersCommon__ext9O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext9O__Type None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext9__Format : T_Format Phy_ParametersCommon__ext9__Type Phy_ParametersCommon__ext9__cond :=
  restrict_add_format Phy_ParametersCommon__ext9__check_all_none Phy_ParametersCommon__ext9O__Format.

Opaque Phy_ParametersCommon__ext9__cond Phy_ParametersCommon__ext9__Format.

Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Format : T_Format Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__nat__Format Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F1 Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F2 Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F1F2 Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__F2F1.

Opaque Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__cond Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Format.

Definition Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Format : T_Format Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__nat__Format Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F1 Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F2 Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F1F2 Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__F2F1.

Opaque Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__cond Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Format.

Definition Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Format : T_Format Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__nat__Format Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F1 Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F2 Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F1F2 Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__F2F1.

Opaque Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__cond Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Format.

Definition Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Format : T_Format Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__nat__Format Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F1 Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F2 Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F1F2 Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__F2F1.

Opaque Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__cond Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Format.

Definition Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Format : T_Format Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__nat__Format Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F1 Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F2 Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F1F2 Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__F2F1.

Opaque Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__cond Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Format.

Definition Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Format : T_Format Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__nat__Format Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F1 Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F2 Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F1F2 Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__F2F1.

Opaque Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__cond Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Format.


Definition Phy_ParametersCommon__ext10O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__ext10O__list.
Definition Phy_ParametersCommon__ext10O__Format_list : Phy_ParametersCommon__ext10O__Format_Type :=
  (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17__Format, (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17__Format, (Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17__Format, (Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17__Format, (Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17__Format, (Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17__Format, unit_format)))))).
Definition Phy_ParametersCommon__ext10O__list__Format := (*Eval compute in *) seq_format Phy_ParametersCommon__ext10O__list Phy_ParametersCommon__ext10O__Format_list.
Definition Phy_ParametersCommon__ext10O__F1 z :=
  (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_Multicast_r17 z, (Phy_ParametersCommon__ext10O__priorityIndicatorInDCI_SPS_Multicast_r17 z, (Phy_ParametersCommon__ext10O__twoHARQ_ACK_CodebookForUnicastAndMulticast_r17 z, (Phy_ParametersCommon__ext10O__multiPUCCH_HARQ_ACK_ForMulticastUnicast_r17 z, (Phy_ParametersCommon__ext10O__srs_AdditionalRepetition_r17 z, (Phy_ParametersCommon__ext10O__pusch_Repetition_CG_SDT_r17 z, tt)))))).
Definition Phy_ParametersCommon__ext10O__F2 (y : seq_type Phy_ParametersCommon__ext10O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__Phy_ParametersCommon__ext10O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma Phy_ParametersCommon__ext10O__F1F2_cond (z : Phy_ParametersCommon__ext10O__Type)
  : Phy_ParametersCommon__ext10O__cond z ->
  (seq_cond Phy_ParametersCommon__ext10O__list (Phy_ParametersCommon__ext10O__F1 z)).
intro H. unfold Phy_ParametersCommon__ext10O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext10O__F1F2_cond2 (z : Phy_ParametersCommon__ext10O__Type)
 : Phy_ParametersCommon__ext10O__F2 (Phy_ParametersCommon__ext10O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersCommon__ext10O__F2F1_cond (y : seq_type Phy_ParametersCommon__ext10O__list)
  : seq_cond Phy_ParametersCommon__ext10O__list y ->
 (Phy_ParametersCommon__ext10O__cond (Phy_ParametersCommon__ext10O__F2 y)) /\  Phy_ParametersCommon__ext10O__F1 (Phy_ParametersCommon__ext10O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersCommon__ext10O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersCommon__ext10O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersCommon__ext10O__Format : T_Format Phy_ParametersCommon__ext10O__Type Phy_ParametersCommon__ext10O__cond :=
        proj2_format  Phy_ParametersCommon__ext10O__cond Phy_ParametersCommon__ext10O__list__Format
    Phy_ParametersCommon__ext10O__F1 Phy_ParametersCommon__ext10O__F2 Phy_ParametersCommon__ext10O__F1F2_cond  Phy_ParametersCommon__ext10O__F1F2_cond2 Phy_ParametersCommon__ext10O__F2F1_cond.
Opaque Phy_ParametersCommon__ext10O__cond Phy_ParametersCommon__ext10O__Format.

Definition Phy_ParametersCommon__ext10__check_all_none (b : Phy_ParametersCommon__ext10O__Type) : bool :=
match b with 
  | make__Phy_ParametersCommon__ext10O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition Phy_ParametersCommon__ext10__Format : T_Format Phy_ParametersCommon__ext10__Type Phy_ParametersCommon__ext10__cond :=
  restrict_add_format Phy_ParametersCommon__ext10__check_all_none Phy_ParametersCommon__ext10O__Format.

Opaque Phy_ParametersCommon__ext10__cond Phy_ParametersCommon__ext10__Format.


Definition Phy_ParametersCommon__root_Format_Type := Eval cbn in seq_format_prod Phy_ParametersCommon__root_list.
Definition Phy_ParametersCommon__root_Format_list : Phy_ParametersCommon__root_Format_Type :=
  (Phy_ParametersCommon__csi_RS_CFRA_ForHO__Format, (Phy_ParametersCommon__dynamicPRB_BundlingDL__Format, (Phy_ParametersCommon__sp_CSI_ReportPUCCH__Format, (Phy_ParametersCommon__sp_CSI_ReportPUSCH__Format, (Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt__Format, (Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH__Format, (Phy_ParametersCommon__precoderGranularityCORESET__Format, (Phy_ParametersCommon__dynamicHARQ_ACK_Codebook__Format, (Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook__Format, (Phy_ParametersCommon__spatialBundlingHARQ_ACK__Format, (Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI__Format, (Phy_ParametersCommon__pucch_Repetition_F1_3_4__Format, (Phy_ParametersCommon__ra_Type0_PUSCH__Format, (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH__Format, (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH__Format, (Phy_ParametersCommon__pdsch_MappingTypeA__Format, (Phy_ParametersCommon__pdsch_MappingTypeB__Format, (Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH__Format, (Phy_ParametersCommon__interSlotFreqHopping_PUSCH__Format, (Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots__Format, (Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots__Format, (Phy_ParametersCommon__pusch_RepetitionMultiSlots__Format, (Phy_ParametersCommon__pdsch_RepetitionMultiSlots__Format, (Phy_ParametersCommon__downlinkSPS__Format, (Phy_ParametersCommon__configuredUL_GrantType1__Format, (Phy_ParametersCommon__configuredUL_GrantType2__Format, (Phy_ParametersCommon__pre_EmptIndication_DL__Format, (Phy_ParametersCommon__cbg_TransIndication_DL__Format, (Phy_ParametersCommon__cbg_TransIndication_UL__Format, (Phy_ParametersCommon__cbg_FlushIndication_DL__Format, (Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL__Format, (Phy_ParametersCommon__rateMatchingResrcSetSemi_Static__Format, (Phy_ParametersCommon__rateMatchingResrcSetDynamic__Format, (Phy_ParametersCommon__bwp_SwitchingDelay__Format, unit_format)))))))))))))))))))))))))))))))))).

Definition Phy_ParametersCommon__ext_Format_Type := Eval cbn in get_formats Phy_ParametersCommon__ext_list.
Definition Phy_ParametersCommon__ext_Format_list : Phy_ParametersCommon__ext_Format_Type :=
  (Phy_ParametersCommon__ext0__Format, (Phy_ParametersCommon__ext1__Format, (Phy_ParametersCommon__ext2__Format, (Phy_ParametersCommon__ext3__Format, (Phy_ParametersCommon__ext4__Format, (Phy_ParametersCommon__ext5__Format, (Phy_ParametersCommon__ext6__Format, (Phy_ParametersCommon__ext7__Format, (Phy_ParametersCommon__ext8__Format, (Phy_ParametersCommon__ext9__Format, (Phy_ParametersCommon__ext10__Format, unit__Format))))))))))).

Definition Phy_ParametersCommon__list_type : Set := (seq_type Phy_ParametersCommon__root_list) * (seq_ext_type Phy_ParametersCommon__ext_list).
Definition Phy_ParametersCommon__list_cond (z : Phy_ParametersCommon__list_type) : Prop :=
        (seq_cond Phy_ParametersCommon__root_list (fst z)) /\ (seq_ext_cond Phy_ParametersCommon__ext_list (snd z)).
Definition Phy_ParametersCommon__list_format : T_Format Phy_ParametersCommon__list_type Phy_ParametersCommon__list_cond :=
 (* Eval compute in *) seq_ext_format Phy_ParametersCommon__root_list Phy_ParametersCommon__root_Format_list Phy_ParametersCommon__ext_list Phy_ParametersCommon__ext_Format_list.

Opaque Phy_ParametersCommon__list_format.
Definition Phy_ParametersCommon__F1 (z : Phy_ParametersCommon__Type) : Phy_ParametersCommon__list_type :=
  (((Phy_ParametersCommon__csi_RS_CFRA_ForHO z, (Phy_ParametersCommon__dynamicPRB_BundlingDL z, (Phy_ParametersCommon__sp_CSI_ReportPUCCH z, (Phy_ParametersCommon__sp_CSI_ReportPUSCH z, (Phy_ParametersCommon__nzp_CSI_RS_IntefMgmt z, (Phy_ParametersCommon__type2_SP_CSI_Feedback_LongPUCCH z, (Phy_ParametersCommon__precoderGranularityCORESET z, (Phy_ParametersCommon__dynamicHARQ_ACK_Codebook z, (Phy_ParametersCommon__semiStaticHARQ_ACK_Codebook z, (Phy_ParametersCommon__spatialBundlingHARQ_ACK z, (Phy_ParametersCommon__dynamicBetaOffsetInd_HARQ_ACK_CSI z, (Phy_ParametersCommon__pucch_Repetition_F1_3_4 z, (Phy_ParametersCommon__ra_Type0_PUSCH z, (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PDSCH z, (Phy_ParametersCommon__dynamicSwitchRA_Type0_1_PUSCH z, (Phy_ParametersCommon__pdsch_MappingTypeA z, (Phy_ParametersCommon__pdsch_MappingTypeB z, (Phy_ParametersCommon__interleavingVRB_ToPRB_PDSCH z, (Phy_ParametersCommon__interSlotFreqHopping_PUSCH z, (Phy_ParametersCommon__type1_PUSCH_RepetitionMultiSlots z, (Phy_ParametersCommon__type2_PUSCH_RepetitionMultiSlots z, (Phy_ParametersCommon__pusch_RepetitionMultiSlots z, (Phy_ParametersCommon__pdsch_RepetitionMultiSlots z, (Phy_ParametersCommon__downlinkSPS z, (Phy_ParametersCommon__configuredUL_GrantType1 z, (Phy_ParametersCommon__configuredUL_GrantType2 z, (Phy_ParametersCommon__pre_EmptIndication_DL z, (Phy_ParametersCommon__cbg_TransIndication_DL z, (Phy_ParametersCommon__cbg_TransIndication_UL z, (Phy_ParametersCommon__cbg_FlushIndication_DL z, (Phy_ParametersCommon__dynamicHARQ_ACK_CodeB_CBG_Retx_DL z, (Phy_ParametersCommon__rateMatchingResrcSetSemi_Static z, (Phy_ParametersCommon__rateMatchingResrcSetDynamic z, (Phy_ParametersCommon__bwp_SwitchingDelay z, tt))))))))))))))))))))))))))))))))))), (
(Phy_ParametersCommon__ext0 z, (Phy_ParametersCommon__ext1 z, (Phy_ParametersCommon__ext2 z, (Phy_ParametersCommon__ext3 z, (Phy_ParametersCommon__ext4 z, (Phy_ParametersCommon__ext5 z, (Phy_ParametersCommon__ext6 z, (Phy_ParametersCommon__ext7 z, (Phy_ParametersCommon__ext8 z, (Phy_ParametersCommon__ext9 z, (Phy_ParametersCommon__ext10 z, tt))))))))))))).
Definition Phy_ParametersCommon__F2 (y : Phy_ParametersCommon__list_type) : Phy_ParametersCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, (j18, (j19, (j20, (j21, (j22, (j23, (j24, (j25, (j26, (j27, (j28, (j29, (j30, (j31, (j32, (j33, _)))))))))))))))))))))))))))))))))), (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, _))))))))))))=>
    make__Phy_ParametersCommon__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j22 j23 j24 j25 j26 j27 j28 j29 j30 j31 j32 j33 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10
  end.
Definition Phy_ParametersCommon__helper1 : (forall a : Phy_ParametersCommon__Type, Phy_ParametersCommon__cond a -> Phy_ParametersCommon__list_cond (Phy_ParametersCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersCommon__helper2 : (forall a : Phy_ParametersCommon__Type, Phy_ParametersCommon__F2 (Phy_ParametersCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersCommon__helper3 : (forall b : Phy_ParametersCommon__list_type, Phy_ParametersCommon__list_cond b -> Phy_ParametersCommon__cond (Phy_ParametersCommon__F2 b) /\ Phy_ParametersCommon__F1 (Phy_ParametersCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold Phy_ParametersCommon__cond, Phy_ParametersCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition Phy_ParametersCommon__Format : T_Format Phy_ParametersCommon__Type Phy_ParametersCommon__cond :=
 proj2_format Phy_ParametersCommon__cond Phy_ParametersCommon__list_format  Phy_ParametersCommon__F1 Phy_ParametersCommon__F2 Phy_ParametersCommon__helper1 Phy_ParametersCommon__helper2 Phy_ParametersCommon__helper3.

Opaque Phy_ParametersCommon__cond Phy_ParametersCommon__Format.

