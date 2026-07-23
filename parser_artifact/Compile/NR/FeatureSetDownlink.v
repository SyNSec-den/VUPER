Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FeatureSetDownlinkPerCC_Id.

Opaque FeatureSetDownlinkPerCC_Id__cond FeatureSetDownlinkPerCC_Id__Format.

Definition FeatureSetDownlink__featureSetListPerDownlinkCC__Type := list FeatureSetDownlinkPerCC_Id__Type.

Lemma FeatureSetDownlink__featureSetListPerDownlinkCC__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma FeatureSetDownlink__featureSetListPerDownlinkCC__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetDownlink__featureSetListPerDownlinkCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetDownlink__featureSetListPerDownlinkCC__cond (z : FeatureSetDownlink__featureSetListPerDownlinkCC__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells)%Z /\ (list_and FeatureSetDownlinkPerCC_Id__cond z) .

Require Import NR.FreqSeparationClass.

Opaque FreqSeparationClass__cond FreqSeparationClass__Format.

Inductive FeatureSetDownlink__scalingFactor__Type : Set :=
 | FeatureSetDownlink__scalingFactor__f0p4
 | FeatureSetDownlink__scalingFactor__f0p75
 | FeatureSetDownlink__scalingFactor__f0p8
.
Definition FeatureSetDownlink__scalingFactor__cond := (fun (_ : FeatureSetDownlink__scalingFactor__Type) => True).
Lemma FeatureSetDownlink__scalingFactor__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__scalingFactor__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetDownlink__scalingFactor__nat__helper.

Definition FeatureSetDownlink__scalingFactor__F1 t :=
  match t with
  | FeatureSetDownlink__scalingFactor__f0p4 => 0
  | FeatureSetDownlink__scalingFactor__f0p75 => 1
  | FeatureSetDownlink__scalingFactor__f0p8 => 2
  end.
Definition FeatureSetDownlink__scalingFactor__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__scalingFactor__f0p4
  | 1 => FeatureSetDownlink__scalingFactor__f0p75
  | 2 => FeatureSetDownlink__scalingFactor__f0p8
  | _ => FeatureSetDownlink__scalingFactor__f0p4
  end.
Lemma FeatureSetDownlink__scalingFactor__F1F2 : forall x : FeatureSetDownlink__scalingFactor__Type, (FeatureSetDownlink__scalingFactor__F1 x <= 2) /\ FeatureSetDownlink__scalingFactor__F2 (FeatureSetDownlink__scalingFactor__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__scalingFactor__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetDownlink__scalingFactor__F1 (FeatureSetDownlink__scalingFactor__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__dummy8__Type : Set :=
 | FeatureSetDownlink__dummy8__supported
.
Definition FeatureSetDownlink__dummy8__cond := (fun (_ : FeatureSetDownlink__dummy8__Type) => True).
Lemma FeatureSetDownlink__dummy8__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__dummy8__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink__dummy8__nat__helper.

Definition FeatureSetDownlink__dummy8__F1 t :=
  match t with
  | FeatureSetDownlink__dummy8__supported => 0
  end.
Definition FeatureSetDownlink__dummy8__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__dummy8__supported
  | _ => FeatureSetDownlink__dummy8__supported
  end.
Lemma FeatureSetDownlink__dummy8__F1F2 : forall x : FeatureSetDownlink__dummy8__Type, (FeatureSetDownlink__dummy8__F1 x <= 0) /\ FeatureSetDownlink__dummy8__F2 (FeatureSetDownlink__dummy8__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__dummy8__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink__dummy8__F1 (FeatureSetDownlink__dummy8__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__scellWithoutSSB__Type : Set :=
 | FeatureSetDownlink__scellWithoutSSB__supported
.
Definition FeatureSetDownlink__scellWithoutSSB__cond := (fun (_ : FeatureSetDownlink__scellWithoutSSB__Type) => True).
Lemma FeatureSetDownlink__scellWithoutSSB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__scellWithoutSSB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink__scellWithoutSSB__nat__helper.

Definition FeatureSetDownlink__scellWithoutSSB__F1 t :=
  match t with
  | FeatureSetDownlink__scellWithoutSSB__supported => 0
  end.
Definition FeatureSetDownlink__scellWithoutSSB__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__scellWithoutSSB__supported
  | _ => FeatureSetDownlink__scellWithoutSSB__supported
  end.
Lemma FeatureSetDownlink__scellWithoutSSB__F1F2 : forall x : FeatureSetDownlink__scellWithoutSSB__Type, (FeatureSetDownlink__scellWithoutSSB__F1 x <= 0) /\ FeatureSetDownlink__scellWithoutSSB__F2 (FeatureSetDownlink__scellWithoutSSB__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__scellWithoutSSB__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink__scellWithoutSSB__F1 (FeatureSetDownlink__scellWithoutSSB__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Type : Set :=
 | FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__supported
.
Definition FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__cond := (fun (_ : FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Type) => True).
Lemma FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__nat__helper.

Definition FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F1 t :=
  match t with
  | FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__supported => 0
  end.
Definition FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__supported
  | _ => FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__supported
  end.
Lemma FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F1F2 : forall x : FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Type, (FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F1 x <= 0) /\ FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F2 (FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F1 (FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__dummy1__Type : Set :=
 | FeatureSetDownlink__dummy1__supported
.
Definition FeatureSetDownlink__dummy1__cond := (fun (_ : FeatureSetDownlink__dummy1__Type) => True).
Lemma FeatureSetDownlink__dummy1__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__dummy1__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink__dummy1__nat__helper.

Definition FeatureSetDownlink__dummy1__F1 t :=
  match t with
  | FeatureSetDownlink__dummy1__supported => 0
  end.
Definition FeatureSetDownlink__dummy1__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__dummy1__supported
  | _ => FeatureSetDownlink__dummy1__supported
  end.
Lemma FeatureSetDownlink__dummy1__F1F2 : forall x : FeatureSetDownlink__dummy1__Type, (FeatureSetDownlink__dummy1__F1 x <= 0) /\ FeatureSetDownlink__dummy1__F2 (FeatureSetDownlink__dummy1__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__dummy1__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink__dummy1__F1 (FeatureSetDownlink__dummy1__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__type1_3_CSS__Type : Set :=
 | FeatureSetDownlink__type1_3_CSS__supported
.
Definition FeatureSetDownlink__type1_3_CSS__cond := (fun (_ : FeatureSetDownlink__type1_3_CSS__Type) => True).
Lemma FeatureSetDownlink__type1_3_CSS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__type1_3_CSS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink__type1_3_CSS__nat__helper.

Definition FeatureSetDownlink__type1_3_CSS__F1 t :=
  match t with
  | FeatureSetDownlink__type1_3_CSS__supported => 0
  end.
Definition FeatureSetDownlink__type1_3_CSS__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__type1_3_CSS__supported
  | _ => FeatureSetDownlink__type1_3_CSS__supported
  end.
Lemma FeatureSetDownlink__type1_3_CSS__F1F2 : forall x : FeatureSetDownlink__type1_3_CSS__Type, (FeatureSetDownlink__type1_3_CSS__F1 x <= 0) /\ FeatureSetDownlink__type1_3_CSS__F2 (FeatureSetDownlink__type1_3_CSS__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__type1_3_CSS__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink__type1_3_CSS__F1 (FeatureSetDownlink__type1_3_CSS__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Type : Set :=
 | FeatureSetDownlink__pdcch_MonitoringAnyOccasions__withoutDCI_Gap
 | FeatureSetDownlink__pdcch_MonitoringAnyOccasions__withDCI_Gap
.
Definition FeatureSetDownlink__pdcch_MonitoringAnyOccasions__cond := (fun (_ : FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Type) => True).
Lemma FeatureSetDownlink__pdcch_MonitoringAnyOccasions__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__pdcch_MonitoringAnyOccasions__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 FeatureSetDownlink__pdcch_MonitoringAnyOccasions__nat__helper.

Definition FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F1 t :=
  match t with
  | FeatureSetDownlink__pdcch_MonitoringAnyOccasions__withoutDCI_Gap => 0
  | FeatureSetDownlink__pdcch_MonitoringAnyOccasions__withDCI_Gap => 1
  end.
Definition FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__pdcch_MonitoringAnyOccasions__withoutDCI_Gap
  | 1 => FeatureSetDownlink__pdcch_MonitoringAnyOccasions__withDCI_Gap
  | _ => FeatureSetDownlink__pdcch_MonitoringAnyOccasions__withoutDCI_Gap
  end.
Lemma FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F1F2 : forall x : FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Type, (FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F1 x <= 1) /\ FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F2 (FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F2F1 : forall (y : nat) (H : y <= 1), FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F1 (FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__dummy2__Type : Set :=
 | FeatureSetDownlink__dummy2__supported
.
Definition FeatureSetDownlink__dummy2__cond := (fun (_ : FeatureSetDownlink__dummy2__Type) => True).
Lemma FeatureSetDownlink__dummy2__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__dummy2__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink__dummy2__nat__helper.

Definition FeatureSetDownlink__dummy2__F1 t :=
  match t with
  | FeatureSetDownlink__dummy2__supported => 0
  end.
Definition FeatureSetDownlink__dummy2__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__dummy2__supported
  | _ => FeatureSetDownlink__dummy2__supported
  end.
Lemma FeatureSetDownlink__dummy2__F1F2 : forall x : FeatureSetDownlink__dummy2__Type, (FeatureSetDownlink__dummy2__F1 x <= 0) /\ FeatureSetDownlink__dummy2__F2 (FeatureSetDownlink__dummy2__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__dummy2__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink__dummy2__F1 (FeatureSetDownlink__dummy2__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Type : Set :=
 | FeatureSetDownlink__ue_SpecificUL_DL_Assignment__supported
.
Definition FeatureSetDownlink__ue_SpecificUL_DL_Assignment__cond := (fun (_ : FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Type) => True).
Lemma FeatureSetDownlink__ue_SpecificUL_DL_Assignment__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__ue_SpecificUL_DL_Assignment__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink__ue_SpecificUL_DL_Assignment__nat__helper.

Definition FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F1 t :=
  match t with
  | FeatureSetDownlink__ue_SpecificUL_DL_Assignment__supported => 0
  end.
Definition FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__ue_SpecificUL_DL_Assignment__supported
  | _ => FeatureSetDownlink__ue_SpecificUL_DL_Assignment__supported
  end.
Lemma FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F1F2 : forall x : FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Type, (FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F1 x <= 0) /\ FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F2 (FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F1 (FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__searchSpaceSharingCA_DL__Type : Set :=
 | FeatureSetDownlink__searchSpaceSharingCA_DL__supported
.
Definition FeatureSetDownlink__searchSpaceSharingCA_DL__cond := (fun (_ : FeatureSetDownlink__searchSpaceSharingCA_DL__Type) => True).
Lemma FeatureSetDownlink__searchSpaceSharingCA_DL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__searchSpaceSharingCA_DL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink__searchSpaceSharingCA_DL__nat__helper.

Definition FeatureSetDownlink__searchSpaceSharingCA_DL__F1 t :=
  match t with
  | FeatureSetDownlink__searchSpaceSharingCA_DL__supported => 0
  end.
Definition FeatureSetDownlink__searchSpaceSharingCA_DL__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__searchSpaceSharingCA_DL__supported
  | _ => FeatureSetDownlink__searchSpaceSharingCA_DL__supported
  end.
Lemma FeatureSetDownlink__searchSpaceSharingCA_DL__F1F2 : forall x : FeatureSetDownlink__searchSpaceSharingCA_DL__Type, (FeatureSetDownlink__searchSpaceSharingCA_DL__F1 x <= 0) /\ FeatureSetDownlink__searchSpaceSharingCA_DL__F2 (FeatureSetDownlink__searchSpaceSharingCA_DL__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__searchSpaceSharingCA_DL__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink__searchSpaceSharingCA_DL__F1 (FeatureSetDownlink__searchSpaceSharingCA_DL__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Type : Set :=
 | FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s7
 | FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s14
 | FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s28
.
Definition FeatureSetDownlink__timeDurationForQCL__scs_60kHz__cond := (fun (_ : FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Type) => True).
Lemma FeatureSetDownlink__timeDurationForQCL__scs_60kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__timeDurationForQCL__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetDownlink__timeDurationForQCL__scs_60kHz__nat__helper.

Definition FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F1 t :=
  match t with
  | FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s7 => 0
  | FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s14 => 1
  | FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s28 => 2
  end.
Definition FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s7
  | 1 => FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s14
  | 2 => FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s28
  | _ => FeatureSetDownlink__timeDurationForQCL__scs_60kHz__s7
  end.
Lemma FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F1F2 : forall x : FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Type, (FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F1 x <= 2) /\ FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F2 (FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F1 (FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Type : Set :=
 | FeatureSetDownlink__timeDurationForQCL__scs_120kHz__s14
 | FeatureSetDownlink__timeDurationForQCL__scs_120kHz__s28
.
Definition FeatureSetDownlink__timeDurationForQCL__scs_120kHz__cond := (fun (_ : FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Type) => True).
Lemma FeatureSetDownlink__timeDurationForQCL__scs_120kHz__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__timeDurationForQCL__scs_120kHz__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 FeatureSetDownlink__timeDurationForQCL__scs_120kHz__nat__helper.

Definition FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F1 t :=
  match t with
  | FeatureSetDownlink__timeDurationForQCL__scs_120kHz__s14 => 0
  | FeatureSetDownlink__timeDurationForQCL__scs_120kHz__s28 => 1
  end.
Definition FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__timeDurationForQCL__scs_120kHz__s14
  | 1 => FeatureSetDownlink__timeDurationForQCL__scs_120kHz__s28
  | _ => FeatureSetDownlink__timeDurationForQCL__scs_120kHz__s14
  end.
Lemma FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F1F2 : forall x : FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Type, (FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F1 x <= 1) /\ FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F2 (FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F2F1 : forall (y : nat) (H : y <= 1), FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F1 (FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetDownlink__timeDurationForQCL__Type : Set :=
  make__FeatureSetDownlink__timeDurationForQCL__Type {
    FeatureSetDownlink__timeDurationForQCL__scs_60kHz : option FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Type ;
    FeatureSetDownlink__timeDurationForQCL__scs_120kHz : option FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Type ;
}.
Definition FeatureSetDownlink__timeDurationForQCL__list := (
 Opt FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Type FeatureSetDownlink__timeDurationForQCL__scs_60kHz__cond ::
 Opt FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Type FeatureSetDownlink__timeDurationForQCL__scs_120kHz__cond ::
 nil).
Definition FeatureSetDownlink__timeDurationForQCL__cond z := 
  opt_cond FeatureSetDownlink__timeDurationForQCL__scs_60kHz__cond (FeatureSetDownlink__timeDurationForQCL__scs_60kHz z) /\
  opt_cond FeatureSetDownlink__timeDurationForQCL__scs_120kHz__cond (FeatureSetDownlink__timeDurationForQCL__scs_120kHz z) /\
  True.

Inductive FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type : Set :=
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto2
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto4
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto7
.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__cond := (fun (_ : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type) => True).
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__nat__helper.

Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 t :=
  match t with
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto2 => 0
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto4 => 1
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto7 => 2
  end.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto2
  | 1 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto4
  | 2 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto7
  | _ => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto2
  end.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1F2 : forall x : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 x <= 2) /\ FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type : Set :=
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto2
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto4
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto7
.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__cond := (fun (_ : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type) => True).
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__nat__helper.

Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 t :=
  match t with
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto2 => 0
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto4 => 1
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto7 => 2
  end.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto2
  | 1 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto4
  | 2 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto7
  | _ => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto2
  end.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1F2 : forall x : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 x <= 2) /\ FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type : Set :=
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto2
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto4
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto7
.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__cond := (fun (_ : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type) => True).
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__nat__helper.

Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 t :=
  match t with
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto2 => 0
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto4 => 1
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto7 => 2
  end.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto2
  | 1 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto4
  | 2 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto7
  | _ => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto2
  end.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1F2 : forall x : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 x <= 2) /\ FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type : Set :=
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto2
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto4
 | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto7
.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__cond := (fun (_ : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type) => True).
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__nat__helper.

Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 t :=
  match t with
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto2 => 0
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto4 => 1
  | FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto7 => 2
  end.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2 n :=
  match n with
  | 0 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto2
  | 1 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto4
  | 2 => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto7
  | _ => FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto2
  end.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1F2 : forall x : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 x <= 2) /\ FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Type : Set :=
  make__FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Type {
    FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz : option FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type ;
    FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz : option FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type ;
    FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz : option FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type ;
    FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz : option FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type ;
}.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list := (
 Opt FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__cond ::
 Opt FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__cond ::
 Opt FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__cond ::
 Opt FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__cond ::
 nil).
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond z := 
  opt_cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__cond (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz z) /\
  opt_cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__cond (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz z) /\
  opt_cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__cond (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz z) /\
  opt_cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__cond (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz z) /\
  True.

Require Import NR.DummyA.

Opaque DummyA__cond DummyA__Format.

Require Import NR.DummyB.

Opaque DummyB__cond DummyB__Format.

Definition FeatureSetDownlink__dummy4__Type := list DummyB__Type.

Lemma FeatureSetDownlink__dummy4__helper1 : (0 <= 1 <= maxNrofCodebooks)%Z. unfold maxNrofCodebooks.
 lia. Qed.
Lemma FeatureSetDownlink__dummy4__helper2 : to_bit_sz (Z.to_nat (maxNrofCodebooks - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCodebooks - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetDownlink__dummy4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetDownlink__dummy4__cond (z : FeatureSetDownlink__dummy4__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCodebooks)%Z /\ (list_and DummyB__cond z) .

Require Import NR.DummyC.

Opaque DummyC__cond DummyC__Format.

Definition FeatureSetDownlink__dummy5__Type := list DummyC__Type.

Lemma FeatureSetDownlink__dummy5__helper1 : (0 <= 1 <= maxNrofCodebooks)%Z. unfold maxNrofCodebooks.
 lia. Qed.
Lemma FeatureSetDownlink__dummy5__helper2 : to_bit_sz (Z.to_nat (maxNrofCodebooks - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCodebooks - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetDownlink__dummy5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetDownlink__dummy5__cond (z : FeatureSetDownlink__dummy5__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCodebooks)%Z /\ (list_and DummyC__cond z) .

Require Import NR.DummyD.

Opaque DummyD__cond DummyD__Format.

Definition FeatureSetDownlink__dummy6__Type := list DummyD__Type.

Lemma FeatureSetDownlink__dummy6__helper1 : (0 <= 1 <= maxNrofCodebooks)%Z. unfold maxNrofCodebooks.
 lia. Qed.
Lemma FeatureSetDownlink__dummy6__helper2 : to_bit_sz (Z.to_nat (maxNrofCodebooks - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCodebooks - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetDownlink__dummy6__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetDownlink__dummy6__cond (z : FeatureSetDownlink__dummy6__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCodebooks)%Z /\ (list_and DummyD__cond z) .

Require Import NR.DummyE.

Opaque DummyE__cond DummyE__Format.

Definition FeatureSetDownlink__dummy7__Type := list DummyE__Type.

Lemma FeatureSetDownlink__dummy7__helper1 : (0 <= 1 <= maxNrofCodebooks)%Z. unfold maxNrofCodebooks.
 lia. Qed.
Lemma FeatureSetDownlink__dummy7__helper2 : to_bit_sz (Z.to_nat (maxNrofCodebooks - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCodebooks - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetDownlink__dummy7__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetDownlink__dummy7__cond (z : FeatureSetDownlink__dummy7__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCodebooks)%Z /\ (list_and DummyE__cond z) .

Record FeatureSetDownlink__Type : Set :=
  make__FeatureSetDownlink__Type {
    FeatureSetDownlink__featureSetListPerDownlinkCC : FeatureSetDownlink__featureSetListPerDownlinkCC__Type ;
    FeatureSetDownlink__intraBandFreqSeparationDL : option FreqSeparationClass__Type ;
    FeatureSetDownlink__scalingFactor : option FeatureSetDownlink__scalingFactor__Type ;
    FeatureSetDownlink__dummy8 : option FeatureSetDownlink__dummy8__Type ;
    FeatureSetDownlink__scellWithoutSSB : option FeatureSetDownlink__scellWithoutSSB__Type ;
    FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB : option FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Type ;
    FeatureSetDownlink__dummy1 : option FeatureSetDownlink__dummy1__Type ;
    FeatureSetDownlink__type1_3_CSS : option FeatureSetDownlink__type1_3_CSS__Type ;
    FeatureSetDownlink__pdcch_MonitoringAnyOccasions : option FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Type ;
    FeatureSetDownlink__dummy2 : option FeatureSetDownlink__dummy2__Type ;
    FeatureSetDownlink__ue_SpecificUL_DL_Assignment : option FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Type ;
    FeatureSetDownlink__searchSpaceSharingCA_DL : option FeatureSetDownlink__searchSpaceSharingCA_DL__Type ;
    FeatureSetDownlink__timeDurationForQCL : option FeatureSetDownlink__timeDurationForQCL__Type ;
    FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot : option FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Type ;
    FeatureSetDownlink__dummy3 : option DummyA__Type ;
    FeatureSetDownlink__dummy4 : option FeatureSetDownlink__dummy4__Type ;
    FeatureSetDownlink__dummy5 : option FeatureSetDownlink__dummy5__Type ;
    FeatureSetDownlink__dummy6 : option FeatureSetDownlink__dummy6__Type ;
    FeatureSetDownlink__dummy7 : option FeatureSetDownlink__dummy7__Type ;
}.
Definition FeatureSetDownlink__list := (
 Nor FeatureSetDownlink__featureSetListPerDownlinkCC__Type FeatureSetDownlink__featureSetListPerDownlinkCC__cond ::
 Opt FreqSeparationClass__Type FreqSeparationClass__cond ::
 Opt FeatureSetDownlink__scalingFactor__Type FeatureSetDownlink__scalingFactor__cond ::
 Opt FeatureSetDownlink__dummy8__Type FeatureSetDownlink__dummy8__cond ::
 Opt FeatureSetDownlink__scellWithoutSSB__Type FeatureSetDownlink__scellWithoutSSB__cond ::
 Opt FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Type FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__cond ::
 Opt FeatureSetDownlink__dummy1__Type FeatureSetDownlink__dummy1__cond ::
 Opt FeatureSetDownlink__type1_3_CSS__Type FeatureSetDownlink__type1_3_CSS__cond ::
 Opt FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Type FeatureSetDownlink__pdcch_MonitoringAnyOccasions__cond ::
 Opt FeatureSetDownlink__dummy2__Type FeatureSetDownlink__dummy2__cond ::
 Opt FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Type FeatureSetDownlink__ue_SpecificUL_DL_Assignment__cond ::
 Opt FeatureSetDownlink__searchSpaceSharingCA_DL__Type FeatureSetDownlink__searchSpaceSharingCA_DL__cond ::
 Opt FeatureSetDownlink__timeDurationForQCL__Type FeatureSetDownlink__timeDurationForQCL__cond ::
 Opt FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Type FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond ::
 Opt DummyA__Type DummyA__cond ::
 Opt FeatureSetDownlink__dummy4__Type FeatureSetDownlink__dummy4__cond ::
 Opt FeatureSetDownlink__dummy5__Type FeatureSetDownlink__dummy5__cond ::
 Opt FeatureSetDownlink__dummy6__Type FeatureSetDownlink__dummy6__cond ::
 Opt FeatureSetDownlink__dummy7__Type FeatureSetDownlink__dummy7__cond ::
 nil).
Definition FeatureSetDownlink__cond z := 
  FeatureSetDownlink__featureSetListPerDownlinkCC__cond (FeatureSetDownlink__featureSetListPerDownlinkCC z) /\
  opt_cond FreqSeparationClass__cond (FeatureSetDownlink__intraBandFreqSeparationDL z) /\
  opt_cond FeatureSetDownlink__scalingFactor__cond (FeatureSetDownlink__scalingFactor z) /\
  opt_cond FeatureSetDownlink__dummy8__cond (FeatureSetDownlink__dummy8 z) /\
  opt_cond FeatureSetDownlink__scellWithoutSSB__cond (FeatureSetDownlink__scellWithoutSSB z) /\
  opt_cond FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__cond (FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB z) /\
  opt_cond FeatureSetDownlink__dummy1__cond (FeatureSetDownlink__dummy1 z) /\
  opt_cond FeatureSetDownlink__type1_3_CSS__cond (FeatureSetDownlink__type1_3_CSS z) /\
  opt_cond FeatureSetDownlink__pdcch_MonitoringAnyOccasions__cond (FeatureSetDownlink__pdcch_MonitoringAnyOccasions z) /\
  opt_cond FeatureSetDownlink__dummy2__cond (FeatureSetDownlink__dummy2 z) /\
  opt_cond FeatureSetDownlink__ue_SpecificUL_DL_Assignment__cond (FeatureSetDownlink__ue_SpecificUL_DL_Assignment z) /\
  opt_cond FeatureSetDownlink__searchSpaceSharingCA_DL__cond (FeatureSetDownlink__searchSpaceSharingCA_DL z) /\
  opt_cond FeatureSetDownlink__timeDurationForQCL__cond (FeatureSetDownlink__timeDurationForQCL z) /\
  opt_cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot z) /\
  opt_cond DummyA__cond (FeatureSetDownlink__dummy3 z) /\
  opt_cond FeatureSetDownlink__dummy4__cond (FeatureSetDownlink__dummy4 z) /\
  opt_cond FeatureSetDownlink__dummy5__cond (FeatureSetDownlink__dummy5 z) /\
  opt_cond FeatureSetDownlink__dummy6__cond (FeatureSetDownlink__dummy6 z) /\
  opt_cond FeatureSetDownlink__dummy7__cond (FeatureSetDownlink__dummy7 z) /\
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
Definition FeatureSetDownlink__featureSetListPerDownlinkCC__Format : T_Format FeatureSetDownlink__featureSetListPerDownlinkCC__Type FeatureSetDownlink__featureSetListPerDownlinkCC__cond := seq_of_format FeatureSetDownlinkPerCC_Id__Format 1 maxNrofServingCells FeatureSetDownlink__featureSetListPerDownlinkCC__helper1 FeatureSetDownlink__featureSetListPerDownlinkCC__helper2.

Opaque FeatureSetDownlink__featureSetListPerDownlinkCC__cond FeatureSetDownlink__featureSetListPerDownlinkCC__Format.

Definition FeatureSetDownlink__scalingFactor__Format : T_Format FeatureSetDownlink__scalingFactor__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__scalingFactor__nat__Format FeatureSetDownlink__scalingFactor__F1 FeatureSetDownlink__scalingFactor__F2 FeatureSetDownlink__scalingFactor__F1F2 FeatureSetDownlink__scalingFactor__F2F1.

Opaque FeatureSetDownlink__scalingFactor__cond FeatureSetDownlink__scalingFactor__Format.

Definition FeatureSetDownlink__dummy8__Format : T_Format FeatureSetDownlink__dummy8__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__dummy8__nat__Format FeatureSetDownlink__dummy8__F1 FeatureSetDownlink__dummy8__F2 FeatureSetDownlink__dummy8__F1F2 FeatureSetDownlink__dummy8__F2F1.

Opaque FeatureSetDownlink__dummy8__cond FeatureSetDownlink__dummy8__Format.

Definition FeatureSetDownlink__scellWithoutSSB__Format : T_Format FeatureSetDownlink__scellWithoutSSB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__scellWithoutSSB__nat__Format FeatureSetDownlink__scellWithoutSSB__F1 FeatureSetDownlink__scellWithoutSSB__F2 FeatureSetDownlink__scellWithoutSSB__F1F2 FeatureSetDownlink__scellWithoutSSB__F2F1.

Opaque FeatureSetDownlink__scellWithoutSSB__cond FeatureSetDownlink__scellWithoutSSB__Format.

Definition FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Format : T_Format FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__nat__Format FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F1 FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F2 FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F1F2 FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__F2F1.

Opaque FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__cond FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Format.

Definition FeatureSetDownlink__dummy1__Format : T_Format FeatureSetDownlink__dummy1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__dummy1__nat__Format FeatureSetDownlink__dummy1__F1 FeatureSetDownlink__dummy1__F2 FeatureSetDownlink__dummy1__F1F2 FeatureSetDownlink__dummy1__F2F1.

Opaque FeatureSetDownlink__dummy1__cond FeatureSetDownlink__dummy1__Format.

Definition FeatureSetDownlink__type1_3_CSS__Format : T_Format FeatureSetDownlink__type1_3_CSS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__type1_3_CSS__nat__Format FeatureSetDownlink__type1_3_CSS__F1 FeatureSetDownlink__type1_3_CSS__F2 FeatureSetDownlink__type1_3_CSS__F1F2 FeatureSetDownlink__type1_3_CSS__F2F1.

Opaque FeatureSetDownlink__type1_3_CSS__cond FeatureSetDownlink__type1_3_CSS__Format.

Definition FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Format : T_Format FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__pdcch_MonitoringAnyOccasions__nat__Format FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F1 FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F2 FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F1F2 FeatureSetDownlink__pdcch_MonitoringAnyOccasions__F2F1.

Opaque FeatureSetDownlink__pdcch_MonitoringAnyOccasions__cond FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Format.

Definition FeatureSetDownlink__dummy2__Format : T_Format FeatureSetDownlink__dummy2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__dummy2__nat__Format FeatureSetDownlink__dummy2__F1 FeatureSetDownlink__dummy2__F2 FeatureSetDownlink__dummy2__F1F2 FeatureSetDownlink__dummy2__F2F1.

Opaque FeatureSetDownlink__dummy2__cond FeatureSetDownlink__dummy2__Format.

Definition FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Format : T_Format FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__ue_SpecificUL_DL_Assignment__nat__Format FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F1 FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F2 FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F1F2 FeatureSetDownlink__ue_SpecificUL_DL_Assignment__F2F1.

Opaque FeatureSetDownlink__ue_SpecificUL_DL_Assignment__cond FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Format.

Definition FeatureSetDownlink__searchSpaceSharingCA_DL__Format : T_Format FeatureSetDownlink__searchSpaceSharingCA_DL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__searchSpaceSharingCA_DL__nat__Format FeatureSetDownlink__searchSpaceSharingCA_DL__F1 FeatureSetDownlink__searchSpaceSharingCA_DL__F2 FeatureSetDownlink__searchSpaceSharingCA_DL__F1F2 FeatureSetDownlink__searchSpaceSharingCA_DL__F2F1.

Opaque FeatureSetDownlink__searchSpaceSharingCA_DL__cond FeatureSetDownlink__searchSpaceSharingCA_DL__Format.

Definition FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Format : T_Format FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__timeDurationForQCL__scs_60kHz__nat__Format FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F1 FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F2 FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F1F2 FeatureSetDownlink__timeDurationForQCL__scs_60kHz__F2F1.

Opaque FeatureSetDownlink__timeDurationForQCL__scs_60kHz__cond FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Format.

Definition FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Format : T_Format FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__timeDurationForQCL__scs_120kHz__nat__Format FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F1 FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F2 FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F1F2 FeatureSetDownlink__timeDurationForQCL__scs_120kHz__F2F1.

Opaque FeatureSetDownlink__timeDurationForQCL__scs_120kHz__cond FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Format.


Definition FeatureSetDownlink__timeDurationForQCL__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink__timeDurationForQCL__list.
Definition FeatureSetDownlink__timeDurationForQCL__Format_list : FeatureSetDownlink__timeDurationForQCL__Format_Type :=
  (FeatureSetDownlink__timeDurationForQCL__scs_60kHz__Format, (FeatureSetDownlink__timeDurationForQCL__scs_120kHz__Format, unit_format)).
Definition FeatureSetDownlink__timeDurationForQCL__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink__timeDurationForQCL__list FeatureSetDownlink__timeDurationForQCL__Format_list.
Definition FeatureSetDownlink__timeDurationForQCL__F1 z :=
  (FeatureSetDownlink__timeDurationForQCL__scs_60kHz z, (FeatureSetDownlink__timeDurationForQCL__scs_120kHz z, tt)).
Definition FeatureSetDownlink__timeDurationForQCL__F2 (y : seq_type FeatureSetDownlink__timeDurationForQCL__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSetDownlink__timeDurationForQCL__Type i0 i1
  end.
Lemma FeatureSetDownlink__timeDurationForQCL__F1F2_cond (z : FeatureSetDownlink__timeDurationForQCL__Type)
  : FeatureSetDownlink__timeDurationForQCL__cond z ->
  (seq_cond FeatureSetDownlink__timeDurationForQCL__list (FeatureSetDownlink__timeDurationForQCL__F1 z)).
intro H. unfold FeatureSetDownlink__timeDurationForQCL__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink__timeDurationForQCL__F1F2_cond2 (z : FeatureSetDownlink__timeDurationForQCL__Type)
 : FeatureSetDownlink__timeDurationForQCL__F2 (FeatureSetDownlink__timeDurationForQCL__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink__timeDurationForQCL__F2F1_cond (y : seq_type FeatureSetDownlink__timeDurationForQCL__list)
  : seq_cond FeatureSetDownlink__timeDurationForQCL__list y ->
 (FeatureSetDownlink__timeDurationForQCL__cond (FeatureSetDownlink__timeDurationForQCL__F2 y)) /\  FeatureSetDownlink__timeDurationForQCL__F1 (FeatureSetDownlink__timeDurationForQCL__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink__timeDurationForQCL__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink__timeDurationForQCL__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink__timeDurationForQCL__Format : T_Format FeatureSetDownlink__timeDurationForQCL__Type FeatureSetDownlink__timeDurationForQCL__cond :=
        proj2_format  FeatureSetDownlink__timeDurationForQCL__cond FeatureSetDownlink__timeDurationForQCL__list__Format
    FeatureSetDownlink__timeDurationForQCL__F1 FeatureSetDownlink__timeDurationForQCL__F2 FeatureSetDownlink__timeDurationForQCL__F1F2_cond  FeatureSetDownlink__timeDurationForQCL__F1F2_cond2 FeatureSetDownlink__timeDurationForQCL__F2F1_cond.
Opaque FeatureSetDownlink__timeDurationForQCL__cond FeatureSetDownlink__timeDurationForQCL__Format.

Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Format : T_Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__nat__Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2F1.

Opaque FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Format.

Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Format : T_Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__nat__Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2F1.

Opaque FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Format.

Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Format : T_Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__nat__Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2F1.

Opaque FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Format.

Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Format : T_Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__nat__Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2F1.

Opaque FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Format.


Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Format_list : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Format_Type :=
  (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Format, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Format, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Format, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Format, unit_format)))).
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Format_list.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1 z :=
  (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz z, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz z, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz z, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz z, tt)))).
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F2 (y : seq_type FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Type i0 i1 i2 i3
  end.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1F2_cond (z : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Type)
  : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond z ->
  (seq_cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1 z)).
intro H. unfold FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1F2_cond2 (z : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Type)
 : FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F2 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F2F1_cond (y : seq_type FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list)
  : seq_cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list y ->
 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F2 y)) /\  FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1 (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Format : T_Format FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Type FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond :=
        proj2_format  FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__list__Format
    FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1F2_cond  FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F1F2_cond2 FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__F2F1_cond.
Opaque FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__cond FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Format.

Definition FeatureSetDownlink__dummy4__Format : T_Format FeatureSetDownlink__dummy4__Type FeatureSetDownlink__dummy4__cond := seq_of_format DummyB__Format 1 maxNrofCodebooks FeatureSetDownlink__dummy4__helper1 FeatureSetDownlink__dummy4__helper2.

Opaque FeatureSetDownlink__dummy4__cond FeatureSetDownlink__dummy4__Format.

Definition FeatureSetDownlink__dummy5__Format : T_Format FeatureSetDownlink__dummy5__Type FeatureSetDownlink__dummy5__cond := seq_of_format DummyC__Format 1 maxNrofCodebooks FeatureSetDownlink__dummy5__helper1 FeatureSetDownlink__dummy5__helper2.

Opaque FeatureSetDownlink__dummy5__cond FeatureSetDownlink__dummy5__Format.

Definition FeatureSetDownlink__dummy6__Format : T_Format FeatureSetDownlink__dummy6__Type FeatureSetDownlink__dummy6__cond := seq_of_format DummyD__Format 1 maxNrofCodebooks FeatureSetDownlink__dummy6__helper1 FeatureSetDownlink__dummy6__helper2.

Opaque FeatureSetDownlink__dummy6__cond FeatureSetDownlink__dummy6__Format.

Definition FeatureSetDownlink__dummy7__Format : T_Format FeatureSetDownlink__dummy7__Type FeatureSetDownlink__dummy7__cond := seq_of_format DummyE__Format 1 maxNrofCodebooks FeatureSetDownlink__dummy7__helper1 FeatureSetDownlink__dummy7__helper2.

Opaque FeatureSetDownlink__dummy7__cond FeatureSetDownlink__dummy7__Format.


Definition FeatureSetDownlink__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink__list.
Definition FeatureSetDownlink__Format_list : FeatureSetDownlink__Format_Type :=
  (FeatureSetDownlink__featureSetListPerDownlinkCC__Format, (FreqSeparationClass__Format, (FeatureSetDownlink__scalingFactor__Format, (FeatureSetDownlink__dummy8__Format, (FeatureSetDownlink__scellWithoutSSB__Format, (FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB__Format, (FeatureSetDownlink__dummy1__Format, (FeatureSetDownlink__type1_3_CSS__Format, (FeatureSetDownlink__pdcch_MonitoringAnyOccasions__Format, (FeatureSetDownlink__dummy2__Format, (FeatureSetDownlink__ue_SpecificUL_DL_Assignment__Format, (FeatureSetDownlink__searchSpaceSharingCA_DL__Format, (FeatureSetDownlink__timeDurationForQCL__Format, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot__Format, (DummyA__Format, (FeatureSetDownlink__dummy4__Format, (FeatureSetDownlink__dummy5__Format, (FeatureSetDownlink__dummy6__Format, (FeatureSetDownlink__dummy7__Format, unit_format))))))))))))))))))).
Definition FeatureSetDownlink__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink__list FeatureSetDownlink__Format_list.
Definition FeatureSetDownlink__F1 z :=
  (FeatureSetDownlink__featureSetListPerDownlinkCC z, (FeatureSetDownlink__intraBandFreqSeparationDL z, (FeatureSetDownlink__scalingFactor z, (FeatureSetDownlink__dummy8 z, (FeatureSetDownlink__scellWithoutSSB z, (FeatureSetDownlink__csi_RS_MeasSCellWithoutSSB z, (FeatureSetDownlink__dummy1 z, (FeatureSetDownlink__type1_3_CSS z, (FeatureSetDownlink__pdcch_MonitoringAnyOccasions z, (FeatureSetDownlink__dummy2 z, (FeatureSetDownlink__ue_SpecificUL_DL_Assignment z, (FeatureSetDownlink__searchSpaceSharingCA_DL z, (FeatureSetDownlink__timeDurationForQCL z, (FeatureSetDownlink__pdsch_ProcessingType1_DifferentTB_PerSlot z, (FeatureSetDownlink__dummy3 z, (FeatureSetDownlink__dummy4 z, (FeatureSetDownlink__dummy5 z, (FeatureSetDownlink__dummy6 z, (FeatureSetDownlink__dummy7 z, tt))))))))))))))))))).
Definition FeatureSetDownlink__F2 (y : seq_type FeatureSetDownlink__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, _)))))))))))))))))))=>
    make__FeatureSetDownlink__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18
  end.
Lemma FeatureSetDownlink__F1F2_cond (z : FeatureSetDownlink__Type)
  : FeatureSetDownlink__cond z ->
  (seq_cond FeatureSetDownlink__list (FeatureSetDownlink__F1 z)).
intro H. unfold FeatureSetDownlink__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink__F1F2_cond2 (z : FeatureSetDownlink__Type)
 : FeatureSetDownlink__F2 (FeatureSetDownlink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink__F2F1_cond (y : seq_type FeatureSetDownlink__list)
  : seq_cond FeatureSetDownlink__list y ->
 (FeatureSetDownlink__cond (FeatureSetDownlink__F2 y)) /\  FeatureSetDownlink__F1 (FeatureSetDownlink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink__Format : T_Format FeatureSetDownlink__Type FeatureSetDownlink__cond :=
        proj2_format  FeatureSetDownlink__cond FeatureSetDownlink__list__Format
    FeatureSetDownlink__F1 FeatureSetDownlink__F2 FeatureSetDownlink__F1F2_cond  FeatureSetDownlink__F1F2_cond2 FeatureSetDownlink__F2F1_cond.
Opaque FeatureSetDownlink__cond FeatureSetDownlink__Format.

