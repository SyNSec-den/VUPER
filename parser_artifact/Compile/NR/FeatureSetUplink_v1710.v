Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Type : Set :=
 | FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n1
 | FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n2
 | FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n4
.
Definition FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__cond := (fun (_ : FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Type) => True).
Lemma FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__nat__helper.

Definition FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F1 t :=
  match t with
  | FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n1 => 0
  | FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n2 => 1
  | FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n4 => 2
  end.
Definition FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n1
  | 1 => FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n2
  | 2 => FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n4
  | _ => FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__n1
  end.
Lemma FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F1F2 : forall x : FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Type, (FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F1 x <= 2) /\ FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F2 (FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F1 (FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Type : Set :=
 | FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n1
 | FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n2
 | FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n3
 | FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n4
.
Definition FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__cond := (fun (_ : FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Type) => True).
Lemma FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__nat__helper.

Definition FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F1 t :=
  match t with
  | FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n1 => 0
  | FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n2 => 1
  | FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n3 => 2
  | FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n4 => 3
  end.
Definition FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n1
  | 1 => FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n2
  | 2 => FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n3
  | 3 => FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n4
  | _ => FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__n1
  end.
Lemma FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F1F2 : forall x : FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Type, (FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F1 x <= 3) /\ FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F2 (FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F2F1 : forall (y : nat) (H : y <= 3), FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F1 (FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Type : Set :=
 | FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf0_2
 | FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf1_3_4
 | FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf0_4
.
Definition FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__cond := (fun (_ : FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Type) => True).
Lemma FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__nat__helper.

Definition FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F1 t :=
  match t with
  | FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf0_2 => 0
  | FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf1_3_4 => 1
  | FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf0_4 => 2
  end.
Definition FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf0_2
  | 1 => FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf1_3_4
  | 2 => FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf0_4
  | _ => FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__pf0_2
  end.
Lemma FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F1F2 : forall x : FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Type, (FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F1 x <= 2) /\ FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F2 (FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F1 (FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Type : Set :=
 | FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__supported
.
Definition FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__cond := (fun (_ : FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Type) => True).
Lemma FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__nat__helper.

Definition FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F1 t :=
  match t with
  | FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__supported => 0
  end.
Definition FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__supported
  | _ => FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__supported
  end.
Lemma FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F1F2 : forall x : FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Type, (FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F1 x <= 0) /\ FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F2 (FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F1 (FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Type : Set :=
 | FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__supported
.
Definition FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__cond := (fun (_ : FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Type) => True).
Lemma FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__nat__helper.

Definition FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F1 t :=
  match t with
  | FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__supported => 0
  end.
Definition FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__supported
  | _ => FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__supported
  end.
Lemma FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F1F2 : forall x : FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Type, (FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F1 x <= 0) /\ FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F2 (FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F1 (FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Type : Set :=
 | FeatureSetUplink_v1710__srs_OneAP_SRS_r17__supported
.
Definition FeatureSetUplink_v1710__srs_OneAP_SRS_r17__cond := (fun (_ : FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Type) => True).
Lemma FeatureSetUplink_v1710__srs_OneAP_SRS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1710__srs_OneAP_SRS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink_v1710__srs_OneAP_SRS_r17__nat__helper.

Definition FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F1 t :=
  match t with
  | FeatureSetUplink_v1710__srs_OneAP_SRS_r17__supported => 0
  end.
Definition FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1710__srs_OneAP_SRS_r17__supported
  | _ => FeatureSetUplink_v1710__srs_OneAP_SRS_r17__supported
  end.
Lemma FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F1F2 : forall x : FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Type, (FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F1 x <= 0) /\ FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F2 (FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F1 (FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Type : Set :=
 | FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc1dot5
 | FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc2
 | FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc3
.
Definition FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__cond := (fun (_ : FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Type) => True).
Lemma FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__nat__helper.

Definition FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F1 t :=
  match t with
  | FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc1dot5 => 0
  | FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc2 => 1
  | FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc3 => 2
  end.
Definition FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc1dot5
  | 1 => FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc2
  | 2 => FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc3
  | _ => FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__pc1dot5
  end.
Lemma FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F1F2 : forall x : FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Type, (FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F1 x <= 2) /\ FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F2 (FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F1 (FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Type : Set :=
 | FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__supported
.
Definition FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__cond := (fun (_ : FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Type) => True).
Lemma FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__nat__helper.

Definition FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F1 t :=
  match t with
  | FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__supported => 0
  end.
Definition FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F2 n :=
  match n with
  | 0 => FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__supported
  | _ => FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__supported
  end.
Lemma FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F1F2 : forall x : FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Type, (FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F1 x <= 0) /\ FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F2 (FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F1 (FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetUplink_v1710__Type : Set :=
  make__FeatureSetUplink_v1710__Type {
    FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17 : option FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Type ;
    FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17 : option FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Type ;
    FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17 : option FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Type ;
    FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17 : option FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Type ;
    FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17 : option FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Type ;
    FeatureSetUplink_v1710__srs_OneAP_SRS_r17 : option FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Type ;
    FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17 : option FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Type ;
    FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17 : option FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Type ;
}.
Definition FeatureSetUplink_v1710__list := (
 Opt FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Type FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__cond ::
 Opt FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Type FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__cond ::
 Opt FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Type FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__cond ::
 Opt FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Type FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__cond ::
 Opt FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Type FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__cond ::
 Opt FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Type FeatureSetUplink_v1710__srs_OneAP_SRS_r17__cond ::
 Opt FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Type FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__cond ::
 Opt FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Type FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__cond ::
 nil).
Definition FeatureSetUplink_v1710__cond z := 
  opt_cond FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__cond (FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17 z) /\
  opt_cond FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__cond (FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17 z) /\
  opt_cond FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__cond (FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17 z) /\
  opt_cond FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__cond (FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17 z) /\
  opt_cond FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__cond (FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17 z) /\
  opt_cond FeatureSetUplink_v1710__srs_OneAP_SRS_r17__cond (FeatureSetUplink_v1710__srs_OneAP_SRS_r17 z) /\
  opt_cond FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__cond (FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17 z) /\
  opt_cond FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__cond (FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17 z) /\
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
Definition FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Format : T_Format FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__nat__Format FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F1 FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F2 FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F1F2 FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__F2F1.

Opaque FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__cond FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Format.

Definition FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Format : T_Format FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__nat__Format FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F1 FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F2 FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F1F2 FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__F2F1.

Opaque FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__cond FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Format.

Definition FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Format : T_Format FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__nat__Format FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F1 FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F2 FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F1F2 FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__F2F1.

Opaque FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__cond FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Format.

Definition FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Format : T_Format FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__nat__Format FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F1 FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F2 FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F1F2 FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__F2F1.

Opaque FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__cond FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Format.

Definition FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Format : T_Format FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__nat__Format FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F1 FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F2 FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F1F2 FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__F2F1.

Opaque FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__cond FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Format.

Definition FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Format : T_Format FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1710__srs_OneAP_SRS_r17__nat__Format FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F1 FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F2 FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F1F2 FeatureSetUplink_v1710__srs_OneAP_SRS_r17__F2F1.

Opaque FeatureSetUplink_v1710__srs_OneAP_SRS_r17__cond FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Format.

Definition FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Format : T_Format FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__nat__Format FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F1 FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F2 FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F1F2 FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__F2F1.

Opaque FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__cond FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Format.

Definition FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Format : T_Format FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__nat__Format FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F1 FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F2 FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F1F2 FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__F2F1.

Opaque FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__cond FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Format.


Definition FeatureSetUplink_v1710__Format_Type := Eval cbn in seq_format_prod FeatureSetUplink_v1710__list.
Definition FeatureSetUplink_v1710__Format_list : FeatureSetUplink_v1710__Format_Type :=
  (FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17__Format, (FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17__Format, (FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17__Format, (FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17__Format, (FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17__Format, (FeatureSetUplink_v1710__srs_OneAP_SRS_r17__Format, (FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17__Format, (FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17__Format, unit_format)))))))).
Definition FeatureSetUplink_v1710__list__Format := (*Eval compute in *) seq_format FeatureSetUplink_v1710__list FeatureSetUplink_v1710__Format_list.
Definition FeatureSetUplink_v1710__F1 z :=
  (FeatureSetUplink_v1710__mTRP_PUSCH_TypeA_CB_r17 z, (FeatureSetUplink_v1710__mTRP_PUSCH_RepetitionTypeA_r17 z, (FeatureSetUplink_v1710__mTRP_PUCCH_IntraSlot_r17 z, (FeatureSetUplink_v1710__srs_AntennaSwitching2SP_1Periodic_r17 z, (FeatureSetUplink_v1710__srs_ExtensionAperiodicSRS_r17 z, (FeatureSetUplink_v1710__srs_OneAP_SRS_r17 z, (FeatureSetUplink_v1710__ue_PowerClassPerBandPerBC_r17 z, (FeatureSetUplink_v1710__tx_Support_UL_GapFR2_r17 z, tt)))))))).
Definition FeatureSetUplink_v1710__F2 (y : seq_type FeatureSetUplink_v1710__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__FeatureSetUplink_v1710__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma FeatureSetUplink_v1710__F1F2_cond (z : FeatureSetUplink_v1710__Type)
  : FeatureSetUplink_v1710__cond z ->
  (seq_cond FeatureSetUplink_v1710__list (FeatureSetUplink_v1710__F1 z)).
intro H. unfold FeatureSetUplink_v1710__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplink_v1710__F1F2_cond2 (z : FeatureSetUplink_v1710__Type)
 : FeatureSetUplink_v1710__F2 (FeatureSetUplink_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplink_v1710__F2F1_cond (y : seq_type FeatureSetUplink_v1710__list)
  : seq_cond FeatureSetUplink_v1710__list y ->
 (FeatureSetUplink_v1710__cond (FeatureSetUplink_v1710__F2 y)) /\  FeatureSetUplink_v1710__F1 (FeatureSetUplink_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplink_v1710__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplink_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplink_v1710__Format : T_Format FeatureSetUplink_v1710__Type FeatureSetUplink_v1710__cond :=
        proj2_format  FeatureSetUplink_v1710__cond FeatureSetUplink_v1710__list__Format
    FeatureSetUplink_v1710__F1 FeatureSetUplink_v1710__F2 FeatureSetUplink_v1710__F1F2_cond  FeatureSetUplink_v1710__F1F2_cond2 FeatureSetUplink_v1710__F2F1_cond.
Opaque FeatureSetUplink_v1710__cond FeatureSetUplink_v1710__Format.

