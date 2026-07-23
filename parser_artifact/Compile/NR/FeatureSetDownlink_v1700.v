Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Type : Set :=
 | FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p4
 | FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p75
 | FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p8
.
Definition FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__cond := (fun (_ : FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__nat__helper.

Definition FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p4 => 0
  | FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p75 => 1
  | FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p8 => 2
  end.
Definition FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p4
  | 1 => FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p75
  | 2 => FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p8
  | _ => FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__f0p4
  end.
Lemma FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F1F2 : forall x : FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Type, (FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F1 x <= 2) /\ FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F2 (FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F1 (FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Type : Set :=
 | FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__s56
 | FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__s112
.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__cond := (fun (_ : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Type) => True).
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__nat__helper.

Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__s56 => 0
  | FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__s112 => 1
  end.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__s56
  | 1 => FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__s112
  | _ => FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__s56
  end.
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F1F2 : forall x : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Type, (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F1 x <= 1) /\ FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F2 (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F2F1 : forall (y : nat) (H : y <= 1), FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F1 (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Type : Set :=
 | FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__s112
 | FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__s224
.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__cond := (fun (_ : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Type) => True).
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__nat__helper.

Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__s112 => 0
  | FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__s224 => 1
  end.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__s112
  | 1 => FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__s224
  | _ => FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__s112
  end.
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F1F2 : forall x : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Type, (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F1 x <= 1) /\ FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F2 (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F2F1 : forall (y : nat) (H : y <= 1), FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F1 (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Type : Set :=
  make__FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Type {
    FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz : option FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Type ;
    FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz : option FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Type ;
}.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list := (
 Opt FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Type FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__cond ::
 Opt FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Type FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__cond ::
 nil).
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond z := 
  opt_cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__cond (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz z) /\
  opt_cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__cond (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz z) /\
  True.

Inductive FeatureSetDownlink_v1700__sfn_SchemeA_r17__Type : Set :=
 | FeatureSetDownlink_v1700__sfn_SchemeA_r17__supported
.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_r17__cond := (fun (_ : FeatureSetDownlink_v1700__sfn_SchemeA_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__sfn_SchemeA_r17__nat__helper.

Definition FeatureSetDownlink_v1700__sfn_SchemeA_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__sfn_SchemeA_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__sfn_SchemeA_r17__supported
  | _ => FeatureSetDownlink_v1700__sfn_SchemeA_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_r17__F1F2 : forall x : FeatureSetDownlink_v1700__sfn_SchemeA_r17__Type, (FeatureSetDownlink_v1700__sfn_SchemeA_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__sfn_SchemeA_r17__F2 (FeatureSetDownlink_v1700__sfn_SchemeA_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__sfn_SchemeA_r17__F1 (FeatureSetDownlink_v1700__sfn_SchemeA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Type : Set :=
 | FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__supported
.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__cond := (fun (_ : FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__nat__helper.

Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__supported
  | _ => FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F1F2 : forall x : FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Type, (FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F2 (FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F1 (FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Type : Set :=
 | FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__supported
.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__cond := (fun (_ : FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__nat__helper.

Definition FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__supported
  | _ => FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F1F2 : forall x : FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Type, (FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F2 (FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F1 (FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Type : Set :=
 | FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__supported
.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__cond := (fun (_ : FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__nat__helper.

Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__supported
  | _ => FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F1F2 : forall x : FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Type, (FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F2 (FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F1 (FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__sfn_SchemeB_r17__Type : Set :=
 | FeatureSetDownlink_v1700__sfn_SchemeB_r17__supported
.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_r17__cond := (fun (_ : FeatureSetDownlink_v1700__sfn_SchemeB_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__sfn_SchemeB_r17__nat__helper.

Definition FeatureSetDownlink_v1700__sfn_SchemeB_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__sfn_SchemeB_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__sfn_SchemeB_r17__supported
  | _ => FeatureSetDownlink_v1700__sfn_SchemeB_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_r17__F1F2 : forall x : FeatureSetDownlink_v1700__sfn_SchemeB_r17__Type, (FeatureSetDownlink_v1700__sfn_SchemeB_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__sfn_SchemeB_r17__F2 (FeatureSetDownlink_v1700__sfn_SchemeB_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__sfn_SchemeB_r17__F1 (FeatureSetDownlink_v1700__sfn_SchemeB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Type : Set :=
 | FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__supported
.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__cond := (fun (_ : FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__nat__helper.

Definition FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__supported
  | _ => FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F1F2 : forall x : FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Type, (FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F2 (FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F1 (FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Type : Set :=
 | FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__supported
.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__cond := (fun (_ : FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__nat__helper.

Definition FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__supported
  | _ => FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F1F2 : forall x : FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Type, (FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F2 (FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F1 (FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PDCCH_RepetitionParameters_r17.

Opaque PDCCH_RepetitionParameters_r17__cond PDCCH_RepetitionParameters_r17__Format.

Require Import NR.PDCCH_RepetitionParameters_r17.

Opaque PDCCH_RepetitionParameters_r17__cond PDCCH_RepetitionParameters_r17__Format.

Require Import NR.PDCCH_RepetitionParameters_r17.

Opaque PDCCH_RepetitionParameters_r17__cond PDCCH_RepetitionParameters_r17__Format.

Require Import NR.PDCCH_RepetitionParameters_r17.

Opaque PDCCH_RepetitionParameters_r17__cond PDCCH_RepetitionParameters_r17__Format.

Record FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Type : Set :=
  make__FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Type {
    FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_15kHz_r17 : option PDCCH_RepetitionParameters_r17__Type ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_30kHz_r17 : option PDCCH_RepetitionParameters_r17__Type ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_60kHz_r17 : option PDCCH_RepetitionParameters_r17__Type ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_120kHz_r17 : option PDCCH_RepetitionParameters_r17__Type ;
}.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list := (
 Opt PDCCH_RepetitionParameters_r17__Type PDCCH_RepetitionParameters_r17__cond ::
 Opt PDCCH_RepetitionParameters_r17__Type PDCCH_RepetitionParameters_r17__cond ::
 Opt PDCCH_RepetitionParameters_r17__Type PDCCH_RepetitionParameters_r17__cond ::
 Opt PDCCH_RepetitionParameters_r17__Type PDCCH_RepetitionParameters_r17__cond ::
 nil).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond z := 
  opt_cond PDCCH_RepetitionParameters_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_15kHz_r17 z) /\
  opt_cond PDCCH_RepetitionParameters_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_30kHz_r17 z) /\
  opt_cond PDCCH_RepetitionParameters_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_60kHz_r17 z) /\
  opt_cond PDCCH_RepetitionParameters_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_120kHz_r17 z) /\
  True.

Require Import NR.PDCCH_RepetitionParameters_r17.

Opaque PDCCH_RepetitionParameters_r17__cond PDCCH_RepetitionParameters_r17__Format.

Require Import NR.PDCCH_RepetitionParameters_r17.

Opaque PDCCH_RepetitionParameters_r17__cond PDCCH_RepetitionParameters_r17__Format.

Record FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Type : Set :=
  make__FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Type {
    FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__scs_15kHz_r17 : option PDCCH_RepetitionParameters_r17__Type ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__scs_30kHz_r17 : option PDCCH_RepetitionParameters_r17__Type ;
}.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list := (
 Opt PDCCH_RepetitionParameters_r17__Type PDCCH_RepetitionParameters_r17__cond ::
 Opt PDCCH_RepetitionParameters_r17__Type PDCCH_RepetitionParameters_r17__cond ::
 nil).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond z := 
  opt_cond PDCCH_RepetitionParameters_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__scs_15kHz_r17 z) /\
  opt_cond PDCCH_RepetitionParameters_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__scs_30kHz_r17 z) /\
  True.

Inductive FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Type : Set :=
 | FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__supported
.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__cond := (fun (_ : FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__nat__helper.

Definition FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__supported
  | _ => FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F1F2 : forall x : FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Type, (FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F2 (FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F1 (FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Type : Set :=
 | FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__supported
.
Definition FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__cond := (fun (_ : FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__nat__helper.

Definition FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__supported => 0
  end.
Definition FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__supported
  | _ => FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__supported
  end.
Lemma FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F1F2 : forall x : FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Type, (FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F1 x <= 0) /\ FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F2 (FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F1 (FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F2 y) = y. enum_solve H y. Qed.

Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__helper1 : (2 <= 3)%Z.  lia. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__helper2 : to_bit_sz (Z.to_nat (3 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__Type := Z.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__cond := (fun z => (2 <= z <= 3)%Z).
Inductive FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Type : Set :=
 | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n1
 | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n2
 | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n3
 | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n5
 | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n10
 | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n20
 | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n40
.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__cond := (fun (_ : FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Type) => True).
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__nat__helper.

Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F1 t :=
  match t with
  | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n1 => 0
  | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n2 => 1
  | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n3 => 2
  | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n5 => 3
  | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n10 => 4
  | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n20 => 5
  | FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n40 => 6
  end.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F2 n :=
  match n with
  | 0 => FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n1
  | 1 => FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n2
  | 2 => FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n3
  | 3 => FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n5
  | 4 => FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n10
  | 5 => FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n20
  | 6 => FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n40
  | _ => FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__n1
  end.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F1F2 : forall x : FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Type, (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F1 x <= 6) /\ FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F2 (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F2F1 : forall (y : nat) (H : y <= 6), FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F1 (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Type : Set :=
  make__FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Type {
    FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17 : Z ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17 : FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Type ;
}.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list := (
 Nor Z FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__cond ::
 Nor FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Type FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__cond ::
 nil).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond z := 
  FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17 z) /\
  FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17 z) /\
  True.

Record FeatureSetDownlink_v1700__Type : Set :=
  make__FeatureSetDownlink_v1700__Type {
    FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17 : option FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Type ;
    FeatureSetDownlink_v1700__timeDurationForQCL_v1710 : option FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Type ;
    FeatureSetDownlink_v1700__sfn_SchemeA_r17 : option FeatureSetDownlink_v1700__sfn_SchemeA_r17__Type ;
    FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17 : option FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Type ;
    FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17 : option FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Type ;
    FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17 : option FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Type ;
    FeatureSetDownlink_v1700__sfn_SchemeB_r17 : option FeatureSetDownlink_v1700__sfn_SchemeB_r17__Type ;
    FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17 : option FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Type ;
    FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17 : option FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Type ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17 : option FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Type ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17 : option FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Type ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17 : option FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Type ;
    FeatureSetDownlink_v1700__dynamicMulticastPCell_r17 : option FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Type ;
    FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17 : option FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Type ;
}.
Definition FeatureSetDownlink_v1700__list := (
 Opt FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Type FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__cond ::
 Opt FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Type FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond ::
 Opt FeatureSetDownlink_v1700__sfn_SchemeA_r17__Type FeatureSetDownlink_v1700__sfn_SchemeA_r17__cond ::
 Opt FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Type FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__cond ::
 Opt FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Type FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__cond ::
 Opt FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Type FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__cond ::
 Opt FeatureSetDownlink_v1700__sfn_SchemeB_r17__Type FeatureSetDownlink_v1700__sfn_SchemeB_r17__cond ::
 Opt FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Type FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__cond ::
 Opt FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Type FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__cond ::
 Opt FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Type FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond ::
 Opt FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Type FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond ::
 Opt FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Type FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__cond ::
 Opt FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Type FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__cond ::
 Opt FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Type FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond ::
 nil).
Definition FeatureSetDownlink_v1700__cond z := 
  opt_cond FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__cond (FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond (FeatureSetDownlink_v1700__timeDurationForQCL_v1710 z) /\
  opt_cond FeatureSetDownlink_v1700__sfn_SchemeA_r17__cond (FeatureSetDownlink_v1700__sfn_SchemeA_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__cond (FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__cond (FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__cond (FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__sfn_SchemeB_r17__cond (FeatureSetDownlink_v1700__sfn_SchemeB_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__cond (FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__cond (FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__cond (FeatureSetDownlink_v1700__dynamicMulticastPCell_r17 z) /\
  opt_cond FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17 z) /\
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
Definition FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Format : T_Format FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__nat__Format FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F1 FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F2 FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F1F2 FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__F2F1.

Opaque FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__cond FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Format.

Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Format : T_Format FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__nat__Format FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F1 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F2 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F1F2 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__F2F1.

Opaque FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Format.

Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Format : T_Format FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__nat__Format FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F1 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F2 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F1F2 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__F2F1.

Opaque FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Format.


Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Format_list : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Format_Type :=
  (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz__Format, (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz__Format, unit_format)).
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Format_list.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1 z :=
  (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_480kHz z, (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__scs_960kHz z, tt)).
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F2 (y : seq_type FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Type i0 i1
  end.
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1F2_cond (z : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Type)
  : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond z ->
  (seq_cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1 z)).
intro H. unfold FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1F2_cond2 (z : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Type)
 : FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F2 (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F2F1_cond (y : seq_type FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list)
  : seq_cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list y ->
 (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F2 y)) /\  FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1 (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Format : T_Format FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Type FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond :=
        proj2_format  FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__list__Format
    FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F2 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1F2_cond  FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F1F2_cond2 FeatureSetDownlink_v1700__timeDurationForQCL_v1710__F2F1_cond.
Opaque FeatureSetDownlink_v1700__timeDurationForQCL_v1710__cond FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Format.

Definition FeatureSetDownlink_v1700__sfn_SchemeA_r17__Format : T_Format FeatureSetDownlink_v1700__sfn_SchemeA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__sfn_SchemeA_r17__nat__Format FeatureSetDownlink_v1700__sfn_SchemeA_r17__F1 FeatureSetDownlink_v1700__sfn_SchemeA_r17__F2 FeatureSetDownlink_v1700__sfn_SchemeA_r17__F1F2 FeatureSetDownlink_v1700__sfn_SchemeA_r17__F2F1.

Opaque FeatureSetDownlink_v1700__sfn_SchemeA_r17__cond FeatureSetDownlink_v1700__sfn_SchemeA_r17__Format.

Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Format : T_Format FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__nat__Format FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F1 FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F2 FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F1F2 FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__F2F1.

Opaque FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__cond FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Format.

Definition FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Format : T_Format FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__nat__Format FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F1 FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F2 FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F1F2 FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__F2F1.

Opaque FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__cond FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Format.

Definition FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Format : T_Format FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__nat__Format FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F1 FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F2 FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F1F2 FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__F2F1.

Opaque FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__cond FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Format.

Definition FeatureSetDownlink_v1700__sfn_SchemeB_r17__Format : T_Format FeatureSetDownlink_v1700__sfn_SchemeB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__sfn_SchemeB_r17__nat__Format FeatureSetDownlink_v1700__sfn_SchemeB_r17__F1 FeatureSetDownlink_v1700__sfn_SchemeB_r17__F2 FeatureSetDownlink_v1700__sfn_SchemeB_r17__F1F2 FeatureSetDownlink_v1700__sfn_SchemeB_r17__F2F1.

Opaque FeatureSetDownlink_v1700__sfn_SchemeB_r17__cond FeatureSetDownlink_v1700__sfn_SchemeB_r17__Format.

Definition FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Format : T_Format FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__nat__Format FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F1 FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F2 FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F1F2 FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__F2F1.

Opaque FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__cond FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Format.

Definition FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Format : T_Format FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__nat__Format FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F1 FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F2 FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F1F2 FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__F2F1.

Opaque FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__cond FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Format.


Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Format_list : FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Format_Type :=
  (PDCCH_RepetitionParameters_r17__Format, (PDCCH_RepetitionParameters_r17__Format, (PDCCH_RepetitionParameters_r17__Format, (PDCCH_RepetitionParameters_r17__Format, unit_format)))).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Format_list.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1 z :=
  (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_15kHz_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_30kHz_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_60kHz_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__scs_120kHz_r17 z, tt)))).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F2 (y : seq_type FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Type i0 i1 i2 i3
  end.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1F2_cond (z : FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Type)
  : FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond z ->
  (seq_cond FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1 z)).
intro H. unfold FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1F2_cond2 (z : FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Type)
 : FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F2 (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F2F1_cond (y : seq_type FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list)
  : seq_cond FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list y ->
 (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F2 y)) /\  FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1 (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Format : T_Format FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Type FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond :=
        proj2_format  FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__list__Format
    FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1 FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F2 FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1F2_cond  FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F1F2_cond2 FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__F2F1_cond.
Opaque FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Format.


Definition FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Format_list : FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Format_Type :=
  (PDCCH_RepetitionParameters_r17__Format, (PDCCH_RepetitionParameters_r17__Format, unit_format)).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Format_list.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1 z :=
  (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__scs_15kHz_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__scs_30kHz_r17 z, tt)).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F2 (y : seq_type FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Type i0 i1
  end.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1F2_cond (z : FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Type)
  : FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond z ->
  (seq_cond FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1 z)).
intro H. unfold FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1F2_cond2 (z : FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Type)
 : FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F2 (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F2F1_cond (y : seq_type FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list)
  : seq_cond FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list y ->
 (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F2 y)) /\  FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1 (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Format : T_Format FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Type FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond :=
        proj2_format  FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__list__Format
    FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1 FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F2 FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1F2_cond  FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F1F2_cond2 FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__F2F1_cond.
Opaque FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Format.

Definition FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Format : T_Format FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__nat__Format FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F1 FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F2 FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F1F2 FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__F2F1.

Opaque FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Format.

Definition FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Format : T_Format FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__nat__Format FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F1 FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F2 FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F1F2 FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__F2F1.

Opaque FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__cond FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Format.

Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__Format : T_Format Z FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__cond :=
 ranged_int_format (2) (3) FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__helper1 FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__helper2.

Opaque FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__Format.

Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Format : T_Format FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__nat__Format FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F1 FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F2 FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F1F2 FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__F2F1.

Opaque FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Format.


Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Format_list : FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Format_Type :=
  (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17__Format, (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17__Format, unit_format)).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Format_list.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1 z :=
  (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__numBD_twoPDCCH_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__maxNumOverlaps_r17 z, tt)).
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F2 (y : seq_type FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Type i0 i1
  end.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1F2_cond (z : FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Type)
  : FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond z ->
  (seq_cond FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1 z)).
intro H. unfold FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1F2_cond2 (z : FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Type)
 : FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F2 (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F2F1_cond (y : seq_type FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list)
  : seq_cond FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list y ->
 (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F2 y)) /\  FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1 (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Format : T_Format FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Type FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond :=
        proj2_format  FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__list__Format
    FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1 FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F2 FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1F2_cond  FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F1F2_cond2 FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__F2F1_cond.
Opaque FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__cond FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Format.


Definition FeatureSetDownlink_v1700__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlink_v1700__list.
Definition FeatureSetDownlink_v1700__Format_list : FeatureSetDownlink_v1700__Format_Type :=
  (FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17__Format, (FeatureSetDownlink_v1700__timeDurationForQCL_v1710__Format, (FeatureSetDownlink_v1700__sfn_SchemeA_r17__Format, (FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17__Format, (FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17__Format, (FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17__Format, (FeatureSetDownlink_v1700__sfn_SchemeB_r17__Format, (FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17__Format, (FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17__Format, (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17__Format, (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17__Format, (FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17__Format, (FeatureSetDownlink_v1700__dynamicMulticastPCell_r17__Format, (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17__Format, unit_format)))))))))))))).
Definition FeatureSetDownlink_v1700__list__Format := (*Eval compute in *) seq_format FeatureSetDownlink_v1700__list FeatureSetDownlink_v1700__Format_list.
Definition FeatureSetDownlink_v1700__F1 z :=
  (FeatureSetDownlink_v1700__scalingFactor_1024QAM_FR1_r17 z, (FeatureSetDownlink_v1700__timeDurationForQCL_v1710 z, (FeatureSetDownlink_v1700__sfn_SchemeA_r17 z, (FeatureSetDownlink_v1700__sfn_SchemeA_PDCCH_only_r17 z, (FeatureSetDownlink_v1700__sfn_SchemeA_DynamicSwitching_r17 z, (FeatureSetDownlink_v1700__sfn_SchemeA_PDSCH_only_r17 z, (FeatureSetDownlink_v1700__sfn_SchemeB_r17 z, (FeatureSetDownlink_v1700__sfn_SchemeB_DynamicSwitching_r17 z, (FeatureSetDownlink_v1700__sfn_SchemeB_PDSCH_only_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_Case2_1SpanGap_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_legacyMonitoring_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_multiDCI_multiTRP_r17 z, (FeatureSetDownlink_v1700__dynamicMulticastPCell_r17 z, (FeatureSetDownlink_v1700__mTRP_PDCCH_Repetition_r17 z, tt)))))))))))))).
Definition FeatureSetDownlink_v1700__F2 (y : seq_type FeatureSetDownlink_v1700__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, _))))))))))))))=>
    make__FeatureSetDownlink_v1700__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  end.
Lemma FeatureSetDownlink_v1700__F1F2_cond (z : FeatureSetDownlink_v1700__Type)
  : FeatureSetDownlink_v1700__cond z ->
  (seq_cond FeatureSetDownlink_v1700__list (FeatureSetDownlink_v1700__F1 z)).
intro H. unfold FeatureSetDownlink_v1700__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__F1F2_cond2 (z : FeatureSetDownlink_v1700__Type)
 : FeatureSetDownlink_v1700__F2 (FeatureSetDownlink_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlink_v1700__F2F1_cond (y : seq_type FeatureSetDownlink_v1700__list)
  : seq_cond FeatureSetDownlink_v1700__list y ->
 (FeatureSetDownlink_v1700__cond (FeatureSetDownlink_v1700__F2 y)) /\  FeatureSetDownlink_v1700__F1 (FeatureSetDownlink_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlink_v1700__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlink_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlink_v1700__Format : T_Format FeatureSetDownlink_v1700__Type FeatureSetDownlink_v1700__cond :=
        proj2_format  FeatureSetDownlink_v1700__cond FeatureSetDownlink_v1700__list__Format
    FeatureSetDownlink_v1700__F1 FeatureSetDownlink_v1700__F2 FeatureSetDownlink_v1700__F1F2_cond  FeatureSetDownlink_v1700__F1F2_cond2 FeatureSetDownlink_v1700__F2F1_cond.
Opaque FeatureSetDownlink_v1700__cond FeatureSetDownlink_v1700__Format.

