Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Type : Set :=
 | CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__supported
.
Definition CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__cond := (fun (_ : CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Type) => True).
Lemma CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__nat__helper.

Definition CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__supported
  | _ => CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__supported
  end.
Lemma CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F1F2 : forall x : CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Type, (CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F2 (CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F1 (CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Type : Set :=
 | CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__supported
.
Definition CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__cond := (fun (_ : CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Type) => True).
Lemma CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__nat__helper.

Definition CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__supported
  | _ => CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__supported
  end.
Lemma CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F1F2 : forall x : CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Type, (CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F2 (CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F1 (CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Type : Set :=
 | CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
 | CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly
 | CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup
.
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__cond := (fun (_ : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Type) => True).
Lemma CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__nat__helper.

Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__primaryGroupOnly => 0
  | CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly => 1
  | CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup => 2
  end.
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
  | 1 => CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly
  | 2 => CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup
  | _ => CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
  end.
Lemma CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F1F2 : forall x : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Type, (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F1 x <= 2) /\ CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F2 (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F1 (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PUCCH_Group_Config_r17.

Opaque PUCCH_Group_Config_r17__cond PUCCH_Group_Config_r17__Format.

Record CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Type : Set :=
  make__CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Type {
    CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17 : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Type ;
    CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_Config_r17 : PUCCH_Group_Config_r17__Type ;
}.
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list := (
 Nor CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Type CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__cond ::
 Nor PUCCH_Group_Config_r17__Type PUCCH_Group_Config_r17__cond ::
 nil).
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond z := 
  CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__cond (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17 z) /\
  PUCCH_Group_Config_r17__cond (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_Config_r17 z) /\
  True.

Require Import NR.TwoPUCCH_Grp_Configurations_r17.

Opaque TwoPUCCH_Grp_Configurations_r17__cond TwoPUCCH_Grp_Configurations_r17__Format.

Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__Type := list TwoPUCCH_Grp_Configurations_r17__Type.

Lemma CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__helper1 : (0 <= 1 <= maxTwoPUCCH_Grp_ConfigList_r17)%Z. unfold maxTwoPUCCH_Grp_ConfigList_r17.
 lia. Qed.
Lemma CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__helper2 : to_bit_sz (Z.to_nat (maxTwoPUCCH_Grp_ConfigList_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxTwoPUCCH_Grp_ConfigList_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__cond (z : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxTwoPUCCH_Grp_ConfigList_r17)%Z /\ (list_and TwoPUCCH_Grp_Configurations_r17__cond z) .

Inductive CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Type : Set :=
 | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
 | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly
 | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup
.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__cond := (fun (_ : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Type) => True).
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__nat__helper.

Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__primaryGroupOnly => 0
  | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly => 1
  | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup => 2
  end.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
  | 1 => CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly
  | 2 => CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup
  | _ => CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
  end.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F1F2 : forall x : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Type, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F1 x <= 2) /\ CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F2 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F1 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PUCCH_Group_Config_r17.

Opaque PUCCH_Group_Config_r17__cond PUCCH_Group_Config_r17__Format.

Record CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Type : Set :=
  make__CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Type {
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17 : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Type ;
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_Config_r17 : PUCCH_Group_Config_r17__Type ;
}.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list := (
 Nor CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__cond ::
 Nor PUCCH_Group_Config_r17__Type PUCCH_Group_Config_r17__cond ::
 nil).
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond z := 
  CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17 z) /\
  PUCCH_Group_Config_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_Config_r17 z) /\
  True.

Inductive CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Type : Set :=
 | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
 | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly
 | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup
.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__cond := (fun (_ : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Type) => True).
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__nat__helper.

Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__primaryGroupOnly => 0
  | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly => 1
  | CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup => 2
  end.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
  | 1 => CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__secondaryGroupOnly
  | 2 => CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__eitherPrimaryOrSecondaryGroup
  | _ => CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__primaryGroupOnly
  end.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F1F2 : forall x : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Type, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F1 x <= 2) /\ CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F2 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F1 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PUCCH_Group_Config_r17.

Opaque PUCCH_Group_Config_r17__cond PUCCH_Group_Config_r17__Format.

Record CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Type : Set :=
  make__CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Type {
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17 : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Type ;
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_Config_r17 : PUCCH_Group_Config_r17__Type ;
}.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list := (
 Nor CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__cond ::
 Nor PUCCH_Group_Config_r17__Type PUCCH_Group_Config_r17__cond ::
 nil).
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond z := 
  CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17 z) /\
  PUCCH_Group_Config_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_Config_r17 z) /\
  True.

Require Import NR.TwoPUCCH_Grp_Configurations_r17.

Opaque TwoPUCCH_Grp_Configurations_r17__cond TwoPUCCH_Grp_Configurations_r17__Format.

Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__Type := list TwoPUCCH_Grp_Configurations_r17__Type.

Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__helper1 : (0 <= 1 <= maxTwoPUCCH_Grp_ConfigList_r17)%Z. unfold maxTwoPUCCH_Grp_ConfigList_r17.
 lia. Qed.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__helper2 : to_bit_sz (Z.to_nat (maxTwoPUCCH_Grp_ConfigList_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxTwoPUCCH_Grp_ConfigList_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__cond (z : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxTwoPUCCH_Grp_ConfigList_r17)%Z /\ (list_and TwoPUCCH_Grp_Configurations_r17__cond z) .

Require Import NR.TwoPUCCH_Grp_Configurations_r17.

Opaque TwoPUCCH_Grp_Configurations_r17__cond TwoPUCCH_Grp_Configurations_r17__Format.

Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__Type := list TwoPUCCH_Grp_Configurations_r17__Type.

Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__helper1 : (0 <= 1 <= maxTwoPUCCH_Grp_ConfigList_r17)%Z. unfold maxTwoPUCCH_Grp_ConfigList_r17.
 lia. Qed.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__helper2 : to_bit_sz (Z.to_nat (maxTwoPUCCH_Grp_ConfigList_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxTwoPUCCH_Grp_ConfigList_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__cond (z : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxTwoPUCCH_Grp_ConfigList_r17)%Z /\ (list_and TwoPUCCH_Grp_Configurations_r17__cond z) .

Inductive CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Type : Set :=
 | CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__supported
.
Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__cond := (fun (_ : CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Type) => True).
Lemma CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__nat__helper.

Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__supported
  | _ => CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__supported
  end.
Lemma CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F1F2 : forall x : CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Type, (CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F2 (CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F1 (CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Type : Set :=
 | CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__supported
.
Definition CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__cond := (fun (_ : CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Type) => True).
Lemma CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__nat__helper.

Definition CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__supported
  | _ => CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__supported
  end.
Lemma CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F1F2 : forall x : CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Type, (CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F2 (CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F1 (CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Type : Set :=
 | CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__supported
.
Definition CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__cond := (fun (_ : CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Type) => True).
Lemma CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__nat__helper.

Definition CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__supported
  | _ => CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__supported
  end.
Lemma CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F1F2 : forall x : CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Type, (CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F2 (CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F1 (CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Type : Set :=
 | CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__supported
.
Definition CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__cond := (fun (_ : CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Type) => True).
Lemma CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__nat__helper.

Definition CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__supported
  | _ => CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__supported
  end.
Lemma CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F1F2 : forall x : CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Type, (CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F2 (CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F1 (CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Type : Set :=
 | CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__supported
.
Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__cond := (fun (_ : CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Type) => True).
Lemma CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__nat__helper.

Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__supported
  | _ => CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__supported
  end.
Lemma CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F1F2 : forall x : CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Type, (CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F2 (CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F1 (CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Type : Set :=
 | CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__supported
.
Definition CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__cond := (fun (_ : CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Type) => True).
Lemma CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__nat__helper.

Definition CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__supported
  | _ => CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__supported
  end.
Lemma CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F1F2 : forall x : CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Type, (CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F2 (CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F1 (CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__higherPowerLimit_r17__Type : Set :=
 | CA_ParametersNR_v1720__higherPowerLimit_r17__supported
.
Definition CA_ParametersNR_v1720__higherPowerLimit_r17__cond := (fun (_ : CA_ParametersNR_v1720__higherPowerLimit_r17__Type) => True).
Lemma CA_ParametersNR_v1720__higherPowerLimit_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__higherPowerLimit_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__higherPowerLimit_r17__nat__helper.

Definition CA_ParametersNR_v1720__higherPowerLimit_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__higherPowerLimit_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__higherPowerLimit_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__higherPowerLimit_r17__supported
  | _ => CA_ParametersNR_v1720__higherPowerLimit_r17__supported
  end.
Lemma CA_ParametersNR_v1720__higherPowerLimit_r17__F1F2 : forall x : CA_ParametersNR_v1720__higherPowerLimit_r17__Type, (CA_ParametersNR_v1720__higherPowerLimit_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__higherPowerLimit_r17__F2 (CA_ParametersNR_v1720__higherPowerLimit_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__higherPowerLimit_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__higherPowerLimit_r17__F1 (CA_ParametersNR_v1720__higherPowerLimit_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Type : Set :=
 | CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__supported
.
Definition CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__cond := (fun (_ : CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Type) => True).
Lemma CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__nat__helper.

Definition CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__supported => 0
  end.
Definition CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__supported
  | _ => CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__supported
  end.
Lemma CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F1F2 : forall x : CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Type, (CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F1 x <= 0) /\ CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F2 (CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F1 (CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F2 y) = y. enum_solve H y. Qed.

Lemma CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__helper1 : (4 <= 16)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__helper2 : to_bit_sz (Z.to_nat (16 - 4)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 4))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__Type := Z.
Definition CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__cond := (fun z => (4 <= z <= 16)%Z).
Require Import NR.PDCCH_BlindDetectionMCG_SCG_r17.

Opaque PDCCH_BlindDetectionMCG_SCG_r17__cond PDCCH_BlindDetectionMCG_SCG_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__Type := list PDCCH_BlindDetectionMCG_SCG_r17__Type.

Lemma CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__helper1 : (0 <= 1 <= maxNrofPdcch_BlindDetection_r17)%Z. unfold maxNrofPdcch_BlindDetection_r17.
 lia. Qed.
Lemma CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPdcch_BlindDetection_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPdcch_BlindDetection_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__cond (z : CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPdcch_BlindDetection_r17)%Z /\ (list_and PDCCH_BlindDetectionMCG_SCG_r17__cond z) .

Require Import NR.PDCCH_BlindDetectionMixed_r17.

Opaque PDCCH_BlindDetectionMixed_r17__cond PDCCH_BlindDetectionMixed_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__Type := list PDCCH_BlindDetectionMixed_r17__Type.

Lemma CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__helper1 : (0 <= 1 <= maxNrofPdcch_BlindDetection_r17)%Z. unfold maxNrofPdcch_BlindDetection_r17.
 lia. Qed.
Lemma CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPdcch_BlindDetection_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPdcch_BlindDetection_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__cond (z : CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPdcch_BlindDetection_r17)%Z /\ (list_and PDCCH_BlindDetectionMixed_r17__cond z) .

Require Import NR.PDCCH_BlindDetectionMixed_r17.

Opaque PDCCH_BlindDetectionMixed_r17__cond PDCCH_BlindDetectionMixed_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__Type := list PDCCH_BlindDetectionMixed_r17__Type.

Lemma CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__helper1 : (0 <= 1 <= maxNrofPdcch_BlindDetection_r17)%Z. unfold maxNrofPdcch_BlindDetection_r17.
 lia. Qed.
Lemma CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPdcch_BlindDetection_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPdcch_BlindDetection_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__cond (z : CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPdcch_BlindDetection_r17)%Z /\ (list_and PDCCH_BlindDetectionMixed_r17__cond z) .

Require Import NR.PDCCH_BlindDetectionMixed1_r17.

Opaque PDCCH_BlindDetectionMixed1_r17__cond PDCCH_BlindDetectionMixed1_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__Type := list PDCCH_BlindDetectionMixed1_r17__Type.

Lemma CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__helper1 : (0 <= 1 <= maxNrofPdcch_BlindDetection_r17)%Z. unfold maxNrofPdcch_BlindDetection_r17.
 lia. Qed.
Lemma CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPdcch_BlindDetection_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPdcch_BlindDetection_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__cond (z : CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPdcch_BlindDetection_r17)%Z /\ (list_and PDCCH_BlindDetectionMixed1_r17__cond z) .

Record CA_ParametersNR_v1720__Type : Set :=
  make__CA_ParametersNR_v1720__Type {
    CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17 : option CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Type ;
    CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17 : option CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Type ;
    CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17 : option CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Type ;
    CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17 : option CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__Type ;
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17 : option CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Type ;
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17 : option CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Type ;
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17 : option CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__Type ;
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17 : option CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__Type ;
    CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17 : option CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Type ;
    CA_ParametersNR_v1720__ptp_Retx_Multicast_r17 : option CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Type ;
    CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17 : option CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Type ;
    CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17 : option CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Type ;
    CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17 : option CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Type ;
    CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17 : option CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Type ;
    CA_ParametersNR_v1720__higherPowerLimit_r17 : option CA_ParametersNR_v1720__higherPowerLimit_r17__Type ;
    CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17 : option CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Type ;
    CA_ParametersNR_v1720__pdcch_MonitoringCA_r17 : option Z ;
    CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17 : option CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__Type ;
    CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17 : option CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__Type ;
    CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17 : option CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__Type ;
    CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17 : option CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__Type ;
}.
Definition CA_ParametersNR_v1720__list := (
 Opt CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Type CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__cond ::
 Opt CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Type CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__cond ::
 Opt CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Type CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond ::
 Opt CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__Type CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__cond ::
 Opt CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond ::
 Opt CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond ::
 Opt CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__cond ::
 Opt CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__cond ::
 Opt CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Type CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__cond ::
 Opt CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Type CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__cond ::
 Opt CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Type CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__cond ::
 Opt CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Type CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__cond ::
 Opt CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Type CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__cond ::
 Opt CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Type CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__cond ::
 Opt CA_ParametersNR_v1720__higherPowerLimit_r17__Type CA_ParametersNR_v1720__higherPowerLimit_r17__cond ::
 Opt CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Type CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__cond ::
 Opt Z CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__cond ::
 Opt CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__Type CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__cond ::
 Opt CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__Type CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__cond ::
 Opt CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__Type CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__cond ::
 Opt CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__Type CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__cond ::
 nil).
Definition CA_ParametersNR_v1720__cond z := 
  opt_cond CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__cond (CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17 z) /\
  opt_cond CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__cond (CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17 z) /\
  opt_cond CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17 z) /\
  opt_cond CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__cond (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17 z) /\
  opt_cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17 z) /\
  opt_cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17 z) /\
  opt_cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17 z) /\
  opt_cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17 z) /\
  opt_cond CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__cond (CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17 z) /\
  opt_cond CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__cond (CA_ParametersNR_v1720__ptp_Retx_Multicast_r17 z) /\
  opt_cond CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__cond (CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17 z) /\
  opt_cond CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__cond (CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17 z) /\
  opt_cond CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__cond (CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17 z) /\
  opt_cond CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__cond (CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17 z) /\
  opt_cond CA_ParametersNR_v1720__higherPowerLimit_r17__cond (CA_ParametersNR_v1720__higherPowerLimit_r17 z) /\
  opt_cond CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__cond (CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17 z) /\
  opt_cond CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__cond (CA_ParametersNR_v1720__pdcch_MonitoringCA_r17 z) /\
  opt_cond CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__cond (CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17 z) /\
  opt_cond CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__cond (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17 z) /\
  opt_cond CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__cond (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17 z) /\
  opt_cond CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__cond (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17 z) /\
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
Definition CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Format : T_Format CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__nat__Format CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F1 CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F2 CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F1F2 CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__F2F1.

Opaque CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__cond CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Format.

Definition CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Format : T_Format CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__nat__Format CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F1 CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F2 CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F1F2 CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__F2F1.

Opaque CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__cond CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Format.

Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Format : T_Format CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__nat__Format CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F1 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F2 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F1F2 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__F2F1.

Opaque CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__cond CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Format.


Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list.
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Format_list : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Format_Type :=
  (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17__Format, (PUCCH_Group_Config_r17__Format, unit_format)).
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Format_list.
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1 z :=
  (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_r17 z, (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__pucch_Group_Config_r17 z, tt)).
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F2 (y : seq_type CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Type i0 i1
  end.
Lemma CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1F2_cond (z : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Type)
  : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond z ->
  (seq_cond CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1 z)).
intro H. unfold CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1F2_cond2 (z : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Type)
 : CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F2 (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F2F1_cond (y : seq_type CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list)
  : seq_cond CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list y ->
 (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F2 y)) /\  CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1 (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Format : T_Format CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Type CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond :=
        proj2_format  CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__list__Format
    CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F2 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1F2_cond  CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F1F2_cond2 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__F2F1_cond.
Opaque CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__cond CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Format.

Definition CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__Format : T_Format CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__Type CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__cond := seq_of_format TwoPUCCH_Grp_Configurations_r17__Format 1 maxTwoPUCCH_Grp_ConfigList_r17 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__helper1 CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__helper2.

Opaque CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__cond CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__Format.

Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Format : T_Format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__nat__Format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F1 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F1F2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__F2F1.

Opaque CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Format.


Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Format_list : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Format_Type :=
  (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17__Format, (PUCCH_Group_Config_r17__Format, unit_format)).
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Format_list.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1 z :=
  (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_r17 z, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__pucch_Group_Config_r17 z, tt)).
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F2 (y : seq_type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Type i0 i1
  end.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1F2_cond (z : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Type)
  : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond z ->
  (seq_cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1 z)).
intro H. unfold CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1F2_cond2 (z : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Type)
 : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F2 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F2F1_cond (y : seq_type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list)
  : seq_cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list y ->
 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F2 y)) /\  CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Format : T_Format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond :=
        proj2_format  CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__list__Format
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1F2_cond  CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F1F2_cond2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__F2F1_cond.
Opaque CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Format.

Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Format : T_Format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__nat__Format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F1 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F1F2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__F2F1.

Opaque CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Format.


Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Format_list : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Format_Type :=
  (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17__Format, (PUCCH_Group_Config_r17__Format, unit_format)).
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Format_list.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1 z :=
  (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_r17 z, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__pucch_Group_Config_r17 z, tt)).
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F2 (y : seq_type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Type i0 i1
  end.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1F2_cond (z : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Type)
  : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond z ->
  (seq_cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1 z)).
intro H. unfold CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1F2_cond2 (z : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Type)
 : CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F2 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F2F1_cond (y : seq_type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list)
  : seq_cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list y ->
 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F2 y)) /\  CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1 (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Format : T_Format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond :=
        proj2_format  CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__list__Format
    CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1F2_cond  CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F1F2_cond2 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__F2F1_cond.
Opaque CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Format.

Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__Format : T_Format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__cond := seq_of_format TwoPUCCH_Grp_Configurations_r17__Format 1 maxTwoPUCCH_Grp_ConfigList_r17 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__helper1 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__helper2.

Opaque CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__Format.

Definition CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__Format : T_Format CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__Type CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__cond := seq_of_format TwoPUCCH_Grp_Configurations_r17__Format 1 maxTwoPUCCH_Grp_ConfigList_r17 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__helper1 CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__helper2.

Opaque CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__cond CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__Format.

Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Format : T_Format CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__nat__Format CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F1 CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F2 CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F1F2 CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__F2F1.

Opaque CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__cond CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Format.

Definition CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Format : T_Format CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__nat__Format CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F1 CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F2 CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F1F2 CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__F2F1.

Opaque CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__cond CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Format.

Definition CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Format : T_Format CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__nat__Format CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F1 CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F2 CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F1F2 CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__F2F1.

Opaque CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__cond CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Format.

Definition CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Format : T_Format CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__nat__Format CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F1 CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F2 CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F1F2 CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__F2F1.

Opaque CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__cond CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Format.

Definition CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Format : T_Format CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__nat__Format CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F1 CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F2 CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F1F2 CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__F2F1.

Opaque CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__cond CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Format.

Definition CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Format : T_Format CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__nat__Format CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F1 CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F2 CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F1F2 CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__F2F1.

Opaque CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__cond CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Format.

Definition CA_ParametersNR_v1720__higherPowerLimit_r17__Format : T_Format CA_ParametersNR_v1720__higherPowerLimit_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__higherPowerLimit_r17__nat__Format CA_ParametersNR_v1720__higherPowerLimit_r17__F1 CA_ParametersNR_v1720__higherPowerLimit_r17__F2 CA_ParametersNR_v1720__higherPowerLimit_r17__F1F2 CA_ParametersNR_v1720__higherPowerLimit_r17__F2F1.

Opaque CA_ParametersNR_v1720__higherPowerLimit_r17__cond CA_ParametersNR_v1720__higherPowerLimit_r17__Format.

Definition CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Format : T_Format CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__nat__Format CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F1 CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F2 CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F1F2 CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__F2F1.

Opaque CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__cond CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__Format : T_Format Z CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__cond :=
 ranged_int_format (4) (16) CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__helper1 CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__helper2.

Opaque CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__cond CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__Format : T_Format CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__Type CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__cond := seq_of_format PDCCH_BlindDetectionMCG_SCG_r17__Format 1 maxNrofPdcch_BlindDetection_r17 CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__helper1 CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__helper2.

Opaque CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__cond CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__Format : T_Format CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__Type CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__cond := seq_of_format PDCCH_BlindDetectionMixed_r17__Format 1 maxNrofPdcch_BlindDetection_r17 CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__helper1 CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__helper2.

Opaque CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__cond CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__Format : T_Format CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__Type CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__cond := seq_of_format PDCCH_BlindDetectionMixed_r17__Format 1 maxNrofPdcch_BlindDetection_r17 CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__helper1 CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__helper2.

Opaque CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__cond CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__Format.

Definition CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__Format : T_Format CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__Type CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__cond := seq_of_format PDCCH_BlindDetectionMixed1_r17__Format 1 maxNrofPdcch_BlindDetection_r17 CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__helper1 CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__helper2.

Opaque CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__cond CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__Format.


Definition CA_ParametersNR_v1720__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1720__list.
Definition CA_ParametersNR_v1720__Format_list : CA_ParametersNR_v1720__Format_Type :=
  (CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17__Format, (CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17__Format, (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17__Format, (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17__Format, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17__Format, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17__Format, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17__Format, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17__Format, (CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17__Format, (CA_ParametersNR_v1720__ptp_Retx_Multicast_r17__Format, (CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17__Format, (CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17__Format, (CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17__Format, (CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17__Format, (CA_ParametersNR_v1720__higherPowerLimit_r17__Format, (CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17__Format, (CA_ParametersNR_v1720__pdcch_MonitoringCA_r17__Format, (CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17__Format, (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17__Format, (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17__Format, (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17__Format, unit_format))))))))))))))))))))).
Definition CA_ParametersNR_v1720__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1720__list CA_ParametersNR_v1720__Format_list.
Definition CA_ParametersNR_v1720__F1 z :=
  (CA_ParametersNR_v1720__parallelTxSRS_PUCCH_PUSCH_intraBand_r17 z, (CA_ParametersNR_v1720__parallelTxPRACH_SRS_PUCCH_PUSCH_intraBand_r17 z, (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchSingleGroup_r17 z, (CA_ParametersNR_v1720__semiStaticPUCCH_CellSwitchTwoGroups_r17 z, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthSingleGroup_r17 z, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthSingleGroup_r17 z, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchSameLengthTwoGroups_r17 z, (CA_ParametersNR_v1720__dynamicPUCCH_CellSwitchDiffLengthTwoGroups_r17 z, (CA_ParametersNR_v1720__ack_NACK_FeedbackForMulticast_r17 z, (CA_ParametersNR_v1720__ptp_Retx_Multicast_r17 z, (CA_ParametersNR_v1720__nack_OnlyFeedbackForMulticast_r17 z, (CA_ParametersNR_v1720__nack_OnlyFeedbackSpecificResourceForMulticast_r17 z, (CA_ParametersNR_v1720__ack_NACK_FeedbackForSPS_Multicast_r17 z, (CA_ParametersNR_v1720__ptp_Retx_SPS_Multicast_r17 z, (CA_ParametersNR_v1720__higherPowerLimit_r17 z, (CA_ParametersNR_v1720__parallelTxMsgA_SRS_PUCCH_PUSCH_intraBand_r17 z, (CA_ParametersNR_v1720__pdcch_MonitoringCA_r17 z, (CA_ParametersNR_v1720__pdcch_BlindDetectionMCG_SCG_List_r17 z, (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList1_r17 z, (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList2_r17 z, (CA_ParametersNR_v1720__pdcch_BlindDetectionMixedList3_r17 z, tt))))))))))))))))))))).
Definition CA_ParametersNR_v1720__F2 (y : seq_type CA_ParametersNR_v1720__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, _)))))))))))))))))))))=>
    make__CA_ParametersNR_v1720__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20
  end.
Lemma CA_ParametersNR_v1720__F1F2_cond (z : CA_ParametersNR_v1720__Type)
  : CA_ParametersNR_v1720__cond z ->
  (seq_cond CA_ParametersNR_v1720__list (CA_ParametersNR_v1720__F1 z)).
intro H. unfold CA_ParametersNR_v1720__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1720__F1F2_cond2 (z : CA_ParametersNR_v1720__Type)
 : CA_ParametersNR_v1720__F2 (CA_ParametersNR_v1720__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1720__F2F1_cond (y : seq_type CA_ParametersNR_v1720__list)
  : seq_cond CA_ParametersNR_v1720__list y ->
 (CA_ParametersNR_v1720__cond (CA_ParametersNR_v1720__F2 y)) /\  CA_ParametersNR_v1720__F1 (CA_ParametersNR_v1720__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1720__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1720__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1720__Format : T_Format CA_ParametersNR_v1720__Type CA_ParametersNR_v1720__cond :=
        proj2_format  CA_ParametersNR_v1720__cond CA_ParametersNR_v1720__list__Format
    CA_ParametersNR_v1720__F1 CA_ParametersNR_v1720__F2 CA_ParametersNR_v1720__F1F2_cond  CA_ParametersNR_v1720__F1F2_cond2 CA_ParametersNR_v1720__F2F1_cond.
Opaque CA_ParametersNR_v1720__cond CA_ParametersNR_v1720__Format.

