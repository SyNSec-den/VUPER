Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MAC_ParametersCommon__lcp_Restriction__Type : Set :=
 | MAC_ParametersCommon__lcp_Restriction__supported
.
Definition MAC_ParametersCommon__lcp_Restriction__cond := (fun (_ : MAC_ParametersCommon__lcp_Restriction__Type) => True).
Lemma MAC_ParametersCommon__lcp_Restriction__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__lcp_Restriction__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__lcp_Restriction__nat__helper.

Definition MAC_ParametersCommon__lcp_Restriction__F1 t :=
  match t with
  | MAC_ParametersCommon__lcp_Restriction__supported => 0
  end.
Definition MAC_ParametersCommon__lcp_Restriction__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__lcp_Restriction__supported
  | _ => MAC_ParametersCommon__lcp_Restriction__supported
  end.
Lemma MAC_ParametersCommon__lcp_Restriction__F1F2 : forall x : MAC_ParametersCommon__lcp_Restriction__Type, (MAC_ParametersCommon__lcp_Restriction__F1 x <= 0) /\ MAC_ParametersCommon__lcp_Restriction__F2 (MAC_ParametersCommon__lcp_Restriction__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__lcp_Restriction__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__lcp_Restriction__F1 (MAC_ParametersCommon__lcp_Restriction__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__dummy__Type : Set :=
 | MAC_ParametersCommon__dummy__supported
.
Definition MAC_ParametersCommon__dummy__cond := (fun (_ : MAC_ParametersCommon__dummy__Type) => True).
Lemma MAC_ParametersCommon__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__dummy__nat__helper.

Definition MAC_ParametersCommon__dummy__F1 t :=
  match t with
  | MAC_ParametersCommon__dummy__supported => 0
  end.
Definition MAC_ParametersCommon__dummy__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__dummy__supported
  | _ => MAC_ParametersCommon__dummy__supported
  end.
Lemma MAC_ParametersCommon__dummy__F1F2 : forall x : MAC_ParametersCommon__dummy__Type, (MAC_ParametersCommon__dummy__F1 x <= 0) /\ MAC_ParametersCommon__dummy__F2 (MAC_ParametersCommon__dummy__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__dummy__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__dummy__F1 (MAC_ParametersCommon__dummy__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__lch_ToSCellRestriction__Type : Set :=
 | MAC_ParametersCommon__lch_ToSCellRestriction__supported
.
Definition MAC_ParametersCommon__lch_ToSCellRestriction__cond := (fun (_ : MAC_ParametersCommon__lch_ToSCellRestriction__Type) => True).
Lemma MAC_ParametersCommon__lch_ToSCellRestriction__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__lch_ToSCellRestriction__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__lch_ToSCellRestriction__nat__helper.

Definition MAC_ParametersCommon__lch_ToSCellRestriction__F1 t :=
  match t with
  | MAC_ParametersCommon__lch_ToSCellRestriction__supported => 0
  end.
Definition MAC_ParametersCommon__lch_ToSCellRestriction__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__lch_ToSCellRestriction__supported
  | _ => MAC_ParametersCommon__lch_ToSCellRestriction__supported
  end.
Lemma MAC_ParametersCommon__lch_ToSCellRestriction__F1F2 : forall x : MAC_ParametersCommon__lch_ToSCellRestriction__Type, (MAC_ParametersCommon__lch_ToSCellRestriction__F1 x <= 0) /\ MAC_ParametersCommon__lch_ToSCellRestriction__F2 (MAC_ParametersCommon__lch_ToSCellRestriction__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__lch_ToSCellRestriction__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__lch_ToSCellRestriction__F1 (MAC_ParametersCommon__lch_ToSCellRestriction__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext0O__recommendedBitRate__Type : Set :=
 | MAC_ParametersCommon__ext0O__recommendedBitRate__supported
.
Definition MAC_ParametersCommon__ext0O__recommendedBitRate__cond := (fun (_ : MAC_ParametersCommon__ext0O__recommendedBitRate__Type) => True).
Lemma MAC_ParametersCommon__ext0O__recommendedBitRate__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext0O__recommendedBitRate__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext0O__recommendedBitRate__nat__helper.

Definition MAC_ParametersCommon__ext0O__recommendedBitRate__F1 t :=
  match t with
  | MAC_ParametersCommon__ext0O__recommendedBitRate__supported => 0
  end.
Definition MAC_ParametersCommon__ext0O__recommendedBitRate__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext0O__recommendedBitRate__supported
  | _ => MAC_ParametersCommon__ext0O__recommendedBitRate__supported
  end.
Lemma MAC_ParametersCommon__ext0O__recommendedBitRate__F1F2 : forall x : MAC_ParametersCommon__ext0O__recommendedBitRate__Type, (MAC_ParametersCommon__ext0O__recommendedBitRate__F1 x <= 0) /\ MAC_ParametersCommon__ext0O__recommendedBitRate__F2 (MAC_ParametersCommon__ext0O__recommendedBitRate__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext0O__recommendedBitRate__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext0O__recommendedBitRate__F1 (MAC_ParametersCommon__ext0O__recommendedBitRate__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Type : Set :=
 | MAC_ParametersCommon__ext0O__recommendedBitRateQuery__supported
.
Definition MAC_ParametersCommon__ext0O__recommendedBitRateQuery__cond := (fun (_ : MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Type) => True).
Lemma MAC_ParametersCommon__ext0O__recommendedBitRateQuery__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext0O__recommendedBitRateQuery__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext0O__recommendedBitRateQuery__nat__helper.

Definition MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F1 t :=
  match t with
  | MAC_ParametersCommon__ext0O__recommendedBitRateQuery__supported => 0
  end.
Definition MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext0O__recommendedBitRateQuery__supported
  | _ => MAC_ParametersCommon__ext0O__recommendedBitRateQuery__supported
  end.
Lemma MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F1F2 : forall x : MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Type, (MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F1 x <= 0) /\ MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F2 (MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F1 (MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F2 y) = y. enum_solve H y. Qed.

Record MAC_ParametersCommon__ext0O__Type : Set :=
  make__MAC_ParametersCommon__ext0O__Type {
    MAC_ParametersCommon__ext0O__recommendedBitRate : option MAC_ParametersCommon__ext0O__recommendedBitRate__Type ;
    MAC_ParametersCommon__ext0O__recommendedBitRateQuery : option MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Type ;
}.
Definition MAC_ParametersCommon__ext0O__list := (
 Opt MAC_ParametersCommon__ext0O__recommendedBitRate__Type MAC_ParametersCommon__ext0O__recommendedBitRate__cond ::
 Opt MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Type MAC_ParametersCommon__ext0O__recommendedBitRateQuery__cond ::
 nil).
Definition MAC_ParametersCommon__ext0O__cond z := 
  opt_cond MAC_ParametersCommon__ext0O__recommendedBitRate__cond (MAC_ParametersCommon__ext0O__recommendedBitRate z) /\
  opt_cond MAC_ParametersCommon__ext0O__recommendedBitRateQuery__cond (MAC_ParametersCommon__ext0O__recommendedBitRateQuery z) /\
  True.

Definition MAC_ParametersCommon__ext0__Type := MAC_ParametersCommon__ext0O__Type.
Definition MAC_ParametersCommon__ext0__cond := MAC_ParametersCommon__ext0O__cond.

Inductive MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__supported
.
Definition MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__supported
  | _ => MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Type, (MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F2 (MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F1 (MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__supported
.
Definition MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__supported
  | _ => MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Type, (MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F2 (MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F1 (MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__autonomousTransmission_r16__supported
.
Definition MAC_ParametersCommon__ext1O__autonomousTransmission_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__autonomousTransmission_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__autonomousTransmission_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__autonomousTransmission_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__autonomousTransmission_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__autonomousTransmission_r16__supported
  | _ => MAC_ParametersCommon__ext1O__autonomousTransmission_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Type, (MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F2 (MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F1 (MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__supported
.
Definition MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__supported
  | _ => MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Type, (MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F2 (MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F1 (MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__supported
.
Definition MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__supported
  | _ => MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Type, (MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F2 (MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F1 (MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__supported
.
Definition MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__supported
  | _ => MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Type, (MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F2 (MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F1 (MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__singlePHR_P_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__singlePHR_P_r16__supported
.
Definition MAC_ParametersCommon__ext1O__singlePHR_P_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__singlePHR_P_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__singlePHR_P_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__singlePHR_P_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__singlePHR_P_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__singlePHR_P_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__singlePHR_P_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__singlePHR_P_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__singlePHR_P_r16__supported
  | _ => MAC_ParametersCommon__ext1O__singlePHR_P_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__singlePHR_P_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__singlePHR_P_r16__Type, (MAC_ParametersCommon__ext1O__singlePHR_P_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__singlePHR_P_r16__F2 (MAC_ParametersCommon__ext1O__singlePHR_P_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__singlePHR_P_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__singlePHR_P_r16__F1 (MAC_ParametersCommon__ext1O__singlePHR_P_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__supported
.
Definition MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__supported
  | _ => MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Type, (MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F2 (MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F1 (MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__supported
.
Definition MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__supported
  | _ => MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Type, (MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F2 (MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F1 (MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Type : Set :=
 | MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__supported
.
Definition MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__cond := (fun (_ : MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Type) => True).
Lemma MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__nat__helper.

Definition MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__supported
  | _ => MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__supported
  end.
Lemma MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F1F2 : forall x : MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Type, (MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F2 (MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F1 (MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F2 y) = y. enum_solve H y. Qed.

Record MAC_ParametersCommon__ext1O__Type : Set :=
  make__MAC_ParametersCommon__ext1O__Type {
    MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16 : option MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Type ;
    MAC_ParametersCommon__ext1O__preEmptiveBSR_r16 : option MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Type ;
    MAC_ParametersCommon__ext1O__autonomousTransmission_r16 : option MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Type ;
    MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16 : option MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Type ;
    MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16 : option MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Type ;
    MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16 : option MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Type ;
    MAC_ParametersCommon__ext1O__singlePHR_P_r16 : option MAC_ParametersCommon__ext1O__singlePHR_P_r16__Type ;
    MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16 : option MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Type ;
    MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16 : option MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Type ;
    MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16 : option MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Type ;
}.
Definition MAC_ParametersCommon__ext1O__list := (
 Opt MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Type MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Type MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Type MAC_ParametersCommon__ext1O__autonomousTransmission_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Type MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Type MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Type MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__singlePHR_P_r16__Type MAC_ParametersCommon__ext1O__singlePHR_P_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Type MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Type MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__cond ::
 Opt MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Type MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__cond ::
 nil).
Definition MAC_ParametersCommon__ext1O__cond z := 
  opt_cond MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__cond (MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__cond (MAC_ParametersCommon__ext1O__preEmptiveBSR_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__autonomousTransmission_r16__cond (MAC_ParametersCommon__ext1O__autonomousTransmission_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__cond (MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__cond (MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__cond (MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__singlePHR_P_r16__cond (MAC_ParametersCommon__ext1O__singlePHR_P_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__cond (MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__cond (MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16 z) /\
  opt_cond MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__cond (MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16 z) /\
  True.

Definition MAC_ParametersCommon__ext1__Type := MAC_ParametersCommon__ext1O__Type.
Definition MAC_ParametersCommon__ext1__cond := MAC_ParametersCommon__ext1O__cond.

Inductive MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Type : Set :=
 | MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__supported
.
Definition MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__cond := (fun (_ : MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Type) => True).
Lemma MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__nat__helper.

Definition MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__supported
  | _ => MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__supported
  end.
Lemma MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F1F2 : forall x : MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Type, (MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F2 (MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F1 (MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F2 y) = y. enum_solve H y. Qed.

Record MAC_ParametersCommon__ext2O__Type : Set :=
  make__MAC_ParametersCommon__ext2O__Type {
    MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16 : option MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Type ;
}.
Definition MAC_ParametersCommon__ext2O__list := (
 Opt MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Type MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__cond ::
 nil).
Definition MAC_ParametersCommon__ext2O__cond z := 
  opt_cond MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__cond (MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16 z) /\
  True.

Definition MAC_ParametersCommon__ext2__Type := MAC_ParametersCommon__ext2O__Type.
Definition MAC_ParametersCommon__ext2__cond := MAC_ParametersCommon__ext2O__cond.

Inductive MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Type : Set :=
 | MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__supported
.
Definition MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__cond := (fun (_ : MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Type) => True).
Lemma MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__nat__helper.

Definition MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F1 t :=
  match t with
  | MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__supported => 0
  end.
Definition MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__supported
  | _ => MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__supported
  end.
Lemma MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F1F2 : forall x : MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Type, (MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F1 x <= 0) /\ MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F2 (MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F1 (MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F2 y) = y. enum_solve H y. Qed.

Record MAC_ParametersCommon__ext3O__Type : Set :=
  make__MAC_ParametersCommon__ext3O__Type {
    MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16 : option MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Type ;
}.
Definition MAC_ParametersCommon__ext3O__list := (
 Opt MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Type MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__cond ::
 nil).
Definition MAC_ParametersCommon__ext3O__cond z := 
  opt_cond MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__cond (MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16 z) /\
  True.

Definition MAC_ParametersCommon__ext3__Type := MAC_ParametersCommon__ext3O__Type.
Definition MAC_ParametersCommon__ext3__cond := MAC_ParametersCommon__ext3O__cond.

Inductive MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__supported
.
Definition MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__supported
  | _ => MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Type, (MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F2 (MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F1 (MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__supported
.
Definition MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__supported
  | _ => MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Type, (MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F2 (MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F1 (MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__supported
.
Definition MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__supported
  | _ => MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Type, (MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F2 (MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F1 (MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__supported
.
Definition MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__supported
  | _ => MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Type, (MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F2 (MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F1 (MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__supported
.
Definition MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__supported
  | _ => MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Type, (MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F2 (MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F1 (MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__survivalTime_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__survivalTime_r17__supported
.
Definition MAC_ParametersCommon__ext4O__survivalTime_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__survivalTime_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__survivalTime_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__survivalTime_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__survivalTime_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__survivalTime_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__survivalTime_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__survivalTime_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__survivalTime_r17__supported
  | _ => MAC_ParametersCommon__ext4O__survivalTime_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__survivalTime_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__survivalTime_r17__Type, (MAC_ParametersCommon__ext4O__survivalTime_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__survivalTime_r17__F2 (MAC_ParametersCommon__ext4O__survivalTime_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__survivalTime_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__survivalTime_r17__F1 (MAC_ParametersCommon__ext4O__survivalTime_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__supported
.
Definition MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__supported
  | _ => MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Type, (MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F2 (MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F1 (MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__supported
.
Definition MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__supported
  | _ => MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Type, (MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F2 (MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F1 (MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__supported
.
Definition MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__supported
  | _ => MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Type, (MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F2 (MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F1 (MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__supported
.
Definition MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__supported
  | _ => MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Type, (MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F2 (MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F1 (MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__supported
.
Definition MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__supported
  | _ => MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Type, (MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F2 (MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F1 (MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__supported
.
Definition MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__supported
  | _ => MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Type, (MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F2 (MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F1 (MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Type : Set :=
 | MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__supported
.
Definition MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__cond := (fun (_ : MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Type) => True).
Lemma MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__nat__helper.

Definition MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F1 t :=
  match t with
  | MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__supported => 0
  end.
Definition MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F2 n :=
  match n with
  | 0 => MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__supported
  | _ => MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__supported
  end.
Lemma MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F1F2 : forall x : MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Type, (MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F1 x <= 0) /\ MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F2 (MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F1 x) = x. imp_solve. Qed.
Lemma MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F2F1 : forall (y : nat) (H : y <= 0), MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F1 (MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F2 y) = y. enum_solve H y. Qed.

Record MAC_ParametersCommon__ext4O__Type : Set :=
  make__MAC_ParametersCommon__ext4O__Type {
    MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17 : option MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Type ;
    MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17 : option MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Type ;
    MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17 : option MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Type ;
    MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17 : option MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Type ;
    MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17 : option MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Type ;
    MAC_ParametersCommon__ext4O__survivalTime_r17 : option MAC_ParametersCommon__ext4O__survivalTime_r17__Type ;
    MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17 : option MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Type ;
    MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17 : option MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Type ;
    MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17 : option MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Type ;
    MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17 : option MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Type ;
    MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17 : option MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Type ;
    MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17 : option MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Type ;
    MAC_ParametersCommon__ext4O__lastTransmissionUL_r17 : option MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Type ;
}.
Definition MAC_ParametersCommon__ext4O__list := (
 Opt MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Type MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Type MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Type MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Type MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Type MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__survivalTime_r17__Type MAC_ParametersCommon__ext4O__survivalTime_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Type MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Type MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Type MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Type MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Type MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Type MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__cond ::
 Opt MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Type MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__cond ::
 nil).
Definition MAC_ParametersCommon__ext4O__cond z := 
  opt_cond MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__cond (MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__cond (MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__cond (MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__cond (MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__cond (MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__survivalTime_r17__cond (MAC_ParametersCommon__ext4O__survivalTime_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__cond (MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__cond (MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__cond (MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__cond (MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__cond (MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__cond (MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17 z) /\
  opt_cond MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__cond (MAC_ParametersCommon__ext4O__lastTransmissionUL_r17 z) /\
  True.

Definition MAC_ParametersCommon__ext4__Type := MAC_ParametersCommon__ext4O__Type.
Definition MAC_ParametersCommon__ext4__cond := MAC_ParametersCommon__ext4O__cond.

Record MAC_ParametersCommon__Type : Set :=
  make__MAC_ParametersCommon__Type {
    MAC_ParametersCommon__lcp_Restriction : option MAC_ParametersCommon__lcp_Restriction__Type ;
    MAC_ParametersCommon__dummy : option MAC_ParametersCommon__dummy__Type ;
    MAC_ParametersCommon__lch_ToSCellRestriction : option MAC_ParametersCommon__lch_ToSCellRestriction__Type ;
    MAC_ParametersCommon__ext0 : option MAC_ParametersCommon__ext0__Type ;
    MAC_ParametersCommon__ext1 : option MAC_ParametersCommon__ext1__Type ;
    MAC_ParametersCommon__ext2 : option MAC_ParametersCommon__ext2__Type ;
    MAC_ParametersCommon__ext3 : option MAC_ParametersCommon__ext3__Type ;
    MAC_ParametersCommon__ext4 : option MAC_ParametersCommon__ext4__Type ;
}.
Definition MAC_ParametersCommon__root_list : list seq_elem := (
 Opt MAC_ParametersCommon__lcp_Restriction__Type MAC_ParametersCommon__lcp_Restriction__cond ::
 Opt MAC_ParametersCommon__dummy__Type MAC_ParametersCommon__dummy__cond ::
 Opt MAC_ParametersCommon__lch_ToSCellRestriction__Type MAC_ParametersCommon__lch_ToSCellRestriction__cond ::
 nil).
Definition MAC_ParametersCommon__ext_list : list typ := (
  typ_cons MAC_ParametersCommon__ext0__Type MAC_ParametersCommon__ext0__cond ::
  typ_cons MAC_ParametersCommon__ext1__Type MAC_ParametersCommon__ext1__cond ::
  typ_cons MAC_ParametersCommon__ext2__Type MAC_ParametersCommon__ext2__cond ::
  typ_cons MAC_ParametersCommon__ext3__Type MAC_ParametersCommon__ext3__cond ::
  typ_cons MAC_ParametersCommon__ext4__Type MAC_ParametersCommon__ext4__cond ::
  nil).
Definition MAC_ParametersCommon__cond (z : MAC_ParametersCommon__Type) := 
(  opt_cond MAC_ParametersCommon__lcp_Restriction__cond (MAC_ParametersCommon__lcp_Restriction z) /\
  opt_cond MAC_ParametersCommon__dummy__cond (MAC_ParametersCommon__dummy z) /\
  opt_cond MAC_ParametersCommon__lch_ToSCellRestriction__cond (MAC_ParametersCommon__lch_ToSCellRestriction z) /\
  True) /\ 
(  opt_cond MAC_ParametersCommon__ext0__cond (MAC_ParametersCommon__ext0 z) /\
  opt_cond MAC_ParametersCommon__ext1__cond (MAC_ParametersCommon__ext1 z) /\
  opt_cond MAC_ParametersCommon__ext2__cond (MAC_ParametersCommon__ext2 z) /\
  opt_cond MAC_ParametersCommon__ext3__cond (MAC_ParametersCommon__ext3 z) /\
  opt_cond MAC_ParametersCommon__ext4__cond (MAC_ParametersCommon__ext4 z) /\
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
Definition MAC_ParametersCommon__lcp_Restriction__Format : T_Format MAC_ParametersCommon__lcp_Restriction__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__lcp_Restriction__nat__Format MAC_ParametersCommon__lcp_Restriction__F1 MAC_ParametersCommon__lcp_Restriction__F2 MAC_ParametersCommon__lcp_Restriction__F1F2 MAC_ParametersCommon__lcp_Restriction__F2F1.

Opaque MAC_ParametersCommon__lcp_Restriction__cond MAC_ParametersCommon__lcp_Restriction__Format.

Definition MAC_ParametersCommon__dummy__Format : T_Format MAC_ParametersCommon__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__dummy__nat__Format MAC_ParametersCommon__dummy__F1 MAC_ParametersCommon__dummy__F2 MAC_ParametersCommon__dummy__F1F2 MAC_ParametersCommon__dummy__F2F1.

Opaque MAC_ParametersCommon__dummy__cond MAC_ParametersCommon__dummy__Format.

Definition MAC_ParametersCommon__lch_ToSCellRestriction__Format : T_Format MAC_ParametersCommon__lch_ToSCellRestriction__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__lch_ToSCellRestriction__nat__Format MAC_ParametersCommon__lch_ToSCellRestriction__F1 MAC_ParametersCommon__lch_ToSCellRestriction__F2 MAC_ParametersCommon__lch_ToSCellRestriction__F1F2 MAC_ParametersCommon__lch_ToSCellRestriction__F2F1.

Opaque MAC_ParametersCommon__lch_ToSCellRestriction__cond MAC_ParametersCommon__lch_ToSCellRestriction__Format.

Definition MAC_ParametersCommon__ext0O__recommendedBitRate__Format : T_Format MAC_ParametersCommon__ext0O__recommendedBitRate__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext0O__recommendedBitRate__nat__Format MAC_ParametersCommon__ext0O__recommendedBitRate__F1 MAC_ParametersCommon__ext0O__recommendedBitRate__F2 MAC_ParametersCommon__ext0O__recommendedBitRate__F1F2 MAC_ParametersCommon__ext0O__recommendedBitRate__F2F1.

Opaque MAC_ParametersCommon__ext0O__recommendedBitRate__cond MAC_ParametersCommon__ext0O__recommendedBitRate__Format.

Definition MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Format : T_Format MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext0O__recommendedBitRateQuery__nat__Format MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F1 MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F2 MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F1F2 MAC_ParametersCommon__ext0O__recommendedBitRateQuery__F2F1.

Opaque MAC_ParametersCommon__ext0O__recommendedBitRateQuery__cond MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Format.


Definition MAC_ParametersCommon__ext0O__Format_Type := Eval cbn in seq_format_prod MAC_ParametersCommon__ext0O__list.
Definition MAC_ParametersCommon__ext0O__Format_list : MAC_ParametersCommon__ext0O__Format_Type :=
  (MAC_ParametersCommon__ext0O__recommendedBitRate__Format, (MAC_ParametersCommon__ext0O__recommendedBitRateQuery__Format, unit_format)).
Definition MAC_ParametersCommon__ext0O__list__Format := (*Eval compute in *) seq_format MAC_ParametersCommon__ext0O__list MAC_ParametersCommon__ext0O__Format_list.
Definition MAC_ParametersCommon__ext0O__F1 z :=
  (MAC_ParametersCommon__ext0O__recommendedBitRate z, (MAC_ParametersCommon__ext0O__recommendedBitRateQuery z, tt)).
Definition MAC_ParametersCommon__ext0O__F2 (y : seq_type MAC_ParametersCommon__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MAC_ParametersCommon__ext0O__Type i0 i1
  end.
Lemma MAC_ParametersCommon__ext0O__F1F2_cond (z : MAC_ParametersCommon__ext0O__Type)
  : MAC_ParametersCommon__ext0O__cond z ->
  (seq_cond MAC_ParametersCommon__ext0O__list (MAC_ParametersCommon__ext0O__F1 z)).
intro H. unfold MAC_ParametersCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext0O__F1F2_cond2 (z : MAC_ParametersCommon__ext0O__Type)
 : MAC_ParametersCommon__ext0O__F2 (MAC_ParametersCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext0O__F2F1_cond (y : seq_type MAC_ParametersCommon__ext0O__list)
  : seq_cond MAC_ParametersCommon__ext0O__list y ->
 (MAC_ParametersCommon__ext0O__cond (MAC_ParametersCommon__ext0O__F2 y)) /\  MAC_ParametersCommon__ext0O__F1 (MAC_ParametersCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_ParametersCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold MAC_ParametersCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_ParametersCommon__ext0O__Format : T_Format MAC_ParametersCommon__ext0O__Type MAC_ParametersCommon__ext0O__cond :=
        proj2_format  MAC_ParametersCommon__ext0O__cond MAC_ParametersCommon__ext0O__list__Format
    MAC_ParametersCommon__ext0O__F1 MAC_ParametersCommon__ext0O__F2 MAC_ParametersCommon__ext0O__F1F2_cond  MAC_ParametersCommon__ext0O__F1F2_cond2 MAC_ParametersCommon__ext0O__F2F1_cond.
Opaque MAC_ParametersCommon__ext0O__cond MAC_ParametersCommon__ext0O__Format.

Definition MAC_ParametersCommon__ext0__check_all_none (b : MAC_ParametersCommon__ext0O__Type) : bool :=
match b with 
  | make__MAC_ParametersCommon__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition MAC_ParametersCommon__ext0__Format : T_Format MAC_ParametersCommon__ext0__Type MAC_ParametersCommon__ext0__cond :=
  restrict_add_format MAC_ParametersCommon__ext0__check_all_none MAC_ParametersCommon__ext0O__Format.

Opaque MAC_ParametersCommon__ext0__cond MAC_ParametersCommon__ext0__Format.

Definition MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Format : T_Format MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__nat__Format MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F1 MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F2 MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F1F2 MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__cond MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Format.

Definition MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Format : T_Format MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__nat__Format MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F1 MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F2 MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F1F2 MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__cond MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Format.

Definition MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Format : T_Format MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__autonomousTransmission_r16__nat__Format MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F1 MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F2 MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F1F2 MAC_ParametersCommon__ext1O__autonomousTransmission_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__autonomousTransmission_r16__cond MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Format.

Definition MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Format : T_Format MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__nat__Format MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F1 MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F2 MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F1F2 MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__cond MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Format.

Definition MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Format : T_Format MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__nat__Format MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F1 MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F2 MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F1F2 MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__cond MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Format.

Definition MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Format : T_Format MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__nat__Format MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F1 MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F2 MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F1F2 MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__cond MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Format.

Definition MAC_ParametersCommon__ext1O__singlePHR_P_r16__Format : T_Format MAC_ParametersCommon__ext1O__singlePHR_P_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__singlePHR_P_r16__nat__Format MAC_ParametersCommon__ext1O__singlePHR_P_r16__F1 MAC_ParametersCommon__ext1O__singlePHR_P_r16__F2 MAC_ParametersCommon__ext1O__singlePHR_P_r16__F1F2 MAC_ParametersCommon__ext1O__singlePHR_P_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__singlePHR_P_r16__cond MAC_ParametersCommon__ext1O__singlePHR_P_r16__Format.

Definition MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Format : T_Format MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__nat__Format MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F1 MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F2 MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F1F2 MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__cond MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Format.

Definition MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Format : T_Format MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__nat__Format MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F1 MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F2 MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F1F2 MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__cond MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Format.

Definition MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Format : T_Format MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__nat__Format MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F1 MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F2 MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F1F2 MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__F2F1.

Opaque MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__cond MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Format.


Definition MAC_ParametersCommon__ext1O__Format_Type := Eval cbn in seq_format_prod MAC_ParametersCommon__ext1O__list.
Definition MAC_ParametersCommon__ext1O__Format_list : MAC_ParametersCommon__ext1O__Format_Type :=
  (MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16__Format, (MAC_ParametersCommon__ext1O__preEmptiveBSR_r16__Format, (MAC_ParametersCommon__ext1O__autonomousTransmission_r16__Format, (MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16__Format, (MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16__Format, (MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16__Format, (MAC_ParametersCommon__ext1O__singlePHR_P_r16__Format, (MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16__Format, (MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16__Format, (MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16__Format, unit_format)))))))))).
Definition MAC_ParametersCommon__ext1O__list__Format := (*Eval compute in *) seq_format MAC_ParametersCommon__ext1O__list MAC_ParametersCommon__ext1O__Format_list.
Definition MAC_ParametersCommon__ext1O__F1 z :=
  (MAC_ParametersCommon__ext1O__recommendedBitRateMultiplier_r16 z, (MAC_ParametersCommon__ext1O__preEmptiveBSR_r16 z, (MAC_ParametersCommon__ext1O__autonomousTransmission_r16 z, (MAC_ParametersCommon__ext1O__lch_PriorityBasedPrioritization_r16 z, (MAC_ParametersCommon__ext1O__lch_ToConfiguredGrantMapping_r16 z, (MAC_ParametersCommon__ext1O__lch_ToGrantPriorityRestriction_r16 z, (MAC_ParametersCommon__ext1O__singlePHR_P_r16 z, (MAC_ParametersCommon__ext1O__ul_LBT_FailureDetectionRecovery_r16 z, (MAC_ParametersCommon__ext1O__tdd_MPE_P_MPR_Reporting_r16 z, (MAC_ParametersCommon__ext1O__lcid_ExtensionIAB_r16 z, tt)))))))))).
Definition MAC_ParametersCommon__ext1O__F2 (y : seq_type MAC_ParametersCommon__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__MAC_ParametersCommon__ext1O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma MAC_ParametersCommon__ext1O__F1F2_cond (z : MAC_ParametersCommon__ext1O__Type)
  : MAC_ParametersCommon__ext1O__cond z ->
  (seq_cond MAC_ParametersCommon__ext1O__list (MAC_ParametersCommon__ext1O__F1 z)).
intro H. unfold MAC_ParametersCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext1O__F1F2_cond2 (z : MAC_ParametersCommon__ext1O__Type)
 : MAC_ParametersCommon__ext1O__F2 (MAC_ParametersCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext1O__F2F1_cond (y : seq_type MAC_ParametersCommon__ext1O__list)
  : seq_cond MAC_ParametersCommon__ext1O__list y ->
 (MAC_ParametersCommon__ext1O__cond (MAC_ParametersCommon__ext1O__F2 y)) /\  MAC_ParametersCommon__ext1O__F1 (MAC_ParametersCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_ParametersCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold MAC_ParametersCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_ParametersCommon__ext1O__Format : T_Format MAC_ParametersCommon__ext1O__Type MAC_ParametersCommon__ext1O__cond :=
        proj2_format  MAC_ParametersCommon__ext1O__cond MAC_ParametersCommon__ext1O__list__Format
    MAC_ParametersCommon__ext1O__F1 MAC_ParametersCommon__ext1O__F2 MAC_ParametersCommon__ext1O__F1F2_cond  MAC_ParametersCommon__ext1O__F1F2_cond2 MAC_ParametersCommon__ext1O__F2F1_cond.
Opaque MAC_ParametersCommon__ext1O__cond MAC_ParametersCommon__ext1O__Format.

Definition MAC_ParametersCommon__ext1__check_all_none (b : MAC_ParametersCommon__ext1O__Type) : bool :=
match b with 
  | make__MAC_ParametersCommon__ext1O__Type None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MAC_ParametersCommon__ext1__Format : T_Format MAC_ParametersCommon__ext1__Type MAC_ParametersCommon__ext1__cond :=
  restrict_add_format MAC_ParametersCommon__ext1__check_all_none MAC_ParametersCommon__ext1O__Format.

Opaque MAC_ParametersCommon__ext1__cond MAC_ParametersCommon__ext1__Format.

Definition MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Format : T_Format MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__nat__Format MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F1 MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F2 MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F1F2 MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__F2F1.

Opaque MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__cond MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Format.


Definition MAC_ParametersCommon__ext2O__Format_Type := Eval cbn in seq_format_prod MAC_ParametersCommon__ext2O__list.
Definition MAC_ParametersCommon__ext2O__Format_list : MAC_ParametersCommon__ext2O__Format_Type :=
  (MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16__Format, unit_format).
Definition MAC_ParametersCommon__ext2O__list__Format := (*Eval compute in *) seq_format MAC_ParametersCommon__ext2O__list MAC_ParametersCommon__ext2O__Format_list.
Definition MAC_ParametersCommon__ext2O__F1 z :=
  (MAC_ParametersCommon__ext2O__spCell_BFR_CBRA_r16 z, tt).
Definition MAC_ParametersCommon__ext2O__F2 (y : seq_type MAC_ParametersCommon__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__MAC_ParametersCommon__ext2O__Type i0
  end.
Lemma MAC_ParametersCommon__ext2O__F1F2_cond (z : MAC_ParametersCommon__ext2O__Type)
  : MAC_ParametersCommon__ext2O__cond z ->
  (seq_cond MAC_ParametersCommon__ext2O__list (MAC_ParametersCommon__ext2O__F1 z)).
intro H. unfold MAC_ParametersCommon__ext2O__cond in H. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext2O__F1F2_cond2 (z : MAC_ParametersCommon__ext2O__Type)
 : MAC_ParametersCommon__ext2O__F2 (MAC_ParametersCommon__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext2O__F2F1_cond (y : seq_type MAC_ParametersCommon__ext2O__list)
  : seq_cond MAC_ParametersCommon__ext2O__list y ->
 (MAC_ParametersCommon__ext2O__cond (MAC_ParametersCommon__ext2O__F2 y)) /\  MAC_ParametersCommon__ext2O__F1 (MAC_ParametersCommon__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_ParametersCommon__ext2O__cond. simpl in *. auto.
 - simpl. unfold MAC_ParametersCommon__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_ParametersCommon__ext2O__Format : T_Format MAC_ParametersCommon__ext2O__Type MAC_ParametersCommon__ext2O__cond :=
        proj2_format  MAC_ParametersCommon__ext2O__cond MAC_ParametersCommon__ext2O__list__Format
    MAC_ParametersCommon__ext2O__F1 MAC_ParametersCommon__ext2O__F2 MAC_ParametersCommon__ext2O__F1F2_cond  MAC_ParametersCommon__ext2O__F1F2_cond2 MAC_ParametersCommon__ext2O__F2F1_cond.
Opaque MAC_ParametersCommon__ext2O__cond MAC_ParametersCommon__ext2O__Format.

Definition MAC_ParametersCommon__ext2__check_all_none (b : MAC_ParametersCommon__ext2O__Type) : bool :=
match b with 
  | make__MAC_ParametersCommon__ext2O__Type None  => false 
  | _ => true 
 end.
Definition MAC_ParametersCommon__ext2__Format : T_Format MAC_ParametersCommon__ext2__Type MAC_ParametersCommon__ext2__cond :=
  restrict_add_format MAC_ParametersCommon__ext2__check_all_none MAC_ParametersCommon__ext2O__Format.

Opaque MAC_ParametersCommon__ext2__cond MAC_ParametersCommon__ext2__Format.

Definition MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Format : T_Format MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__nat__Format MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F1 MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F2 MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F1F2 MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__F2F1.

Opaque MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__cond MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Format.


Definition MAC_ParametersCommon__ext3O__Format_Type := Eval cbn in seq_format_prod MAC_ParametersCommon__ext3O__list.
Definition MAC_ParametersCommon__ext3O__Format_list : MAC_ParametersCommon__ext3O__Format_Type :=
  (MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16__Format, unit_format).
Definition MAC_ParametersCommon__ext3O__list__Format := (*Eval compute in *) seq_format MAC_ParametersCommon__ext3O__list MAC_ParametersCommon__ext3O__Format_list.
Definition MAC_ParametersCommon__ext3O__F1 z :=
  (MAC_ParametersCommon__ext3O__srs_ResourceId_Ext_r16 z, tt).
Definition MAC_ParametersCommon__ext3O__F2 (y : seq_type MAC_ParametersCommon__ext3O__list) :=
  match y with
  | (i0, _)=>
    make__MAC_ParametersCommon__ext3O__Type i0
  end.
Lemma MAC_ParametersCommon__ext3O__F1F2_cond (z : MAC_ParametersCommon__ext3O__Type)
  : MAC_ParametersCommon__ext3O__cond z ->
  (seq_cond MAC_ParametersCommon__ext3O__list (MAC_ParametersCommon__ext3O__F1 z)).
intro H. unfold MAC_ParametersCommon__ext3O__cond in H. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext3O__F1F2_cond2 (z : MAC_ParametersCommon__ext3O__Type)
 : MAC_ParametersCommon__ext3O__F2 (MAC_ParametersCommon__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext3O__F2F1_cond (y : seq_type MAC_ParametersCommon__ext3O__list)
  : seq_cond MAC_ParametersCommon__ext3O__list y ->
 (MAC_ParametersCommon__ext3O__cond (MAC_ParametersCommon__ext3O__F2 y)) /\  MAC_ParametersCommon__ext3O__F1 (MAC_ParametersCommon__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_ParametersCommon__ext3O__cond. simpl in *. auto.
 - simpl. unfold MAC_ParametersCommon__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_ParametersCommon__ext3O__Format : T_Format MAC_ParametersCommon__ext3O__Type MAC_ParametersCommon__ext3O__cond :=
        proj2_format  MAC_ParametersCommon__ext3O__cond MAC_ParametersCommon__ext3O__list__Format
    MAC_ParametersCommon__ext3O__F1 MAC_ParametersCommon__ext3O__F2 MAC_ParametersCommon__ext3O__F1F2_cond  MAC_ParametersCommon__ext3O__F1F2_cond2 MAC_ParametersCommon__ext3O__F2F1_cond.
Opaque MAC_ParametersCommon__ext3O__cond MAC_ParametersCommon__ext3O__Format.

Definition MAC_ParametersCommon__ext3__check_all_none (b : MAC_ParametersCommon__ext3O__Type) : bool :=
match b with 
  | make__MAC_ParametersCommon__ext3O__Type None  => false 
  | _ => true 
 end.
Definition MAC_ParametersCommon__ext3__Format : T_Format MAC_ParametersCommon__ext3__Type MAC_ParametersCommon__ext3__cond :=
  restrict_add_format MAC_ParametersCommon__ext3__check_all_none MAC_ParametersCommon__ext3O__Format.

Opaque MAC_ParametersCommon__ext3__cond MAC_ParametersCommon__ext3__Format.

Definition MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Format : T_Format MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__nat__Format MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F1 MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F2 MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F1F2 MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__cond MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Format.

Definition MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Format : T_Format MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__nat__Format MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F1 MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F2 MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F1F2 MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__cond MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Format.

Definition MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Format : T_Format MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__nat__Format MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F1 MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F2 MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F1F2 MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__cond MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Format.

Definition MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Format : T_Format MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__nat__Format MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F1 MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F2 MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F1F2 MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__cond MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Format.

Definition MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Format : T_Format MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__nat__Format MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F1 MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F2 MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F1F2 MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__cond MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Format.

Definition MAC_ParametersCommon__ext4O__survivalTime_r17__Format : T_Format MAC_ParametersCommon__ext4O__survivalTime_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__survivalTime_r17__nat__Format MAC_ParametersCommon__ext4O__survivalTime_r17__F1 MAC_ParametersCommon__ext4O__survivalTime_r17__F2 MAC_ParametersCommon__ext4O__survivalTime_r17__F1F2 MAC_ParametersCommon__ext4O__survivalTime_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__survivalTime_r17__cond MAC_ParametersCommon__ext4O__survivalTime_r17__Format.

Definition MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Format : T_Format MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__nat__Format MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F1 MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F2 MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F1F2 MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__cond MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Format.

Definition MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Format : T_Format MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__nat__Format MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F1 MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F2 MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F1F2 MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__cond MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Format.

Definition MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Format : T_Format MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__nat__Format MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F1 MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F2 MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F1F2 MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__cond MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Format.

Definition MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Format : T_Format MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__nat__Format MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F1 MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F2 MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F1F2 MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__cond MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Format.

Definition MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Format : T_Format MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__nat__Format MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F1 MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F2 MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F1F2 MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__cond MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Format.

Definition MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Format : T_Format MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__nat__Format MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F1 MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F2 MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F1F2 MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__cond MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Format.

Definition MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Format : T_Format MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__nat__Format MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F1 MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F2 MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F1F2 MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__F2F1.

Opaque MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__cond MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Format.


Definition MAC_ParametersCommon__ext4O__Format_Type := Eval cbn in seq_format_prod MAC_ParametersCommon__ext4O__list.
Definition MAC_ParametersCommon__ext4O__Format_list : MAC_ParametersCommon__ext4O__Format_Type :=
  (MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17__Format, (MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17__Format, (MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17__Format, (MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17__Format, (MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17__Format, (MAC_ParametersCommon__ext4O__survivalTime_r17__Format, (MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17__Format, (MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17__Format, (MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17__Format, (MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17__Format, (MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17__Format, (MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17__Format, (MAC_ParametersCommon__ext4O__lastTransmissionUL_r17__Format, unit_format))))))))))))).
Definition MAC_ParametersCommon__ext4O__list__Format := (*Eval compute in *) seq_format MAC_ParametersCommon__ext4O__list MAC_ParametersCommon__ext4O__Format_list.
Definition MAC_ParametersCommon__ext4O__F1 z :=
  (MAC_ParametersCommon__ext4O__enhancedUuDRX_forSidelink_r17 z, (MAC_ParametersCommon__ext4O__mg_ActivationRequestPRS_Meas_r17 z, (MAC_ParametersCommon__ext4O__mg_ActivationCommPRS_Meas_r17 z, (MAC_ParametersCommon__ext4O__intraCG_Prioritization_r17 z, (MAC_ParametersCommon__ext4O__jointPrioritizationCG_Retx_Timer_r17 z, (MAC_ParametersCommon__ext4O__survivalTime_r17 z, (MAC_ParametersCommon__ext4O__lcg_ExtensionIAB_r17 z, (MAC_ParametersCommon__ext4O__harq_FeedbackDisabled_r17 z, (MAC_ParametersCommon__ext4O__uplink_Harq_ModeB_r17 z, (MAC_ParametersCommon__ext4O__sr_TriggeredBy_TA_Report_r17 z, (MAC_ParametersCommon__ext4O__extendedDRX_CycleInactive_r17 z, (MAC_ParametersCommon__ext4O__simultaneousSR_PUSCH_DiffPUCCH_groups_r17 z, (MAC_ParametersCommon__ext4O__lastTransmissionUL_r17 z, tt))))))))))))).
Definition MAC_ParametersCommon__ext4O__F2 (y : seq_type MAC_ParametersCommon__ext4O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, _)))))))))))))=>
    make__MAC_ParametersCommon__ext4O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12
  end.
Lemma MAC_ParametersCommon__ext4O__F1F2_cond (z : MAC_ParametersCommon__ext4O__Type)
  : MAC_ParametersCommon__ext4O__cond z ->
  (seq_cond MAC_ParametersCommon__ext4O__list (MAC_ParametersCommon__ext4O__F1 z)).
intro H. unfold MAC_ParametersCommon__ext4O__cond in H. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext4O__F1F2_cond2 (z : MAC_ParametersCommon__ext4O__Type)
 : MAC_ParametersCommon__ext4O__F2 (MAC_ParametersCommon__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MAC_ParametersCommon__ext4O__F2F1_cond (y : seq_type MAC_ParametersCommon__ext4O__list)
  : seq_cond MAC_ParametersCommon__ext4O__list y ->
 (MAC_ParametersCommon__ext4O__cond (MAC_ParametersCommon__ext4O__F2 y)) /\  MAC_ParametersCommon__ext4O__F1 (MAC_ParametersCommon__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MAC_ParametersCommon__ext4O__cond. simpl in *. auto.
 - simpl. unfold MAC_ParametersCommon__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MAC_ParametersCommon__ext4O__Format : T_Format MAC_ParametersCommon__ext4O__Type MAC_ParametersCommon__ext4O__cond :=
        proj2_format  MAC_ParametersCommon__ext4O__cond MAC_ParametersCommon__ext4O__list__Format
    MAC_ParametersCommon__ext4O__F1 MAC_ParametersCommon__ext4O__F2 MAC_ParametersCommon__ext4O__F1F2_cond  MAC_ParametersCommon__ext4O__F1F2_cond2 MAC_ParametersCommon__ext4O__F2F1_cond.
Opaque MAC_ParametersCommon__ext4O__cond MAC_ParametersCommon__ext4O__Format.

Definition MAC_ParametersCommon__ext4__check_all_none (b : MAC_ParametersCommon__ext4O__Type) : bool :=
match b with 
  | make__MAC_ParametersCommon__ext4O__Type None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MAC_ParametersCommon__ext4__Format : T_Format MAC_ParametersCommon__ext4__Type MAC_ParametersCommon__ext4__cond :=
  restrict_add_format MAC_ParametersCommon__ext4__check_all_none MAC_ParametersCommon__ext4O__Format.

Opaque MAC_ParametersCommon__ext4__cond MAC_ParametersCommon__ext4__Format.


Definition MAC_ParametersCommon__root_Format_Type := Eval cbn in seq_format_prod MAC_ParametersCommon__root_list.
Definition MAC_ParametersCommon__root_Format_list : MAC_ParametersCommon__root_Format_Type :=
  (MAC_ParametersCommon__lcp_Restriction__Format, (MAC_ParametersCommon__dummy__Format, (MAC_ParametersCommon__lch_ToSCellRestriction__Format, unit_format))).

Definition MAC_ParametersCommon__ext_Format_Type := Eval cbn in get_formats MAC_ParametersCommon__ext_list.
Definition MAC_ParametersCommon__ext_Format_list : MAC_ParametersCommon__ext_Format_Type :=
  (MAC_ParametersCommon__ext0__Format, (MAC_ParametersCommon__ext1__Format, (MAC_ParametersCommon__ext2__Format, (MAC_ParametersCommon__ext3__Format, (MAC_ParametersCommon__ext4__Format, unit__Format))))).

Definition MAC_ParametersCommon__list_type : Set := (seq_type MAC_ParametersCommon__root_list) * (seq_ext_type MAC_ParametersCommon__ext_list).
Definition MAC_ParametersCommon__list_cond (z : MAC_ParametersCommon__list_type) : Prop :=
        (seq_cond MAC_ParametersCommon__root_list (fst z)) /\ (seq_ext_cond MAC_ParametersCommon__ext_list (snd z)).
Definition MAC_ParametersCommon__list_format : T_Format MAC_ParametersCommon__list_type MAC_ParametersCommon__list_cond :=
 (* Eval compute in *) seq_ext_format MAC_ParametersCommon__root_list MAC_ParametersCommon__root_Format_list MAC_ParametersCommon__ext_list MAC_ParametersCommon__ext_Format_list.

Opaque MAC_ParametersCommon__list_format.
Definition MAC_ParametersCommon__F1 (z : MAC_ParametersCommon__Type) : MAC_ParametersCommon__list_type :=
  (((MAC_ParametersCommon__lcp_Restriction z, (MAC_ParametersCommon__dummy z, (MAC_ParametersCommon__lch_ToSCellRestriction z, tt)))), (
(MAC_ParametersCommon__ext0 z, (MAC_ParametersCommon__ext1 z, (MAC_ParametersCommon__ext2 z, (MAC_ParametersCommon__ext3 z, (MAC_ParametersCommon__ext4 z, tt))))))).
Definition MAC_ParametersCommon__F2 (y : MAC_ParametersCommon__list_type) : MAC_ParametersCommon__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, (i3, (i4, _))))))=>
    make__MAC_ParametersCommon__Type j0 j1 j2 i0 i1 i2 i3 i4
  end.
Definition MAC_ParametersCommon__helper1 : (forall a : MAC_ParametersCommon__Type, MAC_ParametersCommon__cond a -> MAC_ParametersCommon__list_cond (MAC_ParametersCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MAC_ParametersCommon__helper2 : (forall a : MAC_ParametersCommon__Type, MAC_ParametersCommon__F2 (MAC_ParametersCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MAC_ParametersCommon__helper3 : (forall b : MAC_ParametersCommon__list_type, MAC_ParametersCommon__list_cond b -> MAC_ParametersCommon__cond (MAC_ParametersCommon__F2 b) /\ MAC_ParametersCommon__F1 (MAC_ParametersCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MAC_ParametersCommon__cond, MAC_ParametersCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MAC_ParametersCommon__Format : T_Format MAC_ParametersCommon__Type MAC_ParametersCommon__cond :=
 proj2_format MAC_ParametersCommon__cond MAC_ParametersCommon__list_format  MAC_ParametersCommon__F1 MAC_ParametersCommon__F2 MAC_ParametersCommon__helper1 MAC_ParametersCommon__helper2 MAC_ParametersCommon__helper3.

Opaque MAC_ParametersCommon__cond MAC_ParametersCommon__Format.

