Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FeatureSetUplinkPerCC_Id.

Opaque FeatureSetUplinkPerCC_Id__cond FeatureSetUplinkPerCC_Id__Format.

Definition FeatureSetUplink__featureSetListPerUplinkCC__Type := list FeatureSetUplinkPerCC_Id__Type.

Lemma FeatureSetUplink__featureSetListPerUplinkCC__helper1 : (0 <= 1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma FeatureSetUplink__featureSetListPerUplinkCC__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetUplink__featureSetListPerUplinkCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetUplink__featureSetListPerUplinkCC__cond (z : FeatureSetUplink__featureSetListPerUplinkCC__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells)%Z /\ (list_and FeatureSetUplinkPerCC_Id__cond z) .

Inductive FeatureSetUplink__scalingFactor__Type : Set :=
 | FeatureSetUplink__scalingFactor__f0p4
 | FeatureSetUplink__scalingFactor__f0p75
 | FeatureSetUplink__scalingFactor__f0p8
.
Definition FeatureSetUplink__scalingFactor__cond := (fun (_ : FeatureSetUplink__scalingFactor__Type) => True).
Lemma FeatureSetUplink__scalingFactor__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__scalingFactor__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplink__scalingFactor__nat__helper.

Definition FeatureSetUplink__scalingFactor__F1 t :=
  match t with
  | FeatureSetUplink__scalingFactor__f0p4 => 0
  | FeatureSetUplink__scalingFactor__f0p75 => 1
  | FeatureSetUplink__scalingFactor__f0p8 => 2
  end.
Definition FeatureSetUplink__scalingFactor__F2 n :=
  match n with
  | 0 => FeatureSetUplink__scalingFactor__f0p4
  | 1 => FeatureSetUplink__scalingFactor__f0p75
  | 2 => FeatureSetUplink__scalingFactor__f0p8
  | _ => FeatureSetUplink__scalingFactor__f0p4
  end.
Lemma FeatureSetUplink__scalingFactor__F1F2 : forall x : FeatureSetUplink__scalingFactor__Type, (FeatureSetUplink__scalingFactor__F1 x <= 2) /\ FeatureSetUplink__scalingFactor__F2 (FeatureSetUplink__scalingFactor__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__scalingFactor__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplink__scalingFactor__F1 (FeatureSetUplink__scalingFactor__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink__dummy3__Type : Set :=
 | FeatureSetUplink__dummy3__supported
.
Definition FeatureSetUplink__dummy3__cond := (fun (_ : FeatureSetUplink__dummy3__Type) => True).
Lemma FeatureSetUplink__dummy3__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__dummy3__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink__dummy3__nat__helper.

Definition FeatureSetUplink__dummy3__F1 t :=
  match t with
  | FeatureSetUplink__dummy3__supported => 0
  end.
Definition FeatureSetUplink__dummy3__F2 n :=
  match n with
  | 0 => FeatureSetUplink__dummy3__supported
  | _ => FeatureSetUplink__dummy3__supported
  end.
Lemma FeatureSetUplink__dummy3__F1F2 : forall x : FeatureSetUplink__dummy3__Type, (FeatureSetUplink__dummy3__F1 x <= 0) /\ FeatureSetUplink__dummy3__F2 (FeatureSetUplink__dummy3__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__dummy3__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink__dummy3__F1 (FeatureSetUplink__dummy3__F2 y) = y. enum_solve H y. Qed.

Require Import NR.FreqSeparationClass.

Opaque FreqSeparationClass__cond FreqSeparationClass__Format.

Inductive FeatureSetUplink__searchSpaceSharingCA_UL__Type : Set :=
 | FeatureSetUplink__searchSpaceSharingCA_UL__supported
.
Definition FeatureSetUplink__searchSpaceSharingCA_UL__cond := (fun (_ : FeatureSetUplink__searchSpaceSharingCA_UL__Type) => True).
Lemma FeatureSetUplink__searchSpaceSharingCA_UL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__searchSpaceSharingCA_UL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink__searchSpaceSharingCA_UL__nat__helper.

Definition FeatureSetUplink__searchSpaceSharingCA_UL__F1 t :=
  match t with
  | FeatureSetUplink__searchSpaceSharingCA_UL__supported => 0
  end.
Definition FeatureSetUplink__searchSpaceSharingCA_UL__F2 n :=
  match n with
  | 0 => FeatureSetUplink__searchSpaceSharingCA_UL__supported
  | _ => FeatureSetUplink__searchSpaceSharingCA_UL__supported
  end.
Lemma FeatureSetUplink__searchSpaceSharingCA_UL__F1F2 : forall x : FeatureSetUplink__searchSpaceSharingCA_UL__Type, (FeatureSetUplink__searchSpaceSharingCA_UL__F1 x <= 0) /\ FeatureSetUplink__searchSpaceSharingCA_UL__F2 (FeatureSetUplink__searchSpaceSharingCA_UL__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__searchSpaceSharingCA_UL__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink__searchSpaceSharingCA_UL__F1 (FeatureSetUplink__searchSpaceSharingCA_UL__F2 y) = y. enum_solve H y. Qed.

Require Import NR.DummyI.

Opaque DummyI__cond DummyI__Format.

Require Import NR.SRS_Resources.

Opaque SRS_Resources__cond SRS_Resources__Format.

Inductive FeatureSetUplink__twoPUCCH_Group__Type : Set :=
 | FeatureSetUplink__twoPUCCH_Group__supported
.
Definition FeatureSetUplink__twoPUCCH_Group__cond := (fun (_ : FeatureSetUplink__twoPUCCH_Group__Type) => True).
Lemma FeatureSetUplink__twoPUCCH_Group__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__twoPUCCH_Group__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink__twoPUCCH_Group__nat__helper.

Definition FeatureSetUplink__twoPUCCH_Group__F1 t :=
  match t with
  | FeatureSetUplink__twoPUCCH_Group__supported => 0
  end.
Definition FeatureSetUplink__twoPUCCH_Group__F2 n :=
  match n with
  | 0 => FeatureSetUplink__twoPUCCH_Group__supported
  | _ => FeatureSetUplink__twoPUCCH_Group__supported
  end.
Lemma FeatureSetUplink__twoPUCCH_Group__F1F2 : forall x : FeatureSetUplink__twoPUCCH_Group__Type, (FeatureSetUplink__twoPUCCH_Group__F1 x <= 0) /\ FeatureSetUplink__twoPUCCH_Group__F2 (FeatureSetUplink__twoPUCCH_Group__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__twoPUCCH_Group__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink__twoPUCCH_Group__F1 (FeatureSetUplink__twoPUCCH_Group__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink__dynamicSwitchSUL__Type : Set :=
 | FeatureSetUplink__dynamicSwitchSUL__supported
.
Definition FeatureSetUplink__dynamicSwitchSUL__cond := (fun (_ : FeatureSetUplink__dynamicSwitchSUL__Type) => True).
Lemma FeatureSetUplink__dynamicSwitchSUL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__dynamicSwitchSUL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink__dynamicSwitchSUL__nat__helper.

Definition FeatureSetUplink__dynamicSwitchSUL__F1 t :=
  match t with
  | FeatureSetUplink__dynamicSwitchSUL__supported => 0
  end.
Definition FeatureSetUplink__dynamicSwitchSUL__F2 n :=
  match n with
  | 0 => FeatureSetUplink__dynamicSwitchSUL__supported
  | _ => FeatureSetUplink__dynamicSwitchSUL__supported
  end.
Lemma FeatureSetUplink__dynamicSwitchSUL__F1F2 : forall x : FeatureSetUplink__dynamicSwitchSUL__Type, (FeatureSetUplink__dynamicSwitchSUL__F1 x <= 0) /\ FeatureSetUplink__dynamicSwitchSUL__F2 (FeatureSetUplink__dynamicSwitchSUL__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__dynamicSwitchSUL__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink__dynamicSwitchSUL__F1 (FeatureSetUplink__dynamicSwitchSUL__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink__simultaneousTxSUL_NonSUL__Type : Set :=
 | FeatureSetUplink__simultaneousTxSUL_NonSUL__supported
.
Definition FeatureSetUplink__simultaneousTxSUL_NonSUL__cond := (fun (_ : FeatureSetUplink__simultaneousTxSUL_NonSUL__Type) => True).
Lemma FeatureSetUplink__simultaneousTxSUL_NonSUL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__simultaneousTxSUL_NonSUL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplink__simultaneousTxSUL_NonSUL__nat__helper.

Definition FeatureSetUplink__simultaneousTxSUL_NonSUL__F1 t :=
  match t with
  | FeatureSetUplink__simultaneousTxSUL_NonSUL__supported => 0
  end.
Definition FeatureSetUplink__simultaneousTxSUL_NonSUL__F2 n :=
  match n with
  | 0 => FeatureSetUplink__simultaneousTxSUL_NonSUL__supported
  | _ => FeatureSetUplink__simultaneousTxSUL_NonSUL__supported
  end.
Lemma FeatureSetUplink__simultaneousTxSUL_NonSUL__F1F2 : forall x : FeatureSetUplink__simultaneousTxSUL_NonSUL__Type, (FeatureSetUplink__simultaneousTxSUL_NonSUL__F1 x <= 0) /\ FeatureSetUplink__simultaneousTxSUL_NonSUL__F2 (FeatureSetUplink__simultaneousTxSUL_NonSUL__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__simultaneousTxSUL_NonSUL__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplink__simultaneousTxSUL_NonSUL__F1 (FeatureSetUplink__simultaneousTxSUL_NonSUL__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type : Set :=
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto2
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto4
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto7
.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__cond := (fun (_ : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type) => True).
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__nat__helper.

Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 t :=
  match t with
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto2 => 0
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto4 => 1
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto7 => 2
  end.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2 n :=
  match n with
  | 0 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto2
  | 1 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto4
  | 2 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto7
  | _ => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__upto2
  end.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1F2 : forall x : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 x <= 2) /\ FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type : Set :=
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto2
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto4
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto7
.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__cond := (fun (_ : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type) => True).
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__nat__helper.

Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 t :=
  match t with
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto2 => 0
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto4 => 1
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto7 => 2
  end.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2 n :=
  match n with
  | 0 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto2
  | 1 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto4
  | 2 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto7
  | _ => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__upto2
  end.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1F2 : forall x : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 x <= 2) /\ FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type : Set :=
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto2
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto4
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto7
.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__cond := (fun (_ : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type) => True).
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__nat__helper.

Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 t :=
  match t with
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto2 => 0
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto4 => 1
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto7 => 2
  end.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2 n :=
  match n with
  | 0 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto2
  | 1 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto4
  | 2 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto7
  | _ => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__upto2
  end.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1F2 : forall x : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 x <= 2) /\ FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type : Set :=
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto2
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto4
 | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto7
.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__cond := (fun (_ : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type) => True).
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__nat__helper.

Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 t :=
  match t with
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto2 => 0
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto4 => 1
  | FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto7 => 2
  end.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2 n :=
  match n with
  | 0 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto2
  | 1 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto4
  | 2 => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto7
  | _ => FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__upto2
  end.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1F2 : forall x : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 x <= 2) /\ FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2F1 : forall (y : nat) (H : y <= 2), FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2 y) = y. enum_solve H y. Qed.

Record FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Type : Set :=
  make__FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Type {
    FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz : option FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type ;
    FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz : option FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type ;
    FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz : option FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type ;
    FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz : option FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type ;
}.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list := (
 Opt FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__cond ::
 Opt FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__cond ::
 Opt FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__cond ::
 Opt FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__cond ::
 nil).
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond z := 
  opt_cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__cond (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz z) /\
  opt_cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__cond (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz z) /\
  opt_cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__cond (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz z) /\
  opt_cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__cond (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz z) /\
  True.

Require Import NR.DummyF.

Opaque DummyF__cond DummyF__Format.

Record FeatureSetUplink__Type : Set :=
  make__FeatureSetUplink__Type {
    FeatureSetUplink__featureSetListPerUplinkCC : FeatureSetUplink__featureSetListPerUplinkCC__Type ;
    FeatureSetUplink__scalingFactor : option FeatureSetUplink__scalingFactor__Type ;
    FeatureSetUplink__dummy3 : option FeatureSetUplink__dummy3__Type ;
    FeatureSetUplink__intraBandFreqSeparationUL : option FreqSeparationClass__Type ;
    FeatureSetUplink__searchSpaceSharingCA_UL : option FeatureSetUplink__searchSpaceSharingCA_UL__Type ;
    FeatureSetUplink__dummy1 : option DummyI__Type ;
    FeatureSetUplink__supportedSRS_Resources : option SRS_Resources__Type ;
    FeatureSetUplink__twoPUCCH_Group : option FeatureSetUplink__twoPUCCH_Group__Type ;
    FeatureSetUplink__dynamicSwitchSUL : option FeatureSetUplink__dynamicSwitchSUL__Type ;
    FeatureSetUplink__simultaneousTxSUL_NonSUL : option FeatureSetUplink__simultaneousTxSUL_NonSUL__Type ;
    FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot : option FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Type ;
    FeatureSetUplink__dummy2 : option DummyF__Type ;
}.
Definition FeatureSetUplink__list := (
 Nor FeatureSetUplink__featureSetListPerUplinkCC__Type FeatureSetUplink__featureSetListPerUplinkCC__cond ::
 Opt FeatureSetUplink__scalingFactor__Type FeatureSetUplink__scalingFactor__cond ::
 Opt FeatureSetUplink__dummy3__Type FeatureSetUplink__dummy3__cond ::
 Opt FreqSeparationClass__Type FreqSeparationClass__cond ::
 Opt FeatureSetUplink__searchSpaceSharingCA_UL__Type FeatureSetUplink__searchSpaceSharingCA_UL__cond ::
 Opt DummyI__Type DummyI__cond ::
 Opt SRS_Resources__Type SRS_Resources__cond ::
 Opt FeatureSetUplink__twoPUCCH_Group__Type FeatureSetUplink__twoPUCCH_Group__cond ::
 Opt FeatureSetUplink__dynamicSwitchSUL__Type FeatureSetUplink__dynamicSwitchSUL__cond ::
 Opt FeatureSetUplink__simultaneousTxSUL_NonSUL__Type FeatureSetUplink__simultaneousTxSUL_NonSUL__cond ::
 Opt FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Type FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond ::
 Opt DummyF__Type DummyF__cond ::
 nil).
Definition FeatureSetUplink__cond z := 
  FeatureSetUplink__featureSetListPerUplinkCC__cond (FeatureSetUplink__featureSetListPerUplinkCC z) /\
  opt_cond FeatureSetUplink__scalingFactor__cond (FeatureSetUplink__scalingFactor z) /\
  opt_cond FeatureSetUplink__dummy3__cond (FeatureSetUplink__dummy3 z) /\
  opt_cond FreqSeparationClass__cond (FeatureSetUplink__intraBandFreqSeparationUL z) /\
  opt_cond FeatureSetUplink__searchSpaceSharingCA_UL__cond (FeatureSetUplink__searchSpaceSharingCA_UL z) /\
  opt_cond DummyI__cond (FeatureSetUplink__dummy1 z) /\
  opt_cond SRS_Resources__cond (FeatureSetUplink__supportedSRS_Resources z) /\
  opt_cond FeatureSetUplink__twoPUCCH_Group__cond (FeatureSetUplink__twoPUCCH_Group z) /\
  opt_cond FeatureSetUplink__dynamicSwitchSUL__cond (FeatureSetUplink__dynamicSwitchSUL z) /\
  opt_cond FeatureSetUplink__simultaneousTxSUL_NonSUL__cond (FeatureSetUplink__simultaneousTxSUL_NonSUL z) /\
  opt_cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot z) /\
  opt_cond DummyF__cond (FeatureSetUplink__dummy2 z) /\
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
Definition FeatureSetUplink__featureSetListPerUplinkCC__Format : T_Format FeatureSetUplink__featureSetListPerUplinkCC__Type FeatureSetUplink__featureSetListPerUplinkCC__cond := seq_of_format FeatureSetUplinkPerCC_Id__Format 1 maxNrofServingCells FeatureSetUplink__featureSetListPerUplinkCC__helper1 FeatureSetUplink__featureSetListPerUplinkCC__helper2.

Opaque FeatureSetUplink__featureSetListPerUplinkCC__cond FeatureSetUplink__featureSetListPerUplinkCC__Format.

Definition FeatureSetUplink__scalingFactor__Format : T_Format FeatureSetUplink__scalingFactor__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__scalingFactor__nat__Format FeatureSetUplink__scalingFactor__F1 FeatureSetUplink__scalingFactor__F2 FeatureSetUplink__scalingFactor__F1F2 FeatureSetUplink__scalingFactor__F2F1.

Opaque FeatureSetUplink__scalingFactor__cond FeatureSetUplink__scalingFactor__Format.

Definition FeatureSetUplink__dummy3__Format : T_Format FeatureSetUplink__dummy3__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__dummy3__nat__Format FeatureSetUplink__dummy3__F1 FeatureSetUplink__dummy3__F2 FeatureSetUplink__dummy3__F1F2 FeatureSetUplink__dummy3__F2F1.

Opaque FeatureSetUplink__dummy3__cond FeatureSetUplink__dummy3__Format.

Definition FeatureSetUplink__searchSpaceSharingCA_UL__Format : T_Format FeatureSetUplink__searchSpaceSharingCA_UL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__searchSpaceSharingCA_UL__nat__Format FeatureSetUplink__searchSpaceSharingCA_UL__F1 FeatureSetUplink__searchSpaceSharingCA_UL__F2 FeatureSetUplink__searchSpaceSharingCA_UL__F1F2 FeatureSetUplink__searchSpaceSharingCA_UL__F2F1.

Opaque FeatureSetUplink__searchSpaceSharingCA_UL__cond FeatureSetUplink__searchSpaceSharingCA_UL__Format.

Definition FeatureSetUplink__twoPUCCH_Group__Format : T_Format FeatureSetUplink__twoPUCCH_Group__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__twoPUCCH_Group__nat__Format FeatureSetUplink__twoPUCCH_Group__F1 FeatureSetUplink__twoPUCCH_Group__F2 FeatureSetUplink__twoPUCCH_Group__F1F2 FeatureSetUplink__twoPUCCH_Group__F2F1.

Opaque FeatureSetUplink__twoPUCCH_Group__cond FeatureSetUplink__twoPUCCH_Group__Format.

Definition FeatureSetUplink__dynamicSwitchSUL__Format : T_Format FeatureSetUplink__dynamicSwitchSUL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__dynamicSwitchSUL__nat__Format FeatureSetUplink__dynamicSwitchSUL__F1 FeatureSetUplink__dynamicSwitchSUL__F2 FeatureSetUplink__dynamicSwitchSUL__F1F2 FeatureSetUplink__dynamicSwitchSUL__F2F1.

Opaque FeatureSetUplink__dynamicSwitchSUL__cond FeatureSetUplink__dynamicSwitchSUL__Format.

Definition FeatureSetUplink__simultaneousTxSUL_NonSUL__Format : T_Format FeatureSetUplink__simultaneousTxSUL_NonSUL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__simultaneousTxSUL_NonSUL__nat__Format FeatureSetUplink__simultaneousTxSUL_NonSUL__F1 FeatureSetUplink__simultaneousTxSUL_NonSUL__F2 FeatureSetUplink__simultaneousTxSUL_NonSUL__F1F2 FeatureSetUplink__simultaneousTxSUL_NonSUL__F2F1.

Opaque FeatureSetUplink__simultaneousTxSUL_NonSUL__cond FeatureSetUplink__simultaneousTxSUL_NonSUL__Format.

Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Format : T_Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__nat__Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F1F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__F2F1.

Opaque FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Format.

Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Format : T_Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__nat__Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F1F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__F2F1.

Opaque FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Format.

Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Format : T_Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__nat__Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F1F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__F2F1.

Opaque FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Format.

Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Format : T_Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__nat__Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F1F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__F2F1.

Opaque FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Format.


Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Format_Type := Eval cbn in seq_format_prod FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Format_list : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Format_Type :=
  (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz__Format, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz__Format, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz__Format, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz__Format, unit_format)))).
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list__Format := (*Eval compute in *) seq_format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Format_list.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1 z :=
  (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_15kHz z, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_30kHz z, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_60kHz z, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__scs_120kHz z, tt)))).
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F2 (y : seq_type FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Type i0 i1 i2 i3
  end.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1F2_cond (z : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Type)
  : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond z ->
  (seq_cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1 z)).
intro H. unfold FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1F2_cond2 (z : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Type)
 : FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F2 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F2F1_cond (y : seq_type FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list)
  : seq_cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list y ->
 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F2 y)) /\  FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1 (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Format : T_Format FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Type FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond :=
        proj2_format  FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__list__Format
    FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1F2_cond  FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F1F2_cond2 FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__F2F1_cond.
Opaque FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__cond FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Format.


Definition FeatureSetUplink__Format_Type := Eval cbn in seq_format_prod FeatureSetUplink__list.
Definition FeatureSetUplink__Format_list : FeatureSetUplink__Format_Type :=
  (FeatureSetUplink__featureSetListPerUplinkCC__Format, (FeatureSetUplink__scalingFactor__Format, (FeatureSetUplink__dummy3__Format, (FreqSeparationClass__Format, (FeatureSetUplink__searchSpaceSharingCA_UL__Format, (DummyI__Format, (SRS_Resources__Format, (FeatureSetUplink__twoPUCCH_Group__Format, (FeatureSetUplink__dynamicSwitchSUL__Format, (FeatureSetUplink__simultaneousTxSUL_NonSUL__Format, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot__Format, (DummyF__Format, unit_format)))))))))))).
Definition FeatureSetUplink__list__Format := (*Eval compute in *) seq_format FeatureSetUplink__list FeatureSetUplink__Format_list.
Definition FeatureSetUplink__F1 z :=
  (FeatureSetUplink__featureSetListPerUplinkCC z, (FeatureSetUplink__scalingFactor z, (FeatureSetUplink__dummy3 z, (FeatureSetUplink__intraBandFreqSeparationUL z, (FeatureSetUplink__searchSpaceSharingCA_UL z, (FeatureSetUplink__dummy1 z, (FeatureSetUplink__supportedSRS_Resources z, (FeatureSetUplink__twoPUCCH_Group z, (FeatureSetUplink__dynamicSwitchSUL z, (FeatureSetUplink__simultaneousTxSUL_NonSUL z, (FeatureSetUplink__pusch_ProcessingType1_DifferentTB_PerSlot z, (FeatureSetUplink__dummy2 z, tt)))))))))))).
Definition FeatureSetUplink__F2 (y : seq_type FeatureSetUplink__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, _))))))))))))=>
    make__FeatureSetUplink__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  end.
Lemma FeatureSetUplink__F1F2_cond (z : FeatureSetUplink__Type)
  : FeatureSetUplink__cond z ->
  (seq_cond FeatureSetUplink__list (FeatureSetUplink__F1 z)).
intro H. unfold FeatureSetUplink__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplink__F1F2_cond2 (z : FeatureSetUplink__Type)
 : FeatureSetUplink__F2 (FeatureSetUplink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplink__F2F1_cond (y : seq_type FeatureSetUplink__list)
  : seq_cond FeatureSetUplink__list y ->
 (FeatureSetUplink__cond (FeatureSetUplink__F2 y)) /\  FeatureSetUplink__F1 (FeatureSetUplink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplink__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplink__Format : T_Format FeatureSetUplink__Type FeatureSetUplink__cond :=
        proj2_format  FeatureSetUplink__cond FeatureSetUplink__list__Format
    FeatureSetUplink__F1 FeatureSetUplink__F2 FeatureSetUplink__F1F2_cond  FeatureSetUplink__F1F2_cond2 FeatureSetUplink__F2F1_cond.
Opaque FeatureSetUplink__cond FeatureSetUplink__Format.

