Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Lemma CI_ConfigurationPerServingCell_r16__positionInDCI_r16__helper1 : (0 <= maxCI_DCI_PayloadSize_1_r16)%Z. unfold maxCI_DCI_PayloadSize_1_r16.
 lia. Qed.
Lemma CI_ConfigurationPerServingCell_r16__positionInDCI_r16__helper2 : to_bit_sz (Z.to_nat (maxCI_DCI_PayloadSize_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCI_DCI_PayloadSize_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CI_ConfigurationPerServingCell_r16__positionInDCI_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CI_ConfigurationPerServingCell_r16__positionInDCI_r16__Type := Z.
Definition CI_ConfigurationPerServingCell_r16__positionInDCI_r16__cond := (fun z => (0 <= z <= maxCI_DCI_PayloadSize_1_r16)%Z).
Lemma CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__helper1 : (0 <= maxCI_DCI_PayloadSize_1_r16)%Z. unfold maxCI_DCI_PayloadSize_1_r16.
 lia. Qed.
Lemma CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__helper2 : to_bit_sz (Z.to_nat (maxCI_DCI_PayloadSize_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCI_DCI_PayloadSize_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__Type := Z.
Definition CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__cond := (fun z => (0 <= z <= maxCI_DCI_PayloadSize_1_r16)%Z).
Inductive CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Type : Set :=
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n1
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n2
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n4
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n5
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n7
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n8
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n10
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n14
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n16
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n20
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n28
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n32
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n35
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n42
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n56
 | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n112
.
Definition CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__cond := (fun (_ : CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Type) => True).
Lemma CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__nat__helper.

Definition CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F1 t :=
  match t with
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n1 => 0
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n2 => 1
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n4 => 2
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n5 => 3
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n7 => 4
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n8 => 5
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n10 => 6
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n14 => 7
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n16 => 8
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n20 => 9
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n28 => 10
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n32 => 11
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n35 => 12
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n42 => 13
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n56 => 14
  | CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n112 => 15
  end.
Definition CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F2 n :=
  match n with
  | 0 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n1
  | 1 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n2
  | 2 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n4
  | 3 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n5
  | 4 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n7
  | 5 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n8
  | 6 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n10
  | 7 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n14
  | 8 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n16
  | 9 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n20
  | 10 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n28
  | 11 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n32
  | 12 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n35
  | 13 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n42
  | 14 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n56
  | 15 => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n112
  | _ => CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__n1
  end.
Lemma CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F1F2 : forall x : CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Type, (CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F1 x <= 15) /\ CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F2 (CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F1 x) = x. imp_solve. Qed.
Lemma CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F2F1 : forall (y : nat) (H : y <= 15), CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F1 (CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Type : Set :=
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n2
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n4
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n7
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n14
.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__cond := (fun (_ : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Type) => True).
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__nat__helper.

Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F1 t :=
  match t with
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n2 => 0
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n4 => 1
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n7 => 2
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n14 => 3
  end.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F2 n :=
  match n with
  | 0 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n2
  | 1 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n4
  | 2 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n7
  | 3 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n14
  | _ => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__n2
  end.
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F1F2 : forall x : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Type, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F1 x <= 3) /\ CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F2 (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F1 x) = x. imp_solve. Qed.
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F2F1 : forall (y : nat) (H : y <= 3), CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F1 (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Type : Set :=
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n1
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n2
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n4
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n7
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n14
 | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n28
.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__cond := (fun (_ : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Type) => True).
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__nat__helper.

Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F1 t :=
  match t with
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n1 => 0
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n2 => 1
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n4 => 2
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n7 => 3
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n14 => 4
  | CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n28 => 5
  end.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F2 n :=
  match n with
  | 0 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n1
  | 1 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n2
  | 2 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n4
  | 3 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n7
  | 4 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n14
  | 5 => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n28
  | _ => CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__n1
  end.
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F1F2 : forall x : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Type, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F1 x <= 5) /\ CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F2 (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F1 x) = x. imp_solve. Qed.
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F2F1 : forall (y : nat) (H : y <= 5), CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F1 (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F2 y) = y. enum_solve H y. Qed.

Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__helper1 : (0 <= 37949)%Z.  lia. Qed.
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__helper2 : to_bit_sz (Z.to_nat (37949 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (37949 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__Type := Z.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__cond := (fun z => (0 <= z <= 37949)%Z).
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__helper1 : (0 <= 2)%Z.  lia. Qed.
Lemma CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__helper2 : to_bit_sz (Z.to_nat (2 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__Type := Z.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__cond := (fun z => (0 <= z <= 2)%Z).
Record CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type : Set :=
  make__CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type {
    CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16 : option CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Type ;
    CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16 : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Type ;
    CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16 : Z ;
    CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16 : Z ;
}.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_list : list seq_elem := (
 Opt CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Type CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__cond ::
 Nor CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Type CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__cond ::
 Nor Z CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__cond ::
 Nor Z CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__cond ::
 nil).
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_list : list typ := (
  nil).
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond (z : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type) := 
(  opt_cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__cond (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16 z) /\
  CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__cond (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16 z) /\
  CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__cond (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16 z) /\
  CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__cond (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16 z) /\
  True) /\ 
(  True).

Inductive CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Type : Set :=
 | CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__enabled
.
Definition CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__cond := (fun (_ : CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Type) => True).
Lemma CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__nat__helper.

Definition CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F1 t :=
  match t with
  | CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__enabled => 0
  end.
Definition CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F2 n :=
  match n with
  | 0 => CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__enabled
  | _ => CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__enabled
  end.
Lemma CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F1F2 : forall x : CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Type, (CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F1 x <= 0) /\ CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F2 (CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F1 x) = x. imp_solve. Qed.
Lemma CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F2F1 : forall (y : nat) (H : y <= 0), CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F1 (CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F2 y) = y. enum_solve H y. Qed.

Record CI_ConfigurationPerServingCell_r16__Type : Set :=
  make__CI_ConfigurationPerServingCell_r16__Type {
    CI_ConfigurationPerServingCell_r16__servingCellId : ServCellIndex__Type ;
    CI_ConfigurationPerServingCell_r16__positionInDCI_r16 : Z ;
    CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16 : option Z ;
    CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16 : CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Type ;
    CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16 : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type ;
    CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610 : option CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Type ;
}.
Definition CI_ConfigurationPerServingCell_r16__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor Z CI_ConfigurationPerServingCell_r16__positionInDCI_r16__cond ::
 Opt Z CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__cond ::
 Nor CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Type CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__cond ::
 Nor CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond ::
 Opt CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Type CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__cond ::
 nil).
Definition CI_ConfigurationPerServingCell_r16__cond z := 
  ServCellIndex__cond (CI_ConfigurationPerServingCell_r16__servingCellId z) /\
  CI_ConfigurationPerServingCell_r16__positionInDCI_r16__cond (CI_ConfigurationPerServingCell_r16__positionInDCI_r16 z) /\
  opt_cond CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__cond (CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16 z) /\
  CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__cond (CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16 z) /\
  CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16 z) /\
  opt_cond CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__cond (CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610 z) /\
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
Definition CI_ConfigurationPerServingCell_r16__positionInDCI_r16__Format : T_Format Z CI_ConfigurationPerServingCell_r16__positionInDCI_r16__cond :=
 ranged_int_format (0) (maxCI_DCI_PayloadSize_1_r16) CI_ConfigurationPerServingCell_r16__positionInDCI_r16__helper1 CI_ConfigurationPerServingCell_r16__positionInDCI_r16__helper2.

Opaque CI_ConfigurationPerServingCell_r16__positionInDCI_r16__cond CI_ConfigurationPerServingCell_r16__positionInDCI_r16__Format.

Definition CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__Format : T_Format Z CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__cond :=
 ranged_int_format (0) (maxCI_DCI_PayloadSize_1_r16) CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__helper1 CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__helper2.

Opaque CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__cond CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__Format.

Definition CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Format : T_Format CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__nat__Format CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F1 CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F2 CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F1F2 CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__F2F1.

Opaque CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__cond CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Format.

Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Format : T_Format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__nat__Format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F1 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F2 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F1F2 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__F2F1.

Opaque CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Format.

Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Format : T_Format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__nat__Format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F1 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F2 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F1F2 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__F2F1.

Opaque CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Format.

Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__Format : T_Format Z CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__cond :=
 ranged_int_format (0) (37949) CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__helper1 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__helper2.

Opaque CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__Format.

Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__Format : T_Format Z CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__cond :=
 ranged_int_format (0) (2) CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__helper1 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__helper2.

Opaque CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__Format.


Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_Format_Type := Eval cbn in seq_format_prod CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_list.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_Format_list : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_Format_Type :=
  (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16__Format, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16__Format, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16__Format, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16__Format, unit_format)))).

Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_Format_Type := Eval cbn in get_formats CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_list.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_Format_list : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_Format_Type :=
  unit__Format.

Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_type : Set := (seq_type CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_list) * (seq_ext_type CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_list).
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_cond (z : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_type) : Prop :=
        (seq_cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_list (fst z)) /\ (seq_ext_cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_list (snd z)).
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_format : T_Format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_type CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_cond :=
 (* Eval compute in *) seq_ext_format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_list CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__root_Format_list CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_list CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__ext_Format_list.

Opaque CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_format.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F1 (z : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type) : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_type :=
  (((CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeDurationForCI_r16 z, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__timeGranularityForCI_r16 z, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__frequencyRegionForCI_r16 z, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__deltaOffset_r16 z, tt))))), (
tt)).
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F2 (y : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_type) : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type j0 j1 j2 j3
  end.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__helper1 : (forall a : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type, CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond a -> CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_cond (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__helper2 : (forall a : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type, CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F2 (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__helper3 : (forall b : CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_type, CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_cond b -> CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F2 b) /\ CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F1 (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond, CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Format : T_Format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Type CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond :=
 proj2_format CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__list_format  CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F1 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__F2 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__helper1 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__helper2 CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__helper3.

Opaque CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__cond CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Format.

Definition CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Format : T_Format CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__nat__Format CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F1 CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F2 CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F1F2 CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__F2F1.

Opaque CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__cond CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Format.


Definition CI_ConfigurationPerServingCell_r16__Format_Type := Eval cbn in seq_format_prod CI_ConfigurationPerServingCell_r16__list.
Definition CI_ConfigurationPerServingCell_r16__Format_list : CI_ConfigurationPerServingCell_r16__Format_Type :=
  (ServCellIndex__Format, (CI_ConfigurationPerServingCell_r16__positionInDCI_r16__Format, (CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16__Format, (CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16__Format, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16__Format, (CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610__Format, unit_format)))))).
Definition CI_ConfigurationPerServingCell_r16__list__Format := (*Eval compute in *) seq_format CI_ConfigurationPerServingCell_r16__list CI_ConfigurationPerServingCell_r16__Format_list.
Definition CI_ConfigurationPerServingCell_r16__F1 z :=
  (CI_ConfigurationPerServingCell_r16__servingCellId z, (CI_ConfigurationPerServingCell_r16__positionInDCI_r16 z, (CI_ConfigurationPerServingCell_r16__positionInDCI_ForSUL_r16 z, (CI_ConfigurationPerServingCell_r16__ci_PayloadSize_r16 z, (CI_ConfigurationPerServingCell_r16__timeFrequencyRegion_r16 z, (CI_ConfigurationPerServingCell_r16__uplinkCancellationPriority_v1610 z, tt)))))).
Definition CI_ConfigurationPerServingCell_r16__F2 (y : seq_type CI_ConfigurationPerServingCell_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__CI_ConfigurationPerServingCell_r16__Type i0 i1 i2 i3 i4 i5
  end.
Lemma CI_ConfigurationPerServingCell_r16__F1F2_cond (z : CI_ConfigurationPerServingCell_r16__Type)
  : CI_ConfigurationPerServingCell_r16__cond z ->
  (seq_cond CI_ConfigurationPerServingCell_r16__list (CI_ConfigurationPerServingCell_r16__F1 z)).
intro H. unfold CI_ConfigurationPerServingCell_r16__cond in H. simpl. auto. Qed.
Lemma CI_ConfigurationPerServingCell_r16__F1F2_cond2 (z : CI_ConfigurationPerServingCell_r16__Type)
 : CI_ConfigurationPerServingCell_r16__F2 (CI_ConfigurationPerServingCell_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CI_ConfigurationPerServingCell_r16__F2F1_cond (y : seq_type CI_ConfigurationPerServingCell_r16__list)
  : seq_cond CI_ConfigurationPerServingCell_r16__list y ->
 (CI_ConfigurationPerServingCell_r16__cond (CI_ConfigurationPerServingCell_r16__F2 y)) /\  CI_ConfigurationPerServingCell_r16__F1 (CI_ConfigurationPerServingCell_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CI_ConfigurationPerServingCell_r16__cond. simpl in *. auto.
 - simpl. unfold CI_ConfigurationPerServingCell_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CI_ConfigurationPerServingCell_r16__Format : T_Format CI_ConfigurationPerServingCell_r16__Type CI_ConfigurationPerServingCell_r16__cond :=
        proj2_format  CI_ConfigurationPerServingCell_r16__cond CI_ConfigurationPerServingCell_r16__list__Format
    CI_ConfigurationPerServingCell_r16__F1 CI_ConfigurationPerServingCell_r16__F2 CI_ConfigurationPerServingCell_r16__F1F2_cond  CI_ConfigurationPerServingCell_r16__F1F2_cond2 CI_ConfigurationPerServingCell_r16__F2F1_cond.
Opaque CI_ConfigurationPerServingCell_r16__cond CI_ConfigurationPerServingCell_r16__Format.

