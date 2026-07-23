Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_PosResourceId_r16.

Opaque SRS_PosResourceId_r16__cond SRS_PosResourceId_r16__Format.

Lemma SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__Type := Z.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__cond := (fun z => (0 <= z <= 1)%Z).
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__Type := Z.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__cond := (fun z => (0 <= z <= 7)%Z).
Record SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type : Set :=
  make__SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type {
    SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16 : Z ;
    SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16 : Z ;
}.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list := (
 Nor Z SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__cond ::
 Nor Z SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__cond ::
 nil).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond z := 
  SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16 z) /\
  SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16 z) /\
  True.

Lemma SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__Type := Z.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__cond := (fun z => (0 <= z <= 3)%Z).
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__helper1 : (0 <= 11)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__helper2 : to_bit_sz (Z.to_nat (11 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (11 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__Type := Z.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__cond := (fun z => (0 <= z <= 11)%Z).
Record SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type : Set :=
  make__SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type {
    SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16 : Z ;
    SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16 : Z ;
}.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list := (
 Nor Z SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__cond ::
 Nor Z SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__cond ::
 nil).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond z := 
  SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16 z) /\
  SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16 z) /\
  True.

Lemma SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__Type := Z.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__cond := (fun z => (0 <= z <= 7)%Z).
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__helper1 : (0 <= 5)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__helper2 : to_bit_sz (Z.to_nat (5 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__Type := Z.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__cond := (fun z => (0 <= z <= 5)%Z).
Record SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type : Set :=
  make__SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type {
    SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16 : Z ;
    SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16 : Z ;
}.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list := (
 Nor Z SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__cond ::
 Nor Z SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__cond ::
 nil).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond z := 
  SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16 z) /\
  SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16 z) /\
  True.


Inductive SRS_PosResource_r16__transmissionComb_r16__root__Type : Set :=
  | SRS_PosResource_r16__transmissionComb_r16__root__n2_r16 : SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type -> SRS_PosResource_r16__transmissionComb_r16__root__Type
  | SRS_PosResource_r16__transmissionComb_r16__root__n4_r16 : SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type -> SRS_PosResource_r16__transmissionComb_r16__root__Type
  | SRS_PosResource_r16__transmissionComb_r16__root__n8_r16 : SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type -> SRS_PosResource_r16__transmissionComb_r16__root__Type
.
Definition SRS_PosResource_r16__transmissionComb_r16__root__list : list typ := (
typ_cons SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond ::
typ_cons SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond ::
typ_cons SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond ::
 nil).
Definition SRS_PosResource_r16__transmissionComb_r16__root__cond (c : SRS_PosResource_r16__transmissionComb_r16__root__Type) := 
  match c with
  | SRS_PosResource_r16__transmissionComb_r16__root__n2_r16 t => SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond t 
  | SRS_PosResource_r16__transmissionComb_r16__root__n4_r16 t => SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond t 
  | SRS_PosResource_r16__transmissionComb_r16__root__n8_r16 t => SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond t 
  end.

Lemma SRS_PosResource_r16__transmissionComb_r16__root__len_helper1 : to_bit_sz (length SRS_PosResource_r16__transmissionComb_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__len_helper2 : 2 <= length2 SRS_PosResource_r16__transmissionComb_r16__root__list.
 simpl. lia. Qed.

Definition SRS_PosResource_r16__transmissionComb_r16__ext__Type : Set := Empty_set.
Definition SRS_PosResource_r16__transmissionComb_r16__ext__cond (c : SRS_PosResource_r16__transmissionComb_r16__ext__Type) := True.
Definition SRS_PosResource_r16__transmissionComb_r16__Type : Set := SRS_PosResource_r16__transmissionComb_r16__root__Type + SRS_PosResource_r16__transmissionComb_r16__ext__Type.
Definition SRS_PosResource_r16__transmissionComb_r16__cond :=
  sum_cond SRS_PosResource_r16__transmissionComb_r16__root__cond SRS_PosResource_r16__transmissionComb_r16__ext__cond.
Lemma SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__helper1 : (0 <= 13)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__helper2 : to_bit_sz (Z.to_nat (13 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (13 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__Type := Z.
Definition SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__cond := (fun z => (0 <= z <= 13)%Z).
Inductive SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Type : Set :=
 | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n1
 | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n2
 | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n4
 | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n8
 | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n12
.
Definition SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__cond := (fun (_ : SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Type) => True).
Lemma SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__nat__helper.

Definition SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F1 t :=
  match t with
  | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n1 => 0
  | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n2 => 1
  | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n4 => 2
  | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n8 => 3
  | SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n12 => 4
  end.
Definition SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F2 n :=
  match n with
  | 0 => SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n1
  | 1 => SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n2
  | 2 => SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n4
  | 3 => SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n8
  | 4 => SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n12
  | _ => SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__n1
  end.
Lemma SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F1F2 : forall x : SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Type, (SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F1 x <= 4) /\ SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F2 (SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F2F1 : forall (y : nat) (H : y <= 4), SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F1 (SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F2 y) = y. enum_solve H y. Qed.

Record SRS_PosResource_r16__resourceMapping_r16__Type : Set :=
  make__SRS_PosResource_r16__resourceMapping_r16__Type {
    SRS_PosResource_r16__resourceMapping_r16__startPosition_r16 : Z ;
    SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16 : SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Type ;
}.
Definition SRS_PosResource_r16__resourceMapping_r16__list := (
 Nor Z SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__cond ::
 Nor SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Type SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__cond ::
 nil).
Definition SRS_PosResource_r16__resourceMapping_r16__cond z := 
  SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__cond (SRS_PosResource_r16__resourceMapping_r16__startPosition_r16 z) /\
  SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__cond (SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16 z) /\
  True.

Lemma SRS_PosResource_r16__freqDomainShift_r16__helper1 : (0 <= 268)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__freqDomainShift_r16__helper2 : to_bit_sz (Z.to_nat (268 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (268 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__freqDomainShift_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__freqDomainShift_r16__Type := Z.
Definition SRS_PosResource_r16__freqDomainShift_r16__cond := (fun z => (0 <= z <= 268)%Z).
Lemma SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__Type := Z.
Definition SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__cond := (fun z => (0 <= z <= 63)%Z).
Record SRS_PosResource_r16__freqHopping_r16__Type : Set :=
  make__SRS_PosResource_r16__freqHopping_r16__Type {
    SRS_PosResource_r16__freqHopping_r16__c_SRS_r16 : Z ;
}.
Definition SRS_PosResource_r16__freqHopping_r16__root_list : list seq_elem := (
 Nor Z SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__cond ::
 nil).
Definition SRS_PosResource_r16__freqHopping_r16__ext_list : list typ := (
  nil).
Definition SRS_PosResource_r16__freqHopping_r16__cond (z : SRS_PosResource_r16__freqHopping_r16__Type) := 
(  SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__cond (SRS_PosResource_r16__freqHopping_r16__c_SRS_r16 z) /\
  True) /\ 
(  True).

Inductive SRS_PosResource_r16__groupOrSequenceHopping_r16__Type : Set :=
 | SRS_PosResource_r16__groupOrSequenceHopping_r16__neither
 | SRS_PosResource_r16__groupOrSequenceHopping_r16__groupHopping
 | SRS_PosResource_r16__groupOrSequenceHopping_r16__sequenceHopping
.
Definition SRS_PosResource_r16__groupOrSequenceHopping_r16__cond := (fun (_ : SRS_PosResource_r16__groupOrSequenceHopping_r16__Type) => True).
Lemma SRS_PosResource_r16__groupOrSequenceHopping_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_PosResource_r16__groupOrSequenceHopping_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SRS_PosResource_r16__groupOrSequenceHopping_r16__nat__helper.

Definition SRS_PosResource_r16__groupOrSequenceHopping_r16__F1 t :=
  match t with
  | SRS_PosResource_r16__groupOrSequenceHopping_r16__neither => 0
  | SRS_PosResource_r16__groupOrSequenceHopping_r16__groupHopping => 1
  | SRS_PosResource_r16__groupOrSequenceHopping_r16__sequenceHopping => 2
  end.
Definition SRS_PosResource_r16__groupOrSequenceHopping_r16__F2 n :=
  match n with
  | 0 => SRS_PosResource_r16__groupOrSequenceHopping_r16__neither
  | 1 => SRS_PosResource_r16__groupOrSequenceHopping_r16__groupHopping
  | 2 => SRS_PosResource_r16__groupOrSequenceHopping_r16__sequenceHopping
  | _ => SRS_PosResource_r16__groupOrSequenceHopping_r16__neither
  end.
Lemma SRS_PosResource_r16__groupOrSequenceHopping_r16__F1F2 : forall x : SRS_PosResource_r16__groupOrSequenceHopping_r16__Type, (SRS_PosResource_r16__groupOrSequenceHopping_r16__F1 x <= 2) /\ SRS_PosResource_r16__groupOrSequenceHopping_r16__F2 (SRS_PosResource_r16__groupOrSequenceHopping_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_PosResource_r16__groupOrSequenceHopping_r16__F2F1 : forall (y : nat) (H : y <= 2), SRS_PosResource_r16__groupOrSequenceHopping_r16__F1 (SRS_PosResource_r16__groupOrSequenceHopping_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__Type := Z.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__cond := (fun z => (1 <= z <= 32)%Z).
Record SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type : Set :=
  make__SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type {
    SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16 : option Z ;
}.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_list : list seq_elem := (
 Opt Z SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__cond ::
 nil).
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_list : list typ := (
  nil).
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond (z : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type) := 
(  opt_cond SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__cond (SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16 z) /\
  True) /\ 
(  True).

Require Import NR.SRS_PeriodicityAndOffset_r16.

Opaque SRS_PeriodicityAndOffset_r16__cond SRS_PeriodicityAndOffset_r16__Format.

Require Import NR.SRS_PeriodicityAndOffsetExt_r16.

Opaque SRS_PeriodicityAndOffsetExt_r16__cond SRS_PeriodicityAndOffsetExt_r16__Format.

Record SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type : Set :=
  make__SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type {
    SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__periodicityAndOffset_sp_Ext_r16 : option SRS_PeriodicityAndOffsetExt_r16__Type ;
}.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list := (
 Opt SRS_PeriodicityAndOffsetExt_r16__Type SRS_PeriodicityAndOffsetExt_r16__cond ::
 nil).
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond z := 
  opt_cond SRS_PeriodicityAndOffsetExt_r16__cond (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__periodicityAndOffset_sp_Ext_r16 z) /\
  True.

Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__Type := SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__cond := SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond.

Record SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type : Set :=
  make__SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type {
    SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__periodicityAndOffset_sp_r16 : SRS_PeriodicityAndOffset_r16__Type ;
    SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0 : option SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__Type ;
}.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_list : list seq_elem := (
 Nor SRS_PeriodicityAndOffset_r16__Type SRS_PeriodicityAndOffset_r16__cond ::
 nil).
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_list : list typ := (
  typ_cons SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__Type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__cond ::
  nil).
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond (z : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type) := 
(  SRS_PeriodicityAndOffset_r16__cond (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__periodicityAndOffset_sp_r16 z) /\
  True) /\ 
(  opt_cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__cond (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0 z) /\
  True).

Require Import NR.SRS_PeriodicityAndOffset_r16.

Opaque SRS_PeriodicityAndOffset_r16__cond SRS_PeriodicityAndOffset_r16__Format.

Require Import NR.SRS_PeriodicityAndOffsetExt_r16.

Opaque SRS_PeriodicityAndOffsetExt_r16__cond SRS_PeriodicityAndOffsetExt_r16__Format.

Record SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type : Set :=
  make__SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type {
    SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__periodicityAndOffset_p_Ext_r16 : option SRS_PeriodicityAndOffsetExt_r16__Type ;
}.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list := (
 Opt SRS_PeriodicityAndOffsetExt_r16__Type SRS_PeriodicityAndOffsetExt_r16__cond ::
 nil).
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond z := 
  opt_cond SRS_PeriodicityAndOffsetExt_r16__cond (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__periodicityAndOffset_p_Ext_r16 z) /\
  True.

Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__Type := SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__cond := SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond.

Record SRS_PosResource_r16__resourceType_r16__periodic_r16__Type : Set :=
  make__SRS_PosResource_r16__resourceType_r16__periodic_r16__Type {
    SRS_PosResource_r16__resourceType_r16__periodic_r16__periodicityAndOffset_p_r16 : SRS_PeriodicityAndOffset_r16__Type ;
    SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0 : option SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__Type ;
}.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__root_list : list seq_elem := (
 Nor SRS_PeriodicityAndOffset_r16__Type SRS_PeriodicityAndOffset_r16__cond ::
 nil).
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_list : list typ := (
  typ_cons SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__Type SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__cond ::
  nil).
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__cond (z : SRS_PosResource_r16__resourceType_r16__periodic_r16__Type) := 
(  SRS_PeriodicityAndOffset_r16__cond (SRS_PosResource_r16__resourceType_r16__periodic_r16__periodicityAndOffset_p_r16 z) /\
  True) /\ 
(  opt_cond SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__cond (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0 z) /\
  True).


Inductive SRS_PosResource_r16__resourceType_r16__Type : Set :=
  | SRS_PosResource_r16__resourceType_r16__aperiodic_r16 : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type -> SRS_PosResource_r16__resourceType_r16__Type
  | SRS_PosResource_r16__resourceType_r16__semi_persistent_r16 : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type -> SRS_PosResource_r16__resourceType_r16__Type
  | SRS_PosResource_r16__resourceType_r16__periodic_r16 : SRS_PosResource_r16__resourceType_r16__periodic_r16__Type -> SRS_PosResource_r16__resourceType_r16__Type
.
Definition SRS_PosResource_r16__resourceType_r16__list : list typ := (
typ_cons SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond ::
typ_cons SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond ::
typ_cons SRS_PosResource_r16__resourceType_r16__periodic_r16__Type SRS_PosResource_r16__resourceType_r16__periodic_r16__cond ::
 nil).
Definition SRS_PosResource_r16__resourceType_r16__cond (c : SRS_PosResource_r16__resourceType_r16__Type) := 
  match c with
  | SRS_PosResource_r16__resourceType_r16__aperiodic_r16 t => SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond t 
  | SRS_PosResource_r16__resourceType_r16__semi_persistent_r16 t => SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond t 
  | SRS_PosResource_r16__resourceType_r16__periodic_r16 t => SRS_PosResource_r16__resourceType_r16__periodic_r16__cond t 
  end.

Lemma SRS_PosResource_r16__resourceType_r16__len_helper1 : to_bit_sz (length SRS_PosResource_r16__resourceType_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_PosResource_r16__resourceType_r16__len_helper2 : 2 <= length2 SRS_PosResource_r16__resourceType_r16__list.
 simpl. lia. Qed.
Lemma SRS_PosResource_r16__sequenceId_r16__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma SRS_PosResource_r16__sequenceId_r16__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PosResource_r16__sequenceId_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PosResource_r16__sequenceId_r16__Type := Z.
Definition SRS_PosResource_r16__sequenceId_r16__cond := (fun z => (0 <= z <= 65535)%Z).
Require Import NR.SRS_SpatialRelationInfoPos_r16.

Opaque SRS_SpatialRelationInfoPos_r16__cond SRS_SpatialRelationInfoPos_r16__Format.

Record SRS_PosResource_r16__Type : Set :=
  make__SRS_PosResource_r16__Type {
    SRS_PosResource_r16__srs_PosResourceId_r16 : SRS_PosResourceId_r16__Type ;
    SRS_PosResource_r16__transmissionComb_r16 : SRS_PosResource_r16__transmissionComb_r16__Type ;
    SRS_PosResource_r16__resourceMapping_r16 : SRS_PosResource_r16__resourceMapping_r16__Type ;
    SRS_PosResource_r16__freqDomainShift_r16 : Z ;
    SRS_PosResource_r16__freqHopping_r16 : SRS_PosResource_r16__freqHopping_r16__Type ;
    SRS_PosResource_r16__groupOrSequenceHopping_r16 : SRS_PosResource_r16__groupOrSequenceHopping_r16__Type ;
    SRS_PosResource_r16__resourceType_r16 : SRS_PosResource_r16__resourceType_r16__Type ;
    SRS_PosResource_r16__sequenceId_r16 : Z ;
    SRS_PosResource_r16__spatialRelationInfoPos_r16 : option SRS_SpatialRelationInfoPos_r16__Type ;
}.
Definition SRS_PosResource_r16__root_list : list seq_elem := (
 Nor SRS_PosResourceId_r16__Type SRS_PosResourceId_r16__cond ::
 Nor SRS_PosResource_r16__transmissionComb_r16__Type SRS_PosResource_r16__transmissionComb_r16__cond ::
 Nor SRS_PosResource_r16__resourceMapping_r16__Type SRS_PosResource_r16__resourceMapping_r16__cond ::
 Nor Z SRS_PosResource_r16__freqDomainShift_r16__cond ::
 Nor SRS_PosResource_r16__freqHopping_r16__Type SRS_PosResource_r16__freqHopping_r16__cond ::
 Nor SRS_PosResource_r16__groupOrSequenceHopping_r16__Type SRS_PosResource_r16__groupOrSequenceHopping_r16__cond ::
 Nor SRS_PosResource_r16__resourceType_r16__Type SRS_PosResource_r16__resourceType_r16__cond ::
 Nor Z SRS_PosResource_r16__sequenceId_r16__cond ::
 Opt SRS_SpatialRelationInfoPos_r16__Type SRS_SpatialRelationInfoPos_r16__cond ::
 nil).
Definition SRS_PosResource_r16__ext_list : list typ := (
  nil).
Definition SRS_PosResource_r16__cond (z : SRS_PosResource_r16__Type) := 
(  SRS_PosResourceId_r16__cond (SRS_PosResource_r16__srs_PosResourceId_r16 z) /\
  SRS_PosResource_r16__transmissionComb_r16__cond (SRS_PosResource_r16__transmissionComb_r16 z) /\
  SRS_PosResource_r16__resourceMapping_r16__cond (SRS_PosResource_r16__resourceMapping_r16 z) /\
  SRS_PosResource_r16__freqDomainShift_r16__cond (SRS_PosResource_r16__freqDomainShift_r16 z) /\
  SRS_PosResource_r16__freqHopping_r16__cond (SRS_PosResource_r16__freqHopping_r16 z) /\
  SRS_PosResource_r16__groupOrSequenceHopping_r16__cond (SRS_PosResource_r16__groupOrSequenceHopping_r16 z) /\
  SRS_PosResource_r16__resourceType_r16__cond (SRS_PosResource_r16__resourceType_r16 z) /\
  SRS_PosResource_r16__sequenceId_r16__cond (SRS_PosResource_r16__sequenceId_r16 z) /\
  opt_cond SRS_SpatialRelationInfoPos_r16__cond (SRS_PosResource_r16__spatialRelationInfoPos_r16 z) /\
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
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__Format : T_Format Z SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__cond :=
 ranged_int_format (0) (1) SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__helper1 SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__helper2.

Opaque SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__Format.

Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__Format : T_Format Z SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__cond :=
 ranged_int_format (0) (7) SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__helper1 SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__helper2.

Opaque SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__Format.


Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Format_list : SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Format_Type :=
  (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16__Format, (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16__Format, unit_format)).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list__Format := (*Eval compute in *) seq_format SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Format_list.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1 z :=
  (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__combOffset_n2_r16 z, (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cyclicShift_n2_r16 z, tt)).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F2 (y : seq_type SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type i0 i1
  end.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1F2_cond (z : SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type)
  : SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond z ->
  (seq_cond SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1 z)).
intro H. unfold SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond in H. simpl. auto. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1F2_cond2 (z : SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type)
 : SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F2 (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F2F1_cond (y : seq_type SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list)
  : seq_cond SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list y ->
 (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F2 y)) /\  SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1 (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond. simpl in *. auto.
 - simpl. unfold SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Format : T_Format SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond :=
        proj2_format  SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__list__Format
    SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1 SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F2 SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1F2_cond  SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F1F2_cond2 SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__F2F1_cond.
Opaque SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Format.

Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__Format : T_Format Z SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__cond :=
 ranged_int_format (0) (3) SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__helper1 SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__helper2.

Opaque SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__Format.

Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__Format : T_Format Z SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__cond :=
 ranged_int_format (0) (11) SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__helper1 SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__helper2.

Opaque SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__Format.


Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Format_list : SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Format_Type :=
  (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16__Format, (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16__Format, unit_format)).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list__Format := (*Eval compute in *) seq_format SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Format_list.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1 z :=
  (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__combOffset_n4_r16 z, (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cyclicShift_n4_r16 z, tt)).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F2 (y : seq_type SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type i0 i1
  end.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1F2_cond (z : SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type)
  : SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond z ->
  (seq_cond SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1 z)).
intro H. unfold SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond in H. simpl. auto. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1F2_cond2 (z : SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type)
 : SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F2 (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F2F1_cond (y : seq_type SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list)
  : seq_cond SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list y ->
 (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F2 y)) /\  SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1 (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond. simpl in *. auto.
 - simpl. unfold SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Format : T_Format SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond :=
        proj2_format  SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__list__Format
    SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1 SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F2 SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1F2_cond  SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F1F2_cond2 SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__F2F1_cond.
Opaque SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Format.

Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__Format : T_Format Z SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__cond :=
 ranged_int_format (0) (7) SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__helper1 SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__helper2.

Opaque SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__Format.

Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__Format : T_Format Z SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__cond :=
 ranged_int_format (0) (5) SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__helper1 SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__helper2.

Opaque SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__Format.


Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Format_list : SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Format_Type :=
  (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16__Format, (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16__Format, unit_format)).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list__Format := (*Eval compute in *) seq_format SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Format_list.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1 z :=
  (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__combOffset_n8_r16 z, (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cyclicShift_n8_r16 z, tt)).
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F2 (y : seq_type SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type i0 i1
  end.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1F2_cond (z : SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type)
  : SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond z ->
  (seq_cond SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1 z)).
intro H. unfold SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond in H. simpl. auto. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1F2_cond2 (z : SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type)
 : SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F2 (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F2F1_cond (y : seq_type SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list)
  : seq_cond SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list y ->
 (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F2 y)) /\  SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1 (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond. simpl in *. auto.
 - simpl. unfold SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Format : T_Format SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond :=
        proj2_format  SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__list__Format
    SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1 SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F2 SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1F2_cond  SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F1F2_cond2 SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__F2F1_cond.
Opaque SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__cond SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Format.


Definition SRS_PosResource_r16__transmissionComb_r16__root__Format_Type := Eval cbn in get_formats SRS_PosResource_r16__transmissionComb_r16__root__list.
Definition SRS_PosResource_r16__transmissionComb_r16__root__Format_list : SRS_PosResource_r16__transmissionComb_r16__root__Format_Type :=
  (SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Format, (SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Format, (SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Format, unit__Format))).
Definition SRS_PosResource_r16__transmissionComb_r16__root__list__Format := Eval compute in choice_format SRS_PosResource_r16__transmissionComb_r16__root__list SRS_PosResource_r16__transmissionComb_r16__root__len_helper1 SRS_PosResource_r16__transmissionComb_r16__root__len_helper2  SRS_PosResource_r16__transmissionComb_r16__root__Format_list.
Definition SRS_PosResource_r16__transmissionComb_r16__root__F1 (z : SRS_PosResource_r16__transmissionComb_r16__root__Type) : (choice SRS_PosResource_r16__transmissionComb_r16__root__list) :=
  match z with
   | SRS_PosResource_r16__transmissionComb_r16__root__n2_r16 t => existT _ 0 t
  | SRS_PosResource_r16__transmissionComb_r16__root__n4_r16 t => existT _ 1 t
  | SRS_PosResource_r16__transmissionComb_r16__root__n8_r16 t => existT _ 2 t
  end.
Definition SRS_PosResource_r16__transmissionComb_r16__root__g := (fun n => typ_set (get_nth_typ SRS_PosResource_r16__transmissionComb_r16__root__list n)).
Definition SRS_PosResource_r16__transmissionComb_r16__root__F2 (y : choice SRS_PosResource_r16__transmissionComb_r16__root__list) : SRS_PosResource_r16__transmissionComb_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_PosResource_r16__transmissionComb_r16__root__g n -> SRS_PosResource_r16__transmissionComb_r16__root__Type) with
    | 0 => fun (t : SRS_PosResource_r16__transmissionComb_r16__root__n2_r16__Type) => SRS_PosResource_r16__transmissionComb_r16__root__n2_r16 t 
    | 1 => fun (t : SRS_PosResource_r16__transmissionComb_r16__root__n4_r16__Type) => SRS_PosResource_r16__transmissionComb_r16__root__n4_r16 t 
    | 2 => fun (t : SRS_PosResource_r16__transmissionComb_r16__root__n8_r16__Type) => SRS_PosResource_r16__transmissionComb_r16__root__n8_r16 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SRS_PosResource_r16__transmissionComb_r16__root__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SRS_PosResource_r16__transmissionComb_r16__root__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_PosResource_r16__transmissionComb_r16__root__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SRS_PosResource_r16__transmissionComb_r16__root__Type with end) n0
           end t0).

Lemma SRS_PosResource_r16__transmissionComb_r16__root__helper2 :  forall (y : SRS_PosResource_r16__transmissionComb_r16__root__Type), SRS_PosResource_r16__transmissionComb_r16__root__cond y -> choice_cond SRS_PosResource_r16__transmissionComb_r16__root__list (SRS_PosResource_r16__transmissionComb_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_PosResource_r16__transmissionComb_r16__root__helper3 :  forall (y : SRS_PosResource_r16__transmissionComb_r16__root__Type), SRS_PosResource_r16__transmissionComb_r16__root__F2 (SRS_PosResource_r16__transmissionComb_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_PosResource_r16__transmissionComb_r16__root__helper4 : (forall b : choice SRS_PosResource_r16__transmissionComb_r16__root__list, choice_cond SRS_PosResource_r16__transmissionComb_r16__root__list b -> SRS_PosResource_r16__transmissionComb_r16__root__cond (SRS_PosResource_r16__transmissionComb_r16__root__F2 b) /\ SRS_PosResource_r16__transmissionComb_r16__root__F1 (SRS_PosResource_r16__transmissionComb_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_PosResource_r16__transmissionComb_r16__root__F1 SRS_PosResource_r16__transmissionComb_r16__root__F2.
Definition SRS_PosResource_r16__transmissionComb_r16__root__Format : T_Format SRS_PosResource_r16__transmissionComb_r16__root__Type SRS_PosResource_r16__transmissionComb_r16__root__cond :=
  (* Eval compute in *) proj2_format SRS_PosResource_r16__transmissionComb_r16__root__cond SRS_PosResource_r16__transmissionComb_r16__root__list__Format SRS_PosResource_r16__transmissionComb_r16__root__F1 SRS_PosResource_r16__transmissionComb_r16__root__F2 SRS_PosResource_r16__transmissionComb_r16__root__helper2 SRS_PosResource_r16__transmissionComb_r16__root__helper3 SRS_PosResource_r16__transmissionComb_r16__root__helper4.
Opaque SRS_PosResource_r16__transmissionComb_r16__root__cond SRS_PosResource_r16__transmissionComb_r16__root__Format.

Definition SRS_PosResource_r16__transmissionComb_r16__ext__Format : T_Format SRS_PosResource_r16__transmissionComb_r16__ext__Type SRS_PosResource_r16__transmissionComb_r16__ext__cond := empty_format.
Opaque SRS_PosResource_r16__transmissionComb_r16__ext__cond SRS_PosResource_r16__transmissionComb_r16__ext__Format.

Definition SRS_PosResource_r16__transmissionComb_r16__Format : T_Format SRS_PosResource_r16__transmissionComb_r16__Type SRS_PosResource_r16__transmissionComb_r16__cond := sum_format SRS_PosResource_r16__transmissionComb_r16__root__Format SRS_PosResource_r16__transmissionComb_r16__ext__Format.
Opaque SRS_PosResource_r16__transmissionComb_r16__cond SRS_PosResource_r16__transmissionComb_r16__Format.

Definition SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__Format : T_Format Z SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__cond :=
 ranged_int_format (0) (13) SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__helper1 SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__helper2.

Opaque SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__cond SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__Format.

Definition SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Format : T_Format SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__nat__Format SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F1 SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F2 SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F1F2 SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__F2F1.

Opaque SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__cond SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Format.


Definition SRS_PosResource_r16__resourceMapping_r16__Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__resourceMapping_r16__list.
Definition SRS_PosResource_r16__resourceMapping_r16__Format_list : SRS_PosResource_r16__resourceMapping_r16__Format_Type :=
  (SRS_PosResource_r16__resourceMapping_r16__startPosition_r16__Format, (SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16__Format, unit_format)).
Definition SRS_PosResource_r16__resourceMapping_r16__list__Format := (*Eval compute in *) seq_format SRS_PosResource_r16__resourceMapping_r16__list SRS_PosResource_r16__resourceMapping_r16__Format_list.
Definition SRS_PosResource_r16__resourceMapping_r16__F1 z :=
  (SRS_PosResource_r16__resourceMapping_r16__startPosition_r16 z, (SRS_PosResource_r16__resourceMapping_r16__nrofSymbols_r16 z, tt)).
Definition SRS_PosResource_r16__resourceMapping_r16__F2 (y : seq_type SRS_PosResource_r16__resourceMapping_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_PosResource_r16__resourceMapping_r16__Type i0 i1
  end.
Lemma SRS_PosResource_r16__resourceMapping_r16__F1F2_cond (z : SRS_PosResource_r16__resourceMapping_r16__Type)
  : SRS_PosResource_r16__resourceMapping_r16__cond z ->
  (seq_cond SRS_PosResource_r16__resourceMapping_r16__list (SRS_PosResource_r16__resourceMapping_r16__F1 z)).
intro H. unfold SRS_PosResource_r16__resourceMapping_r16__cond in H. simpl. auto. Qed.
Lemma SRS_PosResource_r16__resourceMapping_r16__F1F2_cond2 (z : SRS_PosResource_r16__resourceMapping_r16__Type)
 : SRS_PosResource_r16__resourceMapping_r16__F2 (SRS_PosResource_r16__resourceMapping_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_PosResource_r16__resourceMapping_r16__F2F1_cond (y : seq_type SRS_PosResource_r16__resourceMapping_r16__list)
  : seq_cond SRS_PosResource_r16__resourceMapping_r16__list y ->
 (SRS_PosResource_r16__resourceMapping_r16__cond (SRS_PosResource_r16__resourceMapping_r16__F2 y)) /\  SRS_PosResource_r16__resourceMapping_r16__F1 (SRS_PosResource_r16__resourceMapping_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_PosResource_r16__resourceMapping_r16__cond. simpl in *. auto.
 - simpl. unfold SRS_PosResource_r16__resourceMapping_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_PosResource_r16__resourceMapping_r16__Format : T_Format SRS_PosResource_r16__resourceMapping_r16__Type SRS_PosResource_r16__resourceMapping_r16__cond :=
        proj2_format  SRS_PosResource_r16__resourceMapping_r16__cond SRS_PosResource_r16__resourceMapping_r16__list__Format
    SRS_PosResource_r16__resourceMapping_r16__F1 SRS_PosResource_r16__resourceMapping_r16__F2 SRS_PosResource_r16__resourceMapping_r16__F1F2_cond  SRS_PosResource_r16__resourceMapping_r16__F1F2_cond2 SRS_PosResource_r16__resourceMapping_r16__F2F1_cond.
Opaque SRS_PosResource_r16__resourceMapping_r16__cond SRS_PosResource_r16__resourceMapping_r16__Format.

Definition SRS_PosResource_r16__freqDomainShift_r16__Format : T_Format Z SRS_PosResource_r16__freqDomainShift_r16__cond :=
 ranged_int_format (0) (268) SRS_PosResource_r16__freqDomainShift_r16__helper1 SRS_PosResource_r16__freqDomainShift_r16__helper2.

Opaque SRS_PosResource_r16__freqDomainShift_r16__cond SRS_PosResource_r16__freqDomainShift_r16__Format.

Definition SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__Format : T_Format Z SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__cond :=
 ranged_int_format (0) (63) SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__helper1 SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__helper2.

Opaque SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__cond SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__Format.


Definition SRS_PosResource_r16__freqHopping_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__freqHopping_r16__root_list.
Definition SRS_PosResource_r16__freqHopping_r16__root_Format_list : SRS_PosResource_r16__freqHopping_r16__root_Format_Type :=
  (SRS_PosResource_r16__freqHopping_r16__c_SRS_r16__Format, unit_format).

Definition SRS_PosResource_r16__freqHopping_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResource_r16__freqHopping_r16__ext_list.
Definition SRS_PosResource_r16__freqHopping_r16__ext_Format_list : SRS_PosResource_r16__freqHopping_r16__ext_Format_Type :=
  unit__Format.

Definition SRS_PosResource_r16__freqHopping_r16__list_type : Set := (seq_type SRS_PosResource_r16__freqHopping_r16__root_list) * (seq_ext_type SRS_PosResource_r16__freqHopping_r16__ext_list).
Definition SRS_PosResource_r16__freqHopping_r16__list_cond (z : SRS_PosResource_r16__freqHopping_r16__list_type) : Prop :=
        (seq_cond SRS_PosResource_r16__freqHopping_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResource_r16__freqHopping_r16__ext_list (snd z)).
Definition SRS_PosResource_r16__freqHopping_r16__list_format : T_Format SRS_PosResource_r16__freqHopping_r16__list_type SRS_PosResource_r16__freqHopping_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResource_r16__freqHopping_r16__root_list SRS_PosResource_r16__freqHopping_r16__root_Format_list SRS_PosResource_r16__freqHopping_r16__ext_list SRS_PosResource_r16__freqHopping_r16__ext_Format_list.

Opaque SRS_PosResource_r16__freqHopping_r16__list_format.
Definition SRS_PosResource_r16__freqHopping_r16__F1 (z : SRS_PosResource_r16__freqHopping_r16__Type) : SRS_PosResource_r16__freqHopping_r16__list_type :=
  (((SRS_PosResource_r16__freqHopping_r16__c_SRS_r16 z, tt)), (
tt)).
Definition SRS_PosResource_r16__freqHopping_r16__F2 (y : SRS_PosResource_r16__freqHopping_r16__list_type) : SRS_PosResource_r16__freqHopping_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__SRS_PosResource_r16__freqHopping_r16__Type j0
  end.
Definition SRS_PosResource_r16__freqHopping_r16__helper1 : (forall a : SRS_PosResource_r16__freqHopping_r16__Type, SRS_PosResource_r16__freqHopping_r16__cond a -> SRS_PosResource_r16__freqHopping_r16__list_cond (SRS_PosResource_r16__freqHopping_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__freqHopping_r16__helper2 : (forall a : SRS_PosResource_r16__freqHopping_r16__Type, SRS_PosResource_r16__freqHopping_r16__F2 (SRS_PosResource_r16__freqHopping_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__freqHopping_r16__helper3 : (forall b : SRS_PosResource_r16__freqHopping_r16__list_type, SRS_PosResource_r16__freqHopping_r16__list_cond b -> SRS_PosResource_r16__freqHopping_r16__cond (SRS_PosResource_r16__freqHopping_r16__F2 b) /\ SRS_PosResource_r16__freqHopping_r16__F1 (SRS_PosResource_r16__freqHopping_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResource_r16__freqHopping_r16__cond, SRS_PosResource_r16__freqHopping_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResource_r16__freqHopping_r16__Format : T_Format SRS_PosResource_r16__freqHopping_r16__Type SRS_PosResource_r16__freqHopping_r16__cond :=
 proj2_format SRS_PosResource_r16__freqHopping_r16__cond SRS_PosResource_r16__freqHopping_r16__list_format  SRS_PosResource_r16__freqHopping_r16__F1 SRS_PosResource_r16__freqHopping_r16__F2 SRS_PosResource_r16__freqHopping_r16__helper1 SRS_PosResource_r16__freqHopping_r16__helper2 SRS_PosResource_r16__freqHopping_r16__helper3.

Opaque SRS_PosResource_r16__freqHopping_r16__cond SRS_PosResource_r16__freqHopping_r16__Format.

Definition SRS_PosResource_r16__groupOrSequenceHopping_r16__Format : T_Format SRS_PosResource_r16__groupOrSequenceHopping_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_PosResource_r16__groupOrSequenceHopping_r16__nat__Format SRS_PosResource_r16__groupOrSequenceHopping_r16__F1 SRS_PosResource_r16__groupOrSequenceHopping_r16__F2 SRS_PosResource_r16__groupOrSequenceHopping_r16__F1F2 SRS_PosResource_r16__groupOrSequenceHopping_r16__F2F1.

Opaque SRS_PosResource_r16__groupOrSequenceHopping_r16__cond SRS_PosResource_r16__groupOrSequenceHopping_r16__Format.

Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__Format : T_Format Z SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__cond :=
 ranged_int_format (1) (32) SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__helper1 SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__helper2.

Opaque SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__cond SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__Format.


Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_list.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_Format_list : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_Format_Type :=
  (SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16__Format, unit_format).

Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_list.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_Format_list : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_Format_Type :=
  unit__Format.

Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_type : Set := (seq_type SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_list) * (seq_ext_type SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_list).
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_cond (z : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_type) : Prop :=
        (seq_cond SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_list (snd z)).
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_format : T_Format SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_type SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_list SRS_PosResource_r16__resourceType_r16__aperiodic_r16__root_Format_list SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_list SRS_PosResource_r16__resourceType_r16__aperiodic_r16__ext_Format_list.

Opaque SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_format.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F1 (z : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type) : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_type :=
  (((SRS_PosResource_r16__resourceType_r16__aperiodic_r16__slotOffset_r16 z, tt)), (
tt)).
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F2 (y : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_type) : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type :=
  match y with
  | ((j0, _), _)=>
    make__SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type j0
  end.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__helper1 : (forall a : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type, SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond a -> SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_cond (SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__helper2 : (forall a : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type, SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F2 (SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__helper3 : (forall b : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_type, SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_cond b -> SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond (SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F2 b) /\ SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F1 (SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond, SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Format : T_Format SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond :=
 proj2_format SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond SRS_PosResource_r16__resourceType_r16__aperiodic_r16__list_format  SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F1 SRS_PosResource_r16__resourceType_r16__aperiodic_r16__F2 SRS_PosResource_r16__resourceType_r16__aperiodic_r16__helper1 SRS_PosResource_r16__resourceType_r16__aperiodic_r16__helper2 SRS_PosResource_r16__resourceType_r16__aperiodic_r16__helper3.

Opaque SRS_PosResource_r16__resourceType_r16__aperiodic_r16__cond SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Format.


Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Format_list : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Format_Type :=
  (SRS_PeriodicityAndOffsetExt_r16__Format, unit_format).
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list__Format := (*Eval compute in *) seq_format SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Format_list.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1 z :=
  (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__periodicityAndOffset_sp_Ext_r16 z, tt).
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F2 (y : seq_type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type i0
  end.
Lemma SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1F2_cond (z : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type)
  : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond z ->
  (seq_cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1 z)).
intro H. unfold SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1F2_cond2 (z : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type)
 : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F2 (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F2F1_cond (y : seq_type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list)
  : seq_cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list y ->
 (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F2 y)) /\  SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1 (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Format : T_Format SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond :=
        proj2_format  SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__list__Format
    SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1 SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F2 SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1F2_cond  SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F1F2_cond2 SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__F2F1_cond.
Opaque SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Format.

Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__check_all_none (b : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type) : bool :=
match b with 
  | make__SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__Format : T_Format SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__Type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__cond :=
  restrict_add_format SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__check_all_none SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0O__Format.

Opaque SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__Format.


Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_list.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_Format_list : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_Format_Type :=
  (SRS_PeriodicityAndOffset_r16__Format, unit_format).

Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_list.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_Format_list : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_Format_Type :=
  (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0__Format, unit__Format).

Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_type : Set := (seq_type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_list) * (seq_ext_type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_list).
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_cond (z : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_type) : Prop :=
        (seq_cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_list (snd z)).
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_format : T_Format SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_list SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__root_Format_list SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_list SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext_Format_list.

Opaque SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_format.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F1 (z : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type) : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_type :=
  (((SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__periodicityAndOffset_sp_r16 z, tt)), (
(SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__ext0 z, tt))).
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F2 (y : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_type) : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type j0 i0
  end.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__helper1 : (forall a : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type, SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond a -> SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_cond (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__helper2 : (forall a : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type, SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F2 (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__helper3 : (forall b : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_type, SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_cond b -> SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F2 b) /\ SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F1 (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond, SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Format : T_Format SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond :=
 proj2_format SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__list_format  SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F1 SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__F2 SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__helper1 SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__helper2 SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__helper3.

Opaque SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__cond SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Format.


Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Format_list : SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Format_Type :=
  (SRS_PeriodicityAndOffsetExt_r16__Format, unit_format).
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list__Format := (*Eval compute in *) seq_format SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Format_list.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1 z :=
  (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__periodicityAndOffset_p_Ext_r16 z, tt).
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F2 (y : seq_type SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type i0
  end.
Lemma SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1F2_cond (z : SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type)
  : SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond z ->
  (seq_cond SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1 z)).
intro H. unfold SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1F2_cond2 (z : SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type)
 : SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F2 (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F2F1_cond (y : seq_type SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list)
  : seq_cond SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list y ->
 (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F2 y)) /\  SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1 (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Format : T_Format SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond :=
        proj2_format  SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__list__Format
    SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1 SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F2 SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1F2_cond  SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F1F2_cond2 SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__F2F1_cond.
Opaque SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__cond SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Format.

Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__check_all_none (b : SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type) : bool :=
match b with 
  | make__SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__Format : T_Format SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__Type SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__cond :=
  restrict_add_format SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__check_all_none SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0O__Format.

Opaque SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__cond SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__Format.


Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__resourceType_r16__periodic_r16__root_list.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__root_Format_list : SRS_PosResource_r16__resourceType_r16__periodic_r16__root_Format_Type :=
  (SRS_PeriodicityAndOffset_r16__Format, unit_format).

Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_list.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_Format_list : SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_Format_Type :=
  (SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0__Format, unit__Format).

Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__list_type : Set := (seq_type SRS_PosResource_r16__resourceType_r16__periodic_r16__root_list) * (seq_ext_type SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_list).
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__list_cond (z : SRS_PosResource_r16__resourceType_r16__periodic_r16__list_type) : Prop :=
        (seq_cond SRS_PosResource_r16__resourceType_r16__periodic_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_list (snd z)).
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__list_format : T_Format SRS_PosResource_r16__resourceType_r16__periodic_r16__list_type SRS_PosResource_r16__resourceType_r16__periodic_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResource_r16__resourceType_r16__periodic_r16__root_list SRS_PosResource_r16__resourceType_r16__periodic_r16__root_Format_list SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_list SRS_PosResource_r16__resourceType_r16__periodic_r16__ext_Format_list.

Opaque SRS_PosResource_r16__resourceType_r16__periodic_r16__list_format.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__F1 (z : SRS_PosResource_r16__resourceType_r16__periodic_r16__Type) : SRS_PosResource_r16__resourceType_r16__periodic_r16__list_type :=
  (((SRS_PosResource_r16__resourceType_r16__periodic_r16__periodicityAndOffset_p_r16 z, tt)), (
(SRS_PosResource_r16__resourceType_r16__periodic_r16__ext0 z, tt))).
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__F2 (y : SRS_PosResource_r16__resourceType_r16__periodic_r16__list_type) : SRS_PosResource_r16__resourceType_r16__periodic_r16__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__SRS_PosResource_r16__resourceType_r16__periodic_r16__Type j0 i0
  end.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__helper1 : (forall a : SRS_PosResource_r16__resourceType_r16__periodic_r16__Type, SRS_PosResource_r16__resourceType_r16__periodic_r16__cond a -> SRS_PosResource_r16__resourceType_r16__periodic_r16__list_cond (SRS_PosResource_r16__resourceType_r16__periodic_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__helper2 : (forall a : SRS_PosResource_r16__resourceType_r16__periodic_r16__Type, SRS_PosResource_r16__resourceType_r16__periodic_r16__F2 (SRS_PosResource_r16__resourceType_r16__periodic_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__helper3 : (forall b : SRS_PosResource_r16__resourceType_r16__periodic_r16__list_type, SRS_PosResource_r16__resourceType_r16__periodic_r16__list_cond b -> SRS_PosResource_r16__resourceType_r16__periodic_r16__cond (SRS_PosResource_r16__resourceType_r16__periodic_r16__F2 b) /\ SRS_PosResource_r16__resourceType_r16__periodic_r16__F1 (SRS_PosResource_r16__resourceType_r16__periodic_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResource_r16__resourceType_r16__periodic_r16__cond, SRS_PosResource_r16__resourceType_r16__periodic_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResource_r16__resourceType_r16__periodic_r16__Format : T_Format SRS_PosResource_r16__resourceType_r16__periodic_r16__Type SRS_PosResource_r16__resourceType_r16__periodic_r16__cond :=
 proj2_format SRS_PosResource_r16__resourceType_r16__periodic_r16__cond SRS_PosResource_r16__resourceType_r16__periodic_r16__list_format  SRS_PosResource_r16__resourceType_r16__periodic_r16__F1 SRS_PosResource_r16__resourceType_r16__periodic_r16__F2 SRS_PosResource_r16__resourceType_r16__periodic_r16__helper1 SRS_PosResource_r16__resourceType_r16__periodic_r16__helper2 SRS_PosResource_r16__resourceType_r16__periodic_r16__helper3.

Opaque SRS_PosResource_r16__resourceType_r16__periodic_r16__cond SRS_PosResource_r16__resourceType_r16__periodic_r16__Format.


Definition SRS_PosResource_r16__resourceType_r16__Format_Type := Eval cbn in get_formats SRS_PosResource_r16__resourceType_r16__list.
Definition SRS_PosResource_r16__resourceType_r16__Format_list : SRS_PosResource_r16__resourceType_r16__Format_Type :=
  (SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Format, (SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Format, (SRS_PosResource_r16__resourceType_r16__periodic_r16__Format, unit__Format))).
Definition SRS_PosResource_r16__resourceType_r16__list__Format := Eval compute in choice_format SRS_PosResource_r16__resourceType_r16__list SRS_PosResource_r16__resourceType_r16__len_helper1 SRS_PosResource_r16__resourceType_r16__len_helper2  SRS_PosResource_r16__resourceType_r16__Format_list.
Definition SRS_PosResource_r16__resourceType_r16__F1 (z : SRS_PosResource_r16__resourceType_r16__Type) : (choice SRS_PosResource_r16__resourceType_r16__list) :=
  match z with
   | SRS_PosResource_r16__resourceType_r16__aperiodic_r16 t => existT _ 0 t
  | SRS_PosResource_r16__resourceType_r16__semi_persistent_r16 t => existT _ 1 t
  | SRS_PosResource_r16__resourceType_r16__periodic_r16 t => existT _ 2 t
  end.
Definition SRS_PosResource_r16__resourceType_r16__g := (fun n => typ_set (get_nth_typ SRS_PosResource_r16__resourceType_r16__list n)).
Definition SRS_PosResource_r16__resourceType_r16__F2 (y : choice SRS_PosResource_r16__resourceType_r16__list) : SRS_PosResource_r16__resourceType_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_PosResource_r16__resourceType_r16__g n -> SRS_PosResource_r16__resourceType_r16__Type) with
    | 0 => fun (t : SRS_PosResource_r16__resourceType_r16__aperiodic_r16__Type) => SRS_PosResource_r16__resourceType_r16__aperiodic_r16 t 
    | 1 => fun (t : SRS_PosResource_r16__resourceType_r16__semi_persistent_r16__Type) => SRS_PosResource_r16__resourceType_r16__semi_persistent_r16 t 
    | 2 => fun (t : SRS_PosResource_r16__resourceType_r16__periodic_r16__Type) => SRS_PosResource_r16__resourceType_r16__periodic_r16 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SRS_PosResource_r16__resourceType_r16__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SRS_PosResource_r16__resourceType_r16__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_PosResource_r16__resourceType_r16__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SRS_PosResource_r16__resourceType_r16__Type with end) n0
           end t0).

Lemma SRS_PosResource_r16__resourceType_r16__helper2 :  forall (y : SRS_PosResource_r16__resourceType_r16__Type), SRS_PosResource_r16__resourceType_r16__cond y -> choice_cond SRS_PosResource_r16__resourceType_r16__list (SRS_PosResource_r16__resourceType_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_PosResource_r16__resourceType_r16__helper3 :  forall (y : SRS_PosResource_r16__resourceType_r16__Type), SRS_PosResource_r16__resourceType_r16__F2 (SRS_PosResource_r16__resourceType_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_PosResource_r16__resourceType_r16__helper4 : (forall b : choice SRS_PosResource_r16__resourceType_r16__list, choice_cond SRS_PosResource_r16__resourceType_r16__list b -> SRS_PosResource_r16__resourceType_r16__cond (SRS_PosResource_r16__resourceType_r16__F2 b) /\ SRS_PosResource_r16__resourceType_r16__F1 (SRS_PosResource_r16__resourceType_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_PosResource_r16__resourceType_r16__F1 SRS_PosResource_r16__resourceType_r16__F2.
Definition SRS_PosResource_r16__resourceType_r16__Format : T_Format SRS_PosResource_r16__resourceType_r16__Type SRS_PosResource_r16__resourceType_r16__cond :=
  (* Eval compute in *) proj2_format SRS_PosResource_r16__resourceType_r16__cond SRS_PosResource_r16__resourceType_r16__list__Format SRS_PosResource_r16__resourceType_r16__F1 SRS_PosResource_r16__resourceType_r16__F2 SRS_PosResource_r16__resourceType_r16__helper2 SRS_PosResource_r16__resourceType_r16__helper3 SRS_PosResource_r16__resourceType_r16__helper4.
Opaque SRS_PosResource_r16__resourceType_r16__cond SRS_PosResource_r16__resourceType_r16__Format.

Definition SRS_PosResource_r16__sequenceId_r16__Format : T_Format Z SRS_PosResource_r16__sequenceId_r16__cond :=
 ranged_int_format (0) (65535) SRS_PosResource_r16__sequenceId_r16__helper1 SRS_PosResource_r16__sequenceId_r16__helper2.

Opaque SRS_PosResource_r16__sequenceId_r16__cond SRS_PosResource_r16__sequenceId_r16__Format.


Definition SRS_PosResource_r16__root_Format_Type := Eval cbn in seq_format_prod SRS_PosResource_r16__root_list.
Definition SRS_PosResource_r16__root_Format_list : SRS_PosResource_r16__root_Format_Type :=
  (SRS_PosResourceId_r16__Format, (SRS_PosResource_r16__transmissionComb_r16__Format, (SRS_PosResource_r16__resourceMapping_r16__Format, (SRS_PosResource_r16__freqDomainShift_r16__Format, (SRS_PosResource_r16__freqHopping_r16__Format, (SRS_PosResource_r16__groupOrSequenceHopping_r16__Format, (SRS_PosResource_r16__resourceType_r16__Format, (SRS_PosResource_r16__sequenceId_r16__Format, (SRS_SpatialRelationInfoPos_r16__Format, unit_format))))))))).

Definition SRS_PosResource_r16__ext_Format_Type := Eval cbn in get_formats SRS_PosResource_r16__ext_list.
Definition SRS_PosResource_r16__ext_Format_list : SRS_PosResource_r16__ext_Format_Type :=
  unit__Format.

Definition SRS_PosResource_r16__list_type : Set := (seq_type SRS_PosResource_r16__root_list) * (seq_ext_type SRS_PosResource_r16__ext_list).
Definition SRS_PosResource_r16__list_cond (z : SRS_PosResource_r16__list_type) : Prop :=
        (seq_cond SRS_PosResource_r16__root_list (fst z)) /\ (seq_ext_cond SRS_PosResource_r16__ext_list (snd z)).
Definition SRS_PosResource_r16__list_format : T_Format SRS_PosResource_r16__list_type SRS_PosResource_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_PosResource_r16__root_list SRS_PosResource_r16__root_Format_list SRS_PosResource_r16__ext_list SRS_PosResource_r16__ext_Format_list.

Opaque SRS_PosResource_r16__list_format.
Definition SRS_PosResource_r16__F1 (z : SRS_PosResource_r16__Type) : SRS_PosResource_r16__list_type :=
  (((SRS_PosResource_r16__srs_PosResourceId_r16 z, (SRS_PosResource_r16__transmissionComb_r16 z, (SRS_PosResource_r16__resourceMapping_r16 z, (SRS_PosResource_r16__freqDomainShift_r16 z, (SRS_PosResource_r16__freqHopping_r16 z, (SRS_PosResource_r16__groupOrSequenceHopping_r16 z, (SRS_PosResource_r16__resourceType_r16 z, (SRS_PosResource_r16__sequenceId_r16 z, (SRS_PosResource_r16__spatialRelationInfoPos_r16 z, tt)))))))))), (
tt)).
Definition SRS_PosResource_r16__F2 (y : SRS_PosResource_r16__list_type) : SRS_PosResource_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), _)=>
    make__SRS_PosResource_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8
  end.
Definition SRS_PosResource_r16__helper1 : (forall a : SRS_PosResource_r16__Type, SRS_PosResource_r16__cond a -> SRS_PosResource_r16__list_cond (SRS_PosResource_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__helper2 : (forall a : SRS_PosResource_r16__Type, SRS_PosResource_r16__F2 (SRS_PosResource_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_PosResource_r16__helper3 : (forall b : SRS_PosResource_r16__list_type, SRS_PosResource_r16__list_cond b -> SRS_PosResource_r16__cond (SRS_PosResource_r16__F2 b) /\ SRS_PosResource_r16__F1 (SRS_PosResource_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_PosResource_r16__cond, SRS_PosResource_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_PosResource_r16__Format : T_Format SRS_PosResource_r16__Type SRS_PosResource_r16__cond :=
 proj2_format SRS_PosResource_r16__cond SRS_PosResource_r16__list_format  SRS_PosResource_r16__F1 SRS_PosResource_r16__F2 SRS_PosResource_r16__helper1 SRS_PosResource_r16__helper2 SRS_PosResource_r16__helper3.

Opaque SRS_PosResource_r16__cond SRS_PosResource_r16__Format.

