Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_ResourceId.

Opaque SRS_ResourceId__cond SRS_ResourceId__Format.

Inductive SRS_Resource__nrofSRS_Ports__Type : Set :=
 | SRS_Resource__nrofSRS_Ports__port1
 | SRS_Resource__nrofSRS_Ports__ports2
 | SRS_Resource__nrofSRS_Ports__ports4
.
Definition SRS_Resource__nrofSRS_Ports__cond := (fun (_ : SRS_Resource__nrofSRS_Ports__Type) => True).
Lemma SRS_Resource__nrofSRS_Ports__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__nrofSRS_Ports__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SRS_Resource__nrofSRS_Ports__nat__helper.

Definition SRS_Resource__nrofSRS_Ports__F1 t :=
  match t with
  | SRS_Resource__nrofSRS_Ports__port1 => 0
  | SRS_Resource__nrofSRS_Ports__ports2 => 1
  | SRS_Resource__nrofSRS_Ports__ports4 => 2
  end.
Definition SRS_Resource__nrofSRS_Ports__F2 n :=
  match n with
  | 0 => SRS_Resource__nrofSRS_Ports__port1
  | 1 => SRS_Resource__nrofSRS_Ports__ports2
  | 2 => SRS_Resource__nrofSRS_Ports__ports4
  | _ => SRS_Resource__nrofSRS_Ports__port1
  end.
Lemma SRS_Resource__nrofSRS_Ports__F1F2 : forall x : SRS_Resource__nrofSRS_Ports__Type, (SRS_Resource__nrofSRS_Ports__F1 x <= 2) /\ SRS_Resource__nrofSRS_Ports__F2 (SRS_Resource__nrofSRS_Ports__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__nrofSRS_Ports__F2F1 : forall (y : nat) (H : y <= 2), SRS_Resource__nrofSRS_Ports__F1 (SRS_Resource__nrofSRS_Ports__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_Resource__ptrs_PortIndex__Type : Set :=
 | SRS_Resource__ptrs_PortIndex__n0
 | SRS_Resource__ptrs_PortIndex__n1
.
Definition SRS_Resource__ptrs_PortIndex__cond := (fun (_ : SRS_Resource__ptrs_PortIndex__Type) => True).
Lemma SRS_Resource__ptrs_PortIndex__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__ptrs_PortIndex__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SRS_Resource__ptrs_PortIndex__nat__helper.

Definition SRS_Resource__ptrs_PortIndex__F1 t :=
  match t with
  | SRS_Resource__ptrs_PortIndex__n0 => 0
  | SRS_Resource__ptrs_PortIndex__n1 => 1
  end.
Definition SRS_Resource__ptrs_PortIndex__F2 n :=
  match n with
  | 0 => SRS_Resource__ptrs_PortIndex__n0
  | 1 => SRS_Resource__ptrs_PortIndex__n1
  | _ => SRS_Resource__ptrs_PortIndex__n0
  end.
Lemma SRS_Resource__ptrs_PortIndex__F1F2 : forall x : SRS_Resource__ptrs_PortIndex__Type, (SRS_Resource__ptrs_PortIndex__F1 x <= 1) /\ SRS_Resource__ptrs_PortIndex__F2 (SRS_Resource__ptrs_PortIndex__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__ptrs_PortIndex__F2F1 : forall (y : nat) (H : y <= 1), SRS_Resource__ptrs_PortIndex__F1 (SRS_Resource__ptrs_PortIndex__F2 y) = y. enum_solve H y. Qed.

Lemma SRS_Resource__transmissionComb__n2__combOffset_n2__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma SRS_Resource__transmissionComb__n2__combOffset_n2__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__transmissionComb__n2__combOffset_n2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__transmissionComb__n2__combOffset_n2__Type := Z.
Definition SRS_Resource__transmissionComb__n2__combOffset_n2__cond := (fun z => (0 <= z <= 1)%Z).
Lemma SRS_Resource__transmissionComb__n2__cyclicShift_n2__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma SRS_Resource__transmissionComb__n2__cyclicShift_n2__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__transmissionComb__n2__cyclicShift_n2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__transmissionComb__n2__cyclicShift_n2__Type := Z.
Definition SRS_Resource__transmissionComb__n2__cyclicShift_n2__cond := (fun z => (0 <= z <= 7)%Z).
Record SRS_Resource__transmissionComb__n2__Type : Set :=
  make__SRS_Resource__transmissionComb__n2__Type {
    SRS_Resource__transmissionComb__n2__combOffset_n2 : Z ;
    SRS_Resource__transmissionComb__n2__cyclicShift_n2 : Z ;
}.
Definition SRS_Resource__transmissionComb__n2__list := (
 Nor Z SRS_Resource__transmissionComb__n2__combOffset_n2__cond ::
 Nor Z SRS_Resource__transmissionComb__n2__cyclicShift_n2__cond ::
 nil).
Definition SRS_Resource__transmissionComb__n2__cond z := 
  SRS_Resource__transmissionComb__n2__combOffset_n2__cond (SRS_Resource__transmissionComb__n2__combOffset_n2 z) /\
  SRS_Resource__transmissionComb__n2__cyclicShift_n2__cond (SRS_Resource__transmissionComb__n2__cyclicShift_n2 z) /\
  True.

Lemma SRS_Resource__transmissionComb__n4__combOffset_n4__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SRS_Resource__transmissionComb__n4__combOffset_n4__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__transmissionComb__n4__combOffset_n4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__transmissionComb__n4__combOffset_n4__Type := Z.
Definition SRS_Resource__transmissionComb__n4__combOffset_n4__cond := (fun z => (0 <= z <= 3)%Z).
Lemma SRS_Resource__transmissionComb__n4__cyclicShift_n4__helper1 : (0 <= 11)%Z.  lia. Qed.
Lemma SRS_Resource__transmissionComb__n4__cyclicShift_n4__helper2 : to_bit_sz (Z.to_nat (11 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (11 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__transmissionComb__n4__cyclicShift_n4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__transmissionComb__n4__cyclicShift_n4__Type := Z.
Definition SRS_Resource__transmissionComb__n4__cyclicShift_n4__cond := (fun z => (0 <= z <= 11)%Z).
Record SRS_Resource__transmissionComb__n4__Type : Set :=
  make__SRS_Resource__transmissionComb__n4__Type {
    SRS_Resource__transmissionComb__n4__combOffset_n4 : Z ;
    SRS_Resource__transmissionComb__n4__cyclicShift_n4 : Z ;
}.
Definition SRS_Resource__transmissionComb__n4__list := (
 Nor Z SRS_Resource__transmissionComb__n4__combOffset_n4__cond ::
 Nor Z SRS_Resource__transmissionComb__n4__cyclicShift_n4__cond ::
 nil).
Definition SRS_Resource__transmissionComb__n4__cond z := 
  SRS_Resource__transmissionComb__n4__combOffset_n4__cond (SRS_Resource__transmissionComb__n4__combOffset_n4 z) /\
  SRS_Resource__transmissionComb__n4__cyclicShift_n4__cond (SRS_Resource__transmissionComb__n4__cyclicShift_n4 z) /\
  True.


Inductive SRS_Resource__transmissionComb__Type : Set :=
  | SRS_Resource__transmissionComb__n2 : SRS_Resource__transmissionComb__n2__Type -> SRS_Resource__transmissionComb__Type
  | SRS_Resource__transmissionComb__n4 : SRS_Resource__transmissionComb__n4__Type -> SRS_Resource__transmissionComb__Type
.
Definition SRS_Resource__transmissionComb__list : list typ := (
typ_cons SRS_Resource__transmissionComb__n2__Type SRS_Resource__transmissionComb__n2__cond ::
typ_cons SRS_Resource__transmissionComb__n4__Type SRS_Resource__transmissionComb__n4__cond ::
 nil).
Definition SRS_Resource__transmissionComb__cond (c : SRS_Resource__transmissionComb__Type) := 
  match c with
  | SRS_Resource__transmissionComb__n2 t => SRS_Resource__transmissionComb__n2__cond t 
  | SRS_Resource__transmissionComb__n4 t => SRS_Resource__transmissionComb__n4__cond t 
  end.

Lemma SRS_Resource__transmissionComb__len_helper1 : to_bit_sz (length SRS_Resource__transmissionComb__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_Resource__transmissionComb__len_helper2 : 2 <= length2 SRS_Resource__transmissionComb__list.
 simpl. lia. Qed.
Lemma SRS_Resource__resourceMapping__startPosition__helper1 : (0 <= 5)%Z.  lia. Qed.
Lemma SRS_Resource__resourceMapping__startPosition__helper2 : to_bit_sz (Z.to_nat (5 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__resourceMapping__startPosition__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__resourceMapping__startPosition__Type := Z.
Definition SRS_Resource__resourceMapping__startPosition__cond := (fun z => (0 <= z <= 5)%Z).
Inductive SRS_Resource__resourceMapping__nrofSymbols__Type : Set :=
 | SRS_Resource__resourceMapping__nrofSymbols__n1
 | SRS_Resource__resourceMapping__nrofSymbols__n2
 | SRS_Resource__resourceMapping__nrofSymbols__n4
.
Definition SRS_Resource__resourceMapping__nrofSymbols__cond := (fun (_ : SRS_Resource__resourceMapping__nrofSymbols__Type) => True).
Lemma SRS_Resource__resourceMapping__nrofSymbols__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__resourceMapping__nrofSymbols__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SRS_Resource__resourceMapping__nrofSymbols__nat__helper.

Definition SRS_Resource__resourceMapping__nrofSymbols__F1 t :=
  match t with
  | SRS_Resource__resourceMapping__nrofSymbols__n1 => 0
  | SRS_Resource__resourceMapping__nrofSymbols__n2 => 1
  | SRS_Resource__resourceMapping__nrofSymbols__n4 => 2
  end.
Definition SRS_Resource__resourceMapping__nrofSymbols__F2 n :=
  match n with
  | 0 => SRS_Resource__resourceMapping__nrofSymbols__n1
  | 1 => SRS_Resource__resourceMapping__nrofSymbols__n2
  | 2 => SRS_Resource__resourceMapping__nrofSymbols__n4
  | _ => SRS_Resource__resourceMapping__nrofSymbols__n1
  end.
Lemma SRS_Resource__resourceMapping__nrofSymbols__F1F2 : forall x : SRS_Resource__resourceMapping__nrofSymbols__Type, (SRS_Resource__resourceMapping__nrofSymbols__F1 x <= 2) /\ SRS_Resource__resourceMapping__nrofSymbols__F2 (SRS_Resource__resourceMapping__nrofSymbols__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__resourceMapping__nrofSymbols__F2F1 : forall (y : nat) (H : y <= 2), SRS_Resource__resourceMapping__nrofSymbols__F1 (SRS_Resource__resourceMapping__nrofSymbols__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_Resource__resourceMapping__repetitionFactor__Type : Set :=
 | SRS_Resource__resourceMapping__repetitionFactor__n1
 | SRS_Resource__resourceMapping__repetitionFactor__n2
 | SRS_Resource__resourceMapping__repetitionFactor__n4
.
Definition SRS_Resource__resourceMapping__repetitionFactor__cond := (fun (_ : SRS_Resource__resourceMapping__repetitionFactor__Type) => True).
Lemma SRS_Resource__resourceMapping__repetitionFactor__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__resourceMapping__repetitionFactor__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SRS_Resource__resourceMapping__repetitionFactor__nat__helper.

Definition SRS_Resource__resourceMapping__repetitionFactor__F1 t :=
  match t with
  | SRS_Resource__resourceMapping__repetitionFactor__n1 => 0
  | SRS_Resource__resourceMapping__repetitionFactor__n2 => 1
  | SRS_Resource__resourceMapping__repetitionFactor__n4 => 2
  end.
Definition SRS_Resource__resourceMapping__repetitionFactor__F2 n :=
  match n with
  | 0 => SRS_Resource__resourceMapping__repetitionFactor__n1
  | 1 => SRS_Resource__resourceMapping__repetitionFactor__n2
  | 2 => SRS_Resource__resourceMapping__repetitionFactor__n4
  | _ => SRS_Resource__resourceMapping__repetitionFactor__n1
  end.
Lemma SRS_Resource__resourceMapping__repetitionFactor__F1F2 : forall x : SRS_Resource__resourceMapping__repetitionFactor__Type, (SRS_Resource__resourceMapping__repetitionFactor__F1 x <= 2) /\ SRS_Resource__resourceMapping__repetitionFactor__F2 (SRS_Resource__resourceMapping__repetitionFactor__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__resourceMapping__repetitionFactor__F2F1 : forall (y : nat) (H : y <= 2), SRS_Resource__resourceMapping__repetitionFactor__F1 (SRS_Resource__resourceMapping__repetitionFactor__F2 y) = y. enum_solve H y. Qed.

Record SRS_Resource__resourceMapping__Type : Set :=
  make__SRS_Resource__resourceMapping__Type {
    SRS_Resource__resourceMapping__startPosition : Z ;
    SRS_Resource__resourceMapping__nrofSymbols : SRS_Resource__resourceMapping__nrofSymbols__Type ;
    SRS_Resource__resourceMapping__repetitionFactor : SRS_Resource__resourceMapping__repetitionFactor__Type ;
}.
Definition SRS_Resource__resourceMapping__list := (
 Nor Z SRS_Resource__resourceMapping__startPosition__cond ::
 Nor SRS_Resource__resourceMapping__nrofSymbols__Type SRS_Resource__resourceMapping__nrofSymbols__cond ::
 Nor SRS_Resource__resourceMapping__repetitionFactor__Type SRS_Resource__resourceMapping__repetitionFactor__cond ::
 nil).
Definition SRS_Resource__resourceMapping__cond z := 
  SRS_Resource__resourceMapping__startPosition__cond (SRS_Resource__resourceMapping__startPosition z) /\
  SRS_Resource__resourceMapping__nrofSymbols__cond (SRS_Resource__resourceMapping__nrofSymbols z) /\
  SRS_Resource__resourceMapping__repetitionFactor__cond (SRS_Resource__resourceMapping__repetitionFactor z) /\
  True.

Lemma SRS_Resource__freqDomainPosition__helper1 : (0 <= 67)%Z.  lia. Qed.
Lemma SRS_Resource__freqDomainPosition__helper2 : to_bit_sz (Z.to_nat (67 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (67 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__freqDomainPosition__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__freqDomainPosition__Type := Z.
Definition SRS_Resource__freqDomainPosition__cond := (fun z => (0 <= z <= 67)%Z).
Lemma SRS_Resource__freqDomainShift__helper1 : (0 <= 268)%Z.  lia. Qed.
Lemma SRS_Resource__freqDomainShift__helper2 : to_bit_sz (Z.to_nat (268 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (268 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__freqDomainShift__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__freqDomainShift__Type := Z.
Definition SRS_Resource__freqDomainShift__cond := (fun z => (0 <= z <= 268)%Z).
Lemma SRS_Resource__freqHopping__c_SRS__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SRS_Resource__freqHopping__c_SRS__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__freqHopping__c_SRS__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__freqHopping__c_SRS__Type := Z.
Definition SRS_Resource__freqHopping__c_SRS__cond := (fun z => (0 <= z <= 63)%Z).
Lemma SRS_Resource__freqHopping__b_SRS__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SRS_Resource__freqHopping__b_SRS__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__freqHopping__b_SRS__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__freqHopping__b_SRS__Type := Z.
Definition SRS_Resource__freqHopping__b_SRS__cond := (fun z => (0 <= z <= 3)%Z).
Lemma SRS_Resource__freqHopping__b_hop__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SRS_Resource__freqHopping__b_hop__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__freqHopping__b_hop__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__freqHopping__b_hop__Type := Z.
Definition SRS_Resource__freqHopping__b_hop__cond := (fun z => (0 <= z <= 3)%Z).
Record SRS_Resource__freqHopping__Type : Set :=
  make__SRS_Resource__freqHopping__Type {
    SRS_Resource__freqHopping__c_SRS : Z ;
    SRS_Resource__freqHopping__b_SRS : Z ;
    SRS_Resource__freqHopping__b_hop : Z ;
}.
Definition SRS_Resource__freqHopping__list := (
 Nor Z SRS_Resource__freqHopping__c_SRS__cond ::
 Nor Z SRS_Resource__freqHopping__b_SRS__cond ::
 Nor Z SRS_Resource__freqHopping__b_hop__cond ::
 nil).
Definition SRS_Resource__freqHopping__cond z := 
  SRS_Resource__freqHopping__c_SRS__cond (SRS_Resource__freqHopping__c_SRS z) /\
  SRS_Resource__freqHopping__b_SRS__cond (SRS_Resource__freqHopping__b_SRS z) /\
  SRS_Resource__freqHopping__b_hop__cond (SRS_Resource__freqHopping__b_hop z) /\
  True.

Inductive SRS_Resource__groupOrSequenceHopping__Type : Set :=
 | SRS_Resource__groupOrSequenceHopping__neither
 | SRS_Resource__groupOrSequenceHopping__groupHopping
 | SRS_Resource__groupOrSequenceHopping__sequenceHopping
.
Definition SRS_Resource__groupOrSequenceHopping__cond := (fun (_ : SRS_Resource__groupOrSequenceHopping__Type) => True).
Lemma SRS_Resource__groupOrSequenceHopping__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__groupOrSequenceHopping__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SRS_Resource__groupOrSequenceHopping__nat__helper.

Definition SRS_Resource__groupOrSequenceHopping__F1 t :=
  match t with
  | SRS_Resource__groupOrSequenceHopping__neither => 0
  | SRS_Resource__groupOrSequenceHopping__groupHopping => 1
  | SRS_Resource__groupOrSequenceHopping__sequenceHopping => 2
  end.
Definition SRS_Resource__groupOrSequenceHopping__F2 n :=
  match n with
  | 0 => SRS_Resource__groupOrSequenceHopping__neither
  | 1 => SRS_Resource__groupOrSequenceHopping__groupHopping
  | 2 => SRS_Resource__groupOrSequenceHopping__sequenceHopping
  | _ => SRS_Resource__groupOrSequenceHopping__neither
  end.
Lemma SRS_Resource__groupOrSequenceHopping__F1F2 : forall x : SRS_Resource__groupOrSequenceHopping__Type, (SRS_Resource__groupOrSequenceHopping__F1 x <= 2) /\ SRS_Resource__groupOrSequenceHopping__F2 (SRS_Resource__groupOrSequenceHopping__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__groupOrSequenceHopping__F2F1 : forall (y : nat) (H : y <= 2), SRS_Resource__groupOrSequenceHopping__F1 (SRS_Resource__groupOrSequenceHopping__F2 y) = y. enum_solve H y. Qed.

Record SRS_Resource__resourceType__aperiodic__root__Type : Set := make__SRS_Resource__resourceType__aperiodic__root__Type {}.
Definition SRS_Resource__resourceType__aperiodic__root__cond (z : SRS_Resource__resourceType__aperiodic__root__Type) := True.
Record SRS_Resource__resourceType__aperiodic__Type : Set :=
  make__SRS_Resource__resourceType__aperiodic__Type {
}.
Definition SRS_Resource__resourceType__aperiodic__root_list : list seq_elem := (
 nil).
Definition SRS_Resource__resourceType__aperiodic__ext_list : list typ := (
  nil).
Definition SRS_Resource__resourceType__aperiodic__cond (z : SRS_Resource__resourceType__aperiodic__Type) := 
(  True) /\ 
(  True).

Require Import NR.SRS_PeriodicityAndOffset.

Opaque SRS_PeriodicityAndOffset__cond SRS_PeriodicityAndOffset__Format.

Record SRS_Resource__resourceType__semi_persistent__Type : Set :=
  make__SRS_Resource__resourceType__semi_persistent__Type {
    SRS_Resource__resourceType__semi_persistent__periodicityAndOffset_sp : SRS_PeriodicityAndOffset__Type ;
}.
Definition SRS_Resource__resourceType__semi_persistent__root_list : list seq_elem := (
 Nor SRS_PeriodicityAndOffset__Type SRS_PeriodicityAndOffset__cond ::
 nil).
Definition SRS_Resource__resourceType__semi_persistent__ext_list : list typ := (
  nil).
Definition SRS_Resource__resourceType__semi_persistent__cond (z : SRS_Resource__resourceType__semi_persistent__Type) := 
(  SRS_PeriodicityAndOffset__cond (SRS_Resource__resourceType__semi_persistent__periodicityAndOffset_sp z) /\
  True) /\ 
(  True).

Require Import NR.SRS_PeriodicityAndOffset.

Opaque SRS_PeriodicityAndOffset__cond SRS_PeriodicityAndOffset__Format.

Record SRS_Resource__resourceType__periodic__Type : Set :=
  make__SRS_Resource__resourceType__periodic__Type {
    SRS_Resource__resourceType__periodic__periodicityAndOffset_p : SRS_PeriodicityAndOffset__Type ;
}.
Definition SRS_Resource__resourceType__periodic__root_list : list seq_elem := (
 Nor SRS_PeriodicityAndOffset__Type SRS_PeriodicityAndOffset__cond ::
 nil).
Definition SRS_Resource__resourceType__periodic__ext_list : list typ := (
  nil).
Definition SRS_Resource__resourceType__periodic__cond (z : SRS_Resource__resourceType__periodic__Type) := 
(  SRS_PeriodicityAndOffset__cond (SRS_Resource__resourceType__periodic__periodicityAndOffset_p z) /\
  True) /\ 
(  True).


Inductive SRS_Resource__resourceType__Type : Set :=
  | SRS_Resource__resourceType__aperiodic : SRS_Resource__resourceType__aperiodic__Type -> SRS_Resource__resourceType__Type
  | SRS_Resource__resourceType__semi_persistent : SRS_Resource__resourceType__semi_persistent__Type -> SRS_Resource__resourceType__Type
  | SRS_Resource__resourceType__periodic : SRS_Resource__resourceType__periodic__Type -> SRS_Resource__resourceType__Type
.
Definition SRS_Resource__resourceType__list : list typ := (
typ_cons SRS_Resource__resourceType__aperiodic__Type SRS_Resource__resourceType__aperiodic__cond ::
typ_cons SRS_Resource__resourceType__semi_persistent__Type SRS_Resource__resourceType__semi_persistent__cond ::
typ_cons SRS_Resource__resourceType__periodic__Type SRS_Resource__resourceType__periodic__cond ::
 nil).
Definition SRS_Resource__resourceType__cond (c : SRS_Resource__resourceType__Type) := 
  match c with
  | SRS_Resource__resourceType__aperiodic t => SRS_Resource__resourceType__aperiodic__cond t 
  | SRS_Resource__resourceType__semi_persistent t => SRS_Resource__resourceType__semi_persistent__cond t 
  | SRS_Resource__resourceType__periodic t => SRS_Resource__resourceType__periodic__cond t 
  end.

Lemma SRS_Resource__resourceType__len_helper1 : to_bit_sz (length SRS_Resource__resourceType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_Resource__resourceType__len_helper2 : 2 <= length2 SRS_Resource__resourceType__list.
 simpl. lia. Qed.
Lemma SRS_Resource__sequenceId__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma SRS_Resource__sequenceId__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__sequenceId__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__sequenceId__Type := Z.
Definition SRS_Resource__sequenceId__cond := (fun z => (0 <= z <= 1023)%Z).
Require Import NR.SRS_SpatialRelationInfo.

Opaque SRS_SpatialRelationInfo__cond SRS_SpatialRelationInfo__Format.

Lemma SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__helper1 : (0 <= 13)%Z.  lia. Qed.
Lemma SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__helper2 : to_bit_sz (Z.to_nat (13 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (13 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__Type := Z.
Definition SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__cond := (fun z => (0 <= z <= 13)%Z).
Inductive SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Type : Set :=
 | SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n1
 | SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n2
 | SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n4
.
Definition SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__cond := (fun (_ : SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Type) => True).
Lemma SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__nat__helper.

Definition SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F1 t :=
  match t with
  | SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n1 => 0
  | SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n2 => 1
  | SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n4 => 2
  end.
Definition SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F2 n :=
  match n with
  | 0 => SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n1
  | 1 => SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n2
  | 2 => SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n4
  | _ => SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__n1
  end.
Lemma SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F1F2 : forall x : SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Type, (SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F1 x <= 2) /\ SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F2 (SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F2F1 : forall (y : nat) (H : y <= 2), SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F1 (SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Type : Set :=
 | SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n1
 | SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n2
 | SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n4
.
Definition SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__cond := (fun (_ : SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Type) => True).
Lemma SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__nat__helper.

Definition SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F1 t :=
  match t with
  | SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n1 => 0
  | SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n2 => 1
  | SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n4 => 2
  end.
Definition SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F2 n :=
  match n with
  | 0 => SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n1
  | 1 => SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n2
  | 2 => SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n4
  | _ => SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__n1
  end.
Lemma SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F1F2 : forall x : SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Type, (SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F1 x <= 2) /\ SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F2 (SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F2F1 : forall (y : nat) (H : y <= 2), SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F1 (SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F2 y) = y. enum_solve H y. Qed.

Record SRS_Resource__ext0O__resourceMapping_r16__Type : Set :=
  make__SRS_Resource__ext0O__resourceMapping_r16__Type {
    SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16 : Z ;
    SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16 : SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Type ;
    SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16 : SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Type ;
}.
Definition SRS_Resource__ext0O__resourceMapping_r16__list := (
 Nor Z SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__cond ::
 Nor SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Type SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__cond ::
 Nor SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Type SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__cond ::
 nil).
Definition SRS_Resource__ext0O__resourceMapping_r16__cond z := 
  SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__cond (SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16 z) /\
  SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__cond (SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16 z) /\
  SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__cond (SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16 z) /\
  True.

Record SRS_Resource__ext0O__Type : Set :=
  make__SRS_Resource__ext0O__Type {
    SRS_Resource__ext0O__resourceMapping_r16 : option SRS_Resource__ext0O__resourceMapping_r16__Type ;
}.
Definition SRS_Resource__ext0O__list := (
 Opt SRS_Resource__ext0O__resourceMapping_r16__Type SRS_Resource__ext0O__resourceMapping_r16__cond ::
 nil).
Definition SRS_Resource__ext0O__cond z := 
  opt_cond SRS_Resource__ext0O__resourceMapping_r16__cond (SRS_Resource__ext0O__resourceMapping_r16 z) /\
  True.

Definition SRS_Resource__ext0__Type := SRS_Resource__ext0O__Type.
Definition SRS_Resource__ext0__cond := SRS_Resource__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.SpatialRelationInfo_PDC_r17.
Definition SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__Type := SetupRelease__Type SpatialRelationInfo_PDC_r17__Type.
Definition SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__cond := SetupRelease__cond _ SpatialRelationInfo_PDC_r17__cond.
Definition SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__Format : T_Format SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__Type SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__cond := SetupRelease__Format _ _ SpatialRelationInfo_PDC_r17__Format.
Opaque SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__cond SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__Format.

Lemma SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__helper1 : (0 <= 13)%Z.  lia. Qed.
Lemma SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__helper2 : to_bit_sz (Z.to_nat (13 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (13 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__Type := Z.
Definition SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__cond := (fun z => (0 <= z <= 13)%Z).
Inductive SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Type : Set :=
 | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n1
 | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n2
 | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n4
 | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n8
 | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n10
 | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n12
 | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n14
.
Definition SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__cond := (fun (_ : SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Type) => True).
Lemma SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__nat__helper.

Definition SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F1 t :=
  match t with
  | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n1 => 0
  | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n2 => 1
  | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n4 => 2
  | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n8 => 3
  | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n10 => 4
  | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n12 => 5
  | SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n14 => 6
  end.
Definition SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F2 n :=
  match n with
  | 0 => SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n1
  | 1 => SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n2
  | 2 => SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n4
  | 3 => SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n8
  | 4 => SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n10
  | 5 => SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n12
  | 6 => SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n14
  | _ => SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__n1
  end.
Lemma SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F1F2 : forall x : SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Type, (SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F1 x <= 6) /\ SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F2 (SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F2F1 : forall (y : nat) (H : y <= 6), SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F1 (SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Type : Set :=
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n1
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n2
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n4
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n5
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n6
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n7
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n8
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n10
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n12
 | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n14
.
Definition SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__cond := (fun (_ : SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Type) => True).
Lemma SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__nat__helper.

Definition SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F1 t :=
  match t with
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n1 => 0
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n2 => 1
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n4 => 2
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n5 => 3
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n6 => 4
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n7 => 5
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n8 => 6
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n10 => 7
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n12 => 8
  | SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n14 => 9
  end.
Definition SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F2 n :=
  match n with
  | 0 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n1
  | 1 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n2
  | 2 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n4
  | 3 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n5
  | 4 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n6
  | 5 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n7
  | 6 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n8
  | 7 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n10
  | 8 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n12
  | 9 => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n14
  | _ => SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__n1
  end.
Lemma SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F1F2 : forall x : SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Type, (SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F1 x <= 9) /\ SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F2 (SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F2F1 : forall (y : nat) (H : y <= 9), SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F1 (SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F2 y) = y. enum_solve H y. Qed.

Record SRS_Resource__ext1O__resourceMapping_r17__Type : Set :=
  make__SRS_Resource__ext1O__resourceMapping_r17__Type {
    SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17 : Z ;
    SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17 : SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Type ;
    SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17 : SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Type ;
}.
Definition SRS_Resource__ext1O__resourceMapping_r17__list := (
 Nor Z SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__cond ::
 Nor SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Type SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__cond ::
 Nor SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Type SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__cond ::
 nil).
Definition SRS_Resource__ext1O__resourceMapping_r17__cond z := 
  SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__cond (SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17 z) /\
  SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__cond (SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17 z) /\
  SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__cond (SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17 z) /\
  True.

Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__Type := Z.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__cond := (fun z => (0 <= z <= 1)%Z).
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__Type := Z.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__cond := (fun z => (0 <= z <= 3)%Z).

Inductive SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type : Set :=
  | SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17 : Z -> SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type
  | SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17 : Z -> SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type
.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list : list typ := (
typ_cons Z SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__cond ::
typ_cons Z SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__cond ::
 nil).
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__cond (c : SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type) := 
  match c with
  | SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17 t => SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__cond t 
  | SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17 t => SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__cond t 
  end.

Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__len_helper1 : to_bit_sz (length SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__len_helper2 : 2 <= length2 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list.
 simpl. lia. Qed.
Inductive SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Type : Set :=
 | SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__enable
.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__cond := (fun (_ : SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Type) => True).
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__nat__helper.

Definition SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F1 t :=
  match t with
  | SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__enable => 0
  end.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F2 n :=
  match n with
  | 0 => SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__enable
  | _ => SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__enable
  end.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F1F2 : forall x : SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Type, (SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F1 x <= 0) /\ SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F2 (SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F2F1 : forall (y : nat) (H : y <= 0), SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F1 (SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F2 y) = y. enum_solve H y. Qed.

Record SRS_Resource__ext1O__partialFreqSounding_r17__Type : Set :=
  make__SRS_Resource__ext1O__partialFreqSounding_r17__Type {
    SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17 : SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type ;
    SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17 : option SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Type ;
}.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__list := (
 Nor SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__cond ::
 Opt SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Type SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__cond ::
 nil).
Definition SRS_Resource__ext1O__partialFreqSounding_r17__cond z := 
  SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__cond (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17 z) /\
  opt_cond SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__cond (SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17 z) /\
  True.

Lemma SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__Type := Z.
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__cond := (fun z => (0 <= z <= 7)%Z).
Lemma SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__helper1 : (0 <= 5)%Z.  lia. Qed.
Lemma SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__helper2 : to_bit_sz (Z.to_nat (5 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__Type := Z.
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__cond := (fun z => (0 <= z <= 5)%Z).
Record SRS_Resource__ext1O__transmissionComb_n8_r17__Type : Set :=
  make__SRS_Resource__ext1O__transmissionComb_n8_r17__Type {
    SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17 : Z ;
    SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17 : Z ;
}.
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__list := (
 Nor Z SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__cond ::
 Nor Z SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__cond ::
 nil).
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__cond z := 
  SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__cond (SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17 z) /\
  SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__cond (SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17 z) /\
  True.

Require Import NR.TCI_UL_State_Id_r17.

Opaque TCI_UL_State_Id_r17__cond TCI_UL_State_Id_r17__Format.

Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.


Inductive SRS_Resource__ext1O__srs_TCI_State_r17__Type : Set :=
  | SRS_Resource__ext1O__srs_TCI_State_r17__srs_UL_TCI_State : TCI_UL_State_Id_r17__Type -> SRS_Resource__ext1O__srs_TCI_State_r17__Type
  | SRS_Resource__ext1O__srs_TCI_State_r17__srs_DLorJointTCI_State : TCI_StateId__Type -> SRS_Resource__ext1O__srs_TCI_State_r17__Type
.
Definition SRS_Resource__ext1O__srs_TCI_State_r17__list : list typ := (
typ_cons TCI_UL_State_Id_r17__Type TCI_UL_State_Id_r17__cond ::
typ_cons TCI_StateId__Type TCI_StateId__cond ::
 nil).
Definition SRS_Resource__ext1O__srs_TCI_State_r17__cond (c : SRS_Resource__ext1O__srs_TCI_State_r17__Type) := 
  match c with
  | SRS_Resource__ext1O__srs_TCI_State_r17__srs_UL_TCI_State t => TCI_UL_State_Id_r17__cond t 
  | SRS_Resource__ext1O__srs_TCI_State_r17__srs_DLorJointTCI_State t => TCI_StateId__cond t 
  end.

Lemma SRS_Resource__ext1O__srs_TCI_State_r17__len_helper1 : to_bit_sz (length SRS_Resource__ext1O__srs_TCI_State_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_Resource__ext1O__srs_TCI_State_r17__len_helper2 : 2 <= length2 SRS_Resource__ext1O__srs_TCI_State_r17__list.
 simpl. lia. Qed.
Record SRS_Resource__ext1O__Type : Set :=
  make__SRS_Resource__ext1O__Type {
    SRS_Resource__ext1O__spatialRelationInfo_PDC_r17 : option SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__Type ;
    SRS_Resource__ext1O__resourceMapping_r17 : option SRS_Resource__ext1O__resourceMapping_r17__Type ;
    SRS_Resource__ext1O__partialFreqSounding_r17 : option SRS_Resource__ext1O__partialFreqSounding_r17__Type ;
    SRS_Resource__ext1O__transmissionComb_n8_r17 : option SRS_Resource__ext1O__transmissionComb_n8_r17__Type ;
    SRS_Resource__ext1O__srs_TCI_State_r17 : option SRS_Resource__ext1O__srs_TCI_State_r17__Type ;
}.
Definition SRS_Resource__ext1O__list := (
 Opt SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__Type SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__cond ::
 Opt SRS_Resource__ext1O__resourceMapping_r17__Type SRS_Resource__ext1O__resourceMapping_r17__cond ::
 Opt SRS_Resource__ext1O__partialFreqSounding_r17__Type SRS_Resource__ext1O__partialFreqSounding_r17__cond ::
 Opt SRS_Resource__ext1O__transmissionComb_n8_r17__Type SRS_Resource__ext1O__transmissionComb_n8_r17__cond ::
 Opt SRS_Resource__ext1O__srs_TCI_State_r17__Type SRS_Resource__ext1O__srs_TCI_State_r17__cond ::
 nil).
Definition SRS_Resource__ext1O__cond z := 
  opt_cond SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__cond (SRS_Resource__ext1O__spatialRelationInfo_PDC_r17 z) /\
  opt_cond SRS_Resource__ext1O__resourceMapping_r17__cond (SRS_Resource__ext1O__resourceMapping_r17 z) /\
  opt_cond SRS_Resource__ext1O__partialFreqSounding_r17__cond (SRS_Resource__ext1O__partialFreqSounding_r17 z) /\
  opt_cond SRS_Resource__ext1O__transmissionComb_n8_r17__cond (SRS_Resource__ext1O__transmissionComb_n8_r17 z) /\
  opt_cond SRS_Resource__ext1O__srs_TCI_State_r17__cond (SRS_Resource__ext1O__srs_TCI_State_r17 z) /\
  True.

Definition SRS_Resource__ext1__Type := SRS_Resource__ext1O__Type.
Definition SRS_Resource__ext1__cond := SRS_Resource__ext1O__cond.

Inductive SRS_Resource__ext2O__repetitionFactor_v1730__Type : Set :=
 | SRS_Resource__ext2O__repetitionFactor_v1730__n3
.
Definition SRS_Resource__ext2O__repetitionFactor_v1730__cond := (fun (_ : SRS_Resource__ext2O__repetitionFactor_v1730__Type) => True).
Lemma SRS_Resource__ext2O__repetitionFactor_v1730__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_Resource__ext2O__repetitionFactor_v1730__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SRS_Resource__ext2O__repetitionFactor_v1730__nat__helper.

Definition SRS_Resource__ext2O__repetitionFactor_v1730__F1 t :=
  match t with
  | SRS_Resource__ext2O__repetitionFactor_v1730__n3 => 0
  end.
Definition SRS_Resource__ext2O__repetitionFactor_v1730__F2 n :=
  match n with
  | 0 => SRS_Resource__ext2O__repetitionFactor_v1730__n3
  | _ => SRS_Resource__ext2O__repetitionFactor_v1730__n3
  end.
Lemma SRS_Resource__ext2O__repetitionFactor_v1730__F1F2 : forall x : SRS_Resource__ext2O__repetitionFactor_v1730__Type, (SRS_Resource__ext2O__repetitionFactor_v1730__F1 x <= 0) /\ SRS_Resource__ext2O__repetitionFactor_v1730__F2 (SRS_Resource__ext2O__repetitionFactor_v1730__F1 x) = x. imp_solve. Qed.
Lemma SRS_Resource__ext2O__repetitionFactor_v1730__F2F1 : forall (y : nat) (H : y <= 0), SRS_Resource__ext2O__repetitionFactor_v1730__F1 (SRS_Resource__ext2O__repetitionFactor_v1730__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ServingCellAndBWP_Id_r17.

Opaque ServingCellAndBWP_Id_r17__cond ServingCellAndBWP_Id_r17__Format.

Record SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Type : Set :=
  make__SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Type {
    SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cellAndBWP_r17 : ServingCellAndBWP_Id_r17__Type ;
}.
Definition SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list := (
 Nor ServingCellAndBWP_Id_r17__Type ServingCellAndBWP_Id_r17__cond ::
 nil).
Definition SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond z := 
  ServingCellAndBWP_Id_r17__cond (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cellAndBWP_r17 z) /\
  True.

Record SRS_Resource__ext2O__Type : Set :=
  make__SRS_Resource__ext2O__Type {
    SRS_Resource__ext2O__repetitionFactor_v1730 : option SRS_Resource__ext2O__repetitionFactor_v1730__Type ;
    SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730 : option SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Type ;
}.
Definition SRS_Resource__ext2O__list := (
 Opt SRS_Resource__ext2O__repetitionFactor_v1730__Type SRS_Resource__ext2O__repetitionFactor_v1730__cond ::
 Opt SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Type SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond ::
 nil).
Definition SRS_Resource__ext2O__cond z := 
  opt_cond SRS_Resource__ext2O__repetitionFactor_v1730__cond (SRS_Resource__ext2O__repetitionFactor_v1730 z) /\
  opt_cond SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730 z) /\
  True.

Definition SRS_Resource__ext2__Type := SRS_Resource__ext2O__Type.
Definition SRS_Resource__ext2__cond := SRS_Resource__ext2O__cond.

Record SRS_Resource__Type : Set :=
  make__SRS_Resource__Type {
    SRS_Resource__srs_ResourceId : SRS_ResourceId__Type ;
    SRS_Resource__nrofSRS_Ports : SRS_Resource__nrofSRS_Ports__Type ;
    SRS_Resource__ptrs_PortIndex : option SRS_Resource__ptrs_PortIndex__Type ;
    SRS_Resource__transmissionComb : SRS_Resource__transmissionComb__Type ;
    SRS_Resource__resourceMapping : SRS_Resource__resourceMapping__Type ;
    SRS_Resource__freqDomainPosition : Z ;
    SRS_Resource__freqDomainShift : Z ;
    SRS_Resource__freqHopping : SRS_Resource__freqHopping__Type ;
    SRS_Resource__groupOrSequenceHopping : SRS_Resource__groupOrSequenceHopping__Type ;
    SRS_Resource__resourceType : SRS_Resource__resourceType__Type ;
    SRS_Resource__sequenceId : Z ;
    SRS_Resource__spatialRelationInfo : option SRS_SpatialRelationInfo__Type ;
    SRS_Resource__ext0 : option SRS_Resource__ext0__Type ;
    SRS_Resource__ext1 : option SRS_Resource__ext1__Type ;
    SRS_Resource__ext2 : option SRS_Resource__ext2__Type ;
}.
Definition SRS_Resource__root_list : list seq_elem := (
 Nor SRS_ResourceId__Type SRS_ResourceId__cond ::
 Nor SRS_Resource__nrofSRS_Ports__Type SRS_Resource__nrofSRS_Ports__cond ::
 Opt SRS_Resource__ptrs_PortIndex__Type SRS_Resource__ptrs_PortIndex__cond ::
 Nor SRS_Resource__transmissionComb__Type SRS_Resource__transmissionComb__cond ::
 Nor SRS_Resource__resourceMapping__Type SRS_Resource__resourceMapping__cond ::
 Nor Z SRS_Resource__freqDomainPosition__cond ::
 Nor Z SRS_Resource__freqDomainShift__cond ::
 Nor SRS_Resource__freqHopping__Type SRS_Resource__freqHopping__cond ::
 Nor SRS_Resource__groupOrSequenceHopping__Type SRS_Resource__groupOrSequenceHopping__cond ::
 Nor SRS_Resource__resourceType__Type SRS_Resource__resourceType__cond ::
 Nor Z SRS_Resource__sequenceId__cond ::
 Opt SRS_SpatialRelationInfo__Type SRS_SpatialRelationInfo__cond ::
 nil).
Definition SRS_Resource__ext_list : list typ := (
  typ_cons SRS_Resource__ext0__Type SRS_Resource__ext0__cond ::
  typ_cons SRS_Resource__ext1__Type SRS_Resource__ext1__cond ::
  typ_cons SRS_Resource__ext2__Type SRS_Resource__ext2__cond ::
  nil).
Definition SRS_Resource__cond (z : SRS_Resource__Type) := 
(  SRS_ResourceId__cond (SRS_Resource__srs_ResourceId z) /\
  SRS_Resource__nrofSRS_Ports__cond (SRS_Resource__nrofSRS_Ports z) /\
  opt_cond SRS_Resource__ptrs_PortIndex__cond (SRS_Resource__ptrs_PortIndex z) /\
  SRS_Resource__transmissionComb__cond (SRS_Resource__transmissionComb z) /\
  SRS_Resource__resourceMapping__cond (SRS_Resource__resourceMapping z) /\
  SRS_Resource__freqDomainPosition__cond (SRS_Resource__freqDomainPosition z) /\
  SRS_Resource__freqDomainShift__cond (SRS_Resource__freqDomainShift z) /\
  SRS_Resource__freqHopping__cond (SRS_Resource__freqHopping z) /\
  SRS_Resource__groupOrSequenceHopping__cond (SRS_Resource__groupOrSequenceHopping z) /\
  SRS_Resource__resourceType__cond (SRS_Resource__resourceType z) /\
  SRS_Resource__sequenceId__cond (SRS_Resource__sequenceId z) /\
  opt_cond SRS_SpatialRelationInfo__cond (SRS_Resource__spatialRelationInfo z) /\
  True) /\ 
(  opt_cond SRS_Resource__ext0__cond (SRS_Resource__ext0 z) /\
  opt_cond SRS_Resource__ext1__cond (SRS_Resource__ext1 z) /\
  opt_cond SRS_Resource__ext2__cond (SRS_Resource__ext2 z) /\
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
Definition SRS_Resource__nrofSRS_Ports__Format : T_Format SRS_Resource__nrofSRS_Ports__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__nrofSRS_Ports__nat__Format SRS_Resource__nrofSRS_Ports__F1 SRS_Resource__nrofSRS_Ports__F2 SRS_Resource__nrofSRS_Ports__F1F2 SRS_Resource__nrofSRS_Ports__F2F1.

Opaque SRS_Resource__nrofSRS_Ports__cond SRS_Resource__nrofSRS_Ports__Format.

Definition SRS_Resource__ptrs_PortIndex__Format : T_Format SRS_Resource__ptrs_PortIndex__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__ptrs_PortIndex__nat__Format SRS_Resource__ptrs_PortIndex__F1 SRS_Resource__ptrs_PortIndex__F2 SRS_Resource__ptrs_PortIndex__F1F2 SRS_Resource__ptrs_PortIndex__F2F1.

Opaque SRS_Resource__ptrs_PortIndex__cond SRS_Resource__ptrs_PortIndex__Format.

Definition SRS_Resource__transmissionComb__n2__combOffset_n2__Format : T_Format Z SRS_Resource__transmissionComb__n2__combOffset_n2__cond :=
 ranged_int_format (0) (1) SRS_Resource__transmissionComb__n2__combOffset_n2__helper1 SRS_Resource__transmissionComb__n2__combOffset_n2__helper2.

Opaque SRS_Resource__transmissionComb__n2__combOffset_n2__cond SRS_Resource__transmissionComb__n2__combOffset_n2__Format.

Definition SRS_Resource__transmissionComb__n2__cyclicShift_n2__Format : T_Format Z SRS_Resource__transmissionComb__n2__cyclicShift_n2__cond :=
 ranged_int_format (0) (7) SRS_Resource__transmissionComb__n2__cyclicShift_n2__helper1 SRS_Resource__transmissionComb__n2__cyclicShift_n2__helper2.

Opaque SRS_Resource__transmissionComb__n2__cyclicShift_n2__cond SRS_Resource__transmissionComb__n2__cyclicShift_n2__Format.


Definition SRS_Resource__transmissionComb__n2__Format_Type := Eval cbn in seq_format_prod SRS_Resource__transmissionComb__n2__list.
Definition SRS_Resource__transmissionComb__n2__Format_list : SRS_Resource__transmissionComb__n2__Format_Type :=
  (SRS_Resource__transmissionComb__n2__combOffset_n2__Format, (SRS_Resource__transmissionComb__n2__cyclicShift_n2__Format, unit_format)).
Definition SRS_Resource__transmissionComb__n2__list__Format := (*Eval compute in *) seq_format SRS_Resource__transmissionComb__n2__list SRS_Resource__transmissionComb__n2__Format_list.
Definition SRS_Resource__transmissionComb__n2__F1 z :=
  (SRS_Resource__transmissionComb__n2__combOffset_n2 z, (SRS_Resource__transmissionComb__n2__cyclicShift_n2 z, tt)).
Definition SRS_Resource__transmissionComb__n2__F2 (y : seq_type SRS_Resource__transmissionComb__n2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_Resource__transmissionComb__n2__Type i0 i1
  end.
Lemma SRS_Resource__transmissionComb__n2__F1F2_cond (z : SRS_Resource__transmissionComb__n2__Type)
  : SRS_Resource__transmissionComb__n2__cond z ->
  (seq_cond SRS_Resource__transmissionComb__n2__list (SRS_Resource__transmissionComb__n2__F1 z)).
intro H. unfold SRS_Resource__transmissionComb__n2__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__transmissionComb__n2__F1F2_cond2 (z : SRS_Resource__transmissionComb__n2__Type)
 : SRS_Resource__transmissionComb__n2__F2 (SRS_Resource__transmissionComb__n2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__transmissionComb__n2__F2F1_cond (y : seq_type SRS_Resource__transmissionComb__n2__list)
  : seq_cond SRS_Resource__transmissionComb__n2__list y ->
 (SRS_Resource__transmissionComb__n2__cond (SRS_Resource__transmissionComb__n2__F2 y)) /\  SRS_Resource__transmissionComb__n2__F1 (SRS_Resource__transmissionComb__n2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__transmissionComb__n2__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__transmissionComb__n2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__transmissionComb__n2__Format : T_Format SRS_Resource__transmissionComb__n2__Type SRS_Resource__transmissionComb__n2__cond :=
        proj2_format  SRS_Resource__transmissionComb__n2__cond SRS_Resource__transmissionComb__n2__list__Format
    SRS_Resource__transmissionComb__n2__F1 SRS_Resource__transmissionComb__n2__F2 SRS_Resource__transmissionComb__n2__F1F2_cond  SRS_Resource__transmissionComb__n2__F1F2_cond2 SRS_Resource__transmissionComb__n2__F2F1_cond.
Opaque SRS_Resource__transmissionComb__n2__cond SRS_Resource__transmissionComb__n2__Format.

Definition SRS_Resource__transmissionComb__n4__combOffset_n4__Format : T_Format Z SRS_Resource__transmissionComb__n4__combOffset_n4__cond :=
 ranged_int_format (0) (3) SRS_Resource__transmissionComb__n4__combOffset_n4__helper1 SRS_Resource__transmissionComb__n4__combOffset_n4__helper2.

Opaque SRS_Resource__transmissionComb__n4__combOffset_n4__cond SRS_Resource__transmissionComb__n4__combOffset_n4__Format.

Definition SRS_Resource__transmissionComb__n4__cyclicShift_n4__Format : T_Format Z SRS_Resource__transmissionComb__n4__cyclicShift_n4__cond :=
 ranged_int_format (0) (11) SRS_Resource__transmissionComb__n4__cyclicShift_n4__helper1 SRS_Resource__transmissionComb__n4__cyclicShift_n4__helper2.

Opaque SRS_Resource__transmissionComb__n4__cyclicShift_n4__cond SRS_Resource__transmissionComb__n4__cyclicShift_n4__Format.


Definition SRS_Resource__transmissionComb__n4__Format_Type := Eval cbn in seq_format_prod SRS_Resource__transmissionComb__n4__list.
Definition SRS_Resource__transmissionComb__n4__Format_list : SRS_Resource__transmissionComb__n4__Format_Type :=
  (SRS_Resource__transmissionComb__n4__combOffset_n4__Format, (SRS_Resource__transmissionComb__n4__cyclicShift_n4__Format, unit_format)).
Definition SRS_Resource__transmissionComb__n4__list__Format := (*Eval compute in *) seq_format SRS_Resource__transmissionComb__n4__list SRS_Resource__transmissionComb__n4__Format_list.
Definition SRS_Resource__transmissionComb__n4__F1 z :=
  (SRS_Resource__transmissionComb__n4__combOffset_n4 z, (SRS_Resource__transmissionComb__n4__cyclicShift_n4 z, tt)).
Definition SRS_Resource__transmissionComb__n4__F2 (y : seq_type SRS_Resource__transmissionComb__n4__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_Resource__transmissionComb__n4__Type i0 i1
  end.
Lemma SRS_Resource__transmissionComb__n4__F1F2_cond (z : SRS_Resource__transmissionComb__n4__Type)
  : SRS_Resource__transmissionComb__n4__cond z ->
  (seq_cond SRS_Resource__transmissionComb__n4__list (SRS_Resource__transmissionComb__n4__F1 z)).
intro H. unfold SRS_Resource__transmissionComb__n4__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__transmissionComb__n4__F1F2_cond2 (z : SRS_Resource__transmissionComb__n4__Type)
 : SRS_Resource__transmissionComb__n4__F2 (SRS_Resource__transmissionComb__n4__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__transmissionComb__n4__F2F1_cond (y : seq_type SRS_Resource__transmissionComb__n4__list)
  : seq_cond SRS_Resource__transmissionComb__n4__list y ->
 (SRS_Resource__transmissionComb__n4__cond (SRS_Resource__transmissionComb__n4__F2 y)) /\  SRS_Resource__transmissionComb__n4__F1 (SRS_Resource__transmissionComb__n4__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__transmissionComb__n4__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__transmissionComb__n4__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__transmissionComb__n4__Format : T_Format SRS_Resource__transmissionComb__n4__Type SRS_Resource__transmissionComb__n4__cond :=
        proj2_format  SRS_Resource__transmissionComb__n4__cond SRS_Resource__transmissionComb__n4__list__Format
    SRS_Resource__transmissionComb__n4__F1 SRS_Resource__transmissionComb__n4__F2 SRS_Resource__transmissionComb__n4__F1F2_cond  SRS_Resource__transmissionComb__n4__F1F2_cond2 SRS_Resource__transmissionComb__n4__F2F1_cond.
Opaque SRS_Resource__transmissionComb__n4__cond SRS_Resource__transmissionComb__n4__Format.


Definition SRS_Resource__transmissionComb__Format_Type := Eval cbn in get_formats SRS_Resource__transmissionComb__list.
Definition SRS_Resource__transmissionComb__Format_list : SRS_Resource__transmissionComb__Format_Type :=
  (SRS_Resource__transmissionComb__n2__Format, (SRS_Resource__transmissionComb__n4__Format, unit__Format)).
Definition SRS_Resource__transmissionComb__list__Format := Eval compute in choice_format SRS_Resource__transmissionComb__list SRS_Resource__transmissionComb__len_helper1 SRS_Resource__transmissionComb__len_helper2  SRS_Resource__transmissionComb__Format_list.
Definition SRS_Resource__transmissionComb__F1 (z : SRS_Resource__transmissionComb__Type) : (choice SRS_Resource__transmissionComb__list) :=
  match z with
   | SRS_Resource__transmissionComb__n2 t => existT _ 0 t
  | SRS_Resource__transmissionComb__n4 t => existT _ 1 t
  end.
Definition SRS_Resource__transmissionComb__g := (fun n => typ_set (get_nth_typ SRS_Resource__transmissionComb__list n)).
Definition SRS_Resource__transmissionComb__F2 (y : choice SRS_Resource__transmissionComb__list) : SRS_Resource__transmissionComb__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_Resource__transmissionComb__g n -> SRS_Resource__transmissionComb__Type) with
    | 0 => fun (t : SRS_Resource__transmissionComb__n2__Type) => SRS_Resource__transmissionComb__n2 t 
    | 1 => fun (t : SRS_Resource__transmissionComb__n4__Type) => SRS_Resource__transmissionComb__n4 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SRS_Resource__transmissionComb__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SRS_Resource__transmissionComb__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_Resource__transmissionComb__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SRS_Resource__transmissionComb__Type with end) n0
           end t0).

Lemma SRS_Resource__transmissionComb__helper2 :  forall (y : SRS_Resource__transmissionComb__Type), SRS_Resource__transmissionComb__cond y -> choice_cond SRS_Resource__transmissionComb__list (SRS_Resource__transmissionComb__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_Resource__transmissionComb__helper3 :  forall (y : SRS_Resource__transmissionComb__Type), SRS_Resource__transmissionComb__F2 (SRS_Resource__transmissionComb__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_Resource__transmissionComb__helper4 : (forall b : choice SRS_Resource__transmissionComb__list, choice_cond SRS_Resource__transmissionComb__list b -> SRS_Resource__transmissionComb__cond (SRS_Resource__transmissionComb__F2 b) /\ SRS_Resource__transmissionComb__F1 (SRS_Resource__transmissionComb__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_Resource__transmissionComb__F1 SRS_Resource__transmissionComb__F2.
Definition SRS_Resource__transmissionComb__Format : T_Format SRS_Resource__transmissionComb__Type SRS_Resource__transmissionComb__cond :=
  (* Eval compute in *) proj2_format SRS_Resource__transmissionComb__cond SRS_Resource__transmissionComb__list__Format SRS_Resource__transmissionComb__F1 SRS_Resource__transmissionComb__F2 SRS_Resource__transmissionComb__helper2 SRS_Resource__transmissionComb__helper3 SRS_Resource__transmissionComb__helper4.
Opaque SRS_Resource__transmissionComb__cond SRS_Resource__transmissionComb__Format.

Definition SRS_Resource__resourceMapping__startPosition__Format : T_Format Z SRS_Resource__resourceMapping__startPosition__cond :=
 ranged_int_format (0) (5) SRS_Resource__resourceMapping__startPosition__helper1 SRS_Resource__resourceMapping__startPosition__helper2.

Opaque SRS_Resource__resourceMapping__startPosition__cond SRS_Resource__resourceMapping__startPosition__Format.

Definition SRS_Resource__resourceMapping__nrofSymbols__Format : T_Format SRS_Resource__resourceMapping__nrofSymbols__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__resourceMapping__nrofSymbols__nat__Format SRS_Resource__resourceMapping__nrofSymbols__F1 SRS_Resource__resourceMapping__nrofSymbols__F2 SRS_Resource__resourceMapping__nrofSymbols__F1F2 SRS_Resource__resourceMapping__nrofSymbols__F2F1.

Opaque SRS_Resource__resourceMapping__nrofSymbols__cond SRS_Resource__resourceMapping__nrofSymbols__Format.

Definition SRS_Resource__resourceMapping__repetitionFactor__Format : T_Format SRS_Resource__resourceMapping__repetitionFactor__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__resourceMapping__repetitionFactor__nat__Format SRS_Resource__resourceMapping__repetitionFactor__F1 SRS_Resource__resourceMapping__repetitionFactor__F2 SRS_Resource__resourceMapping__repetitionFactor__F1F2 SRS_Resource__resourceMapping__repetitionFactor__F2F1.

Opaque SRS_Resource__resourceMapping__repetitionFactor__cond SRS_Resource__resourceMapping__repetitionFactor__Format.


Definition SRS_Resource__resourceMapping__Format_Type := Eval cbn in seq_format_prod SRS_Resource__resourceMapping__list.
Definition SRS_Resource__resourceMapping__Format_list : SRS_Resource__resourceMapping__Format_Type :=
  (SRS_Resource__resourceMapping__startPosition__Format, (SRS_Resource__resourceMapping__nrofSymbols__Format, (SRS_Resource__resourceMapping__repetitionFactor__Format, unit_format))).
Definition SRS_Resource__resourceMapping__list__Format := (*Eval compute in *) seq_format SRS_Resource__resourceMapping__list SRS_Resource__resourceMapping__Format_list.
Definition SRS_Resource__resourceMapping__F1 z :=
  (SRS_Resource__resourceMapping__startPosition z, (SRS_Resource__resourceMapping__nrofSymbols z, (SRS_Resource__resourceMapping__repetitionFactor z, tt))).
Definition SRS_Resource__resourceMapping__F2 (y : seq_type SRS_Resource__resourceMapping__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SRS_Resource__resourceMapping__Type i0 i1 i2
  end.
Lemma SRS_Resource__resourceMapping__F1F2_cond (z : SRS_Resource__resourceMapping__Type)
  : SRS_Resource__resourceMapping__cond z ->
  (seq_cond SRS_Resource__resourceMapping__list (SRS_Resource__resourceMapping__F1 z)).
intro H. unfold SRS_Resource__resourceMapping__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__resourceMapping__F1F2_cond2 (z : SRS_Resource__resourceMapping__Type)
 : SRS_Resource__resourceMapping__F2 (SRS_Resource__resourceMapping__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__resourceMapping__F2F1_cond (y : seq_type SRS_Resource__resourceMapping__list)
  : seq_cond SRS_Resource__resourceMapping__list y ->
 (SRS_Resource__resourceMapping__cond (SRS_Resource__resourceMapping__F2 y)) /\  SRS_Resource__resourceMapping__F1 (SRS_Resource__resourceMapping__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__resourceMapping__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__resourceMapping__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__resourceMapping__Format : T_Format SRS_Resource__resourceMapping__Type SRS_Resource__resourceMapping__cond :=
        proj2_format  SRS_Resource__resourceMapping__cond SRS_Resource__resourceMapping__list__Format
    SRS_Resource__resourceMapping__F1 SRS_Resource__resourceMapping__F2 SRS_Resource__resourceMapping__F1F2_cond  SRS_Resource__resourceMapping__F1F2_cond2 SRS_Resource__resourceMapping__F2F1_cond.
Opaque SRS_Resource__resourceMapping__cond SRS_Resource__resourceMapping__Format.

Definition SRS_Resource__freqDomainPosition__Format : T_Format Z SRS_Resource__freqDomainPosition__cond :=
 ranged_int_format (0) (67) SRS_Resource__freqDomainPosition__helper1 SRS_Resource__freqDomainPosition__helper2.

Opaque SRS_Resource__freqDomainPosition__cond SRS_Resource__freqDomainPosition__Format.

Definition SRS_Resource__freqDomainShift__Format : T_Format Z SRS_Resource__freqDomainShift__cond :=
 ranged_int_format (0) (268) SRS_Resource__freqDomainShift__helper1 SRS_Resource__freqDomainShift__helper2.

Opaque SRS_Resource__freqDomainShift__cond SRS_Resource__freqDomainShift__Format.

Definition SRS_Resource__freqHopping__c_SRS__Format : T_Format Z SRS_Resource__freqHopping__c_SRS__cond :=
 ranged_int_format (0) (63) SRS_Resource__freqHopping__c_SRS__helper1 SRS_Resource__freqHopping__c_SRS__helper2.

Opaque SRS_Resource__freqHopping__c_SRS__cond SRS_Resource__freqHopping__c_SRS__Format.

Definition SRS_Resource__freqHopping__b_SRS__Format : T_Format Z SRS_Resource__freqHopping__b_SRS__cond :=
 ranged_int_format (0) (3) SRS_Resource__freqHopping__b_SRS__helper1 SRS_Resource__freqHopping__b_SRS__helper2.

Opaque SRS_Resource__freqHopping__b_SRS__cond SRS_Resource__freqHopping__b_SRS__Format.

Definition SRS_Resource__freqHopping__b_hop__Format : T_Format Z SRS_Resource__freqHopping__b_hop__cond :=
 ranged_int_format (0) (3) SRS_Resource__freqHopping__b_hop__helper1 SRS_Resource__freqHopping__b_hop__helper2.

Opaque SRS_Resource__freqHopping__b_hop__cond SRS_Resource__freqHopping__b_hop__Format.


Definition SRS_Resource__freqHopping__Format_Type := Eval cbn in seq_format_prod SRS_Resource__freqHopping__list.
Definition SRS_Resource__freqHopping__Format_list : SRS_Resource__freqHopping__Format_Type :=
  (SRS_Resource__freqHopping__c_SRS__Format, (SRS_Resource__freqHopping__b_SRS__Format, (SRS_Resource__freqHopping__b_hop__Format, unit_format))).
Definition SRS_Resource__freqHopping__list__Format := (*Eval compute in *) seq_format SRS_Resource__freqHopping__list SRS_Resource__freqHopping__Format_list.
Definition SRS_Resource__freqHopping__F1 z :=
  (SRS_Resource__freqHopping__c_SRS z, (SRS_Resource__freqHopping__b_SRS z, (SRS_Resource__freqHopping__b_hop z, tt))).
Definition SRS_Resource__freqHopping__F2 (y : seq_type SRS_Resource__freqHopping__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SRS_Resource__freqHopping__Type i0 i1 i2
  end.
Lemma SRS_Resource__freqHopping__F1F2_cond (z : SRS_Resource__freqHopping__Type)
  : SRS_Resource__freqHopping__cond z ->
  (seq_cond SRS_Resource__freqHopping__list (SRS_Resource__freqHopping__F1 z)).
intro H. unfold SRS_Resource__freqHopping__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__freqHopping__F1F2_cond2 (z : SRS_Resource__freqHopping__Type)
 : SRS_Resource__freqHopping__F2 (SRS_Resource__freqHopping__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__freqHopping__F2F1_cond (y : seq_type SRS_Resource__freqHopping__list)
  : seq_cond SRS_Resource__freqHopping__list y ->
 (SRS_Resource__freqHopping__cond (SRS_Resource__freqHopping__F2 y)) /\  SRS_Resource__freqHopping__F1 (SRS_Resource__freqHopping__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__freqHopping__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__freqHopping__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__freqHopping__Format : T_Format SRS_Resource__freqHopping__Type SRS_Resource__freqHopping__cond :=
        proj2_format  SRS_Resource__freqHopping__cond SRS_Resource__freqHopping__list__Format
    SRS_Resource__freqHopping__F1 SRS_Resource__freqHopping__F2 SRS_Resource__freqHopping__F1F2_cond  SRS_Resource__freqHopping__F1F2_cond2 SRS_Resource__freqHopping__F2F1_cond.
Opaque SRS_Resource__freqHopping__cond SRS_Resource__freqHopping__Format.

Definition SRS_Resource__groupOrSequenceHopping__Format : T_Format SRS_Resource__groupOrSequenceHopping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__groupOrSequenceHopping__nat__Format SRS_Resource__groupOrSequenceHopping__F1 SRS_Resource__groupOrSequenceHopping__F2 SRS_Resource__groupOrSequenceHopping__F1F2 SRS_Resource__groupOrSequenceHopping__F2F1.

Opaque SRS_Resource__groupOrSequenceHopping__cond SRS_Resource__groupOrSequenceHopping__Format.

Definition SRS_Resource__resourceType__aperiodic__root__helper : forall a : SRS_Resource__resourceType__aperiodic__root__Type, True -> True /\ make__SRS_Resource__resourceType__aperiodic__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SRS_Resource__resourceType__aperiodic__root__Format : T_Format SRS_Resource__resourceType__aperiodic__root__Type SRS_Resource__resourceType__aperiodic__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SRS_Resource__resourceType__aperiodic__root__Type)
    SRS_Resource__resourceType__aperiodic__root__helper unit_unique (fun _ => left I).

Opaque SRS_Resource__resourceType__aperiodic__root__cond SRS_Resource__resourceType__aperiodic__root__Format.


Definition SRS_Resource__resourceType__aperiodic__root_Format_Type := Eval cbn in seq_format_prod SRS_Resource__resourceType__aperiodic__root_list.
Definition SRS_Resource__resourceType__aperiodic__root_Format_list : SRS_Resource__resourceType__aperiodic__root_Format_Type :=
  unit_format.

Definition SRS_Resource__resourceType__aperiodic__ext_Format_Type := Eval cbn in get_formats SRS_Resource__resourceType__aperiodic__ext_list.
Definition SRS_Resource__resourceType__aperiodic__ext_Format_list : SRS_Resource__resourceType__aperiodic__ext_Format_Type :=
  unit__Format.

Definition SRS_Resource__resourceType__aperiodic__list_type : Set := (seq_type SRS_Resource__resourceType__aperiodic__root_list) * (seq_ext_type SRS_Resource__resourceType__aperiodic__ext_list).
Definition SRS_Resource__resourceType__aperiodic__list_cond (z : SRS_Resource__resourceType__aperiodic__list_type) : Prop :=
        (seq_cond SRS_Resource__resourceType__aperiodic__root_list (fst z)) /\ (seq_ext_cond SRS_Resource__resourceType__aperiodic__ext_list (snd z)).
Definition SRS_Resource__resourceType__aperiodic__list_format : T_Format SRS_Resource__resourceType__aperiodic__list_type SRS_Resource__resourceType__aperiodic__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_Resource__resourceType__aperiodic__root_list SRS_Resource__resourceType__aperiodic__root_Format_list SRS_Resource__resourceType__aperiodic__ext_list SRS_Resource__resourceType__aperiodic__ext_Format_list.

Opaque SRS_Resource__resourceType__aperiodic__list_format.
Definition SRS_Resource__resourceType__aperiodic__F1 (z : SRS_Resource__resourceType__aperiodic__Type) : SRS_Resource__resourceType__aperiodic__list_type :=
  ((tt), (
tt)).
Definition SRS_Resource__resourceType__aperiodic__F2 (y : SRS_Resource__resourceType__aperiodic__list_type) : SRS_Resource__resourceType__aperiodic__Type :=
  match y with
  | (_, _)=>
    make__SRS_Resource__resourceType__aperiodic__Type
  end.
Definition SRS_Resource__resourceType__aperiodic__helper1 : (forall a : SRS_Resource__resourceType__aperiodic__Type, SRS_Resource__resourceType__aperiodic__cond a -> SRS_Resource__resourceType__aperiodic__list_cond (SRS_Resource__resourceType__aperiodic__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_Resource__resourceType__aperiodic__helper2 : (forall a : SRS_Resource__resourceType__aperiodic__Type, SRS_Resource__resourceType__aperiodic__F2 (SRS_Resource__resourceType__aperiodic__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_Resource__resourceType__aperiodic__helper3 : (forall b : SRS_Resource__resourceType__aperiodic__list_type, SRS_Resource__resourceType__aperiodic__list_cond b -> SRS_Resource__resourceType__aperiodic__cond (SRS_Resource__resourceType__aperiodic__F2 b) /\ SRS_Resource__resourceType__aperiodic__F1 (SRS_Resource__resourceType__aperiodic__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_Resource__resourceType__aperiodic__cond, SRS_Resource__resourceType__aperiodic__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_Resource__resourceType__aperiodic__Format : T_Format SRS_Resource__resourceType__aperiodic__Type SRS_Resource__resourceType__aperiodic__cond :=
 proj2_format SRS_Resource__resourceType__aperiodic__cond SRS_Resource__resourceType__aperiodic__list_format  SRS_Resource__resourceType__aperiodic__F1 SRS_Resource__resourceType__aperiodic__F2 SRS_Resource__resourceType__aperiodic__helper1 SRS_Resource__resourceType__aperiodic__helper2 SRS_Resource__resourceType__aperiodic__helper3.

Opaque SRS_Resource__resourceType__aperiodic__cond SRS_Resource__resourceType__aperiodic__Format.


Definition SRS_Resource__resourceType__semi_persistent__root_Format_Type := Eval cbn in seq_format_prod SRS_Resource__resourceType__semi_persistent__root_list.
Definition SRS_Resource__resourceType__semi_persistent__root_Format_list : SRS_Resource__resourceType__semi_persistent__root_Format_Type :=
  (SRS_PeriodicityAndOffset__Format, unit_format).

Definition SRS_Resource__resourceType__semi_persistent__ext_Format_Type := Eval cbn in get_formats SRS_Resource__resourceType__semi_persistent__ext_list.
Definition SRS_Resource__resourceType__semi_persistent__ext_Format_list : SRS_Resource__resourceType__semi_persistent__ext_Format_Type :=
  unit__Format.

Definition SRS_Resource__resourceType__semi_persistent__list_type : Set := (seq_type SRS_Resource__resourceType__semi_persistent__root_list) * (seq_ext_type SRS_Resource__resourceType__semi_persistent__ext_list).
Definition SRS_Resource__resourceType__semi_persistent__list_cond (z : SRS_Resource__resourceType__semi_persistent__list_type) : Prop :=
        (seq_cond SRS_Resource__resourceType__semi_persistent__root_list (fst z)) /\ (seq_ext_cond SRS_Resource__resourceType__semi_persistent__ext_list (snd z)).
Definition SRS_Resource__resourceType__semi_persistent__list_format : T_Format SRS_Resource__resourceType__semi_persistent__list_type SRS_Resource__resourceType__semi_persistent__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_Resource__resourceType__semi_persistent__root_list SRS_Resource__resourceType__semi_persistent__root_Format_list SRS_Resource__resourceType__semi_persistent__ext_list SRS_Resource__resourceType__semi_persistent__ext_Format_list.

Opaque SRS_Resource__resourceType__semi_persistent__list_format.
Definition SRS_Resource__resourceType__semi_persistent__F1 (z : SRS_Resource__resourceType__semi_persistent__Type) : SRS_Resource__resourceType__semi_persistent__list_type :=
  (((SRS_Resource__resourceType__semi_persistent__periodicityAndOffset_sp z, tt)), (
tt)).
Definition SRS_Resource__resourceType__semi_persistent__F2 (y : SRS_Resource__resourceType__semi_persistent__list_type) : SRS_Resource__resourceType__semi_persistent__Type :=
  match y with
  | ((j0, _), _)=>
    make__SRS_Resource__resourceType__semi_persistent__Type j0
  end.
Definition SRS_Resource__resourceType__semi_persistent__helper1 : (forall a : SRS_Resource__resourceType__semi_persistent__Type, SRS_Resource__resourceType__semi_persistent__cond a -> SRS_Resource__resourceType__semi_persistent__list_cond (SRS_Resource__resourceType__semi_persistent__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_Resource__resourceType__semi_persistent__helper2 : (forall a : SRS_Resource__resourceType__semi_persistent__Type, SRS_Resource__resourceType__semi_persistent__F2 (SRS_Resource__resourceType__semi_persistent__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_Resource__resourceType__semi_persistent__helper3 : (forall b : SRS_Resource__resourceType__semi_persistent__list_type, SRS_Resource__resourceType__semi_persistent__list_cond b -> SRS_Resource__resourceType__semi_persistent__cond (SRS_Resource__resourceType__semi_persistent__F2 b) /\ SRS_Resource__resourceType__semi_persistent__F1 (SRS_Resource__resourceType__semi_persistent__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_Resource__resourceType__semi_persistent__cond, SRS_Resource__resourceType__semi_persistent__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_Resource__resourceType__semi_persistent__Format : T_Format SRS_Resource__resourceType__semi_persistent__Type SRS_Resource__resourceType__semi_persistent__cond :=
 proj2_format SRS_Resource__resourceType__semi_persistent__cond SRS_Resource__resourceType__semi_persistent__list_format  SRS_Resource__resourceType__semi_persistent__F1 SRS_Resource__resourceType__semi_persistent__F2 SRS_Resource__resourceType__semi_persistent__helper1 SRS_Resource__resourceType__semi_persistent__helper2 SRS_Resource__resourceType__semi_persistent__helper3.

Opaque SRS_Resource__resourceType__semi_persistent__cond SRS_Resource__resourceType__semi_persistent__Format.


Definition SRS_Resource__resourceType__periodic__root_Format_Type := Eval cbn in seq_format_prod SRS_Resource__resourceType__periodic__root_list.
Definition SRS_Resource__resourceType__periodic__root_Format_list : SRS_Resource__resourceType__periodic__root_Format_Type :=
  (SRS_PeriodicityAndOffset__Format, unit_format).

Definition SRS_Resource__resourceType__periodic__ext_Format_Type := Eval cbn in get_formats SRS_Resource__resourceType__periodic__ext_list.
Definition SRS_Resource__resourceType__periodic__ext_Format_list : SRS_Resource__resourceType__periodic__ext_Format_Type :=
  unit__Format.

Definition SRS_Resource__resourceType__periodic__list_type : Set := (seq_type SRS_Resource__resourceType__periodic__root_list) * (seq_ext_type SRS_Resource__resourceType__periodic__ext_list).
Definition SRS_Resource__resourceType__periodic__list_cond (z : SRS_Resource__resourceType__periodic__list_type) : Prop :=
        (seq_cond SRS_Resource__resourceType__periodic__root_list (fst z)) /\ (seq_ext_cond SRS_Resource__resourceType__periodic__ext_list (snd z)).
Definition SRS_Resource__resourceType__periodic__list_format : T_Format SRS_Resource__resourceType__periodic__list_type SRS_Resource__resourceType__periodic__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_Resource__resourceType__periodic__root_list SRS_Resource__resourceType__periodic__root_Format_list SRS_Resource__resourceType__periodic__ext_list SRS_Resource__resourceType__periodic__ext_Format_list.

Opaque SRS_Resource__resourceType__periodic__list_format.
Definition SRS_Resource__resourceType__periodic__F1 (z : SRS_Resource__resourceType__periodic__Type) : SRS_Resource__resourceType__periodic__list_type :=
  (((SRS_Resource__resourceType__periodic__periodicityAndOffset_p z, tt)), (
tt)).
Definition SRS_Resource__resourceType__periodic__F2 (y : SRS_Resource__resourceType__periodic__list_type) : SRS_Resource__resourceType__periodic__Type :=
  match y with
  | ((j0, _), _)=>
    make__SRS_Resource__resourceType__periodic__Type j0
  end.
Definition SRS_Resource__resourceType__periodic__helper1 : (forall a : SRS_Resource__resourceType__periodic__Type, SRS_Resource__resourceType__periodic__cond a -> SRS_Resource__resourceType__periodic__list_cond (SRS_Resource__resourceType__periodic__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_Resource__resourceType__periodic__helper2 : (forall a : SRS_Resource__resourceType__periodic__Type, SRS_Resource__resourceType__periodic__F2 (SRS_Resource__resourceType__periodic__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_Resource__resourceType__periodic__helper3 : (forall b : SRS_Resource__resourceType__periodic__list_type, SRS_Resource__resourceType__periodic__list_cond b -> SRS_Resource__resourceType__periodic__cond (SRS_Resource__resourceType__periodic__F2 b) /\ SRS_Resource__resourceType__periodic__F1 (SRS_Resource__resourceType__periodic__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_Resource__resourceType__periodic__cond, SRS_Resource__resourceType__periodic__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_Resource__resourceType__periodic__Format : T_Format SRS_Resource__resourceType__periodic__Type SRS_Resource__resourceType__periodic__cond :=
 proj2_format SRS_Resource__resourceType__periodic__cond SRS_Resource__resourceType__periodic__list_format  SRS_Resource__resourceType__periodic__F1 SRS_Resource__resourceType__periodic__F2 SRS_Resource__resourceType__periodic__helper1 SRS_Resource__resourceType__periodic__helper2 SRS_Resource__resourceType__periodic__helper3.

Opaque SRS_Resource__resourceType__periodic__cond SRS_Resource__resourceType__periodic__Format.


Definition SRS_Resource__resourceType__Format_Type := Eval cbn in get_formats SRS_Resource__resourceType__list.
Definition SRS_Resource__resourceType__Format_list : SRS_Resource__resourceType__Format_Type :=
  (SRS_Resource__resourceType__aperiodic__Format, (SRS_Resource__resourceType__semi_persistent__Format, (SRS_Resource__resourceType__periodic__Format, unit__Format))).
Definition SRS_Resource__resourceType__list__Format := Eval compute in choice_format SRS_Resource__resourceType__list SRS_Resource__resourceType__len_helper1 SRS_Resource__resourceType__len_helper2  SRS_Resource__resourceType__Format_list.
Definition SRS_Resource__resourceType__F1 (z : SRS_Resource__resourceType__Type) : (choice SRS_Resource__resourceType__list) :=
  match z with
   | SRS_Resource__resourceType__aperiodic t => existT _ 0 t
  | SRS_Resource__resourceType__semi_persistent t => existT _ 1 t
  | SRS_Resource__resourceType__periodic t => existT _ 2 t
  end.
Definition SRS_Resource__resourceType__g := (fun n => typ_set (get_nth_typ SRS_Resource__resourceType__list n)).
Definition SRS_Resource__resourceType__F2 (y : choice SRS_Resource__resourceType__list) : SRS_Resource__resourceType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_Resource__resourceType__g n -> SRS_Resource__resourceType__Type) with
    | 0 => fun (t : SRS_Resource__resourceType__aperiodic__Type) => SRS_Resource__resourceType__aperiodic t 
    | 1 => fun (t : SRS_Resource__resourceType__semi_persistent__Type) => SRS_Resource__resourceType__semi_persistent t 
    | 2 => fun (t : SRS_Resource__resourceType__periodic__Type) => SRS_Resource__resourceType__periodic t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SRS_Resource__resourceType__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SRS_Resource__resourceType__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_Resource__resourceType__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SRS_Resource__resourceType__Type with end) n0
           end t0).

Lemma SRS_Resource__resourceType__helper2 :  forall (y : SRS_Resource__resourceType__Type), SRS_Resource__resourceType__cond y -> choice_cond SRS_Resource__resourceType__list (SRS_Resource__resourceType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_Resource__resourceType__helper3 :  forall (y : SRS_Resource__resourceType__Type), SRS_Resource__resourceType__F2 (SRS_Resource__resourceType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_Resource__resourceType__helper4 : (forall b : choice SRS_Resource__resourceType__list, choice_cond SRS_Resource__resourceType__list b -> SRS_Resource__resourceType__cond (SRS_Resource__resourceType__F2 b) /\ SRS_Resource__resourceType__F1 (SRS_Resource__resourceType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_Resource__resourceType__F1 SRS_Resource__resourceType__F2.
Definition SRS_Resource__resourceType__Format : T_Format SRS_Resource__resourceType__Type SRS_Resource__resourceType__cond :=
  (* Eval compute in *) proj2_format SRS_Resource__resourceType__cond SRS_Resource__resourceType__list__Format SRS_Resource__resourceType__F1 SRS_Resource__resourceType__F2 SRS_Resource__resourceType__helper2 SRS_Resource__resourceType__helper3 SRS_Resource__resourceType__helper4.
Opaque SRS_Resource__resourceType__cond SRS_Resource__resourceType__Format.

Definition SRS_Resource__sequenceId__Format : T_Format Z SRS_Resource__sequenceId__cond :=
 ranged_int_format (0) (1023) SRS_Resource__sequenceId__helper1 SRS_Resource__sequenceId__helper2.

Opaque SRS_Resource__sequenceId__cond SRS_Resource__sequenceId__Format.

Definition SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__Format : T_Format Z SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__cond :=
 ranged_int_format (0) (13) SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__helper1 SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__helper2.

Opaque SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__cond SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__Format.

Definition SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Format : T_Format SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__nat__Format SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F1 SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F2 SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F1F2 SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__F2F1.

Opaque SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__cond SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Format.

Definition SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Format : T_Format SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__nat__Format SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F1 SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F2 SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F1F2 SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__F2F1.

Opaque SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__cond SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Format.


Definition SRS_Resource__ext0O__resourceMapping_r16__Format_Type := Eval cbn in seq_format_prod SRS_Resource__ext0O__resourceMapping_r16__list.
Definition SRS_Resource__ext0O__resourceMapping_r16__Format_list : SRS_Resource__ext0O__resourceMapping_r16__Format_Type :=
  (SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16__Format, (SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16__Format, (SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16__Format, unit_format))).
Definition SRS_Resource__ext0O__resourceMapping_r16__list__Format := (*Eval compute in *) seq_format SRS_Resource__ext0O__resourceMapping_r16__list SRS_Resource__ext0O__resourceMapping_r16__Format_list.
Definition SRS_Resource__ext0O__resourceMapping_r16__F1 z :=
  (SRS_Resource__ext0O__resourceMapping_r16__startPosition_r16 z, (SRS_Resource__ext0O__resourceMapping_r16__nrofSymbols_r16 z, (SRS_Resource__ext0O__resourceMapping_r16__repetitionFactor_r16 z, tt))).
Definition SRS_Resource__ext0O__resourceMapping_r16__F2 (y : seq_type SRS_Resource__ext0O__resourceMapping_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SRS_Resource__ext0O__resourceMapping_r16__Type i0 i1 i2
  end.
Lemma SRS_Resource__ext0O__resourceMapping_r16__F1F2_cond (z : SRS_Resource__ext0O__resourceMapping_r16__Type)
  : SRS_Resource__ext0O__resourceMapping_r16__cond z ->
  (seq_cond SRS_Resource__ext0O__resourceMapping_r16__list (SRS_Resource__ext0O__resourceMapping_r16__F1 z)).
intro H. unfold SRS_Resource__ext0O__resourceMapping_r16__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__ext0O__resourceMapping_r16__F1F2_cond2 (z : SRS_Resource__ext0O__resourceMapping_r16__Type)
 : SRS_Resource__ext0O__resourceMapping_r16__F2 (SRS_Resource__ext0O__resourceMapping_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__ext0O__resourceMapping_r16__F2F1_cond (y : seq_type SRS_Resource__ext0O__resourceMapping_r16__list)
  : seq_cond SRS_Resource__ext0O__resourceMapping_r16__list y ->
 (SRS_Resource__ext0O__resourceMapping_r16__cond (SRS_Resource__ext0O__resourceMapping_r16__F2 y)) /\  SRS_Resource__ext0O__resourceMapping_r16__F1 (SRS_Resource__ext0O__resourceMapping_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__ext0O__resourceMapping_r16__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__ext0O__resourceMapping_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__ext0O__resourceMapping_r16__Format : T_Format SRS_Resource__ext0O__resourceMapping_r16__Type SRS_Resource__ext0O__resourceMapping_r16__cond :=
        proj2_format  SRS_Resource__ext0O__resourceMapping_r16__cond SRS_Resource__ext0O__resourceMapping_r16__list__Format
    SRS_Resource__ext0O__resourceMapping_r16__F1 SRS_Resource__ext0O__resourceMapping_r16__F2 SRS_Resource__ext0O__resourceMapping_r16__F1F2_cond  SRS_Resource__ext0O__resourceMapping_r16__F1F2_cond2 SRS_Resource__ext0O__resourceMapping_r16__F2F1_cond.
Opaque SRS_Resource__ext0O__resourceMapping_r16__cond SRS_Resource__ext0O__resourceMapping_r16__Format.


Definition SRS_Resource__ext0O__Format_Type := Eval cbn in seq_format_prod SRS_Resource__ext0O__list.
Definition SRS_Resource__ext0O__Format_list : SRS_Resource__ext0O__Format_Type :=
  (SRS_Resource__ext0O__resourceMapping_r16__Format, unit_format).
Definition SRS_Resource__ext0O__list__Format := (*Eval compute in *) seq_format SRS_Resource__ext0O__list SRS_Resource__ext0O__Format_list.
Definition SRS_Resource__ext0O__F1 z :=
  (SRS_Resource__ext0O__resourceMapping_r16 z, tt).
Definition SRS_Resource__ext0O__F2 (y : seq_type SRS_Resource__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SRS_Resource__ext0O__Type i0
  end.
Lemma SRS_Resource__ext0O__F1F2_cond (z : SRS_Resource__ext0O__Type)
  : SRS_Resource__ext0O__cond z ->
  (seq_cond SRS_Resource__ext0O__list (SRS_Resource__ext0O__F1 z)).
intro H. unfold SRS_Resource__ext0O__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__ext0O__F1F2_cond2 (z : SRS_Resource__ext0O__Type)
 : SRS_Resource__ext0O__F2 (SRS_Resource__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__ext0O__F2F1_cond (y : seq_type SRS_Resource__ext0O__list)
  : seq_cond SRS_Resource__ext0O__list y ->
 (SRS_Resource__ext0O__cond (SRS_Resource__ext0O__F2 y)) /\  SRS_Resource__ext0O__F1 (SRS_Resource__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__ext0O__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__ext0O__Format : T_Format SRS_Resource__ext0O__Type SRS_Resource__ext0O__cond :=
        proj2_format  SRS_Resource__ext0O__cond SRS_Resource__ext0O__list__Format
    SRS_Resource__ext0O__F1 SRS_Resource__ext0O__F2 SRS_Resource__ext0O__F1F2_cond  SRS_Resource__ext0O__F1F2_cond2 SRS_Resource__ext0O__F2F1_cond.
Opaque SRS_Resource__ext0O__cond SRS_Resource__ext0O__Format.

Definition SRS_Resource__ext0__check_all_none (b : SRS_Resource__ext0O__Type) : bool :=
match b with 
  | make__SRS_Resource__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SRS_Resource__ext0__Format : T_Format SRS_Resource__ext0__Type SRS_Resource__ext0__cond :=
  restrict_add_format SRS_Resource__ext0__check_all_none SRS_Resource__ext0O__Format.

Opaque SRS_Resource__ext0__cond SRS_Resource__ext0__Format.

Opaque SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__cond SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__Format.

Definition SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__Format : T_Format Z SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__cond :=
 ranged_int_format (0) (13) SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__helper1 SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__helper2.

Opaque SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__cond SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__Format.

Definition SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Format : T_Format SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__nat__Format SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F1 SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F2 SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F1F2 SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__F2F1.

Opaque SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__cond SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Format.

Definition SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Format : T_Format SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__nat__Format SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F1 SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F2 SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F1F2 SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__F2F1.

Opaque SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__cond SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Format.


Definition SRS_Resource__ext1O__resourceMapping_r17__Format_Type := Eval cbn in seq_format_prod SRS_Resource__ext1O__resourceMapping_r17__list.
Definition SRS_Resource__ext1O__resourceMapping_r17__Format_list : SRS_Resource__ext1O__resourceMapping_r17__Format_Type :=
  (SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17__Format, (SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17__Format, (SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17__Format, unit_format))).
Definition SRS_Resource__ext1O__resourceMapping_r17__list__Format := (*Eval compute in *) seq_format SRS_Resource__ext1O__resourceMapping_r17__list SRS_Resource__ext1O__resourceMapping_r17__Format_list.
Definition SRS_Resource__ext1O__resourceMapping_r17__F1 z :=
  (SRS_Resource__ext1O__resourceMapping_r17__startPosition_r17 z, (SRS_Resource__ext1O__resourceMapping_r17__nrofSymbols_r17 z, (SRS_Resource__ext1O__resourceMapping_r17__repetitionFactor_r17 z, tt))).
Definition SRS_Resource__ext1O__resourceMapping_r17__F2 (y : seq_type SRS_Resource__ext1O__resourceMapping_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SRS_Resource__ext1O__resourceMapping_r17__Type i0 i1 i2
  end.
Lemma SRS_Resource__ext1O__resourceMapping_r17__F1F2_cond (z : SRS_Resource__ext1O__resourceMapping_r17__Type)
  : SRS_Resource__ext1O__resourceMapping_r17__cond z ->
  (seq_cond SRS_Resource__ext1O__resourceMapping_r17__list (SRS_Resource__ext1O__resourceMapping_r17__F1 z)).
intro H. unfold SRS_Resource__ext1O__resourceMapping_r17__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__ext1O__resourceMapping_r17__F1F2_cond2 (z : SRS_Resource__ext1O__resourceMapping_r17__Type)
 : SRS_Resource__ext1O__resourceMapping_r17__F2 (SRS_Resource__ext1O__resourceMapping_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__ext1O__resourceMapping_r17__F2F1_cond (y : seq_type SRS_Resource__ext1O__resourceMapping_r17__list)
  : seq_cond SRS_Resource__ext1O__resourceMapping_r17__list y ->
 (SRS_Resource__ext1O__resourceMapping_r17__cond (SRS_Resource__ext1O__resourceMapping_r17__F2 y)) /\  SRS_Resource__ext1O__resourceMapping_r17__F1 (SRS_Resource__ext1O__resourceMapping_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__ext1O__resourceMapping_r17__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__ext1O__resourceMapping_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__ext1O__resourceMapping_r17__Format : T_Format SRS_Resource__ext1O__resourceMapping_r17__Type SRS_Resource__ext1O__resourceMapping_r17__cond :=
        proj2_format  SRS_Resource__ext1O__resourceMapping_r17__cond SRS_Resource__ext1O__resourceMapping_r17__list__Format
    SRS_Resource__ext1O__resourceMapping_r17__F1 SRS_Resource__ext1O__resourceMapping_r17__F2 SRS_Resource__ext1O__resourceMapping_r17__F1F2_cond  SRS_Resource__ext1O__resourceMapping_r17__F1F2_cond2 SRS_Resource__ext1O__resourceMapping_r17__F2F1_cond.
Opaque SRS_Resource__ext1O__resourceMapping_r17__cond SRS_Resource__ext1O__resourceMapping_r17__Format.

Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__Format : T_Format Z SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__cond :=
 ranged_int_format (0) (1) SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__helper1 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__helper2.

Opaque SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__cond SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__Format.

Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__Format : T_Format Z SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__cond :=
 ranged_int_format (0) (3) SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__helper1 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__helper2.

Opaque SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__cond SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__Format.


Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Format_Type := Eval cbn in get_formats SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Format_list : SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Format_Type :=
  (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17__Format, (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17__Format, unit__Format)).
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list__Format := Eval compute in choice_format SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__len_helper1 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__len_helper2  SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Format_list.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F1 (z : SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type) : (choice SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list) :=
  match z with
   | SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17 t => existT _ 0 t
  | SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17 t => existT _ 1 t
  end.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__g := (fun n => typ_set (get_nth_typ SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list n)).
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F2 (y : choice SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list) : SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__g n -> SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type) with
    | 0 => fun (t : Z) => SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor2_r17 t 
    | 1 => fun (t : Z) => SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__startRBIndexAndFreqScalingFactor4_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type with end) n0
           end t0).

Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__helper2 :  forall (y : SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type), SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__cond y -> choice_cond SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__helper3 :  forall (y : SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type), SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F2 (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__helper4 : (forall b : choice SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list, choice_cond SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list b -> SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__cond (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F2 b) /\ SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F1 (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F1 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F2.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Format : T_Format SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Type SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__cond :=
  (* Eval compute in *) proj2_format SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__cond SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__list__Format SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F1 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__F2 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__helper2 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__helper3 SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__helper4.
Opaque SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__cond SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Format.

Definition SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Format : T_Format SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__nat__Format SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F1 SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F2 SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F1F2 SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__F2F1.

Opaque SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__cond SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Format.


Definition SRS_Resource__ext1O__partialFreqSounding_r17__Format_Type := Eval cbn in seq_format_prod SRS_Resource__ext1O__partialFreqSounding_r17__list.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__Format_list : SRS_Resource__ext1O__partialFreqSounding_r17__Format_Type :=
  (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17__Format, (SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17__Format, unit_format)).
Definition SRS_Resource__ext1O__partialFreqSounding_r17__list__Format := (*Eval compute in *) seq_format SRS_Resource__ext1O__partialFreqSounding_r17__list SRS_Resource__ext1O__partialFreqSounding_r17__Format_list.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__F1 z :=
  (SRS_Resource__ext1O__partialFreqSounding_r17__startRBIndexFScaling_r17 z, (SRS_Resource__ext1O__partialFreqSounding_r17__enableStartRBHopping_r17 z, tt)).
Definition SRS_Resource__ext1O__partialFreqSounding_r17__F2 (y : seq_type SRS_Resource__ext1O__partialFreqSounding_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_Resource__ext1O__partialFreqSounding_r17__Type i0 i1
  end.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__F1F2_cond (z : SRS_Resource__ext1O__partialFreqSounding_r17__Type)
  : SRS_Resource__ext1O__partialFreqSounding_r17__cond z ->
  (seq_cond SRS_Resource__ext1O__partialFreqSounding_r17__list (SRS_Resource__ext1O__partialFreqSounding_r17__F1 z)).
intro H. unfold SRS_Resource__ext1O__partialFreqSounding_r17__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__F1F2_cond2 (z : SRS_Resource__ext1O__partialFreqSounding_r17__Type)
 : SRS_Resource__ext1O__partialFreqSounding_r17__F2 (SRS_Resource__ext1O__partialFreqSounding_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__ext1O__partialFreqSounding_r17__F2F1_cond (y : seq_type SRS_Resource__ext1O__partialFreqSounding_r17__list)
  : seq_cond SRS_Resource__ext1O__partialFreqSounding_r17__list y ->
 (SRS_Resource__ext1O__partialFreqSounding_r17__cond (SRS_Resource__ext1O__partialFreqSounding_r17__F2 y)) /\  SRS_Resource__ext1O__partialFreqSounding_r17__F1 (SRS_Resource__ext1O__partialFreqSounding_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__ext1O__partialFreqSounding_r17__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__ext1O__partialFreqSounding_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__ext1O__partialFreqSounding_r17__Format : T_Format SRS_Resource__ext1O__partialFreqSounding_r17__Type SRS_Resource__ext1O__partialFreqSounding_r17__cond :=
        proj2_format  SRS_Resource__ext1O__partialFreqSounding_r17__cond SRS_Resource__ext1O__partialFreqSounding_r17__list__Format
    SRS_Resource__ext1O__partialFreqSounding_r17__F1 SRS_Resource__ext1O__partialFreqSounding_r17__F2 SRS_Resource__ext1O__partialFreqSounding_r17__F1F2_cond  SRS_Resource__ext1O__partialFreqSounding_r17__F1F2_cond2 SRS_Resource__ext1O__partialFreqSounding_r17__F2F1_cond.
Opaque SRS_Resource__ext1O__partialFreqSounding_r17__cond SRS_Resource__ext1O__partialFreqSounding_r17__Format.

Definition SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__Format : T_Format Z SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__cond :=
 ranged_int_format (0) (7) SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__helper1 SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__helper2.

Opaque SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__cond SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__Format.

Definition SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__Format : T_Format Z SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__cond :=
 ranged_int_format (0) (5) SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__helper1 SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__helper2.

Opaque SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__cond SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__Format.


Definition SRS_Resource__ext1O__transmissionComb_n8_r17__Format_Type := Eval cbn in seq_format_prod SRS_Resource__ext1O__transmissionComb_n8_r17__list.
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__Format_list : SRS_Resource__ext1O__transmissionComb_n8_r17__Format_Type :=
  (SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17__Format, (SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17__Format, unit_format)).
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__list__Format := (*Eval compute in *) seq_format SRS_Resource__ext1O__transmissionComb_n8_r17__list SRS_Resource__ext1O__transmissionComb_n8_r17__Format_list.
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__F1 z :=
  (SRS_Resource__ext1O__transmissionComb_n8_r17__combOffset_n8_r17 z, (SRS_Resource__ext1O__transmissionComb_n8_r17__cyclicShift_n8_r17 z, tt)).
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__F2 (y : seq_type SRS_Resource__ext1O__transmissionComb_n8_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_Resource__ext1O__transmissionComb_n8_r17__Type i0 i1
  end.
Lemma SRS_Resource__ext1O__transmissionComb_n8_r17__F1F2_cond (z : SRS_Resource__ext1O__transmissionComb_n8_r17__Type)
  : SRS_Resource__ext1O__transmissionComb_n8_r17__cond z ->
  (seq_cond SRS_Resource__ext1O__transmissionComb_n8_r17__list (SRS_Resource__ext1O__transmissionComb_n8_r17__F1 z)).
intro H. unfold SRS_Resource__ext1O__transmissionComb_n8_r17__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__ext1O__transmissionComb_n8_r17__F1F2_cond2 (z : SRS_Resource__ext1O__transmissionComb_n8_r17__Type)
 : SRS_Resource__ext1O__transmissionComb_n8_r17__F2 (SRS_Resource__ext1O__transmissionComb_n8_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__ext1O__transmissionComb_n8_r17__F2F1_cond (y : seq_type SRS_Resource__ext1O__transmissionComb_n8_r17__list)
  : seq_cond SRS_Resource__ext1O__transmissionComb_n8_r17__list y ->
 (SRS_Resource__ext1O__transmissionComb_n8_r17__cond (SRS_Resource__ext1O__transmissionComb_n8_r17__F2 y)) /\  SRS_Resource__ext1O__transmissionComb_n8_r17__F1 (SRS_Resource__ext1O__transmissionComb_n8_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__ext1O__transmissionComb_n8_r17__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__ext1O__transmissionComb_n8_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__ext1O__transmissionComb_n8_r17__Format : T_Format SRS_Resource__ext1O__transmissionComb_n8_r17__Type SRS_Resource__ext1O__transmissionComb_n8_r17__cond :=
        proj2_format  SRS_Resource__ext1O__transmissionComb_n8_r17__cond SRS_Resource__ext1O__transmissionComb_n8_r17__list__Format
    SRS_Resource__ext1O__transmissionComb_n8_r17__F1 SRS_Resource__ext1O__transmissionComb_n8_r17__F2 SRS_Resource__ext1O__transmissionComb_n8_r17__F1F2_cond  SRS_Resource__ext1O__transmissionComb_n8_r17__F1F2_cond2 SRS_Resource__ext1O__transmissionComb_n8_r17__F2F1_cond.
Opaque SRS_Resource__ext1O__transmissionComb_n8_r17__cond SRS_Resource__ext1O__transmissionComb_n8_r17__Format.


Definition SRS_Resource__ext1O__srs_TCI_State_r17__Format_Type := Eval cbn in get_formats SRS_Resource__ext1O__srs_TCI_State_r17__list.
Definition SRS_Resource__ext1O__srs_TCI_State_r17__Format_list : SRS_Resource__ext1O__srs_TCI_State_r17__Format_Type :=
  (TCI_UL_State_Id_r17__Format, (TCI_StateId__Format, unit__Format)).
Definition SRS_Resource__ext1O__srs_TCI_State_r17__list__Format := Eval compute in choice_format SRS_Resource__ext1O__srs_TCI_State_r17__list SRS_Resource__ext1O__srs_TCI_State_r17__len_helper1 SRS_Resource__ext1O__srs_TCI_State_r17__len_helper2  SRS_Resource__ext1O__srs_TCI_State_r17__Format_list.
Definition SRS_Resource__ext1O__srs_TCI_State_r17__F1 (z : SRS_Resource__ext1O__srs_TCI_State_r17__Type) : (choice SRS_Resource__ext1O__srs_TCI_State_r17__list) :=
  match z with
   | SRS_Resource__ext1O__srs_TCI_State_r17__srs_UL_TCI_State t => existT _ 0 t
  | SRS_Resource__ext1O__srs_TCI_State_r17__srs_DLorJointTCI_State t => existT _ 1 t
  end.
Definition SRS_Resource__ext1O__srs_TCI_State_r17__g := (fun n => typ_set (get_nth_typ SRS_Resource__ext1O__srs_TCI_State_r17__list n)).
Definition SRS_Resource__ext1O__srs_TCI_State_r17__F2 (y : choice SRS_Resource__ext1O__srs_TCI_State_r17__list) : SRS_Resource__ext1O__srs_TCI_State_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_Resource__ext1O__srs_TCI_State_r17__g n -> SRS_Resource__ext1O__srs_TCI_State_r17__Type) with
    | 0 => fun (t : TCI_UL_State_Id_r17__Type) => SRS_Resource__ext1O__srs_TCI_State_r17__srs_UL_TCI_State t 
    | 1 => fun (t : TCI_StateId__Type) => SRS_Resource__ext1O__srs_TCI_State_r17__srs_DLorJointTCI_State t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SRS_Resource__ext1O__srs_TCI_State_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SRS_Resource__ext1O__srs_TCI_State_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_Resource__ext1O__srs_TCI_State_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SRS_Resource__ext1O__srs_TCI_State_r17__Type with end) n0
           end t0).

Lemma SRS_Resource__ext1O__srs_TCI_State_r17__helper2 :  forall (y : SRS_Resource__ext1O__srs_TCI_State_r17__Type), SRS_Resource__ext1O__srs_TCI_State_r17__cond y -> choice_cond SRS_Resource__ext1O__srs_TCI_State_r17__list (SRS_Resource__ext1O__srs_TCI_State_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_Resource__ext1O__srs_TCI_State_r17__helper3 :  forall (y : SRS_Resource__ext1O__srs_TCI_State_r17__Type), SRS_Resource__ext1O__srs_TCI_State_r17__F2 (SRS_Resource__ext1O__srs_TCI_State_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_Resource__ext1O__srs_TCI_State_r17__helper4 : (forall b : choice SRS_Resource__ext1O__srs_TCI_State_r17__list, choice_cond SRS_Resource__ext1O__srs_TCI_State_r17__list b -> SRS_Resource__ext1O__srs_TCI_State_r17__cond (SRS_Resource__ext1O__srs_TCI_State_r17__F2 b) /\ SRS_Resource__ext1O__srs_TCI_State_r17__F1 (SRS_Resource__ext1O__srs_TCI_State_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_Resource__ext1O__srs_TCI_State_r17__F1 SRS_Resource__ext1O__srs_TCI_State_r17__F2.
Definition SRS_Resource__ext1O__srs_TCI_State_r17__Format : T_Format SRS_Resource__ext1O__srs_TCI_State_r17__Type SRS_Resource__ext1O__srs_TCI_State_r17__cond :=
  (* Eval compute in *) proj2_format SRS_Resource__ext1O__srs_TCI_State_r17__cond SRS_Resource__ext1O__srs_TCI_State_r17__list__Format SRS_Resource__ext1O__srs_TCI_State_r17__F1 SRS_Resource__ext1O__srs_TCI_State_r17__F2 SRS_Resource__ext1O__srs_TCI_State_r17__helper2 SRS_Resource__ext1O__srs_TCI_State_r17__helper3 SRS_Resource__ext1O__srs_TCI_State_r17__helper4.
Opaque SRS_Resource__ext1O__srs_TCI_State_r17__cond SRS_Resource__ext1O__srs_TCI_State_r17__Format.


Definition SRS_Resource__ext1O__Format_Type := Eval cbn in seq_format_prod SRS_Resource__ext1O__list.
Definition SRS_Resource__ext1O__Format_list : SRS_Resource__ext1O__Format_Type :=
  (SRS_Resource__ext1O__spatialRelationInfo_PDC_r17__Format, (SRS_Resource__ext1O__resourceMapping_r17__Format, (SRS_Resource__ext1O__partialFreqSounding_r17__Format, (SRS_Resource__ext1O__transmissionComb_n8_r17__Format, (SRS_Resource__ext1O__srs_TCI_State_r17__Format, unit_format))))).
Definition SRS_Resource__ext1O__list__Format := (*Eval compute in *) seq_format SRS_Resource__ext1O__list SRS_Resource__ext1O__Format_list.
Definition SRS_Resource__ext1O__F1 z :=
  (SRS_Resource__ext1O__spatialRelationInfo_PDC_r17 z, (SRS_Resource__ext1O__resourceMapping_r17 z, (SRS_Resource__ext1O__partialFreqSounding_r17 z, (SRS_Resource__ext1O__transmissionComb_n8_r17 z, (SRS_Resource__ext1O__srs_TCI_State_r17 z, tt))))).
Definition SRS_Resource__ext1O__F2 (y : seq_type SRS_Resource__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SRS_Resource__ext1O__Type i0 i1 i2 i3 i4
  end.
Lemma SRS_Resource__ext1O__F1F2_cond (z : SRS_Resource__ext1O__Type)
  : SRS_Resource__ext1O__cond z ->
  (seq_cond SRS_Resource__ext1O__list (SRS_Resource__ext1O__F1 z)).
intro H. unfold SRS_Resource__ext1O__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__ext1O__F1F2_cond2 (z : SRS_Resource__ext1O__Type)
 : SRS_Resource__ext1O__F2 (SRS_Resource__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__ext1O__F2F1_cond (y : seq_type SRS_Resource__ext1O__list)
  : seq_cond SRS_Resource__ext1O__list y ->
 (SRS_Resource__ext1O__cond (SRS_Resource__ext1O__F2 y)) /\  SRS_Resource__ext1O__F1 (SRS_Resource__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__ext1O__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__ext1O__Format : T_Format SRS_Resource__ext1O__Type SRS_Resource__ext1O__cond :=
        proj2_format  SRS_Resource__ext1O__cond SRS_Resource__ext1O__list__Format
    SRS_Resource__ext1O__F1 SRS_Resource__ext1O__F2 SRS_Resource__ext1O__F1F2_cond  SRS_Resource__ext1O__F1F2_cond2 SRS_Resource__ext1O__F2F1_cond.
Opaque SRS_Resource__ext1O__cond SRS_Resource__ext1O__Format.

Definition SRS_Resource__ext1__check_all_none (b : SRS_Resource__ext1O__Type) : bool :=
match b with 
  | make__SRS_Resource__ext1O__Type None None None None None  => false 
  | _ => true 
 end.
Definition SRS_Resource__ext1__Format : T_Format SRS_Resource__ext1__Type SRS_Resource__ext1__cond :=
  restrict_add_format SRS_Resource__ext1__check_all_none SRS_Resource__ext1O__Format.

Opaque SRS_Resource__ext1__cond SRS_Resource__ext1__Format.

Definition SRS_Resource__ext2O__repetitionFactor_v1730__Format : T_Format SRS_Resource__ext2O__repetitionFactor_v1730__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_Resource__ext2O__repetitionFactor_v1730__nat__Format SRS_Resource__ext2O__repetitionFactor_v1730__F1 SRS_Resource__ext2O__repetitionFactor_v1730__F2 SRS_Resource__ext2O__repetitionFactor_v1730__F1F2 SRS_Resource__ext2O__repetitionFactor_v1730__F2F1.

Opaque SRS_Resource__ext2O__repetitionFactor_v1730__cond SRS_Resource__ext2O__repetitionFactor_v1730__Format.


Definition SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Format_Type := Eval cbn in seq_format_prod SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list.
Definition SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Format_list : SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Format_Type :=
  (ServingCellAndBWP_Id_r17__Format, unit_format).
Definition SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list__Format := (*Eval compute in *) seq_format SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Format_list.
Definition SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1 z :=
  (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cellAndBWP_r17 z, tt).
Definition SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F2 (y : seq_type SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list) :=
  match y with
  | (i0, _)=>
    make__SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Type i0
  end.
Lemma SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1F2_cond (z : SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Type)
  : SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond z ->
  (seq_cond SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1 z)).
intro H. unfold SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1F2_cond2 (z : SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Type)
 : SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F2 (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F2F1_cond (y : seq_type SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list)
  : seq_cond SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list y ->
 (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F2 y)) /\  SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1 (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Format : T_Format SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Type SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond :=
        proj2_format  SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__list__Format
    SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1 SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F2 SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1F2_cond  SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F1F2_cond2 SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__F2F1_cond.
Opaque SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__cond SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Format.


Definition SRS_Resource__ext2O__Format_Type := Eval cbn in seq_format_prod SRS_Resource__ext2O__list.
Definition SRS_Resource__ext2O__Format_list : SRS_Resource__ext2O__Format_Type :=
  (SRS_Resource__ext2O__repetitionFactor_v1730__Format, (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730__Format, unit_format)).
Definition SRS_Resource__ext2O__list__Format := (*Eval compute in *) seq_format SRS_Resource__ext2O__list SRS_Resource__ext2O__Format_list.
Definition SRS_Resource__ext2O__F1 z :=
  (SRS_Resource__ext2O__repetitionFactor_v1730 z, (SRS_Resource__ext2O__srs_DLorJointTCI_State_v1730 z, tt)).
Definition SRS_Resource__ext2O__F2 (y : seq_type SRS_Resource__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SRS_Resource__ext2O__Type i0 i1
  end.
Lemma SRS_Resource__ext2O__F1F2_cond (z : SRS_Resource__ext2O__Type)
  : SRS_Resource__ext2O__cond z ->
  (seq_cond SRS_Resource__ext2O__list (SRS_Resource__ext2O__F1 z)).
intro H. unfold SRS_Resource__ext2O__cond in H. simpl. auto. Qed.
Lemma SRS_Resource__ext2O__F1F2_cond2 (z : SRS_Resource__ext2O__Type)
 : SRS_Resource__ext2O__F2 (SRS_Resource__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_Resource__ext2O__F2F1_cond (y : seq_type SRS_Resource__ext2O__list)
  : seq_cond SRS_Resource__ext2O__list y ->
 (SRS_Resource__ext2O__cond (SRS_Resource__ext2O__F2 y)) /\  SRS_Resource__ext2O__F1 (SRS_Resource__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_Resource__ext2O__cond. simpl in *. auto.
 - simpl. unfold SRS_Resource__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_Resource__ext2O__Format : T_Format SRS_Resource__ext2O__Type SRS_Resource__ext2O__cond :=
        proj2_format  SRS_Resource__ext2O__cond SRS_Resource__ext2O__list__Format
    SRS_Resource__ext2O__F1 SRS_Resource__ext2O__F2 SRS_Resource__ext2O__F1F2_cond  SRS_Resource__ext2O__F1F2_cond2 SRS_Resource__ext2O__F2F1_cond.
Opaque SRS_Resource__ext2O__cond SRS_Resource__ext2O__Format.

Definition SRS_Resource__ext2__check_all_none (b : SRS_Resource__ext2O__Type) : bool :=
match b with 
  | make__SRS_Resource__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition SRS_Resource__ext2__Format : T_Format SRS_Resource__ext2__Type SRS_Resource__ext2__cond :=
  restrict_add_format SRS_Resource__ext2__check_all_none SRS_Resource__ext2O__Format.

Opaque SRS_Resource__ext2__cond SRS_Resource__ext2__Format.


Definition SRS_Resource__root_Format_Type := Eval cbn in seq_format_prod SRS_Resource__root_list.
Definition SRS_Resource__root_Format_list : SRS_Resource__root_Format_Type :=
  (SRS_ResourceId__Format, (SRS_Resource__nrofSRS_Ports__Format, (SRS_Resource__ptrs_PortIndex__Format, (SRS_Resource__transmissionComb__Format, (SRS_Resource__resourceMapping__Format, (SRS_Resource__freqDomainPosition__Format, (SRS_Resource__freqDomainShift__Format, (SRS_Resource__freqHopping__Format, (SRS_Resource__groupOrSequenceHopping__Format, (SRS_Resource__resourceType__Format, (SRS_Resource__sequenceId__Format, (SRS_SpatialRelationInfo__Format, unit_format)))))))))))).

Definition SRS_Resource__ext_Format_Type := Eval cbn in get_formats SRS_Resource__ext_list.
Definition SRS_Resource__ext_Format_list : SRS_Resource__ext_Format_Type :=
  (SRS_Resource__ext0__Format, (SRS_Resource__ext1__Format, (SRS_Resource__ext2__Format, unit__Format))).

Definition SRS_Resource__list_type : Set := (seq_type SRS_Resource__root_list) * (seq_ext_type SRS_Resource__ext_list).
Definition SRS_Resource__list_cond (z : SRS_Resource__list_type) : Prop :=
        (seq_cond SRS_Resource__root_list (fst z)) /\ (seq_ext_cond SRS_Resource__ext_list (snd z)).
Definition SRS_Resource__list_format : T_Format SRS_Resource__list_type SRS_Resource__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_Resource__root_list SRS_Resource__root_Format_list SRS_Resource__ext_list SRS_Resource__ext_Format_list.

Opaque SRS_Resource__list_format.
Definition SRS_Resource__F1 (z : SRS_Resource__Type) : SRS_Resource__list_type :=
  (((SRS_Resource__srs_ResourceId z, (SRS_Resource__nrofSRS_Ports z, (SRS_Resource__ptrs_PortIndex z, (SRS_Resource__transmissionComb z, (SRS_Resource__resourceMapping z, (SRS_Resource__freqDomainPosition z, (SRS_Resource__freqDomainShift z, (SRS_Resource__freqHopping z, (SRS_Resource__groupOrSequenceHopping z, (SRS_Resource__resourceType z, (SRS_Resource__sequenceId z, (SRS_Resource__spatialRelationInfo z, tt))))))))))))), (
(SRS_Resource__ext0 z, (SRS_Resource__ext1 z, (SRS_Resource__ext2 z, tt))))).
Definition SRS_Resource__F2 (y : SRS_Resource__list_type) : SRS_Resource__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, _)))))))))))), (i0, (i1, (i2, _))))=>
    make__SRS_Resource__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 i0 i1 i2
  end.
Definition SRS_Resource__helper1 : (forall a : SRS_Resource__Type, SRS_Resource__cond a -> SRS_Resource__list_cond (SRS_Resource__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_Resource__helper2 : (forall a : SRS_Resource__Type, SRS_Resource__F2 (SRS_Resource__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_Resource__helper3 : (forall b : SRS_Resource__list_type, SRS_Resource__list_cond b -> SRS_Resource__cond (SRS_Resource__F2 b) /\ SRS_Resource__F1 (SRS_Resource__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_Resource__cond, SRS_Resource__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_Resource__Format : T_Format SRS_Resource__Type SRS_Resource__cond :=
 proj2_format SRS_Resource__cond SRS_Resource__list_format  SRS_Resource__F1 SRS_Resource__F2 SRS_Resource__helper1 SRS_Resource__helper2 SRS_Resource__helper3.

Opaque SRS_Resource__cond SRS_Resource__Format.

