Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PagingCycle.

Opaque PagingCycle__cond PagingCycle__Format.

Lemma PCCH_Config__nAndPagingFrameOffset__halfT__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma PCCH_Config__nAndPagingFrameOffset__halfT__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__nAndPagingFrameOffset__halfT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__nAndPagingFrameOffset__halfT__Type := Z.
Definition PCCH_Config__nAndPagingFrameOffset__halfT__cond := (fun z => (0 <= z <= 1)%Z).
Lemma PCCH_Config__nAndPagingFrameOffset__quarterT__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma PCCH_Config__nAndPagingFrameOffset__quarterT__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__nAndPagingFrameOffset__quarterT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__nAndPagingFrameOffset__quarterT__Type := Z.
Definition PCCH_Config__nAndPagingFrameOffset__quarterT__cond := (fun z => (0 <= z <= 3)%Z).
Lemma PCCH_Config__nAndPagingFrameOffset__oneEighthT__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma PCCH_Config__nAndPagingFrameOffset__oneEighthT__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__nAndPagingFrameOffset__oneEighthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__nAndPagingFrameOffset__oneEighthT__Type := Z.
Definition PCCH_Config__nAndPagingFrameOffset__oneEighthT__cond := (fun z => (0 <= z <= 7)%Z).
Lemma PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__Type := Z.
Definition PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__cond := (fun z => (0 <= z <= 15)%Z).

Inductive PCCH_Config__nAndPagingFrameOffset__Type : Set :=
  | PCCH_Config__nAndPagingFrameOffset__oneT : unit -> PCCH_Config__nAndPagingFrameOffset__Type
  | PCCH_Config__nAndPagingFrameOffset__halfT : Z -> PCCH_Config__nAndPagingFrameOffset__Type
  | PCCH_Config__nAndPagingFrameOffset__quarterT : Z -> PCCH_Config__nAndPagingFrameOffset__Type
  | PCCH_Config__nAndPagingFrameOffset__oneEighthT : Z -> PCCH_Config__nAndPagingFrameOffset__Type
  | PCCH_Config__nAndPagingFrameOffset__oneSixteenthT : Z -> PCCH_Config__nAndPagingFrameOffset__Type
.
Definition PCCH_Config__nAndPagingFrameOffset__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons Z PCCH_Config__nAndPagingFrameOffset__halfT__cond ::
typ_cons Z PCCH_Config__nAndPagingFrameOffset__quarterT__cond ::
typ_cons Z PCCH_Config__nAndPagingFrameOffset__oneEighthT__cond ::
typ_cons Z PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__cond ::
 nil).
Definition PCCH_Config__nAndPagingFrameOffset__cond (c : PCCH_Config__nAndPagingFrameOffset__Type) := 
  match c with
  | PCCH_Config__nAndPagingFrameOffset__oneT t => (fun _ => True) t 
  | PCCH_Config__nAndPagingFrameOffset__halfT t => PCCH_Config__nAndPagingFrameOffset__halfT__cond t 
  | PCCH_Config__nAndPagingFrameOffset__quarterT t => PCCH_Config__nAndPagingFrameOffset__quarterT__cond t 
  | PCCH_Config__nAndPagingFrameOffset__oneEighthT t => PCCH_Config__nAndPagingFrameOffset__oneEighthT__cond t 
  | PCCH_Config__nAndPagingFrameOffset__oneSixteenthT t => PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__cond t 
  end.

Lemma PCCH_Config__nAndPagingFrameOffset__len_helper1 : to_bit_sz (length PCCH_Config__nAndPagingFrameOffset__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PCCH_Config__nAndPagingFrameOffset__len_helper2 : 2 <= length2 PCCH_Config__nAndPagingFrameOffset__list.
 simpl. lia. Qed.
Inductive PCCH_Config__ns__Type : Set :=
 | PCCH_Config__ns__four
 | PCCH_Config__ns__two
 | PCCH_Config__ns__one
.
Definition PCCH_Config__ns__cond := (fun (_ : PCCH_Config__ns__Type) => True).
Lemma PCCH_Config__ns__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PCCH_Config__ns__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PCCH_Config__ns__nat__helper.

Definition PCCH_Config__ns__F1 t :=
  match t with
  | PCCH_Config__ns__four => 0
  | PCCH_Config__ns__two => 1
  | PCCH_Config__ns__one => 2
  end.
Definition PCCH_Config__ns__F2 n :=
  match n with
  | 0 => PCCH_Config__ns__four
  | 1 => PCCH_Config__ns__two
  | 2 => PCCH_Config__ns__one
  | _ => PCCH_Config__ns__four
  end.
Lemma PCCH_Config__ns__F1F2 : forall x : PCCH_Config__ns__Type, (PCCH_Config__ns__F1 x <= 2) /\ PCCH_Config__ns__F2 (PCCH_Config__ns__F1 x) = x. imp_solve. Qed.
Lemma PCCH_Config__ns__F2F1 : forall (y : nat) (H : y <= 2), PCCH_Config__ns__F1 (PCCH_Config__ns__F2 y) = y. enum_solve H y. Qed.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper1 : (0 <= 139)%Z.  lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper2 : to_bit_sz (Z.to_nat (139 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (139 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__Type := Z.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__cond := (fun z => (0 <= z <= 139)%Z).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type := list Z.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__cond z) .

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1 : (0 <= 279)%Z.  lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper2 : to_bit_sz (Z.to_nat (279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Type := Z.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond := (fun z => (0 <= z <= 279)%Z).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type := list Z.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond z) .

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1 : (0 <= 559)%Z.  lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper2 : to_bit_sz (Z.to_nat (559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Type := Z.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond := (fun z => (0 <= z <= 559)%Z).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type := list Z.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond z) .

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1 : (0 <= 1119)%Z.  lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper2 : to_bit_sz (Z.to_nat (1119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Type := Z.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond := (fun z => (0 <= z <= 1119)%Z).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type := list Z.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond z) .

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1 : (0 <= 2239)%Z.  lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (2239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Type := Z.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 2239)%Z).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type := list Z.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond z) .

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1 : (0 <= 4479)%Z.  lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (4479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Type := Z.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 4479)%Z).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type := list Z.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond z) .

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1 : (0 <= 8959)%Z.  lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (8959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Type := Z.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 8959)%Z).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type := list Z.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond z) .

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper1 : (0 <= 17919)%Z.  lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (17919 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (17919 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__Type := Z.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 17919)%Z).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type := list Z.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__cond z) .


Inductive PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type : Set :=
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type
.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list : list typ := (
typ_cons PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond ::
typ_cons PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond ::
typ_cons PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond ::
typ_cons PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond ::
typ_cons PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond ::
typ_cons PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond ::
typ_cons PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond ::
typ_cons PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond ::
 nil).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__cond (c : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type) := 
  match c with
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT t => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond t 
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT t => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond t 
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond t 
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond t 
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond t 
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond t 
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT t => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond t 
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT t => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond t 
  end.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__len_helper1 : to_bit_sz (length PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__len_helper2 : 2 <= length2 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list.
 simpl. lia. Qed.
Lemma PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__helper1 : (2 <= 4)%Z.  lia. Qed.
Lemma PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__helper2 : to_bit_sz (Z.to_nat (4 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__Type := Z.
Definition PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__cond := (fun z => (2 <= z <= 4)%Z).
Record PCCH_Config__ext0O__Type : Set :=
  make__PCCH_Config__ext0O__Type {
    PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16 : option Z ;
}.
Definition PCCH_Config__ext0O__list := (
 Opt Z PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__cond ::
 nil).
Definition PCCH_Config__ext0O__cond z := 
  opt_cond PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__cond (PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16 z) /\
  True.

Definition PCCH_Config__ext0__Type := PCCH_Config__ext0O__Type.
Definition PCCH_Config__ext0__cond := PCCH_Config__ext0O__cond.

Inductive PCCH_Config__ext1O__ranPagingInIdlePO_r17__Type : Set :=
 | PCCH_Config__ext1O__ranPagingInIdlePO_r17__true
.
Definition PCCH_Config__ext1O__ranPagingInIdlePO_r17__cond := (fun (_ : PCCH_Config__ext1O__ranPagingInIdlePO_r17__Type) => True).
Lemma PCCH_Config__ext1O__ranPagingInIdlePO_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PCCH_Config__ext1O__ranPagingInIdlePO_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PCCH_Config__ext1O__ranPagingInIdlePO_r17__nat__helper.

Definition PCCH_Config__ext1O__ranPagingInIdlePO_r17__F1 t :=
  match t with
  | PCCH_Config__ext1O__ranPagingInIdlePO_r17__true => 0
  end.
Definition PCCH_Config__ext1O__ranPagingInIdlePO_r17__F2 n :=
  match n with
  | 0 => PCCH_Config__ext1O__ranPagingInIdlePO_r17__true
  | _ => PCCH_Config__ext1O__ranPagingInIdlePO_r17__true
  end.
Lemma PCCH_Config__ext1O__ranPagingInIdlePO_r17__F1F2 : forall x : PCCH_Config__ext1O__ranPagingInIdlePO_r17__Type, (PCCH_Config__ext1O__ranPagingInIdlePO_r17__F1 x <= 0) /\ PCCH_Config__ext1O__ranPagingInIdlePO_r17__F2 (PCCH_Config__ext1O__ranPagingInIdlePO_r17__F1 x) = x. imp_solve. Qed.
Lemma PCCH_Config__ext1O__ranPagingInIdlePO_r17__F2F1 : forall (y : nat) (H : y <= 0), PCCH_Config__ext1O__ranPagingInIdlePO_r17__F1 (PCCH_Config__ext1O__ranPagingInIdlePO_r17__F2 y) = y. enum_solve H y. Qed.

Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper1 : (0 <= 35839)%Z.  lia. Qed.
Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper2 : to_bit_sz (Z.to_nat (35839 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (35839 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__Type := Z.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__cond := (fun z => (0 <= z <= 35839)%Z).
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type := list Z.

Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond (z : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__cond z) .

Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper1 : (0 <= 71679)%Z.  lia. Qed.
Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (71679 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (71679 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__Type := Z.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 71679)%Z).
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type := list Z.

Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond (z : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__cond z) .


Inductive PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type : Set :=
  | PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type -> PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type
  | PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type -> PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type
.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list : list typ := (
typ_cons PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond ::
typ_cons PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond ::
 nil).
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond (c : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type) := 
  match c with
  | PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT t => PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond t 
  | PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT t => PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond t 
  end.

Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__len_helper1 : to_bit_sz (length PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__len_helper2 : 2 <= length2 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list.
 simpl. lia. Qed.
Record PCCH_Config__ext1O__Type : Set :=
  make__PCCH_Config__ext1O__Type {
    PCCH_Config__ext1O__ranPagingInIdlePO_r17 : option PCCH_Config__ext1O__ranPagingInIdlePO_r17__Type ;
    PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710 : option PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type ;
}.
Definition PCCH_Config__ext1O__list := (
 Opt PCCH_Config__ext1O__ranPagingInIdlePO_r17__Type PCCH_Config__ext1O__ranPagingInIdlePO_r17__cond ::
 Opt PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond ::
 nil).
Definition PCCH_Config__ext1O__cond z := 
  opt_cond PCCH_Config__ext1O__ranPagingInIdlePO_r17__cond (PCCH_Config__ext1O__ranPagingInIdlePO_r17 z) /\
  opt_cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710 z) /\
  True.

Definition PCCH_Config__ext1__Type := PCCH_Config__ext1O__Type.
Definition PCCH_Config__ext1__cond := PCCH_Config__ext1O__cond.

Record PCCH_Config__Type : Set :=
  make__PCCH_Config__Type {
    PCCH_Config__defaultPagingCycle : PagingCycle__Type ;
    PCCH_Config__nAndPagingFrameOffset : PCCH_Config__nAndPagingFrameOffset__Type ;
    PCCH_Config__ns : PCCH_Config__ns__Type ;
    PCCH_Config__firstPDCCH_MonitoringOccasionOfPO : option PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type ;
    PCCH_Config__ext0 : option PCCH_Config__ext0__Type ;
    PCCH_Config__ext1 : option PCCH_Config__ext1__Type ;
}.
Definition PCCH_Config__root_list : list seq_elem := (
 Nor PagingCycle__Type PagingCycle__cond ::
 Nor PCCH_Config__nAndPagingFrameOffset__Type PCCH_Config__nAndPagingFrameOffset__cond ::
 Nor PCCH_Config__ns__Type PCCH_Config__ns__cond ::
 Opt PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__cond ::
 nil).
Definition PCCH_Config__ext_list : list typ := (
  typ_cons PCCH_Config__ext0__Type PCCH_Config__ext0__cond ::
  typ_cons PCCH_Config__ext1__Type PCCH_Config__ext1__cond ::
  nil).
Definition PCCH_Config__cond (z : PCCH_Config__Type) := 
(  PagingCycle__cond (PCCH_Config__defaultPagingCycle z) /\
  PCCH_Config__nAndPagingFrameOffset__cond (PCCH_Config__nAndPagingFrameOffset z) /\
  PCCH_Config__ns__cond (PCCH_Config__ns z) /\
  opt_cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__cond (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO z) /\
  True) /\ 
(  opt_cond PCCH_Config__ext0__cond (PCCH_Config__ext0 z) /\
  opt_cond PCCH_Config__ext1__cond (PCCH_Config__ext1 z) /\
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
Definition PCCH_Config__nAndPagingFrameOffset__halfT__Format : T_Format Z PCCH_Config__nAndPagingFrameOffset__halfT__cond :=
 ranged_int_format (0) (1) PCCH_Config__nAndPagingFrameOffset__halfT__helper1 PCCH_Config__nAndPagingFrameOffset__halfT__helper2.

Opaque PCCH_Config__nAndPagingFrameOffset__halfT__cond PCCH_Config__nAndPagingFrameOffset__halfT__Format.

Definition PCCH_Config__nAndPagingFrameOffset__quarterT__Format : T_Format Z PCCH_Config__nAndPagingFrameOffset__quarterT__cond :=
 ranged_int_format (0) (3) PCCH_Config__nAndPagingFrameOffset__quarterT__helper1 PCCH_Config__nAndPagingFrameOffset__quarterT__helper2.

Opaque PCCH_Config__nAndPagingFrameOffset__quarterT__cond PCCH_Config__nAndPagingFrameOffset__quarterT__Format.

Definition PCCH_Config__nAndPagingFrameOffset__oneEighthT__Format : T_Format Z PCCH_Config__nAndPagingFrameOffset__oneEighthT__cond :=
 ranged_int_format (0) (7) PCCH_Config__nAndPagingFrameOffset__oneEighthT__helper1 PCCH_Config__nAndPagingFrameOffset__oneEighthT__helper2.

Opaque PCCH_Config__nAndPagingFrameOffset__oneEighthT__cond PCCH_Config__nAndPagingFrameOffset__oneEighthT__Format.

Definition PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__Format : T_Format Z PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__cond :=
 ranged_int_format (0) (15) PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__helper1 PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__helper2.

Opaque PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__cond PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__Format.


Definition PCCH_Config__nAndPagingFrameOffset__Format_Type := Eval cbn in get_formats PCCH_Config__nAndPagingFrameOffset__list.
Definition PCCH_Config__nAndPagingFrameOffset__Format_list : PCCH_Config__nAndPagingFrameOffset__Format_Type :=
  (unit__Format, (PCCH_Config__nAndPagingFrameOffset__halfT__Format, (PCCH_Config__nAndPagingFrameOffset__quarterT__Format, (PCCH_Config__nAndPagingFrameOffset__oneEighthT__Format, (PCCH_Config__nAndPagingFrameOffset__oneSixteenthT__Format, unit__Format))))).
Definition PCCH_Config__nAndPagingFrameOffset__list__Format := Eval compute in choice_format PCCH_Config__nAndPagingFrameOffset__list PCCH_Config__nAndPagingFrameOffset__len_helper1 PCCH_Config__nAndPagingFrameOffset__len_helper2  PCCH_Config__nAndPagingFrameOffset__Format_list.
Definition PCCH_Config__nAndPagingFrameOffset__F1 (z : PCCH_Config__nAndPagingFrameOffset__Type) : (choice PCCH_Config__nAndPagingFrameOffset__list) :=
  match z with
   | PCCH_Config__nAndPagingFrameOffset__oneT t => existT _ 0 t
  | PCCH_Config__nAndPagingFrameOffset__halfT t => existT _ 1 t
  | PCCH_Config__nAndPagingFrameOffset__quarterT t => existT _ 2 t
  | PCCH_Config__nAndPagingFrameOffset__oneEighthT t => existT _ 3 t
  | PCCH_Config__nAndPagingFrameOffset__oneSixteenthT t => existT _ 4 t
  end.
Definition PCCH_Config__nAndPagingFrameOffset__g := (fun n => typ_set (get_nth_typ PCCH_Config__nAndPagingFrameOffset__list n)).
Definition PCCH_Config__nAndPagingFrameOffset__F2 (y : choice PCCH_Config__nAndPagingFrameOffset__list) : PCCH_Config__nAndPagingFrameOffset__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PCCH_Config__nAndPagingFrameOffset__g n -> PCCH_Config__nAndPagingFrameOffset__Type) with
    | 0 => fun (t : unit) => PCCH_Config__nAndPagingFrameOffset__oneT t 
    | 1 => fun (t : Z) => PCCH_Config__nAndPagingFrameOffset__halfT t 
    | 2 => fun (t : Z) => PCCH_Config__nAndPagingFrameOffset__quarterT t 
    | 3 => fun (t : Z) => PCCH_Config__nAndPagingFrameOffset__oneEighthT t 
    | 4 => fun (t : Z) => PCCH_Config__nAndPagingFrameOffset__oneSixteenthT t 
 | (S (S (S (S (S n0))))) => (fun (x' : nat) (t'' : PCCH_Config__nAndPagingFrameOffset__g (S (S (S (S (S x')))))) =>let t' :=
           eq_rect (get_nth_typ PCCH_Config__nAndPagingFrameOffset__list (S (S (S (S (S x'))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PCCH_Config__nAndPagingFrameOffset__list (S (S (S (S (S x')))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))) in match t' return PCCH_Config__nAndPagingFrameOffset__Type with end) n0
           end t0).

Lemma PCCH_Config__nAndPagingFrameOffset__helper2 :  forall (y : PCCH_Config__nAndPagingFrameOffset__Type), PCCH_Config__nAndPagingFrameOffset__cond y -> choice_cond PCCH_Config__nAndPagingFrameOffset__list (PCCH_Config__nAndPagingFrameOffset__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PCCH_Config__nAndPagingFrameOffset__helper3 :  forall (y : PCCH_Config__nAndPagingFrameOffset__Type), PCCH_Config__nAndPagingFrameOffset__F2 (PCCH_Config__nAndPagingFrameOffset__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PCCH_Config__nAndPagingFrameOffset__helper4 : (forall b : choice PCCH_Config__nAndPagingFrameOffset__list, choice_cond PCCH_Config__nAndPagingFrameOffset__list b -> PCCH_Config__nAndPagingFrameOffset__cond (PCCH_Config__nAndPagingFrameOffset__F2 b) /\ PCCH_Config__nAndPagingFrameOffset__F1 (PCCH_Config__nAndPagingFrameOffset__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PCCH_Config__nAndPagingFrameOffset__F1 PCCH_Config__nAndPagingFrameOffset__F2.
Definition PCCH_Config__nAndPagingFrameOffset__Format : T_Format PCCH_Config__nAndPagingFrameOffset__Type PCCH_Config__nAndPagingFrameOffset__cond :=
  (* Eval compute in *) proj2_format PCCH_Config__nAndPagingFrameOffset__cond PCCH_Config__nAndPagingFrameOffset__list__Format PCCH_Config__nAndPagingFrameOffset__F1 PCCH_Config__nAndPagingFrameOffset__F2 PCCH_Config__nAndPagingFrameOffset__helper2 PCCH_Config__nAndPagingFrameOffset__helper3 PCCH_Config__nAndPagingFrameOffset__helper4.
Opaque PCCH_Config__nAndPagingFrameOffset__cond PCCH_Config__nAndPagingFrameOffset__Format.

Definition PCCH_Config__ns__Format : T_Format PCCH_Config__ns__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PCCH_Config__ns__nat__Format PCCH_Config__ns__F1 PCCH_Config__ns__F2 PCCH_Config__ns__F1F2 PCCH_Config__ns__F2F1.

Opaque PCCH_Config__ns__cond PCCH_Config__ns__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__Format : T_Format Z PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__cond :=
 ranged_int_format (0) (139) PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond := seq_of_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__Format 1 maxPO_perPF PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format : T_Format Z PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond :=
 ranged_int_format (0) (279) PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond := seq_of_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format 1 maxPO_perPF PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format : T_Format Z PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond :=
 ranged_int_format (0) (559) PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond := seq_of_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format 1 maxPO_perPF PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format : T_Format Z PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond :=
 ranged_int_format (0) (1119) PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond := seq_of_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format 1 maxPO_perPF PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format : T_Format Z PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (2239) PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond := seq_of_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format : T_Format Z PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (4479) PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond := seq_of_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format : T_Format Z PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (8959) PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond := seq_of_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__Format : T_Format Z PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (17919) PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__Format.

Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond := seq_of_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper2.

Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Format.


Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Format_Type := Eval cbn in get_formats PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Format_list : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Format_Type :=
  (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Format, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Format, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Format, unit__Format)))))))).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list__Format := Eval compute in choice_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__len_helper1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__len_helper2  PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Format_list.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F1 (z : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type) : (choice PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list) :=
  match z with
   | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT t => existT _ 0 t
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT t => existT _ 1 t
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t => existT _ 2 t
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t => existT _ 3 t
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t => existT _ 4 t
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t => existT _ 5 t
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT t => existT _ 6 t
  | PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT t => existT _ 7 t
  end.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__g := (fun n => typ_set (get_nth_typ PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list n)).
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F2 (y : choice PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list) : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__g n -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type) with
    | 0 => fun (t : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type) => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT t 
    | 1 => fun (t : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type) => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT t 
    | 2 => fun (t : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type) => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t 
    | 3 => fun (t : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type) => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t 
    | 4 => fun (t : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type) => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t 
    | 5 => fun (t : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type) => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t 
    | 6 => fun (t : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type) => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT t 
    | 7 => fun (t : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type) => PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__sCS480KHZquarterT_SCS120KHZoneSixteenthT t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type with end) n0
           end t0).

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__helper2 :  forall (y : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type), PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__cond y -> choice_cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__helper3 :  forall (y : PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type), PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F2 (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__helper4 : (forall b : choice PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list, choice_cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list b -> PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__cond (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F2 b) /\ PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F1 (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F2.
Definition PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Format : T_Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Type PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__cond :=
  (* Eval compute in *) proj2_format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__list__Format PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F1 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__F2 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__helper2 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__helper3 PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__helper4.
Opaque PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__cond PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Format.

Definition PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__Format : T_Format Z PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__cond :=
 ranged_int_format (2) (4) PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__helper1 PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__helper2.

Opaque PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__cond PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__Format.


Definition PCCH_Config__ext0O__Format_Type := Eval cbn in seq_format_prod PCCH_Config__ext0O__list.
Definition PCCH_Config__ext0O__Format_list : PCCH_Config__ext0O__Format_Type :=
  (PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16__Format, unit_format).
Definition PCCH_Config__ext0O__list__Format := (*Eval compute in *) seq_format PCCH_Config__ext0O__list PCCH_Config__ext0O__Format_list.
Definition PCCH_Config__ext0O__F1 z :=
  (PCCH_Config__ext0O__nrofPDCCH_MonitoringOccasionPerSSB_InPO_r16 z, tt).
Definition PCCH_Config__ext0O__F2 (y : seq_type PCCH_Config__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PCCH_Config__ext0O__Type i0
  end.
Lemma PCCH_Config__ext0O__F1F2_cond (z : PCCH_Config__ext0O__Type)
  : PCCH_Config__ext0O__cond z ->
  (seq_cond PCCH_Config__ext0O__list (PCCH_Config__ext0O__F1 z)).
intro H. unfold PCCH_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma PCCH_Config__ext0O__F1F2_cond2 (z : PCCH_Config__ext0O__Type)
 : PCCH_Config__ext0O__F2 (PCCH_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PCCH_Config__ext0O__F2F1_cond (y : seq_type PCCH_Config__ext0O__list)
  : seq_cond PCCH_Config__ext0O__list y ->
 (PCCH_Config__ext0O__cond (PCCH_Config__ext0O__F2 y)) /\  PCCH_Config__ext0O__F1 (PCCH_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PCCH_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold PCCH_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PCCH_Config__ext0O__Format : T_Format PCCH_Config__ext0O__Type PCCH_Config__ext0O__cond :=
        proj2_format  PCCH_Config__ext0O__cond PCCH_Config__ext0O__list__Format
    PCCH_Config__ext0O__F1 PCCH_Config__ext0O__F2 PCCH_Config__ext0O__F1F2_cond  PCCH_Config__ext0O__F1F2_cond2 PCCH_Config__ext0O__F2F1_cond.
Opaque PCCH_Config__ext0O__cond PCCH_Config__ext0O__Format.

Definition PCCH_Config__ext0__check_all_none (b : PCCH_Config__ext0O__Type) : bool :=
match b with 
  | make__PCCH_Config__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PCCH_Config__ext0__Format : T_Format PCCH_Config__ext0__Type PCCH_Config__ext0__cond :=
  restrict_add_format PCCH_Config__ext0__check_all_none PCCH_Config__ext0O__Format.

Opaque PCCH_Config__ext0__cond PCCH_Config__ext0__Format.

Definition PCCH_Config__ext1O__ranPagingInIdlePO_r17__Format : T_Format PCCH_Config__ext1O__ranPagingInIdlePO_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PCCH_Config__ext1O__ranPagingInIdlePO_r17__nat__Format PCCH_Config__ext1O__ranPagingInIdlePO_r17__F1 PCCH_Config__ext1O__ranPagingInIdlePO_r17__F2 PCCH_Config__ext1O__ranPagingInIdlePO_r17__F1F2 PCCH_Config__ext1O__ranPagingInIdlePO_r17__F2F1.

Opaque PCCH_Config__ext1O__ranPagingInIdlePO_r17__cond PCCH_Config__ext1O__ranPagingInIdlePO_r17__Format.

Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__Format : T_Format Z PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__cond :=
 ranged_int_format (0) (35839) PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper1 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper2.

Opaque PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__Format.

Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Format : T_Format PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond := seq_of_format PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__Format 1 maxPO_perPF PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper1 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper2.

Opaque PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Format.

Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__Format : T_Format Z PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (71679) PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper1 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper2.

Opaque PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__Format.

Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Format : T_Format PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond := seq_of_format PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper1 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper2.

Opaque PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Format.


Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format_Type := Eval cbn in get_formats PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format_list : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format_Type :=
  (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Format, (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Format, unit__Format)).
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list__Format := Eval compute in choice_format PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__len_helper1 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__len_helper2  PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format_list.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 (z : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type) : (choice PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list) :=
  match z with
   | PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT t => existT _ 0 t
  | PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT t => existT _ 1 t
  end.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__g := (fun n => typ_set (get_nth_typ PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list n)).
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 (y : choice PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list) : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__g n -> PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type) with
    | 0 => fun (t : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type) => PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT t 
    | 1 => fun (t : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type) => PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type with end) n0
           end t0).

Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper2 :  forall (y : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type), PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond y -> choice_cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper3 :  forall (y : PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type), PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper4 : (forall b : choice PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list, choice_cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list b -> PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 b) /\ PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2.
Definition PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format : T_Format PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond :=
  (* Eval compute in *) proj2_format PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__list__Format PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper2 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper3 PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper4.
Opaque PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format.


Definition PCCH_Config__ext1O__Format_Type := Eval cbn in seq_format_prod PCCH_Config__ext1O__list.
Definition PCCH_Config__ext1O__Format_list : PCCH_Config__ext1O__Format_Type :=
  (PCCH_Config__ext1O__ranPagingInIdlePO_r17__Format, (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format, unit_format)).
Definition PCCH_Config__ext1O__list__Format := (*Eval compute in *) seq_format PCCH_Config__ext1O__list PCCH_Config__ext1O__Format_list.
Definition PCCH_Config__ext1O__F1 z :=
  (PCCH_Config__ext1O__ranPagingInIdlePO_r17 z, (PCCH_Config__ext1O__firstPDCCH_MonitoringOccasionOfPO_v1710 z, tt)).
Definition PCCH_Config__ext1O__F2 (y : seq_type PCCH_Config__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PCCH_Config__ext1O__Type i0 i1
  end.
Lemma PCCH_Config__ext1O__F1F2_cond (z : PCCH_Config__ext1O__Type)
  : PCCH_Config__ext1O__cond z ->
  (seq_cond PCCH_Config__ext1O__list (PCCH_Config__ext1O__F1 z)).
intro H. unfold PCCH_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma PCCH_Config__ext1O__F1F2_cond2 (z : PCCH_Config__ext1O__Type)
 : PCCH_Config__ext1O__F2 (PCCH_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PCCH_Config__ext1O__F2F1_cond (y : seq_type PCCH_Config__ext1O__list)
  : seq_cond PCCH_Config__ext1O__list y ->
 (PCCH_Config__ext1O__cond (PCCH_Config__ext1O__F2 y)) /\  PCCH_Config__ext1O__F1 (PCCH_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PCCH_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold PCCH_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PCCH_Config__ext1O__Format : T_Format PCCH_Config__ext1O__Type PCCH_Config__ext1O__cond :=
        proj2_format  PCCH_Config__ext1O__cond PCCH_Config__ext1O__list__Format
    PCCH_Config__ext1O__F1 PCCH_Config__ext1O__F2 PCCH_Config__ext1O__F1F2_cond  PCCH_Config__ext1O__F1F2_cond2 PCCH_Config__ext1O__F2F1_cond.
Opaque PCCH_Config__ext1O__cond PCCH_Config__ext1O__Format.

Definition PCCH_Config__ext1__check_all_none (b : PCCH_Config__ext1O__Type) : bool :=
match b with 
  | make__PCCH_Config__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition PCCH_Config__ext1__Format : T_Format PCCH_Config__ext1__Type PCCH_Config__ext1__cond :=
  restrict_add_format PCCH_Config__ext1__check_all_none PCCH_Config__ext1O__Format.

Opaque PCCH_Config__ext1__cond PCCH_Config__ext1__Format.


Definition PCCH_Config__root_Format_Type := Eval cbn in seq_format_prod PCCH_Config__root_list.
Definition PCCH_Config__root_Format_list : PCCH_Config__root_Format_Type :=
  (PagingCycle__Format, (PCCH_Config__nAndPagingFrameOffset__Format, (PCCH_Config__ns__Format, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO__Format, unit_format)))).

Definition PCCH_Config__ext_Format_Type := Eval cbn in get_formats PCCH_Config__ext_list.
Definition PCCH_Config__ext_Format_list : PCCH_Config__ext_Format_Type :=
  (PCCH_Config__ext0__Format, (PCCH_Config__ext1__Format, unit__Format)).

Definition PCCH_Config__list_type : Set := (seq_type PCCH_Config__root_list) * (seq_ext_type PCCH_Config__ext_list).
Definition PCCH_Config__list_cond (z : PCCH_Config__list_type) : Prop :=
        (seq_cond PCCH_Config__root_list (fst z)) /\ (seq_ext_cond PCCH_Config__ext_list (snd z)).
Definition PCCH_Config__list_format : T_Format PCCH_Config__list_type PCCH_Config__list_cond :=
 (* Eval compute in *) seq_ext_format PCCH_Config__root_list PCCH_Config__root_Format_list PCCH_Config__ext_list PCCH_Config__ext_Format_list.

Opaque PCCH_Config__list_format.
Definition PCCH_Config__F1 (z : PCCH_Config__Type) : PCCH_Config__list_type :=
  (((PCCH_Config__defaultPagingCycle z, (PCCH_Config__nAndPagingFrameOffset z, (PCCH_Config__ns z, (PCCH_Config__firstPDCCH_MonitoringOccasionOfPO z, tt))))), (
(PCCH_Config__ext0 z, (PCCH_Config__ext1 z, tt)))).
Definition PCCH_Config__F2 (y : PCCH_Config__list_type) : PCCH_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__PCCH_Config__Type j0 j1 j2 j3 i0 i1
  end.
Definition PCCH_Config__helper1 : (forall a : PCCH_Config__Type, PCCH_Config__cond a -> PCCH_Config__list_cond (PCCH_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PCCH_Config__helper2 : (forall a : PCCH_Config__Type, PCCH_Config__F2 (PCCH_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PCCH_Config__helper3 : (forall b : PCCH_Config__list_type, PCCH_Config__list_cond b -> PCCH_Config__cond (PCCH_Config__F2 b) /\ PCCH_Config__F1 (PCCH_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PCCH_Config__cond, PCCH_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PCCH_Config__Format : T_Format PCCH_Config__Type PCCH_Config__cond :=
 proj2_format PCCH_Config__cond PCCH_Config__list_format  PCCH_Config__F1 PCCH_Config__F2 PCCH_Config__helper1 PCCH_Config__helper2 PCCH_Config__helper3.

Opaque PCCH_Config__cond PCCH_Config__Format.

