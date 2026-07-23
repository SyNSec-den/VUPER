Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ControlResourceSetZero.

Opaque ControlResourceSetZero__cond ControlResourceSetZero__Format.

Require Import NR.ControlResourceSet.

Opaque ControlResourceSet__cond ControlResourceSet__Format.

Require Import NR.SearchSpaceZero.

Opaque SearchSpaceZero__cond SearchSpaceZero__Format.

Require Import NR.SearchSpace.

Opaque SearchSpace__cond SearchSpace__Format.

Definition PDCCH_ConfigCommon__commonSearchSpaceList__Type := list SearchSpace__Type.

Lemma PDCCH_ConfigCommon__commonSearchSpaceList__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__commonSearchSpaceList__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__commonSearchSpaceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__commonSearchSpaceList__cond (z : PDCCH_ConfigCommon__commonSearchSpaceList__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and SearchSpace__cond z) .

Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper1 : (0 <= 139)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper2 : to_bit_sz (Z.to_nat (139 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (139 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__cond := (fun z => (0 <= z <= 139)%Z).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1 : (0 <= 279)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper2 : to_bit_sz (Z.to_nat (279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond := (fun z => (0 <= z <= 279)%Z).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1 : (0 <= 559)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper2 : to_bit_sz (Z.to_nat (559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond := (fun z => (0 <= z <= 559)%Z).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1 : (0 <= 1119)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper2 : to_bit_sz (Z.to_nat (1119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond := (fun z => (0 <= z <= 1119)%Z).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1 : (0 <= 2239)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (2239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 2239)%Z).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1 : (0 <= 4479)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (4479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 4479)%Z).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1 : (0 <= 8959)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (8959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 8959)%Z).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__helper1 : (0 <= 17919)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (17919 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (17919 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 17919)%Z).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__cond z) .


Inductive PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type : Set :=
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type
.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list : list typ := (
typ_cons PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond ::
typ_cons PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond ::
typ_cons PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond ::
typ_cons PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond ::
typ_cons PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond ::
typ_cons PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond ::
typ_cons PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond ::
typ_cons PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__cond (c : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type) := 
  match c with
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT t => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond t 
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT t => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond t 
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond t 
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond t 
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond t 
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond t 
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT t => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond t 
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT t => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__cond t 
  end.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__len_helper1 : to_bit_sz (length PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__len_helper2 : 2 <= length2 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list.
 simpl. lia. Qed.
Record PDCCH_ConfigCommon__ext0O__Type : Set :=
  make__PDCCH_ConfigCommon__ext0O__Type {
    PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO : option PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type ;
}.
Definition PDCCH_ConfigCommon__ext0O__list := (
 Opt PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext0O__cond z := 
  opt_cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__cond (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO z) /\
  True.

Definition PDCCH_ConfigCommon__ext0__Type := PDCCH_ConfigCommon__ext0O__Type.
Definition PDCCH_ConfigCommon__ext0__cond := PDCCH_ConfigCommon__ext0O__cond.

Require Import NR.SearchSpaceExt_r16.

Opaque SearchSpaceExt_r16__cond SearchSpaceExt_r16__Format.

Definition PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__Type := list SearchSpaceExt_r16__Type.

Lemma PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__cond (z : PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and SearchSpaceExt_r16__cond z) .

Record PDCCH_ConfigCommon__ext1O__Type : Set :=
  make__PDCCH_ConfigCommon__ext1O__Type {
    PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16 : option PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__Type ;
}.
Definition PDCCH_ConfigCommon__ext1O__list := (
 Opt PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__Type PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext1O__cond z := 
  opt_cond PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__cond (PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16 z) /\
  True.

Definition PDCCH_ConfigCommon__ext1__Type := PDCCH_ConfigCommon__ext1O__Type.
Definition PDCCH_ConfigCommon__ext1__cond := PDCCH_ConfigCommon__ext1O__cond.

Require Import NR.SearchSpace.

Opaque SearchSpace__cond SearchSpace__Format.

Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.


Inductive PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type : Set :=
  | PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__newSearchSpace : SearchSpace__Type -> PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type
  | PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__existingSearchSpace : SearchSpaceId__Type -> PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type
.
Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list : list typ := (
typ_cons SearchSpace__Type SearchSpace__cond ::
typ_cons SearchSpaceId__Type SearchSpaceId__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__cond (c : PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type) := 
  match c with
  | PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__newSearchSpace t => SearchSpace__cond t 
  | PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__existingSearchSpace t => SearchSpaceId__cond t 
  end.

Lemma PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__len_helper1 : to_bit_sz (length PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__len_helper2 : 2 <= length2 PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list.
 simpl. lia. Qed.
Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Require Import NR.SearchSpaceExt_v1700.

Opaque SearchSpaceExt_v1700__cond SearchSpaceExt_v1700__Format.

Definition PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__Type := list SearchSpaceExt_v1700__Type.

Lemma PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__cond (z : PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and SearchSpaceExt_v1700__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper1 : (0 <= 35839)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper2 : to_bit_sz (Z.to_nat (35839 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (35839 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__cond := (fun z => (0 <= z <= 35839)%Z).
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond (z : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper1 : (0 <= 71679)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (71679 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (71679 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 71679)%Z).
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPO_perPF)%Z. unfold maxPO_perPF.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPO_perPF - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPO_perPF - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPO_perPF)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__cond z) .


Inductive PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type : Set :=
  | PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type -> PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type
  | PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type
.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list : list typ := (
typ_cons PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond (c : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type) := 
  match c with
  | PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT t => PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond t 
  | PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT t => PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond t 
  end.

Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__len_helper1 : to_bit_sz (length PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__len_helper2 : 2 <= length2 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list.
 simpl. lia. Qed.
Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__helper1 : (0 <= 139)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__helper2 : to_bit_sz (Z.to_nat (139 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (139 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__cond := (fun z => (0 <= z <= 139)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1 : (0 <= 279)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper2 : to_bit_sz (Z.to_nat (279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond := (fun z => (0 <= z <= 279)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1 : (0 <= 559)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper2 : to_bit_sz (Z.to_nat (559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond := (fun z => (0 <= z <= 559)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1 : (0 <= 1119)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper2 : to_bit_sz (Z.to_nat (1119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond := (fun z => (0 <= z <= 1119)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1 : (0 <= 2239)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (2239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 2239)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1 : (0 <= 4479)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (4479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 4479)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1 : (0 <= 8959)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (8959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 8959)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper1 : (0 <= 17919)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (17919 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (17919 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 17919)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__helper1 : (0 <= 35839)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__helper2 : to_bit_sz (Z.to_nat (35839 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (35839 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__cond := (fun z => (0 <= z <= 35839)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__cond z) .

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__helper1 : (0 <= 71679)%Z.  lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__helper2 : to_bit_sz (Z.to_nat (71679 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (71679 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__Type := Z.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__cond := (fun z => (0 <= z <= 71679)%Z).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Type := list Z.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__helper1 : (0 <= 1 <= maxPEI_perPF_r17)%Z. unfold maxPEI_perPF_r17.
 lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__helper2 : to_bit_sz (Z.to_nat (maxPEI_perPF_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPEI_perPF_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Type) :=  (1 <= Z.of_nat (length z) <= maxPEI_perPF_r17)%Z /\ (list_and PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__cond z) .


Inductive PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type : Set :=
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Type -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type
.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list : list typ := (
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__cond ::
typ_cons PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__cond (c : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type) := 
  match c with
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__cond t 
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT t => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__cond t 
  end.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__len_helper1 : to_bit_sz (length PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__len_helper2 : 2 <= length2 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list.
 simpl. lia. Qed.
Record PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Type : Set :=
  make__PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Type {
    PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__pei_SearchSpace_r17 : SearchSpaceId__Type ;
    PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17 : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type ;
}.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list := (
 Nor SearchSpaceId__Type SearchSpaceId__cond ::
 Nor PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond z := 
  SearchSpaceId__cond (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__pei_SearchSpace_r17 z) /\
  PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__cond (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17 z) /\
  True.

Record PDCCH_ConfigCommon__ext2O__Type : Set :=
  make__PDCCH_ConfigCommon__ext2O__Type {
    PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17 : option PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type ;
    PDCCH_ConfigCommon__ext2O__searchSpaceMCCH_r17 : option SearchSpaceId__Type ;
    PDCCH_ConfigCommon__ext2O__searchSpaceMTCH_r17 : option SearchSpaceId__Type ;
    PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17 : option PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__Type ;
    PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710 : option PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type ;
    PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17 : option PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Type ;
}.
Definition PDCCH_ConfigCommon__ext2O__list := (
 Opt PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__cond ::
 Opt SearchSpaceId__Type SearchSpaceId__cond ::
 Opt SearchSpaceId__Type SearchSpaceId__cond ::
 Opt PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__Type PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__cond ::
 Opt PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond ::
 Opt PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext2O__cond z := 
  opt_cond PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__cond (PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17 z) /\
  opt_cond SearchSpaceId__cond (PDCCH_ConfigCommon__ext2O__searchSpaceMCCH_r17 z) /\
  opt_cond SearchSpaceId__cond (PDCCH_ConfigCommon__ext2O__searchSpaceMTCH_r17 z) /\
  opt_cond PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__cond (PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17 z) /\
  opt_cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710 z) /\
  opt_cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17 z) /\
  True.

Definition PDCCH_ConfigCommon__ext2__Type := PDCCH_ConfigCommon__ext2O__Type.
Definition PDCCH_ConfigCommon__ext2__cond := PDCCH_ConfigCommon__ext2O__cond.

Inductive PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Type : Set :=
 | PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__enabled
.
Definition PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__cond := (fun (_ : PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Type) => True).
Lemma PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__nat__helper.

Definition PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F1 t :=
  match t with
  | PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__enabled => 0
  end.
Definition PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F2 n :=
  match n with
  | 0 => PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__enabled
  | _ => PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__enabled
  end.
Lemma PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F1F2 : forall x : PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Type, (PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F1 x <= 0) /\ PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F2 (PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F1 x) = x. imp_solve. Qed.
Lemma PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F2F1 : forall (y : nat) (H : y <= 0), PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F1 (PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F2 y) = y. enum_solve H y. Qed.

Record PDCCH_ConfigCommon__ext3O__Type : Set :=
  make__PDCCH_ConfigCommon__ext3O__Type {
    PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720 : option PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Type ;
}.
Definition PDCCH_ConfigCommon__ext3O__list := (
 Opt PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Type PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext3O__cond z := 
  opt_cond PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__cond (PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720 z) /\
  True.

Definition PDCCH_ConfigCommon__ext3__Type := PDCCH_ConfigCommon__ext3O__Type.
Definition PDCCH_ConfigCommon__ext3__cond := PDCCH_ConfigCommon__ext3O__cond.

Record PDCCH_ConfigCommon__Type : Set :=
  make__PDCCH_ConfigCommon__Type {
    PDCCH_ConfigCommon__controlResourceSetZero : option ControlResourceSetZero__Type ;
    PDCCH_ConfigCommon__commonControlResourceSet : option ControlResourceSet__Type ;
    PDCCH_ConfigCommon__searchSpaceZero : option SearchSpaceZero__Type ;
    PDCCH_ConfigCommon__commonSearchSpaceList : option PDCCH_ConfigCommon__commonSearchSpaceList__Type ;
    PDCCH_ConfigCommon__searchSpaceSIB1 : option SearchSpaceId__Type ;
    PDCCH_ConfigCommon__searchSpaceOtherSystemInformation : option SearchSpaceId__Type ;
    PDCCH_ConfigCommon__pagingSearchSpace : option SearchSpaceId__Type ;
    PDCCH_ConfigCommon__ra_SearchSpace : option SearchSpaceId__Type ;
    PDCCH_ConfigCommon__ext0 : option PDCCH_ConfigCommon__ext0__Type ;
    PDCCH_ConfigCommon__ext1 : option PDCCH_ConfigCommon__ext1__Type ;
    PDCCH_ConfigCommon__ext2 : option PDCCH_ConfigCommon__ext2__Type ;
    PDCCH_ConfigCommon__ext3 : option PDCCH_ConfigCommon__ext3__Type ;
}.
Definition PDCCH_ConfigCommon__root_list : list seq_elem := (
 Opt ControlResourceSetZero__Type ControlResourceSetZero__cond ::
 Opt ControlResourceSet__Type ControlResourceSet__cond ::
 Opt SearchSpaceZero__Type SearchSpaceZero__cond ::
 Opt PDCCH_ConfigCommon__commonSearchSpaceList__Type PDCCH_ConfigCommon__commonSearchSpaceList__cond ::
 Opt SearchSpaceId__Type SearchSpaceId__cond ::
 Opt SearchSpaceId__Type SearchSpaceId__cond ::
 Opt SearchSpaceId__Type SearchSpaceId__cond ::
 Opt SearchSpaceId__Type SearchSpaceId__cond ::
 nil).
Definition PDCCH_ConfigCommon__ext_list : list typ := (
  typ_cons PDCCH_ConfigCommon__ext0__Type PDCCH_ConfigCommon__ext0__cond ::
  typ_cons PDCCH_ConfigCommon__ext1__Type PDCCH_ConfigCommon__ext1__cond ::
  typ_cons PDCCH_ConfigCommon__ext2__Type PDCCH_ConfigCommon__ext2__cond ::
  typ_cons PDCCH_ConfigCommon__ext3__Type PDCCH_ConfigCommon__ext3__cond ::
  nil).
Definition PDCCH_ConfigCommon__cond (z : PDCCH_ConfigCommon__Type) := 
(  opt_cond ControlResourceSetZero__cond (PDCCH_ConfigCommon__controlResourceSetZero z) /\
  opt_cond ControlResourceSet__cond (PDCCH_ConfigCommon__commonControlResourceSet z) /\
  opt_cond SearchSpaceZero__cond (PDCCH_ConfigCommon__searchSpaceZero z) /\
  opt_cond PDCCH_ConfigCommon__commonSearchSpaceList__cond (PDCCH_ConfigCommon__commonSearchSpaceList z) /\
  opt_cond SearchSpaceId__cond (PDCCH_ConfigCommon__searchSpaceSIB1 z) /\
  opt_cond SearchSpaceId__cond (PDCCH_ConfigCommon__searchSpaceOtherSystemInformation z) /\
  opt_cond SearchSpaceId__cond (PDCCH_ConfigCommon__pagingSearchSpace z) /\
  opt_cond SearchSpaceId__cond (PDCCH_ConfigCommon__ra_SearchSpace z) /\
  True) /\ 
(  opt_cond PDCCH_ConfigCommon__ext0__cond (PDCCH_ConfigCommon__ext0 z) /\
  opt_cond PDCCH_ConfigCommon__ext1__cond (PDCCH_ConfigCommon__ext1 z) /\
  opt_cond PDCCH_ConfigCommon__ext2__cond (PDCCH_ConfigCommon__ext2 z) /\
  opt_cond PDCCH_ConfigCommon__ext3__cond (PDCCH_ConfigCommon__ext3 z) /\
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
Definition PDCCH_ConfigCommon__commonSearchSpaceList__Format : T_Format PDCCH_ConfigCommon__commonSearchSpaceList__Type PDCCH_ConfigCommon__commonSearchSpaceList__cond := seq_of_format SearchSpace__Format 1 4 PDCCH_ConfigCommon__commonSearchSpaceList__helper1 PDCCH_ConfigCommon__commonSearchSpaceList__helper2.

Opaque PDCCH_ConfigCommon__commonSearchSpaceList__cond PDCCH_ConfigCommon__commonSearchSpaceList__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__cond :=
 ranged_int_format (0) (139) PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond := seq_of_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond :=
 ranged_int_format (0) (279) PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond := seq_of_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond :=
 ranged_int_format (0) (559) PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond := seq_of_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond :=
 ranged_int_format (0) (1119) PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond := seq_of_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (2239) PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (4479) PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (8959) PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (17919) PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Format.


Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Format_Type := Eval cbn in get_formats PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Format_list : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Format_Type :=
  (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Format, (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Format, (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format, (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format, (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format, (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format, (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format, (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Format, unit__Format)))))))).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list__Format := Eval compute in choice_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__len_helper1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__len_helper2  PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Format_list.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F1 (z : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type) : (choice PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list) :=
  match z with
   | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT t => existT _ 0 t
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT t => existT _ 1 t
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t => existT _ 2 t
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t => existT _ 3 t
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t => existT _ 4 t
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t => existT _ 5 t
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT t => existT _ 6 t
  | PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT t => existT _ 7 t
  end.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__g := (fun n => typ_set (get_nth_typ PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list n)).
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F2 (y : choice PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list) : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__g n -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type) with
    | 0 => fun (t : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT__Type) => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS15KHZoneT t 
    | 1 => fun (t : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT__Type) => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS30KHZoneT_SCS15KHZhalfT t 
    | 2 => fun (t : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type) => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t 
    | 3 => fun (t : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type) => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t 
    | 4 => fun (t : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t 
    | 5 => fun (t : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t 
    | 6 => fun (t : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneEighthT_SCS60KHZoneSixteenthT t 
    | 7 => fun (t : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__sCS120KHZoneSixteenthT t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type with end) n0
           end t0).

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__helper2 :  forall (y : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type), PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__cond y -> choice_cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__helper3 :  forall (y : PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type), PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F2 (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__helper4 : (forall b : choice PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list, choice_cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list b -> PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__cond (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F2 b) /\ PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F1 (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F2.
Definition PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Format : T_Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Type PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__cond :=
  (* Eval compute in *) proj2_format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__list__Format PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F1 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__F2 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__helper2 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__helper3 PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__helper4.
Opaque PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__cond PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Format.


Definition PDCCH_ConfigCommon__ext0O__Format_Type := Eval cbn in seq_format_prod PDCCH_ConfigCommon__ext0O__list.
Definition PDCCH_ConfigCommon__ext0O__Format_list : PDCCH_ConfigCommon__ext0O__Format_Type :=
  (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO__Format, unit_format).
Definition PDCCH_ConfigCommon__ext0O__list__Format := (*Eval compute in *) seq_format PDCCH_ConfigCommon__ext0O__list PDCCH_ConfigCommon__ext0O__Format_list.
Definition PDCCH_ConfigCommon__ext0O__F1 z :=
  (PDCCH_ConfigCommon__ext0O__firstPDCCH_MonitoringOccasionOfPO z, tt).
Definition PDCCH_ConfigCommon__ext0O__F2 (y : seq_type PDCCH_ConfigCommon__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PDCCH_ConfigCommon__ext0O__Type i0
  end.
Lemma PDCCH_ConfigCommon__ext0O__F1F2_cond (z : PDCCH_ConfigCommon__ext0O__Type)
  : PDCCH_ConfigCommon__ext0O__cond z ->
  (seq_cond PDCCH_ConfigCommon__ext0O__list (PDCCH_ConfigCommon__ext0O__F1 z)).
intro H. unfold PDCCH_ConfigCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext0O__F1F2_cond2 (z : PDCCH_ConfigCommon__ext0O__Type)
 : PDCCH_ConfigCommon__ext0O__F2 (PDCCH_ConfigCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext0O__F2F1_cond (y : seq_type PDCCH_ConfigCommon__ext0O__list)
  : seq_cond PDCCH_ConfigCommon__ext0O__list y ->
 (PDCCH_ConfigCommon__ext0O__cond (PDCCH_ConfigCommon__ext0O__F2 y)) /\  PDCCH_ConfigCommon__ext0O__F1 (PDCCH_ConfigCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_ConfigCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold PDCCH_ConfigCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_ConfigCommon__ext0O__Format : T_Format PDCCH_ConfigCommon__ext0O__Type PDCCH_ConfigCommon__ext0O__cond :=
        proj2_format  PDCCH_ConfigCommon__ext0O__cond PDCCH_ConfigCommon__ext0O__list__Format
    PDCCH_ConfigCommon__ext0O__F1 PDCCH_ConfigCommon__ext0O__F2 PDCCH_ConfigCommon__ext0O__F1F2_cond  PDCCH_ConfigCommon__ext0O__F1F2_cond2 PDCCH_ConfigCommon__ext0O__F2F1_cond.
Opaque PDCCH_ConfigCommon__ext0O__cond PDCCH_ConfigCommon__ext0O__Format.

Definition PDCCH_ConfigCommon__ext0__check_all_none (b : PDCCH_ConfigCommon__ext0O__Type) : bool :=
match b with 
  | make__PDCCH_ConfigCommon__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PDCCH_ConfigCommon__ext0__Format : T_Format PDCCH_ConfigCommon__ext0__Type PDCCH_ConfigCommon__ext0__cond :=
  restrict_add_format PDCCH_ConfigCommon__ext0__check_all_none PDCCH_ConfigCommon__ext0O__Format.

Opaque PDCCH_ConfigCommon__ext0__cond PDCCH_ConfigCommon__ext0__Format.

Definition PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__Format : T_Format PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__Type PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__cond := seq_of_format SearchSpaceExt_r16__Format 1 4 PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__helper1 PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__helper2.

Opaque PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__cond PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__Format.


Definition PDCCH_ConfigCommon__ext1O__Format_Type := Eval cbn in seq_format_prod PDCCH_ConfigCommon__ext1O__list.
Definition PDCCH_ConfigCommon__ext1O__Format_list : PDCCH_ConfigCommon__ext1O__Format_Type :=
  (PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16__Format, unit_format).
Definition PDCCH_ConfigCommon__ext1O__list__Format := (*Eval compute in *) seq_format PDCCH_ConfigCommon__ext1O__list PDCCH_ConfigCommon__ext1O__Format_list.
Definition PDCCH_ConfigCommon__ext1O__F1 z :=
  (PDCCH_ConfigCommon__ext1O__commonSearchSpaceListExt_r16 z, tt).
Definition PDCCH_ConfigCommon__ext1O__F2 (y : seq_type PDCCH_ConfigCommon__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__PDCCH_ConfigCommon__ext1O__Type i0
  end.
Lemma PDCCH_ConfigCommon__ext1O__F1F2_cond (z : PDCCH_ConfigCommon__ext1O__Type)
  : PDCCH_ConfigCommon__ext1O__cond z ->
  (seq_cond PDCCH_ConfigCommon__ext1O__list (PDCCH_ConfigCommon__ext1O__F1 z)).
intro H. unfold PDCCH_ConfigCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext1O__F1F2_cond2 (z : PDCCH_ConfigCommon__ext1O__Type)
 : PDCCH_ConfigCommon__ext1O__F2 (PDCCH_ConfigCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext1O__F2F1_cond (y : seq_type PDCCH_ConfigCommon__ext1O__list)
  : seq_cond PDCCH_ConfigCommon__ext1O__list y ->
 (PDCCH_ConfigCommon__ext1O__cond (PDCCH_ConfigCommon__ext1O__F2 y)) /\  PDCCH_ConfigCommon__ext1O__F1 (PDCCH_ConfigCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_ConfigCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold PDCCH_ConfigCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_ConfigCommon__ext1O__Format : T_Format PDCCH_ConfigCommon__ext1O__Type PDCCH_ConfigCommon__ext1O__cond :=
        proj2_format  PDCCH_ConfigCommon__ext1O__cond PDCCH_ConfigCommon__ext1O__list__Format
    PDCCH_ConfigCommon__ext1O__F1 PDCCH_ConfigCommon__ext1O__F2 PDCCH_ConfigCommon__ext1O__F1F2_cond  PDCCH_ConfigCommon__ext1O__F1F2_cond2 PDCCH_ConfigCommon__ext1O__F2F1_cond.
Opaque PDCCH_ConfigCommon__ext1O__cond PDCCH_ConfigCommon__ext1O__Format.

Definition PDCCH_ConfigCommon__ext1__check_all_none (b : PDCCH_ConfigCommon__ext1O__Type) : bool :=
match b with 
  | make__PDCCH_ConfigCommon__ext1O__Type None  => false 
  | _ => true 
 end.
Definition PDCCH_ConfigCommon__ext1__Format : T_Format PDCCH_ConfigCommon__ext1__Type PDCCH_ConfigCommon__ext1__cond :=
  restrict_add_format PDCCH_ConfigCommon__ext1__check_all_none PDCCH_ConfigCommon__ext1O__Format.

Opaque PDCCH_ConfigCommon__ext1__cond PDCCH_ConfigCommon__ext1__Format.


Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Format_Type := Eval cbn in get_formats PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list.
Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Format_list : PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Format_Type :=
  (SearchSpace__Format, (SearchSpaceId__Format, unit__Format)).
Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list__Format := Eval compute in choice_format PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__len_helper1 PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__len_helper2  PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Format_list.
Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F1 (z : PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type) : (choice PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list) :=
  match z with
   | PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__newSearchSpace t => existT _ 0 t
  | PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__existingSearchSpace t => existT _ 1 t
  end.
Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__g := (fun n => typ_set (get_nth_typ PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list n)).
Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F2 (y : choice PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list) : PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__g n -> PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type) with
    | 0 => fun (t : SearchSpace__Type) => PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__newSearchSpace t 
    | 1 => fun (t : SearchSpaceId__Type) => PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__existingSearchSpace t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type with end) n0
           end t0).

Lemma PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__helper2 :  forall (y : PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type), PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__cond y -> choice_cond PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list (PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__helper3 :  forall (y : PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type), PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F2 (PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__helper4 : (forall b : choice PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list, choice_cond PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list b -> PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__cond (PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F2 b) /\ PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F1 (PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F1 PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F2.
Definition PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Format : T_Format PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Type PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__cond :=
  (* Eval compute in *) proj2_format PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__cond PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__list__Format PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F1 PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__F2 PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__helper2 PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__helper3 PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__helper4.
Opaque PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__cond PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Format.

Definition PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__Format : T_Format PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__Type PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__cond := seq_of_format SearchSpaceExt_v1700__Format 1 4 PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__helper1 PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__helper2.

Opaque PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__cond PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__Format.

Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__cond :=
 ranged_int_format (0) (35839) PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Format : T_Format PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper1 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Format.

Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (71679) PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__seq_of__Format 1 maxPO_perPF PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Format.


Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format_Type := Eval cbn in get_formats PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format_list : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format_Type :=
  (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Format, (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Format, unit__Format)).
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list__Format := Eval compute in choice_format PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__len_helper1 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__len_helper2  PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format_list.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 (z : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type) : (choice PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list) :=
  match z with
   | PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT t => existT _ 0 t
  | PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT t => existT _ 1 t
  end.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__g := (fun n => typ_set (get_nth_typ PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list n)).
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 (y : choice PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list) : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__g n -> PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type) with
    | 0 => fun (t : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT__Type) => PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneEighthT t 
    | 1 => fun (t : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__sCS480KHZoneSixteenthT t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type with end) n0
           end t0).

Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper2 :  forall (y : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type), PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond y -> choice_cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper3 :  forall (y : PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type), PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper4 : (forall b : choice PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list, choice_cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list b -> PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 b) /\ PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2.
Definition PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format : T_Format PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Type PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond :=
  (* Eval compute in *) proj2_format PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__list__Format PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F1 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__F2 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper2 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper3 PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__helper4.
Opaque PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__cond PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__cond :=
 ranged_int_format (0) (139) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond :=
 ranged_int_format (0) (279) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond :=
 ranged_int_format (0) (559) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond :=
 ranged_int_format (0) (1119) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (2239) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (4479) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (8959) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (17919) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__cond :=
 ranged_int_format (0) (35839) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__Format : T_Format Z PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__cond :=
 ranged_int_format (0) (71679) PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__Format.

Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__cond := seq_of_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__seq_of__Format 1 maxPEI_perPF_r17 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__helper2.

Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Format.


Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Format_Type := Eval cbn in get_formats PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Format_list : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Format_Type :=
  (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Format, unit__Format)))))))))).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list__Format := Eval compute in choice_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__len_helper1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__len_helper2  PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Format_list.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F1 (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type) : (choice PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list) :=
  match z with
   | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT t => existT _ 0 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT t => existT _ 1 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t => existT _ 2 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t => existT _ 3 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t => existT _ 4 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t => existT _ 5 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT t => existT _ 6 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT t => existT _ 7 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT t => existT _ 8 t
  | PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT t => existT _ 9 t
  end.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__g := (fun n => typ_set (get_nth_typ PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list n)).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F2 (y : choice PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list) : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__g n -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type) with
    | 0 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS15KHZoneT t 
    | 1 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS30KHZoneT_SCS15KHZhalfT t 
    | 2 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS60KHZoneT_SCS30KHZhalfT_SCS15KHZquarterT t 
    | 3 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZoneT_SCS60KHZhalfT_SCS30KHZquarterT_SCS15KHZoneEighthT t 
    | 4 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS120KHZhalfT_SCS60KHZquarterT_SCS30KHZoneEighthT_SCS15KHZoneSixteenthT t 
    | 5 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneT_SCS120KHZquarterT_SCS60KHZoneEighthT_SCS30KHZoneSixteenthT t 
    | 6 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZhalfT_SCS120KHZoneEighthT_SCS60KHZoneSixteenthT t 
    | 7 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZquarterT_SCS120KHZoneSixteenthT t 
    | 8 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneEighthT t 
    | 9 => fun (t : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT__Type) => PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__sCS480KHZoneSixteenthT t 
 | (S (S (S (S (S (S (S (S (S (S n0)))))))))) => (fun (x' : nat) (t'' : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__g (S (S (S (S (S (S (S (S (S (S x'))))))))))) =>let t' :=
           eq_rect (get_nth_typ PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list (S (S (S (S (S (S (S (S (S (S x')))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list (S (S (S (S (S (S (S (S (S (S x'))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))) in match t' return PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type with end) n0
           end t0).

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__helper2 :  forall (y : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type), PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__cond y -> choice_cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__helper3 :  forall (y : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type), PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F2 (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__helper4 : (forall b : choice PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list, choice_cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list b -> PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__cond (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F2 b) /\ PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F1 (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F2.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__cond :=
  (* Eval compute in *) proj2_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__list__Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__F2 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__helper2 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__helper3 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__helper4.
Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Format.


Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Format_Type := Eval cbn in seq_format_prod PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Format_list : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Format_Type :=
  (SearchSpaceId__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17__Format, unit_format)).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list__Format := (*Eval compute in *) seq_format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Format_list.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1 z :=
  (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__pei_SearchSpace_r17 z, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__firstPDCCH_MonitoringOccasionOfPEI_O_r17 z, tt)).
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F2 (y : seq_type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Type i0 i1
  end.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1F2_cond (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Type)
  : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond z ->
  (seq_cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1 z)).
intro H. unfold PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond in H. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1F2_cond2 (z : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Type)
 : PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F2 (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F2F1_cond (y : seq_type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list)
  : seq_cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list y ->
 (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F2 y)) /\  PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1 (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond. simpl in *. auto.
 - simpl. unfold PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Format : T_Format PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Type PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond :=
        proj2_format  PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__list__Format
    PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F2 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1F2_cond  PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F1F2_cond2 PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__F2F1_cond.
Opaque PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__cond PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Format.


Definition PDCCH_ConfigCommon__ext2O__Format_Type := Eval cbn in seq_format_prod PDCCH_ConfigCommon__ext2O__list.
Definition PDCCH_ConfigCommon__ext2O__Format_list : PDCCH_ConfigCommon__ext2O__Format_Type :=
  (PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17__Format, (SearchSpaceId__Format, (SearchSpaceId__Format, (PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17__Format, (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710__Format, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17__Format, unit_format)))))).
Definition PDCCH_ConfigCommon__ext2O__list__Format := (*Eval compute in *) seq_format PDCCH_ConfigCommon__ext2O__list PDCCH_ConfigCommon__ext2O__Format_list.
Definition PDCCH_ConfigCommon__ext2O__F1 z :=
  (PDCCH_ConfigCommon__ext2O__sdt_SearchSpace_r17 z, (PDCCH_ConfigCommon__ext2O__searchSpaceMCCH_r17 z, (PDCCH_ConfigCommon__ext2O__searchSpaceMTCH_r17 z, (PDCCH_ConfigCommon__ext2O__commonSearchSpaceListExt2_r17 z, (PDCCH_ConfigCommon__ext2O__firstPDCCH_MonitoringOccasionOfPO_v1710 z, (PDCCH_ConfigCommon__ext2O__pei_ConfigBWP_r17 z, tt)))))).
Definition PDCCH_ConfigCommon__ext2O__F2 (y : seq_type PDCCH_ConfigCommon__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__PDCCH_ConfigCommon__ext2O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma PDCCH_ConfigCommon__ext2O__F1F2_cond (z : PDCCH_ConfigCommon__ext2O__Type)
  : PDCCH_ConfigCommon__ext2O__cond z ->
  (seq_cond PDCCH_ConfigCommon__ext2O__list (PDCCH_ConfigCommon__ext2O__F1 z)).
intro H. unfold PDCCH_ConfigCommon__ext2O__cond in H. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext2O__F1F2_cond2 (z : PDCCH_ConfigCommon__ext2O__Type)
 : PDCCH_ConfigCommon__ext2O__F2 (PDCCH_ConfigCommon__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext2O__F2F1_cond (y : seq_type PDCCH_ConfigCommon__ext2O__list)
  : seq_cond PDCCH_ConfigCommon__ext2O__list y ->
 (PDCCH_ConfigCommon__ext2O__cond (PDCCH_ConfigCommon__ext2O__F2 y)) /\  PDCCH_ConfigCommon__ext2O__F1 (PDCCH_ConfigCommon__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_ConfigCommon__ext2O__cond. simpl in *. auto.
 - simpl. unfold PDCCH_ConfigCommon__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_ConfigCommon__ext2O__Format : T_Format PDCCH_ConfigCommon__ext2O__Type PDCCH_ConfigCommon__ext2O__cond :=
        proj2_format  PDCCH_ConfigCommon__ext2O__cond PDCCH_ConfigCommon__ext2O__list__Format
    PDCCH_ConfigCommon__ext2O__F1 PDCCH_ConfigCommon__ext2O__F2 PDCCH_ConfigCommon__ext2O__F1F2_cond  PDCCH_ConfigCommon__ext2O__F1F2_cond2 PDCCH_ConfigCommon__ext2O__F2F1_cond.
Opaque PDCCH_ConfigCommon__ext2O__cond PDCCH_ConfigCommon__ext2O__Format.

Definition PDCCH_ConfigCommon__ext2__check_all_none (b : PDCCH_ConfigCommon__ext2O__Type) : bool :=
match b with 
  | make__PDCCH_ConfigCommon__ext2O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition PDCCH_ConfigCommon__ext2__Format : T_Format PDCCH_ConfigCommon__ext2__Type PDCCH_ConfigCommon__ext2__cond :=
  restrict_add_format PDCCH_ConfigCommon__ext2__check_all_none PDCCH_ConfigCommon__ext2O__Format.

Opaque PDCCH_ConfigCommon__ext2__cond PDCCH_ConfigCommon__ext2__Format.

Definition PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Format : T_Format PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__nat__Format PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F1 PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F2 PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F1F2 PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__F2F1.

Opaque PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__cond PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Format.


Definition PDCCH_ConfigCommon__ext3O__Format_Type := Eval cbn in seq_format_prod PDCCH_ConfigCommon__ext3O__list.
Definition PDCCH_ConfigCommon__ext3O__Format_list : PDCCH_ConfigCommon__ext3O__Format_Type :=
  (PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720__Format, unit_format).
Definition PDCCH_ConfigCommon__ext3O__list__Format := (*Eval compute in *) seq_format PDCCH_ConfigCommon__ext3O__list PDCCH_ConfigCommon__ext3O__Format_list.
Definition PDCCH_ConfigCommon__ext3O__F1 z :=
  (PDCCH_ConfigCommon__ext3O__followUnifiedTCI_State_v1720 z, tt).
Definition PDCCH_ConfigCommon__ext3O__F2 (y : seq_type PDCCH_ConfigCommon__ext3O__list) :=
  match y with
  | (i0, _)=>
    make__PDCCH_ConfigCommon__ext3O__Type i0
  end.
Lemma PDCCH_ConfigCommon__ext3O__F1F2_cond (z : PDCCH_ConfigCommon__ext3O__Type)
  : PDCCH_ConfigCommon__ext3O__cond z ->
  (seq_cond PDCCH_ConfigCommon__ext3O__list (PDCCH_ConfigCommon__ext3O__F1 z)).
intro H. unfold PDCCH_ConfigCommon__ext3O__cond in H. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext3O__F1F2_cond2 (z : PDCCH_ConfigCommon__ext3O__Type)
 : PDCCH_ConfigCommon__ext3O__F2 (PDCCH_ConfigCommon__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDCCH_ConfigCommon__ext3O__F2F1_cond (y : seq_type PDCCH_ConfigCommon__ext3O__list)
  : seq_cond PDCCH_ConfigCommon__ext3O__list y ->
 (PDCCH_ConfigCommon__ext3O__cond (PDCCH_ConfigCommon__ext3O__F2 y)) /\  PDCCH_ConfigCommon__ext3O__F1 (PDCCH_ConfigCommon__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDCCH_ConfigCommon__ext3O__cond. simpl in *. auto.
 - simpl. unfold PDCCH_ConfigCommon__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDCCH_ConfigCommon__ext3O__Format : T_Format PDCCH_ConfigCommon__ext3O__Type PDCCH_ConfigCommon__ext3O__cond :=
        proj2_format  PDCCH_ConfigCommon__ext3O__cond PDCCH_ConfigCommon__ext3O__list__Format
    PDCCH_ConfigCommon__ext3O__F1 PDCCH_ConfigCommon__ext3O__F2 PDCCH_ConfigCommon__ext3O__F1F2_cond  PDCCH_ConfigCommon__ext3O__F1F2_cond2 PDCCH_ConfigCommon__ext3O__F2F1_cond.
Opaque PDCCH_ConfigCommon__ext3O__cond PDCCH_ConfigCommon__ext3O__Format.

Definition PDCCH_ConfigCommon__ext3__check_all_none (b : PDCCH_ConfigCommon__ext3O__Type) : bool :=
match b with 
  | make__PDCCH_ConfigCommon__ext3O__Type None  => false 
  | _ => true 
 end.
Definition PDCCH_ConfigCommon__ext3__Format : T_Format PDCCH_ConfigCommon__ext3__Type PDCCH_ConfigCommon__ext3__cond :=
  restrict_add_format PDCCH_ConfigCommon__ext3__check_all_none PDCCH_ConfigCommon__ext3O__Format.

Opaque PDCCH_ConfigCommon__ext3__cond PDCCH_ConfigCommon__ext3__Format.


Definition PDCCH_ConfigCommon__root_Format_Type := Eval cbn in seq_format_prod PDCCH_ConfigCommon__root_list.
Definition PDCCH_ConfigCommon__root_Format_list : PDCCH_ConfigCommon__root_Format_Type :=
  (ControlResourceSetZero__Format, (ControlResourceSet__Format, (SearchSpaceZero__Format, (PDCCH_ConfigCommon__commonSearchSpaceList__Format, (SearchSpaceId__Format, (SearchSpaceId__Format, (SearchSpaceId__Format, (SearchSpaceId__Format, unit_format)))))))).

Definition PDCCH_ConfigCommon__ext_Format_Type := Eval cbn in get_formats PDCCH_ConfigCommon__ext_list.
Definition PDCCH_ConfigCommon__ext_Format_list : PDCCH_ConfigCommon__ext_Format_Type :=
  (PDCCH_ConfigCommon__ext0__Format, (PDCCH_ConfigCommon__ext1__Format, (PDCCH_ConfigCommon__ext2__Format, (PDCCH_ConfigCommon__ext3__Format, unit__Format)))).

Definition PDCCH_ConfigCommon__list_type : Set := (seq_type PDCCH_ConfigCommon__root_list) * (seq_ext_type PDCCH_ConfigCommon__ext_list).
Definition PDCCH_ConfigCommon__list_cond (z : PDCCH_ConfigCommon__list_type) : Prop :=
        (seq_cond PDCCH_ConfigCommon__root_list (fst z)) /\ (seq_ext_cond PDCCH_ConfigCommon__ext_list (snd z)).
Definition PDCCH_ConfigCommon__list_format : T_Format PDCCH_ConfigCommon__list_type PDCCH_ConfigCommon__list_cond :=
 (* Eval compute in *) seq_ext_format PDCCH_ConfigCommon__root_list PDCCH_ConfigCommon__root_Format_list PDCCH_ConfigCommon__ext_list PDCCH_ConfigCommon__ext_Format_list.

Opaque PDCCH_ConfigCommon__list_format.
Definition PDCCH_ConfigCommon__F1 (z : PDCCH_ConfigCommon__Type) : PDCCH_ConfigCommon__list_type :=
  (((PDCCH_ConfigCommon__controlResourceSetZero z, (PDCCH_ConfigCommon__commonControlResourceSet z, (PDCCH_ConfigCommon__searchSpaceZero z, (PDCCH_ConfigCommon__commonSearchSpaceList z, (PDCCH_ConfigCommon__searchSpaceSIB1 z, (PDCCH_ConfigCommon__searchSpaceOtherSystemInformation z, (PDCCH_ConfigCommon__pagingSearchSpace z, (PDCCH_ConfigCommon__ra_SearchSpace z, tt))))))))), (
(PDCCH_ConfigCommon__ext0 z, (PDCCH_ConfigCommon__ext1 z, (PDCCH_ConfigCommon__ext2 z, (PDCCH_ConfigCommon__ext3 z, tt)))))).
Definition PDCCH_ConfigCommon__F2 (y : PDCCH_ConfigCommon__list_type) : PDCCH_ConfigCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, (i1, (i2, (i3, _)))))=>
    make__PDCCH_ConfigCommon__Type j0 j1 j2 j3 j4 j5 j6 j7 i0 i1 i2 i3
  end.
Definition PDCCH_ConfigCommon__helper1 : (forall a : PDCCH_ConfigCommon__Type, PDCCH_ConfigCommon__cond a -> PDCCH_ConfigCommon__list_cond (PDCCH_ConfigCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDCCH_ConfigCommon__helper2 : (forall a : PDCCH_ConfigCommon__Type, PDCCH_ConfigCommon__F2 (PDCCH_ConfigCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDCCH_ConfigCommon__helper3 : (forall b : PDCCH_ConfigCommon__list_type, PDCCH_ConfigCommon__list_cond b -> PDCCH_ConfigCommon__cond (PDCCH_ConfigCommon__F2 b) /\ PDCCH_ConfigCommon__F1 (PDCCH_ConfigCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDCCH_ConfigCommon__cond, PDCCH_ConfigCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDCCH_ConfigCommon__Format : T_Format PDCCH_ConfigCommon__Type PDCCH_ConfigCommon__cond :=
 proj2_format PDCCH_ConfigCommon__cond PDCCH_ConfigCommon__list_format  PDCCH_ConfigCommon__F1 PDCCH_ConfigCommon__F2 PDCCH_ConfigCommon__helper1 PDCCH_ConfigCommon__helper2 PDCCH_ConfigCommon__helper3.

Opaque PDCCH_ConfigCommon__cond PDCCH_ConfigCommon__Format.

