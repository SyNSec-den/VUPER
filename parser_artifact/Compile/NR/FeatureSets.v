Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FeatureSetDownlink.

Opaque FeatureSetDownlink__cond FeatureSetDownlink__Format.

Definition FeatureSets__featureSetsDownlink__Type := list FeatureSetDownlink__Type.

Lemma FeatureSets__featureSetsDownlink__helper1 : (0 <= 1 <= maxDownlinkFeatureSets)%Z. unfold maxDownlinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__featureSetsDownlink__helper2 : to_bit_sz (Z.to_nat (maxDownlinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDownlinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__featureSetsDownlink__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__featureSetsDownlink__cond (z : FeatureSets__featureSetsDownlink__Type) :=  (1 <= Z.of_nat (length z) <= maxDownlinkFeatureSets)%Z /\ (list_and FeatureSetDownlink__cond z) .

Require Import NR.FeatureSetDownlinkPerCC.

Opaque FeatureSetDownlinkPerCC__cond FeatureSetDownlinkPerCC__Format.

Definition FeatureSets__featureSetsDownlinkPerCC__Type := list FeatureSetDownlinkPerCC__Type.

Lemma FeatureSets__featureSetsDownlinkPerCC__helper1 : (0 <= 1 <= maxPerCC_FeatureSets)%Z. unfold maxPerCC_FeatureSets.
 lia. Qed.
Lemma FeatureSets__featureSetsDownlinkPerCC__helper2 : to_bit_sz (Z.to_nat (maxPerCC_FeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPerCC_FeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__featureSetsDownlinkPerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__featureSetsDownlinkPerCC__cond (z : FeatureSets__featureSetsDownlinkPerCC__Type) :=  (1 <= Z.of_nat (length z) <= maxPerCC_FeatureSets)%Z /\ (list_and FeatureSetDownlinkPerCC__cond z) .

Require Import NR.FeatureSetUplink.

Opaque FeatureSetUplink__cond FeatureSetUplink__Format.

Definition FeatureSets__featureSetsUplink__Type := list FeatureSetUplink__Type.

Lemma FeatureSets__featureSetsUplink__helper1 : (0 <= 1 <= maxUplinkFeatureSets)%Z. unfold maxUplinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__featureSetsUplink__helper2 : to_bit_sz (Z.to_nat (maxUplinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUplinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__featureSetsUplink__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__featureSetsUplink__cond (z : FeatureSets__featureSetsUplink__Type) :=  (1 <= Z.of_nat (length z) <= maxUplinkFeatureSets)%Z /\ (list_and FeatureSetUplink__cond z) .

Require Import NR.FeatureSetUplinkPerCC.

Opaque FeatureSetUplinkPerCC__cond FeatureSetUplinkPerCC__Format.

Definition FeatureSets__featureSetsUplinkPerCC__Type := list FeatureSetUplinkPerCC__Type.

Lemma FeatureSets__featureSetsUplinkPerCC__helper1 : (0 <= 1 <= maxPerCC_FeatureSets)%Z. unfold maxPerCC_FeatureSets.
 lia. Qed.
Lemma FeatureSets__featureSetsUplinkPerCC__helper2 : to_bit_sz (Z.to_nat (maxPerCC_FeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPerCC_FeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__featureSetsUplinkPerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__featureSetsUplinkPerCC__cond (z : FeatureSets__featureSetsUplinkPerCC__Type) :=  (1 <= Z.of_nat (length z) <= maxPerCC_FeatureSets)%Z /\ (list_and FeatureSetUplinkPerCC__cond z) .

Require Import NR.FeatureSetDownlink_v1540.

Opaque FeatureSetDownlink_v1540__cond FeatureSetDownlink_v1540__Format.

Definition FeatureSets__ext0O__featureSetsDownlink_v1540__Type := list FeatureSetDownlink_v1540__Type.

Lemma FeatureSets__ext0O__featureSetsDownlink_v1540__helper1 : (0 <= 1 <= maxDownlinkFeatureSets)%Z. unfold maxDownlinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext0O__featureSetsDownlink_v1540__helper2 : to_bit_sz (Z.to_nat (maxDownlinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDownlinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext0O__featureSetsDownlink_v1540__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext0O__featureSetsDownlink_v1540__cond (z : FeatureSets__ext0O__featureSetsDownlink_v1540__Type) :=  (1 <= Z.of_nat (length z) <= maxDownlinkFeatureSets)%Z /\ (list_and FeatureSetDownlink_v1540__cond z) .

Require Import NR.FeatureSetUplink_v1540.

Opaque FeatureSetUplink_v1540__cond FeatureSetUplink_v1540__Format.

Definition FeatureSets__ext0O__featureSetsUplink_v1540__Type := list FeatureSetUplink_v1540__Type.

Lemma FeatureSets__ext0O__featureSetsUplink_v1540__helper1 : (0 <= 1 <= maxUplinkFeatureSets)%Z. unfold maxUplinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext0O__featureSetsUplink_v1540__helper2 : to_bit_sz (Z.to_nat (maxUplinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUplinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext0O__featureSetsUplink_v1540__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext0O__featureSetsUplink_v1540__cond (z : FeatureSets__ext0O__featureSetsUplink_v1540__Type) :=  (1 <= Z.of_nat (length z) <= maxUplinkFeatureSets)%Z /\ (list_and FeatureSetUplink_v1540__cond z) .

Require Import NR.FeatureSetUplinkPerCC_v1540.

Opaque FeatureSetUplinkPerCC_v1540__cond FeatureSetUplinkPerCC_v1540__Format.

Definition FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__Type := list FeatureSetUplinkPerCC_v1540__Type.

Lemma FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__helper1 : (0 <= 1 <= maxPerCC_FeatureSets)%Z. unfold maxPerCC_FeatureSets.
 lia. Qed.
Lemma FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__helper2 : to_bit_sz (Z.to_nat (maxPerCC_FeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPerCC_FeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__cond (z : FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__Type) :=  (1 <= Z.of_nat (length z) <= maxPerCC_FeatureSets)%Z /\ (list_and FeatureSetUplinkPerCC_v1540__cond z) .

Record FeatureSets__ext0O__Type : Set :=
  make__FeatureSets__ext0O__Type {
    FeatureSets__ext0O__featureSetsDownlink_v1540 : option FeatureSets__ext0O__featureSetsDownlink_v1540__Type ;
    FeatureSets__ext0O__featureSetsUplink_v1540 : option FeatureSets__ext0O__featureSetsUplink_v1540__Type ;
    FeatureSets__ext0O__featureSetsUplinkPerCC_v1540 : option FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__Type ;
}.
Definition FeatureSets__ext0O__list := (
 Opt FeatureSets__ext0O__featureSetsDownlink_v1540__Type FeatureSets__ext0O__featureSetsDownlink_v1540__cond ::
 Opt FeatureSets__ext0O__featureSetsUplink_v1540__Type FeatureSets__ext0O__featureSetsUplink_v1540__cond ::
 Opt FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__Type FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__cond ::
 nil).
Definition FeatureSets__ext0O__cond z := 
  opt_cond FeatureSets__ext0O__featureSetsDownlink_v1540__cond (FeatureSets__ext0O__featureSetsDownlink_v1540 z) /\
  opt_cond FeatureSets__ext0O__featureSetsUplink_v1540__cond (FeatureSets__ext0O__featureSetsUplink_v1540 z) /\
  opt_cond FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__cond (FeatureSets__ext0O__featureSetsUplinkPerCC_v1540 z) /\
  True.

Definition FeatureSets__ext0__Type := FeatureSets__ext0O__Type.
Definition FeatureSets__ext0__cond := FeatureSets__ext0O__cond.

Require Import NR.FeatureSetDownlink_v15a0.

Opaque FeatureSetDownlink_v15a0__cond FeatureSetDownlink_v15a0__Format.

Definition FeatureSets__ext1O__featureSetsDownlink_v15a0__Type := list FeatureSetDownlink_v15a0__Type.

Lemma FeatureSets__ext1O__featureSetsDownlink_v15a0__helper1 : (0 <= 1 <= maxDownlinkFeatureSets)%Z. unfold maxDownlinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext1O__featureSetsDownlink_v15a0__helper2 : to_bit_sz (Z.to_nat (maxDownlinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDownlinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext1O__featureSetsDownlink_v15a0__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext1O__featureSetsDownlink_v15a0__cond (z : FeatureSets__ext1O__featureSetsDownlink_v15a0__Type) :=  (1 <= Z.of_nat (length z) <= maxDownlinkFeatureSets)%Z /\ (list_and FeatureSetDownlink_v15a0__cond z) .

Record FeatureSets__ext1O__Type : Set :=
  make__FeatureSets__ext1O__Type {
    FeatureSets__ext1O__featureSetsDownlink_v15a0 : option FeatureSets__ext1O__featureSetsDownlink_v15a0__Type ;
}.
Definition FeatureSets__ext1O__list := (
 Opt FeatureSets__ext1O__featureSetsDownlink_v15a0__Type FeatureSets__ext1O__featureSetsDownlink_v15a0__cond ::
 nil).
Definition FeatureSets__ext1O__cond z := 
  opt_cond FeatureSets__ext1O__featureSetsDownlink_v15a0__cond (FeatureSets__ext1O__featureSetsDownlink_v15a0 z) /\
  True.

Definition FeatureSets__ext1__Type := FeatureSets__ext1O__Type.
Definition FeatureSets__ext1__cond := FeatureSets__ext1O__cond.

Require Import NR.FeatureSetDownlink_v1610.

Opaque FeatureSetDownlink_v1610__cond FeatureSetDownlink_v1610__Format.

Definition FeatureSets__ext2O__featureSetsDownlink_v1610__Type := list FeatureSetDownlink_v1610__Type.

Lemma FeatureSets__ext2O__featureSetsDownlink_v1610__helper1 : (0 <= 1 <= maxDownlinkFeatureSets)%Z. unfold maxDownlinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext2O__featureSetsDownlink_v1610__helper2 : to_bit_sz (Z.to_nat (maxDownlinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDownlinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext2O__featureSetsDownlink_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext2O__featureSetsDownlink_v1610__cond (z : FeatureSets__ext2O__featureSetsDownlink_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxDownlinkFeatureSets)%Z /\ (list_and FeatureSetDownlink_v1610__cond z) .

Require Import NR.FeatureSetUplink_v1610.

Opaque FeatureSetUplink_v1610__cond FeatureSetUplink_v1610__Format.

Definition FeatureSets__ext2O__featureSetsUplink_v1610__Type := list FeatureSetUplink_v1610__Type.

Lemma FeatureSets__ext2O__featureSetsUplink_v1610__helper1 : (0 <= 1 <= maxUplinkFeatureSets)%Z. unfold maxUplinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext2O__featureSetsUplink_v1610__helper2 : to_bit_sz (Z.to_nat (maxUplinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUplinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext2O__featureSetsUplink_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext2O__featureSetsUplink_v1610__cond (z : FeatureSets__ext2O__featureSetsUplink_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxUplinkFeatureSets)%Z /\ (list_and FeatureSetUplink_v1610__cond z) .

Require Import NR.FeatureSetDownlinkPerCC_v1620.

Opaque FeatureSetDownlinkPerCC_v1620__cond FeatureSetDownlinkPerCC_v1620__Format.

Definition FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__Type := list FeatureSetDownlinkPerCC_v1620__Type.

Lemma FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__helper1 : (0 <= 1 <= maxPerCC_FeatureSets)%Z. unfold maxPerCC_FeatureSets.
 lia. Qed.
Lemma FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__helper2 : to_bit_sz (Z.to_nat (maxPerCC_FeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPerCC_FeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__cond (z : FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__Type) :=  (1 <= Z.of_nat (length z) <= maxPerCC_FeatureSets)%Z /\ (list_and FeatureSetDownlinkPerCC_v1620__cond z) .

Record FeatureSets__ext2O__Type : Set :=
  make__FeatureSets__ext2O__Type {
    FeatureSets__ext2O__featureSetsDownlink_v1610 : option FeatureSets__ext2O__featureSetsDownlink_v1610__Type ;
    FeatureSets__ext2O__featureSetsUplink_v1610 : option FeatureSets__ext2O__featureSetsUplink_v1610__Type ;
    FeatureSets__ext2O__featureSetDownlinkPerCC_v1620 : option FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__Type ;
}.
Definition FeatureSets__ext2O__list := (
 Opt FeatureSets__ext2O__featureSetsDownlink_v1610__Type FeatureSets__ext2O__featureSetsDownlink_v1610__cond ::
 Opt FeatureSets__ext2O__featureSetsUplink_v1610__Type FeatureSets__ext2O__featureSetsUplink_v1610__cond ::
 Opt FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__Type FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__cond ::
 nil).
Definition FeatureSets__ext2O__cond z := 
  opt_cond FeatureSets__ext2O__featureSetsDownlink_v1610__cond (FeatureSets__ext2O__featureSetsDownlink_v1610 z) /\
  opt_cond FeatureSets__ext2O__featureSetsUplink_v1610__cond (FeatureSets__ext2O__featureSetsUplink_v1610 z) /\
  opt_cond FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__cond (FeatureSets__ext2O__featureSetDownlinkPerCC_v1620 z) /\
  True.

Definition FeatureSets__ext2__Type := FeatureSets__ext2O__Type.
Definition FeatureSets__ext2__cond := FeatureSets__ext2O__cond.

Require Import NR.FeatureSetUplink_v1630.

Opaque FeatureSetUplink_v1630__cond FeatureSetUplink_v1630__Format.

Definition FeatureSets__ext3O__featureSetsUplink_v1630__Type := list FeatureSetUplink_v1630__Type.

Lemma FeatureSets__ext3O__featureSetsUplink_v1630__helper1 : (0 <= 1 <= maxUplinkFeatureSets)%Z. unfold maxUplinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext3O__featureSetsUplink_v1630__helper2 : to_bit_sz (Z.to_nat (maxUplinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUplinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext3O__featureSetsUplink_v1630__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext3O__featureSetsUplink_v1630__cond (z : FeatureSets__ext3O__featureSetsUplink_v1630__Type) :=  (1 <= Z.of_nat (length z) <= maxUplinkFeatureSets)%Z /\ (list_and FeatureSetUplink_v1630__cond z) .

Record FeatureSets__ext3O__Type : Set :=
  make__FeatureSets__ext3O__Type {
    FeatureSets__ext3O__featureSetsUplink_v1630 : option FeatureSets__ext3O__featureSetsUplink_v1630__Type ;
}.
Definition FeatureSets__ext3O__list := (
 Opt FeatureSets__ext3O__featureSetsUplink_v1630__Type FeatureSets__ext3O__featureSetsUplink_v1630__cond ::
 nil).
Definition FeatureSets__ext3O__cond z := 
  opt_cond FeatureSets__ext3O__featureSetsUplink_v1630__cond (FeatureSets__ext3O__featureSetsUplink_v1630 z) /\
  True.

Definition FeatureSets__ext3__Type := FeatureSets__ext3O__Type.
Definition FeatureSets__ext3__cond := FeatureSets__ext3O__cond.

Require Import NR.FeatureSetUplink_v1640.

Opaque FeatureSetUplink_v1640__cond FeatureSetUplink_v1640__Format.

Definition FeatureSets__ext4O__featureSetsUplink_v1640__Type := list FeatureSetUplink_v1640__Type.

Lemma FeatureSets__ext4O__featureSetsUplink_v1640__helper1 : (0 <= 1 <= maxUplinkFeatureSets)%Z. unfold maxUplinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext4O__featureSetsUplink_v1640__helper2 : to_bit_sz (Z.to_nat (maxUplinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUplinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext4O__featureSetsUplink_v1640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext4O__featureSetsUplink_v1640__cond (z : FeatureSets__ext4O__featureSetsUplink_v1640__Type) :=  (1 <= Z.of_nat (length z) <= maxUplinkFeatureSets)%Z /\ (list_and FeatureSetUplink_v1640__cond z) .

Record FeatureSets__ext4O__Type : Set :=
  make__FeatureSets__ext4O__Type {
    FeatureSets__ext4O__featureSetsUplink_v1640 : option FeatureSets__ext4O__featureSetsUplink_v1640__Type ;
}.
Definition FeatureSets__ext4O__list := (
 Opt FeatureSets__ext4O__featureSetsUplink_v1640__Type FeatureSets__ext4O__featureSetsUplink_v1640__cond ::
 nil).
Definition FeatureSets__ext4O__cond z := 
  opt_cond FeatureSets__ext4O__featureSetsUplink_v1640__cond (FeatureSets__ext4O__featureSetsUplink_v1640 z) /\
  True.

Definition FeatureSets__ext4__Type := FeatureSets__ext4O__Type.
Definition FeatureSets__ext4__cond := FeatureSets__ext4O__cond.

Require Import NR.FeatureSetDownlink_v1700.

Opaque FeatureSetDownlink_v1700__cond FeatureSetDownlink_v1700__Format.

Definition FeatureSets__ext5O__featureSetsDownlink_v1700__Type := list FeatureSetDownlink_v1700__Type.

Lemma FeatureSets__ext5O__featureSetsDownlink_v1700__helper1 : (0 <= 1 <= maxDownlinkFeatureSets)%Z. unfold maxDownlinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext5O__featureSetsDownlink_v1700__helper2 : to_bit_sz (Z.to_nat (maxDownlinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDownlinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext5O__featureSetsDownlink_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext5O__featureSetsDownlink_v1700__cond (z : FeatureSets__ext5O__featureSetsDownlink_v1700__Type) :=  (1 <= Z.of_nat (length z) <= maxDownlinkFeatureSets)%Z /\ (list_and FeatureSetDownlink_v1700__cond z) .

Require Import NR.FeatureSetDownlinkPerCC_v1700.

Opaque FeatureSetDownlinkPerCC_v1700__cond FeatureSetDownlinkPerCC_v1700__Format.

Definition FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__Type := list FeatureSetDownlinkPerCC_v1700__Type.

Lemma FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__helper1 : (0 <= 1 <= maxPerCC_FeatureSets)%Z. unfold maxPerCC_FeatureSets.
 lia. Qed.
Lemma FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__helper2 : to_bit_sz (Z.to_nat (maxPerCC_FeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPerCC_FeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__cond (z : FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__Type) :=  (1 <= Z.of_nat (length z) <= maxPerCC_FeatureSets)%Z /\ (list_and FeatureSetDownlinkPerCC_v1700__cond z) .

Require Import NR.FeatureSetUplink_v1710.

Opaque FeatureSetUplink_v1710__cond FeatureSetUplink_v1710__Format.

Definition FeatureSets__ext5O__featureSetsUplink_v1710__Type := list FeatureSetUplink_v1710__Type.

Lemma FeatureSets__ext5O__featureSetsUplink_v1710__helper1 : (0 <= 1 <= maxUplinkFeatureSets)%Z. unfold maxUplinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext5O__featureSetsUplink_v1710__helper2 : to_bit_sz (Z.to_nat (maxUplinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUplinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext5O__featureSetsUplink_v1710__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext5O__featureSetsUplink_v1710__cond (z : FeatureSets__ext5O__featureSetsUplink_v1710__Type) :=  (1 <= Z.of_nat (length z) <= maxUplinkFeatureSets)%Z /\ (list_and FeatureSetUplink_v1710__cond z) .

Require Import NR.FeatureSetUplinkPerCC_v1700.

Opaque FeatureSetUplinkPerCC_v1700__cond FeatureSetUplinkPerCC_v1700__Format.

Definition FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__Type := list FeatureSetUplinkPerCC_v1700__Type.

Lemma FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__helper1 : (0 <= 1 <= maxPerCC_FeatureSets)%Z. unfold maxPerCC_FeatureSets.
 lia. Qed.
Lemma FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__helper2 : to_bit_sz (Z.to_nat (maxPerCC_FeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPerCC_FeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__cond (z : FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__Type) :=  (1 <= Z.of_nat (length z) <= maxPerCC_FeatureSets)%Z /\ (list_and FeatureSetUplinkPerCC_v1700__cond z) .

Record FeatureSets__ext5O__Type : Set :=
  make__FeatureSets__ext5O__Type {
    FeatureSets__ext5O__featureSetsDownlink_v1700 : option FeatureSets__ext5O__featureSetsDownlink_v1700__Type ;
    FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700 : option FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__Type ;
    FeatureSets__ext5O__featureSetsUplink_v1710 : option FeatureSets__ext5O__featureSetsUplink_v1710__Type ;
    FeatureSets__ext5O__featureSetsUplinkPerCC_v1700 : option FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__Type ;
}.
Definition FeatureSets__ext5O__list := (
 Opt FeatureSets__ext5O__featureSetsDownlink_v1700__Type FeatureSets__ext5O__featureSetsDownlink_v1700__cond ::
 Opt FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__Type FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__cond ::
 Opt FeatureSets__ext5O__featureSetsUplink_v1710__Type FeatureSets__ext5O__featureSetsUplink_v1710__cond ::
 Opt FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__Type FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__cond ::
 nil).
Definition FeatureSets__ext5O__cond z := 
  opt_cond FeatureSets__ext5O__featureSetsDownlink_v1700__cond (FeatureSets__ext5O__featureSetsDownlink_v1700 z) /\
  opt_cond FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__cond (FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700 z) /\
  opt_cond FeatureSets__ext5O__featureSetsUplink_v1710__cond (FeatureSets__ext5O__featureSetsUplink_v1710 z) /\
  opt_cond FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__cond (FeatureSets__ext5O__featureSetsUplinkPerCC_v1700 z) /\
  True.

Definition FeatureSets__ext5__Type := FeatureSets__ext5O__Type.
Definition FeatureSets__ext5__cond := FeatureSets__ext5O__cond.

Require Import NR.FeatureSetDownlink_v1720.

Opaque FeatureSetDownlink_v1720__cond FeatureSetDownlink_v1720__Format.

Definition FeatureSets__ext6O__featureSetsDownlink_v1720__Type := list FeatureSetDownlink_v1720__Type.

Lemma FeatureSets__ext6O__featureSetsDownlink_v1720__helper1 : (0 <= 1 <= maxDownlinkFeatureSets)%Z. unfold maxDownlinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext6O__featureSetsDownlink_v1720__helper2 : to_bit_sz (Z.to_nat (maxDownlinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDownlinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext6O__featureSetsDownlink_v1720__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext6O__featureSetsDownlink_v1720__cond (z : FeatureSets__ext6O__featureSetsDownlink_v1720__Type) :=  (1 <= Z.of_nat (length z) <= maxDownlinkFeatureSets)%Z /\ (list_and FeatureSetDownlink_v1720__cond z) .

Require Import NR.FeatureSetDownlinkPerCC_v1720.

Opaque FeatureSetDownlinkPerCC_v1720__cond FeatureSetDownlinkPerCC_v1720__Format.

Definition FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__Type := list FeatureSetDownlinkPerCC_v1720__Type.

Lemma FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__helper1 : (0 <= 1 <= maxPerCC_FeatureSets)%Z. unfold maxPerCC_FeatureSets.
 lia. Qed.
Lemma FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__helper2 : to_bit_sz (Z.to_nat (maxPerCC_FeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPerCC_FeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__cond (z : FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__Type) :=  (1 <= Z.of_nat (length z) <= maxPerCC_FeatureSets)%Z /\ (list_and FeatureSetDownlinkPerCC_v1720__cond z) .

Require Import NR.FeatureSetUplink_v1720.

Opaque FeatureSetUplink_v1720__cond FeatureSetUplink_v1720__Format.

Definition FeatureSets__ext6O__featureSetsUplink_v1720__Type := list FeatureSetUplink_v1720__Type.

Lemma FeatureSets__ext6O__featureSetsUplink_v1720__helper1 : (0 <= 1 <= maxUplinkFeatureSets)%Z. unfold maxUplinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext6O__featureSetsUplink_v1720__helper2 : to_bit_sz (Z.to_nat (maxUplinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUplinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext6O__featureSetsUplink_v1720__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext6O__featureSetsUplink_v1720__cond (z : FeatureSets__ext6O__featureSetsUplink_v1720__Type) :=  (1 <= Z.of_nat (length z) <= maxUplinkFeatureSets)%Z /\ (list_and FeatureSetUplink_v1720__cond z) .

Record FeatureSets__ext6O__Type : Set :=
  make__FeatureSets__ext6O__Type {
    FeatureSets__ext6O__featureSetsDownlink_v1720 : option FeatureSets__ext6O__featureSetsDownlink_v1720__Type ;
    FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720 : option FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__Type ;
    FeatureSets__ext6O__featureSetsUplink_v1720 : option FeatureSets__ext6O__featureSetsUplink_v1720__Type ;
}.
Definition FeatureSets__ext6O__list := (
 Opt FeatureSets__ext6O__featureSetsDownlink_v1720__Type FeatureSets__ext6O__featureSetsDownlink_v1720__cond ::
 Opt FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__Type FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__cond ::
 Opt FeatureSets__ext6O__featureSetsUplink_v1720__Type FeatureSets__ext6O__featureSetsUplink_v1720__cond ::
 nil).
Definition FeatureSets__ext6O__cond z := 
  opt_cond FeatureSets__ext6O__featureSetsDownlink_v1720__cond (FeatureSets__ext6O__featureSetsDownlink_v1720 z) /\
  opt_cond FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__cond (FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720 z) /\
  opt_cond FeatureSets__ext6O__featureSetsUplink_v1720__cond (FeatureSets__ext6O__featureSetsUplink_v1720 z) /\
  True.

Definition FeatureSets__ext6__Type := FeatureSets__ext6O__Type.
Definition FeatureSets__ext6__cond := FeatureSets__ext6O__cond.

Require Import NR.FeatureSetDownlink_v1730.

Opaque FeatureSetDownlink_v1730__cond FeatureSetDownlink_v1730__Format.

Definition FeatureSets__ext7O__featureSetsDownlink_v1730__Type := list FeatureSetDownlink_v1730__Type.

Lemma FeatureSets__ext7O__featureSetsDownlink_v1730__helper1 : (0 <= 1 <= maxDownlinkFeatureSets)%Z. unfold maxDownlinkFeatureSets.
 lia. Qed.
Lemma FeatureSets__ext7O__featureSetsDownlink_v1730__helper2 : to_bit_sz (Z.to_nat (maxDownlinkFeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDownlinkFeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext7O__featureSetsDownlink_v1730__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext7O__featureSetsDownlink_v1730__cond (z : FeatureSets__ext7O__featureSetsDownlink_v1730__Type) :=  (1 <= Z.of_nat (length z) <= maxDownlinkFeatureSets)%Z /\ (list_and FeatureSetDownlink_v1730__cond z) .

Require Import NR.FeatureSetDownlinkPerCC_v1730.

Opaque FeatureSetDownlinkPerCC_v1730__cond FeatureSetDownlinkPerCC_v1730__Format.

Definition FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__Type := list FeatureSetDownlinkPerCC_v1730__Type.

Lemma FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__helper1 : (0 <= 1 <= maxPerCC_FeatureSets)%Z. unfold maxPerCC_FeatureSets.
 lia. Qed.
Lemma FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__helper2 : to_bit_sz (Z.to_nat (maxPerCC_FeatureSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPerCC_FeatureSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__cond (z : FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__Type) :=  (1 <= Z.of_nat (length z) <= maxPerCC_FeatureSets)%Z /\ (list_and FeatureSetDownlinkPerCC_v1730__cond z) .

Record FeatureSets__ext7O__Type : Set :=
  make__FeatureSets__ext7O__Type {
    FeatureSets__ext7O__featureSetsDownlink_v1730 : option FeatureSets__ext7O__featureSetsDownlink_v1730__Type ;
    FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730 : option FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__Type ;
}.
Definition FeatureSets__ext7O__list := (
 Opt FeatureSets__ext7O__featureSetsDownlink_v1730__Type FeatureSets__ext7O__featureSetsDownlink_v1730__cond ::
 Opt FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__Type FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__cond ::
 nil).
Definition FeatureSets__ext7O__cond z := 
  opt_cond FeatureSets__ext7O__featureSetsDownlink_v1730__cond (FeatureSets__ext7O__featureSetsDownlink_v1730 z) /\
  opt_cond FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__cond (FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730 z) /\
  True.

Definition FeatureSets__ext7__Type := FeatureSets__ext7O__Type.
Definition FeatureSets__ext7__cond := FeatureSets__ext7O__cond.

Record FeatureSets__Type : Set :=
  make__FeatureSets__Type {
    FeatureSets__featureSetsDownlink : option FeatureSets__featureSetsDownlink__Type ;
    FeatureSets__featureSetsDownlinkPerCC : option FeatureSets__featureSetsDownlinkPerCC__Type ;
    FeatureSets__featureSetsUplink : option FeatureSets__featureSetsUplink__Type ;
    FeatureSets__featureSetsUplinkPerCC : option FeatureSets__featureSetsUplinkPerCC__Type ;
    FeatureSets__ext0 : option FeatureSets__ext0__Type ;
    FeatureSets__ext1 : option FeatureSets__ext1__Type ;
    FeatureSets__ext2 : option FeatureSets__ext2__Type ;
    FeatureSets__ext3 : option FeatureSets__ext3__Type ;
    FeatureSets__ext4 : option FeatureSets__ext4__Type ;
    FeatureSets__ext5 : option FeatureSets__ext5__Type ;
    FeatureSets__ext6 : option FeatureSets__ext6__Type ;
    FeatureSets__ext7 : option FeatureSets__ext7__Type ;
}.
Definition FeatureSets__root_list : list seq_elem := (
 Opt FeatureSets__featureSetsDownlink__Type FeatureSets__featureSetsDownlink__cond ::
 Opt FeatureSets__featureSetsDownlinkPerCC__Type FeatureSets__featureSetsDownlinkPerCC__cond ::
 Opt FeatureSets__featureSetsUplink__Type FeatureSets__featureSetsUplink__cond ::
 Opt FeatureSets__featureSetsUplinkPerCC__Type FeatureSets__featureSetsUplinkPerCC__cond ::
 nil).
Definition FeatureSets__ext_list : list typ := (
  typ_cons FeatureSets__ext0__Type FeatureSets__ext0__cond ::
  typ_cons FeatureSets__ext1__Type FeatureSets__ext1__cond ::
  typ_cons FeatureSets__ext2__Type FeatureSets__ext2__cond ::
  typ_cons FeatureSets__ext3__Type FeatureSets__ext3__cond ::
  typ_cons FeatureSets__ext4__Type FeatureSets__ext4__cond ::
  typ_cons FeatureSets__ext5__Type FeatureSets__ext5__cond ::
  typ_cons FeatureSets__ext6__Type FeatureSets__ext6__cond ::
  typ_cons FeatureSets__ext7__Type FeatureSets__ext7__cond ::
  nil).
Definition FeatureSets__cond (z : FeatureSets__Type) := 
(  opt_cond FeatureSets__featureSetsDownlink__cond (FeatureSets__featureSetsDownlink z) /\
  opt_cond FeatureSets__featureSetsDownlinkPerCC__cond (FeatureSets__featureSetsDownlinkPerCC z) /\
  opt_cond FeatureSets__featureSetsUplink__cond (FeatureSets__featureSetsUplink z) /\
  opt_cond FeatureSets__featureSetsUplinkPerCC__cond (FeatureSets__featureSetsUplinkPerCC z) /\
  True) /\ 
(  opt_cond FeatureSets__ext0__cond (FeatureSets__ext0 z) /\
  opt_cond FeatureSets__ext1__cond (FeatureSets__ext1 z) /\
  opt_cond FeatureSets__ext2__cond (FeatureSets__ext2 z) /\
  opt_cond FeatureSets__ext3__cond (FeatureSets__ext3 z) /\
  opt_cond FeatureSets__ext4__cond (FeatureSets__ext4 z) /\
  opt_cond FeatureSets__ext5__cond (FeatureSets__ext5 z) /\
  opt_cond FeatureSets__ext6__cond (FeatureSets__ext6 z) /\
  opt_cond FeatureSets__ext7__cond (FeatureSets__ext7 z) /\
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
Definition FeatureSets__featureSetsDownlink__Format : T_Format FeatureSets__featureSetsDownlink__Type FeatureSets__featureSetsDownlink__cond := seq_of_format FeatureSetDownlink__Format 1 maxDownlinkFeatureSets FeatureSets__featureSetsDownlink__helper1 FeatureSets__featureSetsDownlink__helper2.

Opaque FeatureSets__featureSetsDownlink__cond FeatureSets__featureSetsDownlink__Format.

Definition FeatureSets__featureSetsDownlinkPerCC__Format : T_Format FeatureSets__featureSetsDownlinkPerCC__Type FeatureSets__featureSetsDownlinkPerCC__cond := seq_of_format FeatureSetDownlinkPerCC__Format 1 maxPerCC_FeatureSets FeatureSets__featureSetsDownlinkPerCC__helper1 FeatureSets__featureSetsDownlinkPerCC__helper2.

Opaque FeatureSets__featureSetsDownlinkPerCC__cond FeatureSets__featureSetsDownlinkPerCC__Format.

Definition FeatureSets__featureSetsUplink__Format : T_Format FeatureSets__featureSetsUplink__Type FeatureSets__featureSetsUplink__cond := seq_of_format FeatureSetUplink__Format 1 maxUplinkFeatureSets FeatureSets__featureSetsUplink__helper1 FeatureSets__featureSetsUplink__helper2.

Opaque FeatureSets__featureSetsUplink__cond FeatureSets__featureSetsUplink__Format.

Definition FeatureSets__featureSetsUplinkPerCC__Format : T_Format FeatureSets__featureSetsUplinkPerCC__Type FeatureSets__featureSetsUplinkPerCC__cond := seq_of_format FeatureSetUplinkPerCC__Format 1 maxPerCC_FeatureSets FeatureSets__featureSetsUplinkPerCC__helper1 FeatureSets__featureSetsUplinkPerCC__helper2.

Opaque FeatureSets__featureSetsUplinkPerCC__cond FeatureSets__featureSetsUplinkPerCC__Format.

Definition FeatureSets__ext0O__featureSetsDownlink_v1540__Format : T_Format FeatureSets__ext0O__featureSetsDownlink_v1540__Type FeatureSets__ext0O__featureSetsDownlink_v1540__cond := seq_of_format FeatureSetDownlink_v1540__Format 1 maxDownlinkFeatureSets FeatureSets__ext0O__featureSetsDownlink_v1540__helper1 FeatureSets__ext0O__featureSetsDownlink_v1540__helper2.

Opaque FeatureSets__ext0O__featureSetsDownlink_v1540__cond FeatureSets__ext0O__featureSetsDownlink_v1540__Format.

Definition FeatureSets__ext0O__featureSetsUplink_v1540__Format : T_Format FeatureSets__ext0O__featureSetsUplink_v1540__Type FeatureSets__ext0O__featureSetsUplink_v1540__cond := seq_of_format FeatureSetUplink_v1540__Format 1 maxUplinkFeatureSets FeatureSets__ext0O__featureSetsUplink_v1540__helper1 FeatureSets__ext0O__featureSetsUplink_v1540__helper2.

Opaque FeatureSets__ext0O__featureSetsUplink_v1540__cond FeatureSets__ext0O__featureSetsUplink_v1540__Format.

Definition FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__Format : T_Format FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__Type FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__cond := seq_of_format FeatureSetUplinkPerCC_v1540__Format 1 maxPerCC_FeatureSets FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__helper1 FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__helper2.

Opaque FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__cond FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__Format.


Definition FeatureSets__ext0O__Format_Type := Eval cbn in seq_format_prod FeatureSets__ext0O__list.
Definition FeatureSets__ext0O__Format_list : FeatureSets__ext0O__Format_Type :=
  (FeatureSets__ext0O__featureSetsDownlink_v1540__Format, (FeatureSets__ext0O__featureSetsUplink_v1540__Format, (FeatureSets__ext0O__featureSetsUplinkPerCC_v1540__Format, unit_format))).
Definition FeatureSets__ext0O__list__Format := (*Eval compute in *) seq_format FeatureSets__ext0O__list FeatureSets__ext0O__Format_list.
Definition FeatureSets__ext0O__F1 z :=
  (FeatureSets__ext0O__featureSetsDownlink_v1540 z, (FeatureSets__ext0O__featureSetsUplink_v1540 z, (FeatureSets__ext0O__featureSetsUplinkPerCC_v1540 z, tt))).
Definition FeatureSets__ext0O__F2 (y : seq_type FeatureSets__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FeatureSets__ext0O__Type i0 i1 i2
  end.
Lemma FeatureSets__ext0O__F1F2_cond (z : FeatureSets__ext0O__Type)
  : FeatureSets__ext0O__cond z ->
  (seq_cond FeatureSets__ext0O__list (FeatureSets__ext0O__F1 z)).
intro H. unfold FeatureSets__ext0O__cond in H. simpl. auto. Qed.
Lemma FeatureSets__ext0O__F1F2_cond2 (z : FeatureSets__ext0O__Type)
 : FeatureSets__ext0O__F2 (FeatureSets__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSets__ext0O__F2F1_cond (y : seq_type FeatureSets__ext0O__list)
  : seq_cond FeatureSets__ext0O__list y ->
 (FeatureSets__ext0O__cond (FeatureSets__ext0O__F2 y)) /\  FeatureSets__ext0O__F1 (FeatureSets__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSets__ext0O__cond. simpl in *. auto.
 - simpl. unfold FeatureSets__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSets__ext0O__Format : T_Format FeatureSets__ext0O__Type FeatureSets__ext0O__cond :=
        proj2_format  FeatureSets__ext0O__cond FeatureSets__ext0O__list__Format
    FeatureSets__ext0O__F1 FeatureSets__ext0O__F2 FeatureSets__ext0O__F1F2_cond  FeatureSets__ext0O__F1F2_cond2 FeatureSets__ext0O__F2F1_cond.
Opaque FeatureSets__ext0O__cond FeatureSets__ext0O__Format.

Definition FeatureSets__ext0__check_all_none (b : FeatureSets__ext0O__Type) : bool :=
match b with 
  | make__FeatureSets__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition FeatureSets__ext0__Format : T_Format FeatureSets__ext0__Type FeatureSets__ext0__cond :=
  restrict_add_format FeatureSets__ext0__check_all_none FeatureSets__ext0O__Format.

Opaque FeatureSets__ext0__cond FeatureSets__ext0__Format.

Definition FeatureSets__ext1O__featureSetsDownlink_v15a0__Format : T_Format FeatureSets__ext1O__featureSetsDownlink_v15a0__Type FeatureSets__ext1O__featureSetsDownlink_v15a0__cond := seq_of_format FeatureSetDownlink_v15a0__Format 1 maxDownlinkFeatureSets FeatureSets__ext1O__featureSetsDownlink_v15a0__helper1 FeatureSets__ext1O__featureSetsDownlink_v15a0__helper2.

Opaque FeatureSets__ext1O__featureSetsDownlink_v15a0__cond FeatureSets__ext1O__featureSetsDownlink_v15a0__Format.


Definition FeatureSets__ext1O__Format_Type := Eval cbn in seq_format_prod FeatureSets__ext1O__list.
Definition FeatureSets__ext1O__Format_list : FeatureSets__ext1O__Format_Type :=
  (FeatureSets__ext1O__featureSetsDownlink_v15a0__Format, unit_format).
Definition FeatureSets__ext1O__list__Format := (*Eval compute in *) seq_format FeatureSets__ext1O__list FeatureSets__ext1O__Format_list.
Definition FeatureSets__ext1O__F1 z :=
  (FeatureSets__ext1O__featureSetsDownlink_v15a0 z, tt).
Definition FeatureSets__ext1O__F2 (y : seq_type FeatureSets__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__FeatureSets__ext1O__Type i0
  end.
Lemma FeatureSets__ext1O__F1F2_cond (z : FeatureSets__ext1O__Type)
  : FeatureSets__ext1O__cond z ->
  (seq_cond FeatureSets__ext1O__list (FeatureSets__ext1O__F1 z)).
intro H. unfold FeatureSets__ext1O__cond in H. simpl. auto. Qed.
Lemma FeatureSets__ext1O__F1F2_cond2 (z : FeatureSets__ext1O__Type)
 : FeatureSets__ext1O__F2 (FeatureSets__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSets__ext1O__F2F1_cond (y : seq_type FeatureSets__ext1O__list)
  : seq_cond FeatureSets__ext1O__list y ->
 (FeatureSets__ext1O__cond (FeatureSets__ext1O__F2 y)) /\  FeatureSets__ext1O__F1 (FeatureSets__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSets__ext1O__cond. simpl in *. auto.
 - simpl. unfold FeatureSets__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSets__ext1O__Format : T_Format FeatureSets__ext1O__Type FeatureSets__ext1O__cond :=
        proj2_format  FeatureSets__ext1O__cond FeatureSets__ext1O__list__Format
    FeatureSets__ext1O__F1 FeatureSets__ext1O__F2 FeatureSets__ext1O__F1F2_cond  FeatureSets__ext1O__F1F2_cond2 FeatureSets__ext1O__F2F1_cond.
Opaque FeatureSets__ext1O__cond FeatureSets__ext1O__Format.

Definition FeatureSets__ext1__check_all_none (b : FeatureSets__ext1O__Type) : bool :=
match b with 
  | make__FeatureSets__ext1O__Type None  => false 
  | _ => true 
 end.
Definition FeatureSets__ext1__Format : T_Format FeatureSets__ext1__Type FeatureSets__ext1__cond :=
  restrict_add_format FeatureSets__ext1__check_all_none FeatureSets__ext1O__Format.

Opaque FeatureSets__ext1__cond FeatureSets__ext1__Format.

Definition FeatureSets__ext2O__featureSetsDownlink_v1610__Format : T_Format FeatureSets__ext2O__featureSetsDownlink_v1610__Type FeatureSets__ext2O__featureSetsDownlink_v1610__cond := seq_of_format FeatureSetDownlink_v1610__Format 1 maxDownlinkFeatureSets FeatureSets__ext2O__featureSetsDownlink_v1610__helper1 FeatureSets__ext2O__featureSetsDownlink_v1610__helper2.

Opaque FeatureSets__ext2O__featureSetsDownlink_v1610__cond FeatureSets__ext2O__featureSetsDownlink_v1610__Format.

Definition FeatureSets__ext2O__featureSetsUplink_v1610__Format : T_Format FeatureSets__ext2O__featureSetsUplink_v1610__Type FeatureSets__ext2O__featureSetsUplink_v1610__cond := seq_of_format FeatureSetUplink_v1610__Format 1 maxUplinkFeatureSets FeatureSets__ext2O__featureSetsUplink_v1610__helper1 FeatureSets__ext2O__featureSetsUplink_v1610__helper2.

Opaque FeatureSets__ext2O__featureSetsUplink_v1610__cond FeatureSets__ext2O__featureSetsUplink_v1610__Format.

Definition FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__Format : T_Format FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__Type FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__cond := seq_of_format FeatureSetDownlinkPerCC_v1620__Format 1 maxPerCC_FeatureSets FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__helper1 FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__helper2.

Opaque FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__cond FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__Format.


Definition FeatureSets__ext2O__Format_Type := Eval cbn in seq_format_prod FeatureSets__ext2O__list.
Definition FeatureSets__ext2O__Format_list : FeatureSets__ext2O__Format_Type :=
  (FeatureSets__ext2O__featureSetsDownlink_v1610__Format, (FeatureSets__ext2O__featureSetsUplink_v1610__Format, (FeatureSets__ext2O__featureSetDownlinkPerCC_v1620__Format, unit_format))).
Definition FeatureSets__ext2O__list__Format := (*Eval compute in *) seq_format FeatureSets__ext2O__list FeatureSets__ext2O__Format_list.
Definition FeatureSets__ext2O__F1 z :=
  (FeatureSets__ext2O__featureSetsDownlink_v1610 z, (FeatureSets__ext2O__featureSetsUplink_v1610 z, (FeatureSets__ext2O__featureSetDownlinkPerCC_v1620 z, tt))).
Definition FeatureSets__ext2O__F2 (y : seq_type FeatureSets__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FeatureSets__ext2O__Type i0 i1 i2
  end.
Lemma FeatureSets__ext2O__F1F2_cond (z : FeatureSets__ext2O__Type)
  : FeatureSets__ext2O__cond z ->
  (seq_cond FeatureSets__ext2O__list (FeatureSets__ext2O__F1 z)).
intro H. unfold FeatureSets__ext2O__cond in H. simpl. auto. Qed.
Lemma FeatureSets__ext2O__F1F2_cond2 (z : FeatureSets__ext2O__Type)
 : FeatureSets__ext2O__F2 (FeatureSets__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSets__ext2O__F2F1_cond (y : seq_type FeatureSets__ext2O__list)
  : seq_cond FeatureSets__ext2O__list y ->
 (FeatureSets__ext2O__cond (FeatureSets__ext2O__F2 y)) /\  FeatureSets__ext2O__F1 (FeatureSets__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSets__ext2O__cond. simpl in *. auto.
 - simpl. unfold FeatureSets__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSets__ext2O__Format : T_Format FeatureSets__ext2O__Type FeatureSets__ext2O__cond :=
        proj2_format  FeatureSets__ext2O__cond FeatureSets__ext2O__list__Format
    FeatureSets__ext2O__F1 FeatureSets__ext2O__F2 FeatureSets__ext2O__F1F2_cond  FeatureSets__ext2O__F1F2_cond2 FeatureSets__ext2O__F2F1_cond.
Opaque FeatureSets__ext2O__cond FeatureSets__ext2O__Format.

Definition FeatureSets__ext2__check_all_none (b : FeatureSets__ext2O__Type) : bool :=
match b with 
  | make__FeatureSets__ext2O__Type None None None  => false 
  | _ => true 
 end.
Definition FeatureSets__ext2__Format : T_Format FeatureSets__ext2__Type FeatureSets__ext2__cond :=
  restrict_add_format FeatureSets__ext2__check_all_none FeatureSets__ext2O__Format.

Opaque FeatureSets__ext2__cond FeatureSets__ext2__Format.

Definition FeatureSets__ext3O__featureSetsUplink_v1630__Format : T_Format FeatureSets__ext3O__featureSetsUplink_v1630__Type FeatureSets__ext3O__featureSetsUplink_v1630__cond := seq_of_format FeatureSetUplink_v1630__Format 1 maxUplinkFeatureSets FeatureSets__ext3O__featureSetsUplink_v1630__helper1 FeatureSets__ext3O__featureSetsUplink_v1630__helper2.

Opaque FeatureSets__ext3O__featureSetsUplink_v1630__cond FeatureSets__ext3O__featureSetsUplink_v1630__Format.


Definition FeatureSets__ext3O__Format_Type := Eval cbn in seq_format_prod FeatureSets__ext3O__list.
Definition FeatureSets__ext3O__Format_list : FeatureSets__ext3O__Format_Type :=
  (FeatureSets__ext3O__featureSetsUplink_v1630__Format, unit_format).
Definition FeatureSets__ext3O__list__Format := (*Eval compute in *) seq_format FeatureSets__ext3O__list FeatureSets__ext3O__Format_list.
Definition FeatureSets__ext3O__F1 z :=
  (FeatureSets__ext3O__featureSetsUplink_v1630 z, tt).
Definition FeatureSets__ext3O__F2 (y : seq_type FeatureSets__ext3O__list) :=
  match y with
  | (i0, _)=>
    make__FeatureSets__ext3O__Type i0
  end.
Lemma FeatureSets__ext3O__F1F2_cond (z : FeatureSets__ext3O__Type)
  : FeatureSets__ext3O__cond z ->
  (seq_cond FeatureSets__ext3O__list (FeatureSets__ext3O__F1 z)).
intro H. unfold FeatureSets__ext3O__cond in H. simpl. auto. Qed.
Lemma FeatureSets__ext3O__F1F2_cond2 (z : FeatureSets__ext3O__Type)
 : FeatureSets__ext3O__F2 (FeatureSets__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSets__ext3O__F2F1_cond (y : seq_type FeatureSets__ext3O__list)
  : seq_cond FeatureSets__ext3O__list y ->
 (FeatureSets__ext3O__cond (FeatureSets__ext3O__F2 y)) /\  FeatureSets__ext3O__F1 (FeatureSets__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSets__ext3O__cond. simpl in *. auto.
 - simpl. unfold FeatureSets__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSets__ext3O__Format : T_Format FeatureSets__ext3O__Type FeatureSets__ext3O__cond :=
        proj2_format  FeatureSets__ext3O__cond FeatureSets__ext3O__list__Format
    FeatureSets__ext3O__F1 FeatureSets__ext3O__F2 FeatureSets__ext3O__F1F2_cond  FeatureSets__ext3O__F1F2_cond2 FeatureSets__ext3O__F2F1_cond.
Opaque FeatureSets__ext3O__cond FeatureSets__ext3O__Format.

Definition FeatureSets__ext3__check_all_none (b : FeatureSets__ext3O__Type) : bool :=
match b with 
  | make__FeatureSets__ext3O__Type None  => false 
  | _ => true 
 end.
Definition FeatureSets__ext3__Format : T_Format FeatureSets__ext3__Type FeatureSets__ext3__cond :=
  restrict_add_format FeatureSets__ext3__check_all_none FeatureSets__ext3O__Format.

Opaque FeatureSets__ext3__cond FeatureSets__ext3__Format.

Definition FeatureSets__ext4O__featureSetsUplink_v1640__Format : T_Format FeatureSets__ext4O__featureSetsUplink_v1640__Type FeatureSets__ext4O__featureSetsUplink_v1640__cond := seq_of_format FeatureSetUplink_v1640__Format 1 maxUplinkFeatureSets FeatureSets__ext4O__featureSetsUplink_v1640__helper1 FeatureSets__ext4O__featureSetsUplink_v1640__helper2.

Opaque FeatureSets__ext4O__featureSetsUplink_v1640__cond FeatureSets__ext4O__featureSetsUplink_v1640__Format.


Definition FeatureSets__ext4O__Format_Type := Eval cbn in seq_format_prod FeatureSets__ext4O__list.
Definition FeatureSets__ext4O__Format_list : FeatureSets__ext4O__Format_Type :=
  (FeatureSets__ext4O__featureSetsUplink_v1640__Format, unit_format).
Definition FeatureSets__ext4O__list__Format := (*Eval compute in *) seq_format FeatureSets__ext4O__list FeatureSets__ext4O__Format_list.
Definition FeatureSets__ext4O__F1 z :=
  (FeatureSets__ext4O__featureSetsUplink_v1640 z, tt).
Definition FeatureSets__ext4O__F2 (y : seq_type FeatureSets__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__FeatureSets__ext4O__Type i0
  end.
Lemma FeatureSets__ext4O__F1F2_cond (z : FeatureSets__ext4O__Type)
  : FeatureSets__ext4O__cond z ->
  (seq_cond FeatureSets__ext4O__list (FeatureSets__ext4O__F1 z)).
intro H. unfold FeatureSets__ext4O__cond in H. simpl. auto. Qed.
Lemma FeatureSets__ext4O__F1F2_cond2 (z : FeatureSets__ext4O__Type)
 : FeatureSets__ext4O__F2 (FeatureSets__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSets__ext4O__F2F1_cond (y : seq_type FeatureSets__ext4O__list)
  : seq_cond FeatureSets__ext4O__list y ->
 (FeatureSets__ext4O__cond (FeatureSets__ext4O__F2 y)) /\  FeatureSets__ext4O__F1 (FeatureSets__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSets__ext4O__cond. simpl in *. auto.
 - simpl. unfold FeatureSets__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSets__ext4O__Format : T_Format FeatureSets__ext4O__Type FeatureSets__ext4O__cond :=
        proj2_format  FeatureSets__ext4O__cond FeatureSets__ext4O__list__Format
    FeatureSets__ext4O__F1 FeatureSets__ext4O__F2 FeatureSets__ext4O__F1F2_cond  FeatureSets__ext4O__F1F2_cond2 FeatureSets__ext4O__F2F1_cond.
Opaque FeatureSets__ext4O__cond FeatureSets__ext4O__Format.

Definition FeatureSets__ext4__check_all_none (b : FeatureSets__ext4O__Type) : bool :=
match b with 
  | make__FeatureSets__ext4O__Type None  => false 
  | _ => true 
 end.
Definition FeatureSets__ext4__Format : T_Format FeatureSets__ext4__Type FeatureSets__ext4__cond :=
  restrict_add_format FeatureSets__ext4__check_all_none FeatureSets__ext4O__Format.

Opaque FeatureSets__ext4__cond FeatureSets__ext4__Format.

Definition FeatureSets__ext5O__featureSetsDownlink_v1700__Format : T_Format FeatureSets__ext5O__featureSetsDownlink_v1700__Type FeatureSets__ext5O__featureSetsDownlink_v1700__cond := seq_of_format FeatureSetDownlink_v1700__Format 1 maxDownlinkFeatureSets FeatureSets__ext5O__featureSetsDownlink_v1700__helper1 FeatureSets__ext5O__featureSetsDownlink_v1700__helper2.

Opaque FeatureSets__ext5O__featureSetsDownlink_v1700__cond FeatureSets__ext5O__featureSetsDownlink_v1700__Format.

Definition FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__Format : T_Format FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__Type FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__cond := seq_of_format FeatureSetDownlinkPerCC_v1700__Format 1 maxPerCC_FeatureSets FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__helper1 FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__helper2.

Opaque FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__cond FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__Format.

Definition FeatureSets__ext5O__featureSetsUplink_v1710__Format : T_Format FeatureSets__ext5O__featureSetsUplink_v1710__Type FeatureSets__ext5O__featureSetsUplink_v1710__cond := seq_of_format FeatureSetUplink_v1710__Format 1 maxUplinkFeatureSets FeatureSets__ext5O__featureSetsUplink_v1710__helper1 FeatureSets__ext5O__featureSetsUplink_v1710__helper2.

Opaque FeatureSets__ext5O__featureSetsUplink_v1710__cond FeatureSets__ext5O__featureSetsUplink_v1710__Format.

Definition FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__Format : T_Format FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__Type FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__cond := seq_of_format FeatureSetUplinkPerCC_v1700__Format 1 maxPerCC_FeatureSets FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__helper1 FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__helper2.

Opaque FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__cond FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__Format.


Definition FeatureSets__ext5O__Format_Type := Eval cbn in seq_format_prod FeatureSets__ext5O__list.
Definition FeatureSets__ext5O__Format_list : FeatureSets__ext5O__Format_Type :=
  (FeatureSets__ext5O__featureSetsDownlink_v1700__Format, (FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700__Format, (FeatureSets__ext5O__featureSetsUplink_v1710__Format, (FeatureSets__ext5O__featureSetsUplinkPerCC_v1700__Format, unit_format)))).
Definition FeatureSets__ext5O__list__Format := (*Eval compute in *) seq_format FeatureSets__ext5O__list FeatureSets__ext5O__Format_list.
Definition FeatureSets__ext5O__F1 z :=
  (FeatureSets__ext5O__featureSetsDownlink_v1700 z, (FeatureSets__ext5O__featureSetsDownlinkPerCC_v1700 z, (FeatureSets__ext5O__featureSetsUplink_v1710 z, (FeatureSets__ext5O__featureSetsUplinkPerCC_v1700 z, tt)))).
Definition FeatureSets__ext5O__F2 (y : seq_type FeatureSets__ext5O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__FeatureSets__ext5O__Type i0 i1 i2 i3
  end.
Lemma FeatureSets__ext5O__F1F2_cond (z : FeatureSets__ext5O__Type)
  : FeatureSets__ext5O__cond z ->
  (seq_cond FeatureSets__ext5O__list (FeatureSets__ext5O__F1 z)).
intro H. unfold FeatureSets__ext5O__cond in H. simpl. auto. Qed.
Lemma FeatureSets__ext5O__F1F2_cond2 (z : FeatureSets__ext5O__Type)
 : FeatureSets__ext5O__F2 (FeatureSets__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSets__ext5O__F2F1_cond (y : seq_type FeatureSets__ext5O__list)
  : seq_cond FeatureSets__ext5O__list y ->
 (FeatureSets__ext5O__cond (FeatureSets__ext5O__F2 y)) /\  FeatureSets__ext5O__F1 (FeatureSets__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSets__ext5O__cond. simpl in *. auto.
 - simpl. unfold FeatureSets__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSets__ext5O__Format : T_Format FeatureSets__ext5O__Type FeatureSets__ext5O__cond :=
        proj2_format  FeatureSets__ext5O__cond FeatureSets__ext5O__list__Format
    FeatureSets__ext5O__F1 FeatureSets__ext5O__F2 FeatureSets__ext5O__F1F2_cond  FeatureSets__ext5O__F1F2_cond2 FeatureSets__ext5O__F2F1_cond.
Opaque FeatureSets__ext5O__cond FeatureSets__ext5O__Format.

Definition FeatureSets__ext5__check_all_none (b : FeatureSets__ext5O__Type) : bool :=
match b with 
  | make__FeatureSets__ext5O__Type None None None None  => false 
  | _ => true 
 end.
Definition FeatureSets__ext5__Format : T_Format FeatureSets__ext5__Type FeatureSets__ext5__cond :=
  restrict_add_format FeatureSets__ext5__check_all_none FeatureSets__ext5O__Format.

Opaque FeatureSets__ext5__cond FeatureSets__ext5__Format.

Definition FeatureSets__ext6O__featureSetsDownlink_v1720__Format : T_Format FeatureSets__ext6O__featureSetsDownlink_v1720__Type FeatureSets__ext6O__featureSetsDownlink_v1720__cond := seq_of_format FeatureSetDownlink_v1720__Format 1 maxDownlinkFeatureSets FeatureSets__ext6O__featureSetsDownlink_v1720__helper1 FeatureSets__ext6O__featureSetsDownlink_v1720__helper2.

Opaque FeatureSets__ext6O__featureSetsDownlink_v1720__cond FeatureSets__ext6O__featureSetsDownlink_v1720__Format.

Definition FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__Format : T_Format FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__Type FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__cond := seq_of_format FeatureSetDownlinkPerCC_v1720__Format 1 maxPerCC_FeatureSets FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__helper1 FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__helper2.

Opaque FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__cond FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__Format.

Definition FeatureSets__ext6O__featureSetsUplink_v1720__Format : T_Format FeatureSets__ext6O__featureSetsUplink_v1720__Type FeatureSets__ext6O__featureSetsUplink_v1720__cond := seq_of_format FeatureSetUplink_v1720__Format 1 maxUplinkFeatureSets FeatureSets__ext6O__featureSetsUplink_v1720__helper1 FeatureSets__ext6O__featureSetsUplink_v1720__helper2.

Opaque FeatureSets__ext6O__featureSetsUplink_v1720__cond FeatureSets__ext6O__featureSetsUplink_v1720__Format.


Definition FeatureSets__ext6O__Format_Type := Eval cbn in seq_format_prod FeatureSets__ext6O__list.
Definition FeatureSets__ext6O__Format_list : FeatureSets__ext6O__Format_Type :=
  (FeatureSets__ext6O__featureSetsDownlink_v1720__Format, (FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720__Format, (FeatureSets__ext6O__featureSetsUplink_v1720__Format, unit_format))).
Definition FeatureSets__ext6O__list__Format := (*Eval compute in *) seq_format FeatureSets__ext6O__list FeatureSets__ext6O__Format_list.
Definition FeatureSets__ext6O__F1 z :=
  (FeatureSets__ext6O__featureSetsDownlink_v1720 z, (FeatureSets__ext6O__featureSetsDownlinkPerCC_v1720 z, (FeatureSets__ext6O__featureSetsUplink_v1720 z, tt))).
Definition FeatureSets__ext6O__F2 (y : seq_type FeatureSets__ext6O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FeatureSets__ext6O__Type i0 i1 i2
  end.
Lemma FeatureSets__ext6O__F1F2_cond (z : FeatureSets__ext6O__Type)
  : FeatureSets__ext6O__cond z ->
  (seq_cond FeatureSets__ext6O__list (FeatureSets__ext6O__F1 z)).
intro H. unfold FeatureSets__ext6O__cond in H. simpl. auto. Qed.
Lemma FeatureSets__ext6O__F1F2_cond2 (z : FeatureSets__ext6O__Type)
 : FeatureSets__ext6O__F2 (FeatureSets__ext6O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSets__ext6O__F2F1_cond (y : seq_type FeatureSets__ext6O__list)
  : seq_cond FeatureSets__ext6O__list y ->
 (FeatureSets__ext6O__cond (FeatureSets__ext6O__F2 y)) /\  FeatureSets__ext6O__F1 (FeatureSets__ext6O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSets__ext6O__cond. simpl in *. auto.
 - simpl. unfold FeatureSets__ext6O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSets__ext6O__Format : T_Format FeatureSets__ext6O__Type FeatureSets__ext6O__cond :=
        proj2_format  FeatureSets__ext6O__cond FeatureSets__ext6O__list__Format
    FeatureSets__ext6O__F1 FeatureSets__ext6O__F2 FeatureSets__ext6O__F1F2_cond  FeatureSets__ext6O__F1F2_cond2 FeatureSets__ext6O__F2F1_cond.
Opaque FeatureSets__ext6O__cond FeatureSets__ext6O__Format.

Definition FeatureSets__ext6__check_all_none (b : FeatureSets__ext6O__Type) : bool :=
match b with 
  | make__FeatureSets__ext6O__Type None None None  => false 
  | _ => true 
 end.
Definition FeatureSets__ext6__Format : T_Format FeatureSets__ext6__Type FeatureSets__ext6__cond :=
  restrict_add_format FeatureSets__ext6__check_all_none FeatureSets__ext6O__Format.

Opaque FeatureSets__ext6__cond FeatureSets__ext6__Format.

Definition FeatureSets__ext7O__featureSetsDownlink_v1730__Format : T_Format FeatureSets__ext7O__featureSetsDownlink_v1730__Type FeatureSets__ext7O__featureSetsDownlink_v1730__cond := seq_of_format FeatureSetDownlink_v1730__Format 1 maxDownlinkFeatureSets FeatureSets__ext7O__featureSetsDownlink_v1730__helper1 FeatureSets__ext7O__featureSetsDownlink_v1730__helper2.

Opaque FeatureSets__ext7O__featureSetsDownlink_v1730__cond FeatureSets__ext7O__featureSetsDownlink_v1730__Format.

Definition FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__Format : T_Format FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__Type FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__cond := seq_of_format FeatureSetDownlinkPerCC_v1730__Format 1 maxPerCC_FeatureSets FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__helper1 FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__helper2.

Opaque FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__cond FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__Format.


Definition FeatureSets__ext7O__Format_Type := Eval cbn in seq_format_prod FeatureSets__ext7O__list.
Definition FeatureSets__ext7O__Format_list : FeatureSets__ext7O__Format_Type :=
  (FeatureSets__ext7O__featureSetsDownlink_v1730__Format, (FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730__Format, unit_format)).
Definition FeatureSets__ext7O__list__Format := (*Eval compute in *) seq_format FeatureSets__ext7O__list FeatureSets__ext7O__Format_list.
Definition FeatureSets__ext7O__F1 z :=
  (FeatureSets__ext7O__featureSetsDownlink_v1730 z, (FeatureSets__ext7O__featureSetsDownlinkPerCC_v1730 z, tt)).
Definition FeatureSets__ext7O__F2 (y : seq_type FeatureSets__ext7O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSets__ext7O__Type i0 i1
  end.
Lemma FeatureSets__ext7O__F1F2_cond (z : FeatureSets__ext7O__Type)
  : FeatureSets__ext7O__cond z ->
  (seq_cond FeatureSets__ext7O__list (FeatureSets__ext7O__F1 z)).
intro H. unfold FeatureSets__ext7O__cond in H. simpl. auto. Qed.
Lemma FeatureSets__ext7O__F1F2_cond2 (z : FeatureSets__ext7O__Type)
 : FeatureSets__ext7O__F2 (FeatureSets__ext7O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSets__ext7O__F2F1_cond (y : seq_type FeatureSets__ext7O__list)
  : seq_cond FeatureSets__ext7O__list y ->
 (FeatureSets__ext7O__cond (FeatureSets__ext7O__F2 y)) /\  FeatureSets__ext7O__F1 (FeatureSets__ext7O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSets__ext7O__cond. simpl in *. auto.
 - simpl. unfold FeatureSets__ext7O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSets__ext7O__Format : T_Format FeatureSets__ext7O__Type FeatureSets__ext7O__cond :=
        proj2_format  FeatureSets__ext7O__cond FeatureSets__ext7O__list__Format
    FeatureSets__ext7O__F1 FeatureSets__ext7O__F2 FeatureSets__ext7O__F1F2_cond  FeatureSets__ext7O__F1F2_cond2 FeatureSets__ext7O__F2F1_cond.
Opaque FeatureSets__ext7O__cond FeatureSets__ext7O__Format.

Definition FeatureSets__ext7__check_all_none (b : FeatureSets__ext7O__Type) : bool :=
match b with 
  | make__FeatureSets__ext7O__Type None None  => false 
  | _ => true 
 end.
Definition FeatureSets__ext7__Format : T_Format FeatureSets__ext7__Type FeatureSets__ext7__cond :=
  restrict_add_format FeatureSets__ext7__check_all_none FeatureSets__ext7O__Format.

Opaque FeatureSets__ext7__cond FeatureSets__ext7__Format.


Definition FeatureSets__root_Format_Type := Eval cbn in seq_format_prod FeatureSets__root_list.
Definition FeatureSets__root_Format_list : FeatureSets__root_Format_Type :=
  (FeatureSets__featureSetsDownlink__Format, (FeatureSets__featureSetsDownlinkPerCC__Format, (FeatureSets__featureSetsUplink__Format, (FeatureSets__featureSetsUplinkPerCC__Format, unit_format)))).

Definition FeatureSets__ext_Format_Type := Eval cbn in get_formats FeatureSets__ext_list.
Definition FeatureSets__ext_Format_list : FeatureSets__ext_Format_Type :=
  (FeatureSets__ext0__Format, (FeatureSets__ext1__Format, (FeatureSets__ext2__Format, (FeatureSets__ext3__Format, (FeatureSets__ext4__Format, (FeatureSets__ext5__Format, (FeatureSets__ext6__Format, (FeatureSets__ext7__Format, unit__Format)))))))).

Definition FeatureSets__list_type : Set := (seq_type FeatureSets__root_list) * (seq_ext_type FeatureSets__ext_list).
Definition FeatureSets__list_cond (z : FeatureSets__list_type) : Prop :=
        (seq_cond FeatureSets__root_list (fst z)) /\ (seq_ext_cond FeatureSets__ext_list (snd z)).
Definition FeatureSets__list_format : T_Format FeatureSets__list_type FeatureSets__list_cond :=
 (* Eval compute in *) seq_ext_format FeatureSets__root_list FeatureSets__root_Format_list FeatureSets__ext_list FeatureSets__ext_Format_list.

Opaque FeatureSets__list_format.
Definition FeatureSets__F1 (z : FeatureSets__Type) : FeatureSets__list_type :=
  (((FeatureSets__featureSetsDownlink z, (FeatureSets__featureSetsDownlinkPerCC z, (FeatureSets__featureSetsUplink z, (FeatureSets__featureSetsUplinkPerCC z, tt))))), (
(FeatureSets__ext0 z, (FeatureSets__ext1 z, (FeatureSets__ext2 z, (FeatureSets__ext3 z, (FeatureSets__ext4 z, (FeatureSets__ext5 z, (FeatureSets__ext6 z, (FeatureSets__ext7 z, tt)))))))))).
Definition FeatureSets__F2 (y : FeatureSets__list_type) : FeatureSets__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _)))))))))=>
    make__FeatureSets__Type j0 j1 j2 j3 i0 i1 i2 i3 i4 i5 i6 i7
  end.
Definition FeatureSets__helper1 : (forall a : FeatureSets__Type, FeatureSets__cond a -> FeatureSets__list_cond (FeatureSets__F1 a)).
                     intros. destruct a. auto. Qed.
Definition FeatureSets__helper2 : (forall a : FeatureSets__Type, FeatureSets__F2 (FeatureSets__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition FeatureSets__helper3 : (forall b : FeatureSets__list_type, FeatureSets__list_cond b -> FeatureSets__cond (FeatureSets__F2 b) /\ FeatureSets__F1 (FeatureSets__F2 b) = b).
                     intros. destruct b as [y y1]. unfold FeatureSets__cond, FeatureSets__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition FeatureSets__Format : T_Format FeatureSets__Type FeatureSets__cond :=
 proj2_format FeatureSets__cond FeatureSets__list_format  FeatureSets__F1 FeatureSets__F2 FeatureSets__helper1 FeatureSets__helper2 FeatureSets__helper3.

Opaque FeatureSets__cond FeatureSets__Format.

