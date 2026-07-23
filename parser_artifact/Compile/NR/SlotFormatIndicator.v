Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Lemma SlotFormatIndicator__dci_PayloadSize__helper1 : (1 <= maxSFI_DCI_PayloadSize)%Z. unfold maxSFI_DCI_PayloadSize.
 lia. Qed.
Lemma SlotFormatIndicator__dci_PayloadSize__helper2 : to_bit_sz (Z.to_nat (maxSFI_DCI_PayloadSize - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSFI_DCI_PayloadSize - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__dci_PayloadSize__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__dci_PayloadSize__Type := Z.
Definition SlotFormatIndicator__dci_PayloadSize__cond := (fun z => (1 <= z <= maxSFI_DCI_PayloadSize)%Z).
Require Import NR.SlotFormatCombinationsPerCell.

Opaque SlotFormatCombinationsPerCell__cond SlotFormatCombinationsPerCell__Format.

Definition SlotFormatIndicator__slotFormatCombToAddModList__Type := list SlotFormatCombinationsPerCell__Type.

Lemma SlotFormatIndicator__slotFormatCombToAddModList__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroup)%Z. unfold maxNrofAggregatedCellsPerCellGroup.
 lia. Qed.
Lemma SlotFormatIndicator__slotFormatCombToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__slotFormatCombToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__slotFormatCombToAddModList__cond (z : SlotFormatIndicator__slotFormatCombToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroup)%Z /\ (list_and SlotFormatCombinationsPerCell__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition SlotFormatIndicator__slotFormatCombToReleaseList__Type := list ServCellIndex__Type.

Lemma SlotFormatIndicator__slotFormatCombToReleaseList__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroup)%Z. unfold maxNrofAggregatedCellsPerCellGroup.
 lia. Qed.
Lemma SlotFormatIndicator__slotFormatCombToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__slotFormatCombToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__slotFormatCombToReleaseList__cond (z : SlotFormatIndicator__slotFormatCombToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroup)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.AvailableRB_SetsPerCell_r16.

Opaque AvailableRB_SetsPerCell_r16__cond AvailableRB_SetsPerCell_r16__Format.

Definition SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__Type := list AvailableRB_SetsPerCell_r16__Type.

Lemma SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroup)%Z. unfold maxNrofAggregatedCellsPerCellGroup.
 lia. Qed.
Lemma SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__cond (z : SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroup)%Z /\ (list_and AvailableRB_SetsPerCell_r16__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__Type := list ServCellIndex__Type.

Lemma SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroup)%Z. unfold maxNrofAggregatedCellsPerCellGroup.
 lia. Qed.
Lemma SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__cond (z : SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroup)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.SearchSpaceSwitchTrigger_r16.

Opaque SearchSpaceSwitchTrigger_r16__cond SearchSpaceSwitchTrigger_r16__Format.

Definition SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__Type := list SearchSpaceSwitchTrigger_r16__Type.

Lemma SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__cond (z : SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and SearchSpaceSwitchTrigger_r16__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__Type := list ServCellIndex__Type.

Lemma SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__cond (z : SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.CO_DurationsPerCell_r16.

Opaque CO_DurationsPerCell_r16__cond CO_DurationsPerCell_r16__Format.

Definition SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__Type := list CO_DurationsPerCell_r16__Type.

Lemma SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroup)%Z. unfold maxNrofAggregatedCellsPerCellGroup.
 lia. Qed.
Lemma SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__cond (z : SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroup)%Z /\ (list_and CO_DurationsPerCell_r16__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__Type := list ServCellIndex__Type.

Lemma SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroup)%Z. unfold maxNrofAggregatedCellsPerCellGroup.
 lia. Qed.
Lemma SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__cond (z : SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroup)%Z /\ (list_and ServCellIndex__cond z) .

Record SlotFormatIndicator__ext0O__Type : Set :=
  make__SlotFormatIndicator__ext0O__Type {
    SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16 : option SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__Type ;
    SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16 : option SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__Type ;
    SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16 : option SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__Type ;
    SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16 : option SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__Type ;
    SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16 : option SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__Type ;
    SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16 : option SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__Type ;
}.
Definition SlotFormatIndicator__ext0O__list := (
 Opt SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__Type SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__cond ::
 Opt SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__Type SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__cond ::
 Opt SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__Type SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__cond ::
 Opt SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__Type SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__cond ::
 Opt SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__Type SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__cond ::
 Opt SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__Type SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__cond ::
 nil).
Definition SlotFormatIndicator__ext0O__cond z := 
  opt_cond SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__cond (SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16 z) /\
  opt_cond SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__cond (SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16 z) /\
  opt_cond SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__cond (SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16 z) /\
  opt_cond SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__cond (SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16 z) /\
  opt_cond SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__cond (SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16 z) /\
  opt_cond SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__cond (SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16 z) /\
  True.

Definition SlotFormatIndicator__ext0__Type := SlotFormatIndicator__ext0O__Type.
Definition SlotFormatIndicator__ext0__cond := SlotFormatIndicator__ext0O__cond.

Require Import NR.SearchSpaceSwitchTrigger_r16.

Opaque SearchSpaceSwitchTrigger_r16__cond SearchSpaceSwitchTrigger_r16__Format.

Definition SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__Type := list SearchSpaceSwitchTrigger_r16__Type.

Lemma SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroupMinus4_r16)%Z. unfold maxNrofAggregatedCellsPerCellGroupMinus4_r16.
 lia. Qed.
Lemma SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroupMinus4_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroupMinus4_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__cond (z : SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroupMinus4_r16)%Z /\ (list_and SearchSpaceSwitchTrigger_r16__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__Type := list ServCellIndex__Type.

Lemma SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroupMinus4_r16)%Z. unfold maxNrofAggregatedCellsPerCellGroupMinus4_r16.
 lia. Qed.
Lemma SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroupMinus4_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroupMinus4_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__cond (z : SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroupMinus4_r16)%Z /\ (list_and ServCellIndex__cond z) .

Record SlotFormatIndicator__ext1O__Type : Set :=
  make__SlotFormatIndicator__ext1O__Type {
    SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16 : option SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__Type ;
    SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16 : option SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__Type ;
}.
Definition SlotFormatIndicator__ext1O__list := (
 Opt SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__Type SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__cond ::
 Opt SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__Type SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__cond ::
 nil).
Definition SlotFormatIndicator__ext1O__cond z := 
  opt_cond SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__cond (SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16 z) /\
  opt_cond SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__cond (SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16 z) /\
  True.

Definition SlotFormatIndicator__ext1__Type := SlotFormatIndicator__ext1O__Type.
Definition SlotFormatIndicator__ext1__cond := SlotFormatIndicator__ext1O__cond.

Require Import NR.CO_DurationsPerCell_r17.

Opaque CO_DurationsPerCell_r17__cond CO_DurationsPerCell_r17__Format.

Definition SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__Type := list CO_DurationsPerCell_r17__Type.

Lemma SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__helper1 : (0 <= 1 <= maxNrofAggregatedCellsPerCellGroup)%Z. unfold maxNrofAggregatedCellsPerCellGroup.
 lia. Qed.
Lemma SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofAggregatedCellsPerCellGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAggregatedCellsPerCellGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__cond (z : SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAggregatedCellsPerCellGroup)%Z /\ (list_and CO_DurationsPerCell_r17__cond z) .

Record SlotFormatIndicator__ext2O__Type : Set :=
  make__SlotFormatIndicator__ext2O__Type {
    SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17 : option SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__Type ;
}.
Definition SlotFormatIndicator__ext2O__list := (
 Opt SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__Type SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__cond ::
 nil).
Definition SlotFormatIndicator__ext2O__cond z := 
  opt_cond SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__cond (SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17 z) /\
  True.

Definition SlotFormatIndicator__ext2__Type := SlotFormatIndicator__ext2O__Type.
Definition SlotFormatIndicator__ext2__cond := SlotFormatIndicator__ext2O__cond.

Record SlotFormatIndicator__Type : Set :=
  make__SlotFormatIndicator__Type {
    SlotFormatIndicator__sfi_RNTI : RNTI_Value__Type ;
    SlotFormatIndicator__dci_PayloadSize : Z ;
    SlotFormatIndicator__slotFormatCombToAddModList : option SlotFormatIndicator__slotFormatCombToAddModList__Type ;
    SlotFormatIndicator__slotFormatCombToReleaseList : option SlotFormatIndicator__slotFormatCombToReleaseList__Type ;
    SlotFormatIndicator__ext0 : option SlotFormatIndicator__ext0__Type ;
    SlotFormatIndicator__ext1 : option SlotFormatIndicator__ext1__Type ;
    SlotFormatIndicator__ext2 : option SlotFormatIndicator__ext2__Type ;
}.
Definition SlotFormatIndicator__root_list : list seq_elem := (
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Nor Z SlotFormatIndicator__dci_PayloadSize__cond ::
 Opt SlotFormatIndicator__slotFormatCombToAddModList__Type SlotFormatIndicator__slotFormatCombToAddModList__cond ::
 Opt SlotFormatIndicator__slotFormatCombToReleaseList__Type SlotFormatIndicator__slotFormatCombToReleaseList__cond ::
 nil).
Definition SlotFormatIndicator__ext_list : list typ := (
  typ_cons SlotFormatIndicator__ext0__Type SlotFormatIndicator__ext0__cond ::
  typ_cons SlotFormatIndicator__ext1__Type SlotFormatIndicator__ext1__cond ::
  typ_cons SlotFormatIndicator__ext2__Type SlotFormatIndicator__ext2__cond ::
  nil).
Definition SlotFormatIndicator__cond (z : SlotFormatIndicator__Type) := 
(  RNTI_Value__cond (SlotFormatIndicator__sfi_RNTI z) /\
  SlotFormatIndicator__dci_PayloadSize__cond (SlotFormatIndicator__dci_PayloadSize z) /\
  opt_cond SlotFormatIndicator__slotFormatCombToAddModList__cond (SlotFormatIndicator__slotFormatCombToAddModList z) /\
  opt_cond SlotFormatIndicator__slotFormatCombToReleaseList__cond (SlotFormatIndicator__slotFormatCombToReleaseList z) /\
  True) /\ 
(  opt_cond SlotFormatIndicator__ext0__cond (SlotFormatIndicator__ext0 z) /\
  opt_cond SlotFormatIndicator__ext1__cond (SlotFormatIndicator__ext1 z) /\
  opt_cond SlotFormatIndicator__ext2__cond (SlotFormatIndicator__ext2 z) /\
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
Definition SlotFormatIndicator__dci_PayloadSize__Format : T_Format Z SlotFormatIndicator__dci_PayloadSize__cond :=
 ranged_int_format (1) (maxSFI_DCI_PayloadSize) SlotFormatIndicator__dci_PayloadSize__helper1 SlotFormatIndicator__dci_PayloadSize__helper2.

Opaque SlotFormatIndicator__dci_PayloadSize__cond SlotFormatIndicator__dci_PayloadSize__Format.

Definition SlotFormatIndicator__slotFormatCombToAddModList__Format : T_Format SlotFormatIndicator__slotFormatCombToAddModList__Type SlotFormatIndicator__slotFormatCombToAddModList__cond := seq_of_format SlotFormatCombinationsPerCell__Format 1 maxNrofAggregatedCellsPerCellGroup SlotFormatIndicator__slotFormatCombToAddModList__helper1 SlotFormatIndicator__slotFormatCombToAddModList__helper2.

Opaque SlotFormatIndicator__slotFormatCombToAddModList__cond SlotFormatIndicator__slotFormatCombToAddModList__Format.

Definition SlotFormatIndicator__slotFormatCombToReleaseList__Format : T_Format SlotFormatIndicator__slotFormatCombToReleaseList__Type SlotFormatIndicator__slotFormatCombToReleaseList__cond := seq_of_format ServCellIndex__Format 1 maxNrofAggregatedCellsPerCellGroup SlotFormatIndicator__slotFormatCombToReleaseList__helper1 SlotFormatIndicator__slotFormatCombToReleaseList__helper2.

Opaque SlotFormatIndicator__slotFormatCombToReleaseList__cond SlotFormatIndicator__slotFormatCombToReleaseList__Format.

Definition SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__Format : T_Format SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__Type SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__cond := seq_of_format AvailableRB_SetsPerCell_r16__Format 1 maxNrofAggregatedCellsPerCellGroup SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__helper1 SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__helper2.

Opaque SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__cond SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__Format.

Definition SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__Format : T_Format SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__Type SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__cond := seq_of_format ServCellIndex__Format 1 maxNrofAggregatedCellsPerCellGroup SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__helper1 SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__helper2.

Opaque SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__cond SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__Format.

Definition SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__Format : T_Format SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__Type SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__cond := seq_of_format SearchSpaceSwitchTrigger_r16__Format 1 4 SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__helper1 SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__helper2.

Opaque SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__cond SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__Format.

Definition SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__Format : T_Format SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__Type SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__cond := seq_of_format ServCellIndex__Format 1 4 SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__helper1 SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__helper2.

Opaque SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__cond SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__Format.

Definition SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__Format : T_Format SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__Type SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__cond := seq_of_format CO_DurationsPerCell_r16__Format 1 maxNrofAggregatedCellsPerCellGroup SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__helper1 SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__helper2.

Opaque SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__cond SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__Format.

Definition SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__Format : T_Format SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__Type SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__cond := seq_of_format ServCellIndex__Format 1 maxNrofAggregatedCellsPerCellGroup SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__helper1 SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__helper2.

Opaque SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__cond SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__Format.


Definition SlotFormatIndicator__ext0O__Format_Type := Eval cbn in seq_format_prod SlotFormatIndicator__ext0O__list.
Definition SlotFormatIndicator__ext0O__Format_list : SlotFormatIndicator__ext0O__Format_Type :=
  (SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16__Format, (SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16__Format, (SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16__Format, (SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16__Format, (SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16__Format, (SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16__Format, unit_format)))))).
Definition SlotFormatIndicator__ext0O__list__Format := (*Eval compute in *) seq_format SlotFormatIndicator__ext0O__list SlotFormatIndicator__ext0O__Format_list.
Definition SlotFormatIndicator__ext0O__F1 z :=
  (SlotFormatIndicator__ext0O__availableRB_SetsToAddModList_r16 z, (SlotFormatIndicator__ext0O__availableRB_SetsToReleaseList_r16 z, (SlotFormatIndicator__ext0O__switchTriggerToAddModList_r16 z, (SlotFormatIndicator__ext0O__switchTriggerToReleaseList_r16 z, (SlotFormatIndicator__ext0O__co_DurationsPerCellToAddModList_r16 z, (SlotFormatIndicator__ext0O__co_DurationsPerCellToReleaseList_r16 z, tt)))))).
Definition SlotFormatIndicator__ext0O__F2 (y : seq_type SlotFormatIndicator__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__SlotFormatIndicator__ext0O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma SlotFormatIndicator__ext0O__F1F2_cond (z : SlotFormatIndicator__ext0O__Type)
  : SlotFormatIndicator__ext0O__cond z ->
  (seq_cond SlotFormatIndicator__ext0O__list (SlotFormatIndicator__ext0O__F1 z)).
intro H. unfold SlotFormatIndicator__ext0O__cond in H. simpl. auto. Qed.
Lemma SlotFormatIndicator__ext0O__F1F2_cond2 (z : SlotFormatIndicator__ext0O__Type)
 : SlotFormatIndicator__ext0O__F2 (SlotFormatIndicator__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SlotFormatIndicator__ext0O__F2F1_cond (y : seq_type SlotFormatIndicator__ext0O__list)
  : seq_cond SlotFormatIndicator__ext0O__list y ->
 (SlotFormatIndicator__ext0O__cond (SlotFormatIndicator__ext0O__F2 y)) /\  SlotFormatIndicator__ext0O__F1 (SlotFormatIndicator__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SlotFormatIndicator__ext0O__cond. simpl in *. auto.
 - simpl. unfold SlotFormatIndicator__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SlotFormatIndicator__ext0O__Format : T_Format SlotFormatIndicator__ext0O__Type SlotFormatIndicator__ext0O__cond :=
        proj2_format  SlotFormatIndicator__ext0O__cond SlotFormatIndicator__ext0O__list__Format
    SlotFormatIndicator__ext0O__F1 SlotFormatIndicator__ext0O__F2 SlotFormatIndicator__ext0O__F1F2_cond  SlotFormatIndicator__ext0O__F1F2_cond2 SlotFormatIndicator__ext0O__F2F1_cond.
Opaque SlotFormatIndicator__ext0O__cond SlotFormatIndicator__ext0O__Format.

Definition SlotFormatIndicator__ext0__check_all_none (b : SlotFormatIndicator__ext0O__Type) : bool :=
match b with 
  | make__SlotFormatIndicator__ext0O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition SlotFormatIndicator__ext0__Format : T_Format SlotFormatIndicator__ext0__Type SlotFormatIndicator__ext0__cond :=
  restrict_add_format SlotFormatIndicator__ext0__check_all_none SlotFormatIndicator__ext0O__Format.

Opaque SlotFormatIndicator__ext0__cond SlotFormatIndicator__ext0__Format.

Definition SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__Format : T_Format SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__Type SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__cond := seq_of_format SearchSpaceSwitchTrigger_r16__Format 1 maxNrofAggregatedCellsPerCellGroupMinus4_r16 SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__helper1 SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__helper2.

Opaque SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__cond SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__Format.

Definition SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__Format : T_Format SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__Type SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__cond := seq_of_format ServCellIndex__Format 1 maxNrofAggregatedCellsPerCellGroupMinus4_r16 SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__helper1 SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__helper2.

Opaque SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__cond SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__Format.


Definition SlotFormatIndicator__ext1O__Format_Type := Eval cbn in seq_format_prod SlotFormatIndicator__ext1O__list.
Definition SlotFormatIndicator__ext1O__Format_list : SlotFormatIndicator__ext1O__Format_Type :=
  (SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16__Format, (SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16__Format, unit_format)).
Definition SlotFormatIndicator__ext1O__list__Format := (*Eval compute in *) seq_format SlotFormatIndicator__ext1O__list SlotFormatIndicator__ext1O__Format_list.
Definition SlotFormatIndicator__ext1O__F1 z :=
  (SlotFormatIndicator__ext1O__switchTriggerToAddModListSizeExt_r16 z, (SlotFormatIndicator__ext1O__switchTriggerToReleaseListSizeExt_r16 z, tt)).
Definition SlotFormatIndicator__ext1O__F2 (y : seq_type SlotFormatIndicator__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SlotFormatIndicator__ext1O__Type i0 i1
  end.
Lemma SlotFormatIndicator__ext1O__F1F2_cond (z : SlotFormatIndicator__ext1O__Type)
  : SlotFormatIndicator__ext1O__cond z ->
  (seq_cond SlotFormatIndicator__ext1O__list (SlotFormatIndicator__ext1O__F1 z)).
intro H. unfold SlotFormatIndicator__ext1O__cond in H. simpl. auto. Qed.
Lemma SlotFormatIndicator__ext1O__F1F2_cond2 (z : SlotFormatIndicator__ext1O__Type)
 : SlotFormatIndicator__ext1O__F2 (SlotFormatIndicator__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SlotFormatIndicator__ext1O__F2F1_cond (y : seq_type SlotFormatIndicator__ext1O__list)
  : seq_cond SlotFormatIndicator__ext1O__list y ->
 (SlotFormatIndicator__ext1O__cond (SlotFormatIndicator__ext1O__F2 y)) /\  SlotFormatIndicator__ext1O__F1 (SlotFormatIndicator__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SlotFormatIndicator__ext1O__cond. simpl in *. auto.
 - simpl. unfold SlotFormatIndicator__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SlotFormatIndicator__ext1O__Format : T_Format SlotFormatIndicator__ext1O__Type SlotFormatIndicator__ext1O__cond :=
        proj2_format  SlotFormatIndicator__ext1O__cond SlotFormatIndicator__ext1O__list__Format
    SlotFormatIndicator__ext1O__F1 SlotFormatIndicator__ext1O__F2 SlotFormatIndicator__ext1O__F1F2_cond  SlotFormatIndicator__ext1O__F1F2_cond2 SlotFormatIndicator__ext1O__F2F1_cond.
Opaque SlotFormatIndicator__ext1O__cond SlotFormatIndicator__ext1O__Format.

Definition SlotFormatIndicator__ext1__check_all_none (b : SlotFormatIndicator__ext1O__Type) : bool :=
match b with 
  | make__SlotFormatIndicator__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition SlotFormatIndicator__ext1__Format : T_Format SlotFormatIndicator__ext1__Type SlotFormatIndicator__ext1__cond :=
  restrict_add_format SlotFormatIndicator__ext1__check_all_none SlotFormatIndicator__ext1O__Format.

Opaque SlotFormatIndicator__ext1__cond SlotFormatIndicator__ext1__Format.

Definition SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__Format : T_Format SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__Type SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__cond := seq_of_format CO_DurationsPerCell_r17__Format 1 maxNrofAggregatedCellsPerCellGroup SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__helper1 SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__helper2.

Opaque SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__cond SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__Format.


Definition SlotFormatIndicator__ext2O__Format_Type := Eval cbn in seq_format_prod SlotFormatIndicator__ext2O__list.
Definition SlotFormatIndicator__ext2O__Format_list : SlotFormatIndicator__ext2O__Format_Type :=
  (SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17__Format, unit_format).
Definition SlotFormatIndicator__ext2O__list__Format := (*Eval compute in *) seq_format SlotFormatIndicator__ext2O__list SlotFormatIndicator__ext2O__Format_list.
Definition SlotFormatIndicator__ext2O__F1 z :=
  (SlotFormatIndicator__ext2O__co_DurationsPerCellToAddModList_r17 z, tt).
Definition SlotFormatIndicator__ext2O__F2 (y : seq_type SlotFormatIndicator__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__SlotFormatIndicator__ext2O__Type i0
  end.
Lemma SlotFormatIndicator__ext2O__F1F2_cond (z : SlotFormatIndicator__ext2O__Type)
  : SlotFormatIndicator__ext2O__cond z ->
  (seq_cond SlotFormatIndicator__ext2O__list (SlotFormatIndicator__ext2O__F1 z)).
intro H. unfold SlotFormatIndicator__ext2O__cond in H. simpl. auto. Qed.
Lemma SlotFormatIndicator__ext2O__F1F2_cond2 (z : SlotFormatIndicator__ext2O__Type)
 : SlotFormatIndicator__ext2O__F2 (SlotFormatIndicator__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SlotFormatIndicator__ext2O__F2F1_cond (y : seq_type SlotFormatIndicator__ext2O__list)
  : seq_cond SlotFormatIndicator__ext2O__list y ->
 (SlotFormatIndicator__ext2O__cond (SlotFormatIndicator__ext2O__F2 y)) /\  SlotFormatIndicator__ext2O__F1 (SlotFormatIndicator__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SlotFormatIndicator__ext2O__cond. simpl in *. auto.
 - simpl. unfold SlotFormatIndicator__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SlotFormatIndicator__ext2O__Format : T_Format SlotFormatIndicator__ext2O__Type SlotFormatIndicator__ext2O__cond :=
        proj2_format  SlotFormatIndicator__ext2O__cond SlotFormatIndicator__ext2O__list__Format
    SlotFormatIndicator__ext2O__F1 SlotFormatIndicator__ext2O__F2 SlotFormatIndicator__ext2O__F1F2_cond  SlotFormatIndicator__ext2O__F1F2_cond2 SlotFormatIndicator__ext2O__F2F1_cond.
Opaque SlotFormatIndicator__ext2O__cond SlotFormatIndicator__ext2O__Format.

Definition SlotFormatIndicator__ext2__check_all_none (b : SlotFormatIndicator__ext2O__Type) : bool :=
match b with 
  | make__SlotFormatIndicator__ext2O__Type None  => false 
  | _ => true 
 end.
Definition SlotFormatIndicator__ext2__Format : T_Format SlotFormatIndicator__ext2__Type SlotFormatIndicator__ext2__cond :=
  restrict_add_format SlotFormatIndicator__ext2__check_all_none SlotFormatIndicator__ext2O__Format.

Opaque SlotFormatIndicator__ext2__cond SlotFormatIndicator__ext2__Format.


Definition SlotFormatIndicator__root_Format_Type := Eval cbn in seq_format_prod SlotFormatIndicator__root_list.
Definition SlotFormatIndicator__root_Format_list : SlotFormatIndicator__root_Format_Type :=
  (RNTI_Value__Format, (SlotFormatIndicator__dci_PayloadSize__Format, (SlotFormatIndicator__slotFormatCombToAddModList__Format, (SlotFormatIndicator__slotFormatCombToReleaseList__Format, unit_format)))).

Definition SlotFormatIndicator__ext_Format_Type := Eval cbn in get_formats SlotFormatIndicator__ext_list.
Definition SlotFormatIndicator__ext_Format_list : SlotFormatIndicator__ext_Format_Type :=
  (SlotFormatIndicator__ext0__Format, (SlotFormatIndicator__ext1__Format, (SlotFormatIndicator__ext2__Format, unit__Format))).

Definition SlotFormatIndicator__list_type : Set := (seq_type SlotFormatIndicator__root_list) * (seq_ext_type SlotFormatIndicator__ext_list).
Definition SlotFormatIndicator__list_cond (z : SlotFormatIndicator__list_type) : Prop :=
        (seq_cond SlotFormatIndicator__root_list (fst z)) /\ (seq_ext_cond SlotFormatIndicator__ext_list (snd z)).
Definition SlotFormatIndicator__list_format : T_Format SlotFormatIndicator__list_type SlotFormatIndicator__list_cond :=
 (* Eval compute in *) seq_ext_format SlotFormatIndicator__root_list SlotFormatIndicator__root_Format_list SlotFormatIndicator__ext_list SlotFormatIndicator__ext_Format_list.

Opaque SlotFormatIndicator__list_format.
Definition SlotFormatIndicator__F1 (z : SlotFormatIndicator__Type) : SlotFormatIndicator__list_type :=
  (((SlotFormatIndicator__sfi_RNTI z, (SlotFormatIndicator__dci_PayloadSize z, (SlotFormatIndicator__slotFormatCombToAddModList z, (SlotFormatIndicator__slotFormatCombToReleaseList z, tt))))), (
(SlotFormatIndicator__ext0 z, (SlotFormatIndicator__ext1 z, (SlotFormatIndicator__ext2 z, tt))))).
Definition SlotFormatIndicator__F2 (y : SlotFormatIndicator__list_type) : SlotFormatIndicator__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, (i2, _))))=>
    make__SlotFormatIndicator__Type j0 j1 j2 j3 i0 i1 i2
  end.
Definition SlotFormatIndicator__helper1 : (forall a : SlotFormatIndicator__Type, SlotFormatIndicator__cond a -> SlotFormatIndicator__list_cond (SlotFormatIndicator__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SlotFormatIndicator__helper2 : (forall a : SlotFormatIndicator__Type, SlotFormatIndicator__F2 (SlotFormatIndicator__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SlotFormatIndicator__helper3 : (forall b : SlotFormatIndicator__list_type, SlotFormatIndicator__list_cond b -> SlotFormatIndicator__cond (SlotFormatIndicator__F2 b) /\ SlotFormatIndicator__F1 (SlotFormatIndicator__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SlotFormatIndicator__cond, SlotFormatIndicator__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SlotFormatIndicator__Format : T_Format SlotFormatIndicator__Type SlotFormatIndicator__cond :=
 proj2_format SlotFormatIndicator__cond SlotFormatIndicator__list_format  SlotFormatIndicator__F1 SlotFormatIndicator__F2 SlotFormatIndicator__helper1 SlotFormatIndicator__helper2 SlotFormatIndicator__helper3.

Opaque SlotFormatIndicator__cond SlotFormatIndicator__Format.

