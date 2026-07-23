Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__Type := Z.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__Type := Z.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__Type := Z.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__Type := Z.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__Type := Z.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__cond := (fun z => (0 <= z <= 10239)%Z).
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__helper1 : (0 <= 20479)%Z.  lia. Qed.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__helper2 : to_bit_sz (Z.to_nat (20479 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20479 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__Type := Z.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__cond := (fun z => (0 <= z <= 20479)%Z).

Inductive SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type : Set :=
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32 : Z -> SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64 : Z -> SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128 : Z -> SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120 : Z -> SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240 : Z -> SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480 : Z -> SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type
.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list : list typ := (
typ_cons Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__cond ::
typ_cons Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__cond ::
typ_cons Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__cond ::
typ_cons Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__cond ::
typ_cons Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__cond ::
typ_cons Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__cond ::
 nil).
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__cond (c : SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type) := 
  match c with
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32 t => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__cond t 
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64 t => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__cond t 
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128 t => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__cond t 
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120 t => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__cond t 
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240 t => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__cond t 
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480 t => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__cond t 
  end.

Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__len_helper1 : to_bit_sz (length SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__len_helper2 : 2 <= length2 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list.
 simpl. lia. Qed.
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__Type := bit_string_fixed.
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__Type := bit_string_fixed.
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).

Inductive SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type : Set :=
  | SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17 : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__Type -> SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type
  | SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17 : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__Type -> SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type
.
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list : list typ := (
typ_cons SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__Type SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__cond ::
typ_cons SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__Type SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__cond ::
 nil).
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__cond (c : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type) := 
  match c with
  | SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17 t => SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__cond t 
  | SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17 t => SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__cond t 
  end.

Lemma SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__len_helper1 : to_bit_sz (length SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__len_helper2 : 2 <= length2 SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list.
 simpl. lia. Qed.
Lemma SearchSpaceExt_v1700__duration_r17__helper1 : (4 <= 20476)%Z.  lia. Qed.
Lemma SearchSpaceExt_v1700__duration_r17__helper2 : to_bit_sz (Z.to_nat (20476 - 4)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20476 - 4))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__duration_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__duration_r17__Type := Z.
Definition SearchSpaceExt_v1700__duration_r17__cond := (fun z => (4 <= z <= 20476)%Z).
Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Type : Set := make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Type {}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Type) := True.
Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type : Set :=
  make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type {
}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_list : list seq_elem := (
 nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_list : list typ := (
  nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type) := 
(  True) /\ 
(  True).

Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Type : Set := make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Type {}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Type) := True.
Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type : Set :=
  make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type {
}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_list : list seq_elem := (
 nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_list : list typ := (
  nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type) := 
(  True) /\ 
(  True).

Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Type : Set := make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Type {}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Type) := True.
Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type : Set :=
  make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type {
}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_list : list seq_elem := (
 nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_list : list typ := (
  nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type) := 
(  True) /\ 
(  True).

Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Type : Set := make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Type {}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Type) := True.
Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type : Set :=
  make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type {
}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_list : list seq_elem := (
 nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_list : list typ := (
  nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type) := 
(  True) /\ 
(  True).

Inductive SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Type : Set :=
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n0
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n1
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n2
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n3
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n4
.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__cond := (fun (_ : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Type) => True).
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__nat__helper.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F1 t :=
  match t with
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n0 => 0
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n1 => 1
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n2 => 2
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n3 => 3
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n4 => 4
  end.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F2 n :=
  match n with
  | 0 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n0
  | 1 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n1
  | 2 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n2
  | 3 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n3
  | 4 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n4
  | _ => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__n0
  end.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F1F2 : forall x : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Type, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F1 x <= 4) /\ SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F1 x) = x. imp_solve. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F2F1 : forall (y : nat) (H : y <= 4), SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Type : Set :=
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n0
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n1
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n2
.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__cond := (fun (_ : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Type) => True).
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__nat__helper.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F1 t :=
  match t with
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n0 => 0
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n1 => 1
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n2 => 2
  end.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F2 n :=
  match n with
  | 0 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n0
  | 1 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n1
  | 2 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n2
  | _ => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__n0
  end.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F1F2 : forall x : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Type, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F1 x <= 2) /\ SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F1 x) = x. imp_solve. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F2F1 : forall (y : nat) (H : y <= 2), SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Type : Set :=
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__n0
 | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__n1
.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__cond := (fun (_ : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Type) => True).
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__nat__helper.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F1 t :=
  match t with
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__n0 => 0
  | SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__n1 => 1
  end.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F2 n :=
  match n with
  | 0 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__n0
  | 1 => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__n1
  | _ => SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__n0
  end.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F1F2 : forall x : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Type, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F1 x <= 1) /\ SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F1 x) = x. imp_solve. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F2F1 : forall (y : nat) (H : y <= 1), SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F2 y) = y. enum_solve H y. Qed.

Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Type : Set :=
  make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Type {
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Type ;
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Type ;
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Type ;
}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list := (
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__cond ::
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__cond ::
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__cond ::
 nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond z := 
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17 z) /\
  True.

Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type : Set :=
  make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type {
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17 : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Type ;
}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_list : list seq_elem := (
 Nor SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond ::
 nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_list : list typ := (
  nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type) := 
(  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17 z) /\
  True) /\ 
(  True).

Record SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Type : Set :=
  make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Type {
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type ;
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type ;
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type ;
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type ;
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type ;
}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list := (
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond ::
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond ::
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond ::
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond ::
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond ::
 nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond z := 
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17 z) /\
  True.

Record SearchSpaceExt_v1700__searchSpaceType_r17__Type : Set :=
  make__SearchSpaceExt_v1700__searchSpaceType_r17__Type {
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17 : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Type ;
}.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__list := (
 Nor SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond ::
 nil).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__cond z := 
  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17 z) /\
  True.

Lemma SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__helper1 : (0 <= maxNrofSearchSpaceGroups_1_r17)%Z. unfold maxNrofSearchSpaceGroups_1_r17.
 lia. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofSearchSpaceGroups_1_r17 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSearchSpaceGroups_1_r17 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__Type := Z.
Definition SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__cond := (fun z => (0 <= z <= maxNrofSearchSpaceGroups_1_r17)%Z).
Definition SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__Type := list Z.

Lemma SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__helper1 : (0 <= 1 <= 3)%Z.  lia. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__cond (z : SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__Type) :=  (1 <= Z.of_nat (length z) <= 3)%Z /\ (list_and SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__cond z) .

Lemma SearchSpaceExt_v1700__searchSpaceLinkingId_r17__helper1 : (0 <= maxNrofSearchSpacesLinks_1_r17)%Z. unfold maxNrofSearchSpacesLinks_1_r17.
 lia. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceLinkingId_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSearchSpacesLinks_1_r17 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSearchSpacesLinks_1_r17 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpaceExt_v1700__searchSpaceLinkingId_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpaceExt_v1700__searchSpaceLinkingId_r17__Type := Z.
Definition SearchSpaceExt_v1700__searchSpaceLinkingId_r17__cond := (fun z => (0 <= z <= maxNrofSearchSpacesLinks_1_r17)%Z).
Record SearchSpaceExt_v1700__Type : Set :=
  make__SearchSpaceExt_v1700__Type {
    SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710 : option SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type ;
    SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17 : option SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type ;
    SearchSpaceExt_v1700__duration_r17 : option Z ;
    SearchSpaceExt_v1700__searchSpaceType_r17 : option SearchSpaceExt_v1700__searchSpaceType_r17__Type ;
    SearchSpaceExt_v1700__searchSpaceGroupIdList_r17 : option SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__Type ;
    SearchSpaceExt_v1700__searchSpaceLinkingId_r17 : option Z ;
}.
Definition SearchSpaceExt_v1700__list := (
 Opt SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__cond ::
 Opt SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__cond ::
 Opt Z SearchSpaceExt_v1700__duration_r17__cond ::
 Opt SearchSpaceExt_v1700__searchSpaceType_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__cond ::
 Opt SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__Type SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__cond ::
 Opt Z SearchSpaceExt_v1700__searchSpaceLinkingId_r17__cond ::
 nil).
Definition SearchSpaceExt_v1700__cond z := 
  opt_cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__cond (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710 z) /\
  opt_cond SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__cond (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17 z) /\
  opt_cond SearchSpaceExt_v1700__duration_r17__cond (SearchSpaceExt_v1700__duration_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceType_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__cond (SearchSpaceExt_v1700__searchSpaceGroupIdList_r17 z) /\
  opt_cond SearchSpaceExt_v1700__searchSpaceLinkingId_r17__cond (SearchSpaceExt_v1700__searchSpaceLinkingId_r17 z) /\
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
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__Format : T_Format Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__cond :=
 ranged_int_format (0) (31) SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__helper1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__helper2.

Opaque SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__Format.

Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__Format : T_Format Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__cond :=
 ranged_int_format (0) (63) SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__helper1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__helper2.

Opaque SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__Format.

Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__Format : T_Format Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__cond :=
 ranged_int_format (0) (127) SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__helper1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__helper2.

Opaque SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__Format.

Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__Format : T_Format Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__cond :=
 ranged_int_format (0) (5119) SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__helper1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__helper2.

Opaque SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__Format.

Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__Format : T_Format Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__cond :=
 ranged_int_format (0) (10239) SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__helper1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__helper2.

Opaque SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__Format.

Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__Format : T_Format Z SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__cond :=
 ranged_int_format (0) (20479) SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__helper1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__helper2.

Opaque SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__Format.


Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Format_Type := Eval cbn in get_formats SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Format_list : SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Format_Type :=
  (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32__Format, (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64__Format, (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128__Format, (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120__Format, (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240__Format, (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480__Format, unit__Format)))))).
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list__Format := Eval compute in choice_format SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__len_helper1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__len_helper2  SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Format_list.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F1 (z : SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type) : (choice SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list) :=
  match z with
   | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32 t => existT _ 0 t
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64 t => existT _ 1 t
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128 t => existT _ 2 t
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120 t => existT _ 3 t
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240 t => existT _ 4 t
  | SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480 t => existT _ 5 t
  end.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__g := (fun n => typ_set (get_nth_typ SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list n)).
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F2 (y : choice SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list) : SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__g n -> SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type) with
    | 0 => fun (t : Z) => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl32 t 
    | 1 => fun (t : Z) => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl64 t 
    | 2 => fun (t : Z) => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl128 t 
    | 3 => fun (t : Z) => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl5120 t 
    | 4 => fun (t : Z) => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl10240 t 
    | 5 => fun (t : Z) => SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__sl20480 t 
 | (S (S (S (S (S (S n0)))))) => (fun (x' : nat) (t'' : SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__g (S (S (S (S (S (S x'))))))) =>let t' :=
           eq_rect (get_nth_typ SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list (S (S (S (S (S (S x')))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list (S (S (S (S (S (S x'))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))) in match t' return SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type with end) n0
           end t0).

Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__helper2 :  forall (y : SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type), SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__cond y -> choice_cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__helper3 :  forall (y : SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type), SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F2 (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__helper4 : (forall b : choice SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list, choice_cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list b -> SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__cond (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F2 b) /\ SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F1 (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F2.
Definition SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Format : T_Format SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Type SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__cond :=
  (* Eval compute in *) proj2_format SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__list__Format SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F1 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__F2 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__helper2 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__helper3 SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__helper4.
Opaque SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__cond SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Format.

Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__Format : T_Format SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__Type SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__cond SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__Format.

Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__Format : T_Format SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__Type SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__cond SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__Format.


Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Format_Type := Eval cbn in get_formats SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list.
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Format_list : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Format_Type :=
  (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__Format, (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__Format, unit__Format)).
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list__Format := Eval compute in choice_format SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__len_helper1 SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__len_helper2  SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Format_list.
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F1 (z : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type) : (choice SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list) :=
  match z with
   | SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17 t => existT _ 0 t
  | SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17 t => existT _ 1 t
  end.
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__g := (fun n => typ_set (get_nth_typ SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list n)).
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F2 (y : choice SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list) : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__g n -> SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type) with
    | 0 => fun (t : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17__Type) => SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength4_r17 t 
    | 1 => fun (t : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17__Type) => SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__slotGroupLength8_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type with end) n0
           end t0).

Lemma SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__helper2 :  forall (y : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type), SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__cond y -> choice_cond SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__helper3 :  forall (y : SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type), SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F2 (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__helper4 : (forall b : choice SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list, choice_cond SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list b -> SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__cond (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F2 b) /\ SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F1 (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F1 SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F2.
Definition SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Format : T_Format SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Type SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__cond :=
  (* Eval compute in *) proj2_format SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__cond SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__list__Format SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F1 SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__F2 SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__helper2 SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__helper3 SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__helper4.
Opaque SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__cond SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Format.

Definition SearchSpaceExt_v1700__duration_r17__Format : T_Format Z SearchSpaceExt_v1700__duration_r17__cond :=
 ranged_int_format (4) (20476) SearchSpaceExt_v1700__duration_r17__helper1 SearchSpaceExt_v1700__duration_r17__helper2.

Opaque SearchSpaceExt_v1700__duration_r17__cond SearchSpaceExt_v1700__duration_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__helper : forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Type, True -> True /\ make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Type)
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__helper unit_unique (fun _ => left I).

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root__Format.


Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_Format_Type :=
  unit_format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_Format_Type := Eval cbn in get_formats SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_Format_Type :=
  unit__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_type : Set := (seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_list) * (seq_ext_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_list).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_type) : Prop :=
        (seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_list (fst z)) /\ (seq_ext_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_list (snd z)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__root_Format_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__ext_Format_list.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_format.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F1 (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_type :=
  ((tt), (
tt)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F2 (y : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type :=
  match y with
  | (_, _)=>
    make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type
  end.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__helper1 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond a -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__helper2 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__helper3 : (forall b : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_cond b -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F2 b) /\ SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond :=
 proj2_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__list_format  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__helper1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__helper2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__helper3.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__helper : forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Type, True -> True /\ make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Type)
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__helper unit_unique (fun _ => left I).

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root__Format.


Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_Format_Type :=
  unit_format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_Format_Type := Eval cbn in get_formats SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_Format_Type :=
  unit__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_type : Set := (seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_list) * (seq_ext_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_list).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_type) : Prop :=
        (seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_list (fst z)) /\ (seq_ext_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_list (snd z)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__root_Format_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__ext_Format_list.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_format.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F1 (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_type :=
  ((tt), (
tt)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F2 (y : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type :=
  match y with
  | (_, _)=>
    make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type
  end.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__helper1 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond a -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__helper2 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__helper3 : (forall b : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_cond b -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F2 b) /\ SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond :=
 proj2_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__list_format  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__helper1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__helper2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__helper3.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__helper : forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Type, True -> True /\ make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Type)
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__helper unit_unique (fun _ => left I).

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root__Format.


Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_Format_Type :=
  unit_format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_Format_Type := Eval cbn in get_formats SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_Format_Type :=
  unit__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_type : Set := (seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_list) * (seq_ext_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_list).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_type) : Prop :=
        (seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_list (fst z)) /\ (seq_ext_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_list (snd z)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__root_Format_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__ext_Format_list.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_format.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F1 (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_type :=
  ((tt), (
tt)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F2 (y : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type :=
  match y with
  | (_, _)=>
    make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type
  end.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__helper1 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond a -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__helper2 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__helper3 : (forall b : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_cond b -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F2 b) /\ SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond :=
 proj2_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__list_format  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__helper1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__helper2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__helper3.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__helper : forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Type, True -> True /\ make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Type)
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__helper unit_unique (fun _ => left I).

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root__Format.


Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_Format_Type :=
  unit_format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_Format_Type := Eval cbn in get_formats SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_Format_Type :=
  unit__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_type : Set := (seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_list) * (seq_ext_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_list).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_type) : Prop :=
        (seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_list (fst z)) /\ (seq_ext_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_list (snd z)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__root_Format_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__ext_Format_list.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_format.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F1 (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_type :=
  ((tt), (
tt)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F2 (y : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type :=
  match y with
  | (_, _)=>
    make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type
  end.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__helper1 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond a -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__helper2 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__helper3 : (forall b : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_cond b -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F2 b) /\ SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond :=
 proj2_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__list_format  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__helper1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__helper2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__helper3.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__nat__Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F1F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__F2F1.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__nat__Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F1F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__F2F1.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__nat__Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F1F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__F2F1.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Format.


Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Format_Type :=
  (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17__Format, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17__Format, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17__Format, unit_format))).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list__Format := (*Eval compute in *) seq_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Format_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1 z :=
  (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel4_r17 z, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel8_r17 z, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__aggregationLevel16_r17 z, tt))).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F2 (y : seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Type i0 i1 i2
  end.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1F2_cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Type)
  : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond z ->
  (seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1 z)).
intro H. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond in H. simpl. auto. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1F2_cond2 (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Type)
 : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F2F1_cond (y : seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list)
  : seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list y ->
 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F2 y)) /\  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond. simpl in *. auto.
 - simpl. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond :=
        proj2_format  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__list__Format
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1F2_cond  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F1F2_cond2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__F2F1_cond.
Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Format.


Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_Format_Type :=
  (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17__Format, unit_format).

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_Format_Type := Eval cbn in get_formats SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_Format_Type :=
  unit__Format.

Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_type : Set := (seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_list) * (seq_ext_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_list).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_type) : Prop :=
        (seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_list (fst z)) /\ (seq_ext_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_list (snd z)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__root_Format_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__ext_Format_list.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_format.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F1 (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_type :=
  (((SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__nrofCandidates_PEI_r17 z, tt)), (
tt)).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F2 (y : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_type) : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type :=
  match y with
  | ((j0, _), _)=>
    make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type j0
  end.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__helper1 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond a -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__helper2 : (forall a : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__helper3 : (forall b : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_type, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_cond b -> SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F2 b) /\ SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond, SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond :=
 proj2_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__list_format  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__helper1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__helper2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__helper3.

Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Format.


Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Format_Type :=
  (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17__Format, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17__Format, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17__Format, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17__Format, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17__Format, unit_format))))).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list__Format := (*Eval compute in *) seq_format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Format_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1 z :=
  (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_0_r17 z, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_r17 z, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_2_r17 z, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format4_1_AndFormat4_2_r17 z, (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__dci_Format2_7_r17 z, tt))))).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F2 (y : seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Type i0 i1 i2 i3 i4
  end.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1F2_cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Type)
  : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond z ->
  (seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1 z)).
intro H. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond in H. simpl. auto. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1F2_cond2 (z : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Type)
 : SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F2F1_cond (y : seq_type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list)
  : seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list y ->
 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F2 y)) /\  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond. simpl in *. auto.
 - simpl. unfold SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond :=
        proj2_format  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__list__Format
    SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1F2_cond  SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F1F2_cond2 SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__F2F1_cond.
Opaque SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Format.


Definition SearchSpaceExt_v1700__searchSpaceType_r17__Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__searchSpaceType_r17__list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__Format_list : SearchSpaceExt_v1700__searchSpaceType_r17__Format_Type :=
  (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17__Format, unit_format).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__list__Format := (*Eval compute in *) seq_format SearchSpaceExt_v1700__searchSpaceType_r17__list SearchSpaceExt_v1700__searchSpaceType_r17__Format_list.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__F1 z :=
  (SearchSpaceExt_v1700__searchSpaceType_r17__common_r17 z, tt).
Definition SearchSpaceExt_v1700__searchSpaceType_r17__F2 (y : seq_type SearchSpaceExt_v1700__searchSpaceType_r17__list) :=
  match y with
  | (i0, _)=>
    make__SearchSpaceExt_v1700__searchSpaceType_r17__Type i0
  end.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__F1F2_cond (z : SearchSpaceExt_v1700__searchSpaceType_r17__Type)
  : SearchSpaceExt_v1700__searchSpaceType_r17__cond z ->
  (seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__list (SearchSpaceExt_v1700__searchSpaceType_r17__F1 z)).
intro H. unfold SearchSpaceExt_v1700__searchSpaceType_r17__cond in H. simpl. auto. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__F1F2_cond2 (z : SearchSpaceExt_v1700__searchSpaceType_r17__Type)
 : SearchSpaceExt_v1700__searchSpaceType_r17__F2 (SearchSpaceExt_v1700__searchSpaceType_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpaceExt_v1700__searchSpaceType_r17__F2F1_cond (y : seq_type SearchSpaceExt_v1700__searchSpaceType_r17__list)
  : seq_cond SearchSpaceExt_v1700__searchSpaceType_r17__list y ->
 (SearchSpaceExt_v1700__searchSpaceType_r17__cond (SearchSpaceExt_v1700__searchSpaceType_r17__F2 y)) /\  SearchSpaceExt_v1700__searchSpaceType_r17__F1 (SearchSpaceExt_v1700__searchSpaceType_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpaceExt_v1700__searchSpaceType_r17__cond. simpl in *. auto.
 - simpl. unfold SearchSpaceExt_v1700__searchSpaceType_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpaceExt_v1700__searchSpaceType_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceType_r17__Type SearchSpaceExt_v1700__searchSpaceType_r17__cond :=
        proj2_format  SearchSpaceExt_v1700__searchSpaceType_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__list__Format
    SearchSpaceExt_v1700__searchSpaceType_r17__F1 SearchSpaceExt_v1700__searchSpaceType_r17__F2 SearchSpaceExt_v1700__searchSpaceType_r17__F1F2_cond  SearchSpaceExt_v1700__searchSpaceType_r17__F1F2_cond2 SearchSpaceExt_v1700__searchSpaceType_r17__F2F1_cond.
Opaque SearchSpaceExt_v1700__searchSpaceType_r17__cond SearchSpaceExt_v1700__searchSpaceType_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__Format : T_Format Z SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__cond :=
 ranged_int_format (0) (maxNrofSearchSpaceGroups_1_r17) SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__helper1 SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__helper2.

Opaque SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__cond SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__Format.

Definition SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__Format : T_Format SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__Type SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__cond := seq_of_format SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__seq_of__Format 1 3 SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__helper1 SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__helper2.

Opaque SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__cond SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__Format.

Definition SearchSpaceExt_v1700__searchSpaceLinkingId_r17__Format : T_Format Z SearchSpaceExt_v1700__searchSpaceLinkingId_r17__cond :=
 ranged_int_format (0) (maxNrofSearchSpacesLinks_1_r17) SearchSpaceExt_v1700__searchSpaceLinkingId_r17__helper1 SearchSpaceExt_v1700__searchSpaceLinkingId_r17__helper2.

Opaque SearchSpaceExt_v1700__searchSpaceLinkingId_r17__cond SearchSpaceExt_v1700__searchSpaceLinkingId_r17__Format.


Definition SearchSpaceExt_v1700__Format_Type := Eval cbn in seq_format_prod SearchSpaceExt_v1700__list.
Definition SearchSpaceExt_v1700__Format_list : SearchSpaceExt_v1700__Format_Type :=
  (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710__Format, (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17__Format, (SearchSpaceExt_v1700__duration_r17__Format, (SearchSpaceExt_v1700__searchSpaceType_r17__Format, (SearchSpaceExt_v1700__searchSpaceGroupIdList_r17__Format, (SearchSpaceExt_v1700__searchSpaceLinkingId_r17__Format, unit_format)))))).
Definition SearchSpaceExt_v1700__list__Format := (*Eval compute in *) seq_format SearchSpaceExt_v1700__list SearchSpaceExt_v1700__Format_list.
Definition SearchSpaceExt_v1700__F1 z :=
  (SearchSpaceExt_v1700__monitoringSlotPeriodicityAndOffset_v1710 z, (SearchSpaceExt_v1700__monitoringSlotsWithinSlotGroup_r17 z, (SearchSpaceExt_v1700__duration_r17 z, (SearchSpaceExt_v1700__searchSpaceType_r17 z, (SearchSpaceExt_v1700__searchSpaceGroupIdList_r17 z, (SearchSpaceExt_v1700__searchSpaceLinkingId_r17 z, tt)))))).
Definition SearchSpaceExt_v1700__F2 (y : seq_type SearchSpaceExt_v1700__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__SearchSpaceExt_v1700__Type i0 i1 i2 i3 i4 i5
  end.
Lemma SearchSpaceExt_v1700__F1F2_cond (z : SearchSpaceExt_v1700__Type)
  : SearchSpaceExt_v1700__cond z ->
  (seq_cond SearchSpaceExt_v1700__list (SearchSpaceExt_v1700__F1 z)).
intro H. unfold SearchSpaceExt_v1700__cond in H. simpl. auto. Qed.
Lemma SearchSpaceExt_v1700__F1F2_cond2 (z : SearchSpaceExt_v1700__Type)
 : SearchSpaceExt_v1700__F2 (SearchSpaceExt_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpaceExt_v1700__F2F1_cond (y : seq_type SearchSpaceExt_v1700__list)
  : seq_cond SearchSpaceExt_v1700__list y ->
 (SearchSpaceExt_v1700__cond (SearchSpaceExt_v1700__F2 y)) /\  SearchSpaceExt_v1700__F1 (SearchSpaceExt_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpaceExt_v1700__cond. simpl in *. auto.
 - simpl. unfold SearchSpaceExt_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpaceExt_v1700__Format : T_Format SearchSpaceExt_v1700__Type SearchSpaceExt_v1700__cond :=
        proj2_format  SearchSpaceExt_v1700__cond SearchSpaceExt_v1700__list__Format
    SearchSpaceExt_v1700__F1 SearchSpaceExt_v1700__F2 SearchSpaceExt_v1700__F1F2_cond  SearchSpaceExt_v1700__F1F2_cond2 SearchSpaceExt_v1700__F2F1_cond.
Opaque SearchSpaceExt_v1700__cond SearchSpaceExt_v1700__Format.

