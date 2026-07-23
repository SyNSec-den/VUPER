Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PDSCH_Config__dataScramblingIdentityPDSCH__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma PDSCH_Config__dataScramblingIdentityPDSCH__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__dataScramblingIdentityPDSCH__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__dataScramblingIdentityPDSCH__Type := Z.
Definition PDSCH_Config__dataScramblingIdentityPDSCH__cond := (fun z => (0 <= z <= 1023)%Z).
Require Import NR.SetupRelease.
Require Import NR.DMRS_DownlinkConfig.
Definition PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__Type := SetupRelease__Type DMRS_DownlinkConfig__Type.
Definition PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__cond := SetupRelease__cond _ DMRS_DownlinkConfig__cond.
Definition PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__Format : T_Format PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__Type PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__cond := SetupRelease__Format _ _ DMRS_DownlinkConfig__Format.
Opaque PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__cond PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__Format.

Require Import NR.SetupRelease.
Require Import NR.DMRS_DownlinkConfig.
Definition PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__Type := SetupRelease__Type DMRS_DownlinkConfig__Type.
Definition PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__cond := SetupRelease__cond _ DMRS_DownlinkConfig__cond.
Definition PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__Format : T_Format PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__Type PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__cond := SetupRelease__Format _ _ DMRS_DownlinkConfig__Format.
Opaque PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__cond PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__Format.

Require Import NR.TCI_State.

Opaque TCI_State__cond TCI_State__Format.

Definition PDSCH_Config__tci_StatesToAddModList__Type := list TCI_State__Type.

Lemma PDSCH_Config__tci_StatesToAddModList__helper1 : (0 <= 1 <= maxNrofTCI_States)%Z. unfold maxNrofTCI_States.
 lia. Qed.
Lemma PDSCH_Config__tci_StatesToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofTCI_States - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTCI_States - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__tci_StatesToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__tci_StatesToAddModList__cond (z : PDSCH_Config__tci_StatesToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofTCI_States)%Z /\ (list_and TCI_State__cond z) .

Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Definition PDSCH_Config__tci_StatesToReleaseList__Type := list TCI_StateId__Type.

Lemma PDSCH_Config__tci_StatesToReleaseList__helper1 : (0 <= 1 <= maxNrofTCI_States)%Z. unfold maxNrofTCI_States.
 lia. Qed.
Lemma PDSCH_Config__tci_StatesToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofTCI_States - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTCI_States - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__tci_StatesToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__tci_StatesToReleaseList__cond (z : PDSCH_Config__tci_StatesToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofTCI_States)%Z /\ (list_and TCI_StateId__cond z) .

Inductive PDSCH_Config__vrb_ToPRB_Interleaver__Type : Set :=
 | PDSCH_Config__vrb_ToPRB_Interleaver__n2
 | PDSCH_Config__vrb_ToPRB_Interleaver__n4
.
Definition PDSCH_Config__vrb_ToPRB_Interleaver__cond := (fun (_ : PDSCH_Config__vrb_ToPRB_Interleaver__Type) => True).
Lemma PDSCH_Config__vrb_ToPRB_Interleaver__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__vrb_ToPRB_Interleaver__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__vrb_ToPRB_Interleaver__nat__helper.

Definition PDSCH_Config__vrb_ToPRB_Interleaver__F1 t :=
  match t with
  | PDSCH_Config__vrb_ToPRB_Interleaver__n2 => 0
  | PDSCH_Config__vrb_ToPRB_Interleaver__n4 => 1
  end.
Definition PDSCH_Config__vrb_ToPRB_Interleaver__F2 n :=
  match n with
  | 0 => PDSCH_Config__vrb_ToPRB_Interleaver__n2
  | 1 => PDSCH_Config__vrb_ToPRB_Interleaver__n4
  | _ => PDSCH_Config__vrb_ToPRB_Interleaver__n2
  end.
Lemma PDSCH_Config__vrb_ToPRB_Interleaver__F1F2 : forall x : PDSCH_Config__vrb_ToPRB_Interleaver__Type, (PDSCH_Config__vrb_ToPRB_Interleaver__F1 x <= 1) /\ PDSCH_Config__vrb_ToPRB_Interleaver__F2 (PDSCH_Config__vrb_ToPRB_Interleaver__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__vrb_ToPRB_Interleaver__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__vrb_ToPRB_Interleaver__F1 (PDSCH_Config__vrb_ToPRB_Interleaver__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__resourceAllocation__Type : Set :=
 | PDSCH_Config__resourceAllocation__resourceAllocationType0
 | PDSCH_Config__resourceAllocation__resourceAllocationType1
 | PDSCH_Config__resourceAllocation__dynamicSwitch
.
Definition PDSCH_Config__resourceAllocation__cond := (fun (_ : PDSCH_Config__resourceAllocation__Type) => True).
Lemma PDSCH_Config__resourceAllocation__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__resourceAllocation__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PDSCH_Config__resourceAllocation__nat__helper.

Definition PDSCH_Config__resourceAllocation__F1 t :=
  match t with
  | PDSCH_Config__resourceAllocation__resourceAllocationType0 => 0
  | PDSCH_Config__resourceAllocation__resourceAllocationType1 => 1
  | PDSCH_Config__resourceAllocation__dynamicSwitch => 2
  end.
Definition PDSCH_Config__resourceAllocation__F2 n :=
  match n with
  | 0 => PDSCH_Config__resourceAllocation__resourceAllocationType0
  | 1 => PDSCH_Config__resourceAllocation__resourceAllocationType1
  | 2 => PDSCH_Config__resourceAllocation__dynamicSwitch
  | _ => PDSCH_Config__resourceAllocation__resourceAllocationType0
  end.
Lemma PDSCH_Config__resourceAllocation__F1F2 : forall x : PDSCH_Config__resourceAllocation__Type, (PDSCH_Config__resourceAllocation__F1 x <= 2) /\ PDSCH_Config__resourceAllocation__F2 (PDSCH_Config__resourceAllocation__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__resourceAllocation__F2F1 : forall (y : nat) (H : y <= 2), PDSCH_Config__resourceAllocation__F1 (PDSCH_Config__resourceAllocation__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PDSCH_TimeDomainResourceAllocationList.
Definition PDSCH_Config__pdsch_TimeDomainAllocationList__Type := SetupRelease__Type PDSCH_TimeDomainResourceAllocationList__Type.
Definition PDSCH_Config__pdsch_TimeDomainAllocationList__cond := SetupRelease__cond _ PDSCH_TimeDomainResourceAllocationList__cond.
Definition PDSCH_Config__pdsch_TimeDomainAllocationList__Format : T_Format PDSCH_Config__pdsch_TimeDomainAllocationList__Type PDSCH_Config__pdsch_TimeDomainAllocationList__cond := SetupRelease__Format _ _ PDSCH_TimeDomainResourceAllocationList__Format.
Opaque PDSCH_Config__pdsch_TimeDomainAllocationList__cond PDSCH_Config__pdsch_TimeDomainAllocationList__Format.

Inductive PDSCH_Config__pdsch_AggregationFactor__Type : Set :=
 | PDSCH_Config__pdsch_AggregationFactor__n2
 | PDSCH_Config__pdsch_AggregationFactor__n4
 | PDSCH_Config__pdsch_AggregationFactor__n8
.
Definition PDSCH_Config__pdsch_AggregationFactor__cond := (fun (_ : PDSCH_Config__pdsch_AggregationFactor__Type) => True).
Lemma PDSCH_Config__pdsch_AggregationFactor__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__pdsch_AggregationFactor__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PDSCH_Config__pdsch_AggregationFactor__nat__helper.

Definition PDSCH_Config__pdsch_AggregationFactor__F1 t :=
  match t with
  | PDSCH_Config__pdsch_AggregationFactor__n2 => 0
  | PDSCH_Config__pdsch_AggregationFactor__n4 => 1
  | PDSCH_Config__pdsch_AggregationFactor__n8 => 2
  end.
Definition PDSCH_Config__pdsch_AggregationFactor__F2 n :=
  match n with
  | 0 => PDSCH_Config__pdsch_AggregationFactor__n2
  | 1 => PDSCH_Config__pdsch_AggregationFactor__n4
  | 2 => PDSCH_Config__pdsch_AggregationFactor__n8
  | _ => PDSCH_Config__pdsch_AggregationFactor__n2
  end.
Lemma PDSCH_Config__pdsch_AggregationFactor__F1F2 : forall x : PDSCH_Config__pdsch_AggregationFactor__Type, (PDSCH_Config__pdsch_AggregationFactor__F1 x <= 2) /\ PDSCH_Config__pdsch_AggregationFactor__F2 (PDSCH_Config__pdsch_AggregationFactor__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__pdsch_AggregationFactor__F2F1 : forall (y : nat) (H : y <= 2), PDSCH_Config__pdsch_AggregationFactor__F1 (PDSCH_Config__pdsch_AggregationFactor__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RateMatchPattern.

Opaque RateMatchPattern__cond RateMatchPattern__Format.

Definition PDSCH_Config__rateMatchPatternToAddModList__Type := list RateMatchPattern__Type.

Lemma PDSCH_Config__rateMatchPatternToAddModList__helper1 : (0 <= 1 <= maxNrofRateMatchPatterns)%Z. unfold maxNrofRateMatchPatterns.
 lia. Qed.
Lemma PDSCH_Config__rateMatchPatternToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofRateMatchPatterns - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRateMatchPatterns - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__rateMatchPatternToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__rateMatchPatternToAddModList__cond (z : PDSCH_Config__rateMatchPatternToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRateMatchPatterns)%Z /\ (list_and RateMatchPattern__cond z) .

Require Import NR.RateMatchPatternId.

Opaque RateMatchPatternId__cond RateMatchPatternId__Format.

Definition PDSCH_Config__rateMatchPatternToReleaseList__Type := list RateMatchPatternId__Type.

Lemma PDSCH_Config__rateMatchPatternToReleaseList__helper1 : (0 <= 1 <= maxNrofRateMatchPatterns)%Z. unfold maxNrofRateMatchPatterns.
 lia. Qed.
Lemma PDSCH_Config__rateMatchPatternToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofRateMatchPatterns - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRateMatchPatterns - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__rateMatchPatternToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__rateMatchPatternToReleaseList__cond (z : PDSCH_Config__rateMatchPatternToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRateMatchPatterns)%Z /\ (list_and RateMatchPatternId__cond z) .

Require Import NR.RateMatchPatternGroup.

Opaque RateMatchPatternGroup__cond RateMatchPatternGroup__Format.

Require Import NR.RateMatchPatternGroup.

Opaque RateMatchPatternGroup__cond RateMatchPatternGroup__Format.

Inductive PDSCH_Config__rbg_Size__Type : Set :=
 | PDSCH_Config__rbg_Size__config1
 | PDSCH_Config__rbg_Size__config2
.
Definition PDSCH_Config__rbg_Size__cond := (fun (_ : PDSCH_Config__rbg_Size__Type) => True).
Lemma PDSCH_Config__rbg_Size__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__rbg_Size__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__rbg_Size__nat__helper.

Definition PDSCH_Config__rbg_Size__F1 t :=
  match t with
  | PDSCH_Config__rbg_Size__config1 => 0
  | PDSCH_Config__rbg_Size__config2 => 1
  end.
Definition PDSCH_Config__rbg_Size__F2 n :=
  match n with
  | 0 => PDSCH_Config__rbg_Size__config1
  | 1 => PDSCH_Config__rbg_Size__config2
  | _ => PDSCH_Config__rbg_Size__config1
  end.
Lemma PDSCH_Config__rbg_Size__F1F2 : forall x : PDSCH_Config__rbg_Size__Type, (PDSCH_Config__rbg_Size__F1 x <= 1) /\ PDSCH_Config__rbg_Size__F2 (PDSCH_Config__rbg_Size__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__rbg_Size__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__rbg_Size__F1 (PDSCH_Config__rbg_Size__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__mcs_Table__Type : Set :=
 | PDSCH_Config__mcs_Table__qam256
 | PDSCH_Config__mcs_Table__qam64LowSE
.
Definition PDSCH_Config__mcs_Table__cond := (fun (_ : PDSCH_Config__mcs_Table__Type) => True).
Lemma PDSCH_Config__mcs_Table__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__mcs_Table__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__mcs_Table__nat__helper.

Definition PDSCH_Config__mcs_Table__F1 t :=
  match t with
  | PDSCH_Config__mcs_Table__qam256 => 0
  | PDSCH_Config__mcs_Table__qam64LowSE => 1
  end.
Definition PDSCH_Config__mcs_Table__F2 n :=
  match n with
  | 0 => PDSCH_Config__mcs_Table__qam256
  | 1 => PDSCH_Config__mcs_Table__qam64LowSE
  | _ => PDSCH_Config__mcs_Table__qam256
  end.
Lemma PDSCH_Config__mcs_Table__F1F2 : forall x : PDSCH_Config__mcs_Table__Type, (PDSCH_Config__mcs_Table__F1 x <= 1) /\ PDSCH_Config__mcs_Table__F2 (PDSCH_Config__mcs_Table__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__mcs_Table__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__mcs_Table__F1 (PDSCH_Config__mcs_Table__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Type : Set :=
 | PDSCH_Config__maxNrofCodeWordsScheduledByDCI__n1
 | PDSCH_Config__maxNrofCodeWordsScheduledByDCI__n2
.
Definition PDSCH_Config__maxNrofCodeWordsScheduledByDCI__cond := (fun (_ : PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Type) => True).
Lemma PDSCH_Config__maxNrofCodeWordsScheduledByDCI__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__maxNrofCodeWordsScheduledByDCI__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__maxNrofCodeWordsScheduledByDCI__nat__helper.

Definition PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F1 t :=
  match t with
  | PDSCH_Config__maxNrofCodeWordsScheduledByDCI__n1 => 0
  | PDSCH_Config__maxNrofCodeWordsScheduledByDCI__n2 => 1
  end.
Definition PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F2 n :=
  match n with
  | 0 => PDSCH_Config__maxNrofCodeWordsScheduledByDCI__n1
  | 1 => PDSCH_Config__maxNrofCodeWordsScheduledByDCI__n2
  | _ => PDSCH_Config__maxNrofCodeWordsScheduledByDCI__n1
  end.
Lemma PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F1F2 : forall x : PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Type, (PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F1 x <= 1) /\ PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F2 (PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F1 (PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Type : Set :=
 | PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__n4
 | PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__wideband
.
Definition PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__cond := (fun (_ : PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Type) => True).
Lemma PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__nat__helper.

Definition PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F1 t :=
  match t with
  | PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__n4 => 0
  | PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__wideband => 1
  end.
Definition PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F2 n :=
  match n with
  | 0 => PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__n4
  | 1 => PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__wideband
  | _ => PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__n4
  end.
Lemma PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F1F2 : forall x : PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Type, (PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F1 x <= 1) /\ PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F2 (PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F1 (PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_Config__prb_BundlingType__staticBundling__Type : Set :=
  make__PDSCH_Config__prb_BundlingType__staticBundling__Type {
    PDSCH_Config__prb_BundlingType__staticBundling__bundleSize : option PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Type ;
}.
Definition PDSCH_Config__prb_BundlingType__staticBundling__list := (
 Opt PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Type PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__cond ::
 nil).
Definition PDSCH_Config__prb_BundlingType__staticBundling__cond z := 
  opt_cond PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__cond (PDSCH_Config__prb_BundlingType__staticBundling__bundleSize z) /\
  True.

Inductive PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Type : Set :=
 | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n4
 | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__wideband
 | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n2_wideband
 | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n4_wideband
.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__cond := (fun (_ : PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Type) => True).
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__nat__helper.

Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F1 t :=
  match t with
  | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n4 => 0
  | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__wideband => 1
  | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n2_wideband => 2
  | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n4_wideband => 3
  end.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F2 n :=
  match n with
  | 0 => PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n4
  | 1 => PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__wideband
  | 2 => PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n2_wideband
  | 3 => PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n4_wideband
  | _ => PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__n4
  end.
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F1F2 : forall x : PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Type, (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F1 x <= 3) /\ PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F2 (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F2F1 : forall (y : nat) (H : y <= 3), PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F1 (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Type : Set :=
 | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__n4
 | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__wideband
.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__cond := (fun (_ : PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Type) => True).
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__nat__helper.

Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F1 t :=
  match t with
  | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__n4 => 0
  | PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__wideband => 1
  end.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F2 n :=
  match n with
  | 0 => PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__n4
  | 1 => PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__wideband
  | _ => PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__n4
  end.
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F1F2 : forall x : PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Type, (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F1 x <= 1) /\ PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F2 (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F1 (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_Config__prb_BundlingType__dynamicBundling__Type : Set :=
  make__PDSCH_Config__prb_BundlingType__dynamicBundling__Type {
    PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1 : option PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Type ;
    PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2 : option PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Type ;
}.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__list := (
 Opt PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Type PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__cond ::
 Opt PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Type PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__cond ::
 nil).
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__cond z := 
  opt_cond PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__cond (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1 z) /\
  opt_cond PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__cond (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2 z) /\
  True.


Inductive PDSCH_Config__prb_BundlingType__Type : Set :=
  | PDSCH_Config__prb_BundlingType__staticBundling : PDSCH_Config__prb_BundlingType__staticBundling__Type -> PDSCH_Config__prb_BundlingType__Type
  | PDSCH_Config__prb_BundlingType__dynamicBundling : PDSCH_Config__prb_BundlingType__dynamicBundling__Type -> PDSCH_Config__prb_BundlingType__Type
.
Definition PDSCH_Config__prb_BundlingType__list : list typ := (
typ_cons PDSCH_Config__prb_BundlingType__staticBundling__Type PDSCH_Config__prb_BundlingType__staticBundling__cond ::
typ_cons PDSCH_Config__prb_BundlingType__dynamicBundling__Type PDSCH_Config__prb_BundlingType__dynamicBundling__cond ::
 nil).
Definition PDSCH_Config__prb_BundlingType__cond (c : PDSCH_Config__prb_BundlingType__Type) := 
  match c with
  | PDSCH_Config__prb_BundlingType__staticBundling t => PDSCH_Config__prb_BundlingType__staticBundling__cond t 
  | PDSCH_Config__prb_BundlingType__dynamicBundling t => PDSCH_Config__prb_BundlingType__dynamicBundling__cond t 
  end.

Lemma PDSCH_Config__prb_BundlingType__len_helper1 : to_bit_sz (length PDSCH_Config__prb_BundlingType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDSCH_Config__prb_BundlingType__len_helper2 : 2 <= length2 PDSCH_Config__prb_BundlingType__list.
 simpl. lia. Qed.
Require Import NR.ZP_CSI_RS_Resource.

Opaque ZP_CSI_RS_Resource__cond ZP_CSI_RS_Resource__Format.

Definition PDSCH_Config__zp_CSI_RS_ResourceToAddModList__Type := list ZP_CSI_RS_Resource__Type.

Lemma PDSCH_Config__zp_CSI_RS_ResourceToAddModList__helper1 : (0 <= 1 <= maxNrofZP_CSI_RS_Resources)%Z. unfold maxNrofZP_CSI_RS_Resources.
 lia. Qed.
Lemma PDSCH_Config__zp_CSI_RS_ResourceToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofZP_CSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofZP_CSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__zp_CSI_RS_ResourceToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__zp_CSI_RS_ResourceToAddModList__cond (z : PDSCH_Config__zp_CSI_RS_ResourceToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofZP_CSI_RS_Resources)%Z /\ (list_and ZP_CSI_RS_Resource__cond z) .

Require Import NR.ZP_CSI_RS_ResourceId.

Opaque ZP_CSI_RS_ResourceId__cond ZP_CSI_RS_ResourceId__Format.

Definition PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__Type := list ZP_CSI_RS_ResourceId__Type.

Lemma PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__helper1 : (0 <= 1 <= maxNrofZP_CSI_RS_Resources)%Z. unfold maxNrofZP_CSI_RS_Resources.
 lia. Qed.
Lemma PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofZP_CSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofZP_CSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__cond (z : PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofZP_CSI_RS_Resources)%Z /\ (list_and ZP_CSI_RS_ResourceId__cond z) .

Require Import NR.ZP_CSI_RS_ResourceSet.

Opaque ZP_CSI_RS_ResourceSet__cond ZP_CSI_RS_ResourceSet__Format.

Definition PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__Type := list ZP_CSI_RS_ResourceSet__Type.

Lemma PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__helper1 : (0 <= 1 <= maxNrofZP_CSI_RS_ResourceSets)%Z. unfold maxNrofZP_CSI_RS_ResourceSets.
 lia. Qed.
Lemma PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofZP_CSI_RS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofZP_CSI_RS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__cond (z : PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofZP_CSI_RS_ResourceSets)%Z /\ (list_and ZP_CSI_RS_ResourceSet__cond z) .

Require Import NR.ZP_CSI_RS_ResourceSetId.

Opaque ZP_CSI_RS_ResourceSetId__cond ZP_CSI_RS_ResourceSetId__Format.

Definition PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__Type := list ZP_CSI_RS_ResourceSetId__Type.

Lemma PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__helper1 : (0 <= 1 <= maxNrofZP_CSI_RS_ResourceSets)%Z. unfold maxNrofZP_CSI_RS_ResourceSets.
 lia. Qed.
Lemma PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofZP_CSI_RS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofZP_CSI_RS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__cond (z : PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofZP_CSI_RS_ResourceSets)%Z /\ (list_and ZP_CSI_RS_ResourceSetId__cond z) .

Require Import NR.ZP_CSI_RS_ResourceSet.

Opaque ZP_CSI_RS_ResourceSet__cond ZP_CSI_RS_ResourceSet__Format.

Definition PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__Type := list ZP_CSI_RS_ResourceSet__Type.

Lemma PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__helper1 : (0 <= 1 <= maxNrofZP_CSI_RS_ResourceSets)%Z. unfold maxNrofZP_CSI_RS_ResourceSets.
 lia. Qed.
Lemma PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofZP_CSI_RS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofZP_CSI_RS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__cond (z : PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofZP_CSI_RS_ResourceSets)%Z /\ (list_and ZP_CSI_RS_ResourceSet__cond z) .

Require Import NR.ZP_CSI_RS_ResourceSetId.

Opaque ZP_CSI_RS_ResourceSetId__cond ZP_CSI_RS_ResourceSetId__Format.

Definition PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__Type := list ZP_CSI_RS_ResourceSetId__Type.

Lemma PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__helper1 : (0 <= 1 <= maxNrofZP_CSI_RS_ResourceSets)%Z. unfold maxNrofZP_CSI_RS_ResourceSets.
 lia. Qed.
Lemma PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofZP_CSI_RS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofZP_CSI_RS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__cond (z : PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofZP_CSI_RS_ResourceSets)%Z /\ (list_and ZP_CSI_RS_ResourceSetId__cond z) .

Require Import NR.SetupRelease.
Require Import NR.ZP_CSI_RS_ResourceSet.
Definition PDSCH_Config__p_ZP_CSI_RS_ResourceSet__Type := SetupRelease__Type ZP_CSI_RS_ResourceSet__Type.
Definition PDSCH_Config__p_ZP_CSI_RS_ResourceSet__cond := SetupRelease__cond _ ZP_CSI_RS_ResourceSet__cond.
Definition PDSCH_Config__p_ZP_CSI_RS_ResourceSet__Format : T_Format PDSCH_Config__p_ZP_CSI_RS_ResourceSet__Type PDSCH_Config__p_ZP_CSI_RS_ResourceSet__cond := SetupRelease__Format _ _ ZP_CSI_RS_ResourceSet__Format.
Opaque PDSCH_Config__p_ZP_CSI_RS_ResourceSet__cond PDSCH_Config__p_ZP_CSI_RS_ResourceSet__Format.

Require Import NR.SetupRelease.
Require Import NR.MaxMIMO_LayersDL_r16.
Definition PDSCH_Config__ext0O__maxMIMO_Layers_r16__Type := SetupRelease__Type MaxMIMO_LayersDL_r16__Type.
Definition PDSCH_Config__ext0O__maxMIMO_Layers_r16__cond := SetupRelease__cond _ MaxMIMO_LayersDL_r16__cond.
Definition PDSCH_Config__ext0O__maxMIMO_Layers_r16__Format : T_Format PDSCH_Config__ext0O__maxMIMO_Layers_r16__Type PDSCH_Config__ext0O__maxMIMO_Layers_r16__cond := SetupRelease__Format _ _ MaxMIMO_LayersDL_r16__Format.
Opaque PDSCH_Config__ext0O__maxMIMO_Layers_r16__cond PDSCH_Config__ext0O__maxMIMO_Layers_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.MinSchedulingOffsetK0_Values_r16.
Definition PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__Type := SetupRelease__Type MinSchedulingOffsetK0_Values_r16__Type.
Definition PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__cond := SetupRelease__cond _ MinSchedulingOffsetK0_Values_r16__cond.
Definition PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__Format : T_Format PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__Type PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__cond := SetupRelease__Format _ _ MinSchedulingOffsetK0_Values_r16__Format.
Opaque PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__cond PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__Format.

Inductive PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Type : Set :=
 | PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__enabled
.
Definition PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__cond := (fun (_ : PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__nat__helper.

Definition PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__enabled => 0
  end.
Definition PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__enabled
  | _ => PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__enabled
  end.
Lemma PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F1F2 : forall x : PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Type, (PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F1 x <= 0) /\ PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F2 (PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F1 (PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ZP_CSI_RS_ResourceSet.

Opaque ZP_CSI_RS_ResourceSet__cond ZP_CSI_RS_ResourceSet__Format.

Definition PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__Type := list ZP_CSI_RS_ResourceSet__Type.

Lemma PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__helper1 : (0 <= 1 <= maxNrofZP_CSI_RS_ResourceSets)%Z. unfold maxNrofZP_CSI_RS_ResourceSets.
 lia. Qed.
Lemma PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofZP_CSI_RS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofZP_CSI_RS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__cond (z : PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofZP_CSI_RS_ResourceSets)%Z /\ (list_and ZP_CSI_RS_ResourceSet__cond z) .

Require Import NR.ZP_CSI_RS_ResourceSetId.

Opaque ZP_CSI_RS_ResourceSetId__cond ZP_CSI_RS_ResourceSetId__Format.

Definition PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__Type := list ZP_CSI_RS_ResourceSetId__Type.

Lemma PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__helper1 : (0 <= 1 <= maxNrofZP_CSI_RS_ResourceSets)%Z. unfold maxNrofZP_CSI_RS_ResourceSets.
 lia. Qed.
Lemma PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofZP_CSI_RS_ResourceSets - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofZP_CSI_RS_ResourceSets - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__cond (z : PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofZP_CSI_RS_ResourceSets)%Z /\ (list_and ZP_CSI_RS_ResourceSetId__cond z) .

Require Import NR.SetupRelease.
Require Import NR.DMRS_DownlinkConfig.
Definition PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__Type := SetupRelease__Type DMRS_DownlinkConfig__Type.
Definition PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__cond := SetupRelease__cond _ DMRS_DownlinkConfig__cond.
Definition PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__Type PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__cond := SetupRelease__Format _ _ DMRS_DownlinkConfig__Format.
Opaque PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__cond PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.DMRS_DownlinkConfig.
Definition PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__Type := SetupRelease__Type DMRS_DownlinkConfig__Type.
Definition PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__cond := SetupRelease__cond _ DMRS_DownlinkConfig__cond.
Definition PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__Type PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__cond := SetupRelease__Format _ _ DMRS_DownlinkConfig__Format.
Opaque PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__cond PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__Format.

Inductive PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Type : Set :=
 | PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__enabled
.
Definition PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__cond := (fun (_ : PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__nat__helper.

Definition PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__enabled => 0
  end.
Definition PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__enabled
  | _ => PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__enabled
  end.
Lemma PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F1F2 : forall x : PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Type, (PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F1 x <= 0) /\ PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F2 (PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F1 (PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Lemma PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__Type := Z.
Definition PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__cond := (fun z => (0 <= z <= 4)%Z).
Inductive PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Type : Set :=
 | PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__qam256
 | PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__qam64LowSE
.
Definition PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__cond := (fun (_ : PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__nat__helper.

Definition PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__qam256 => 0
  | PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__qam64LowSE => 1
  end.
Definition PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__qam256
  | 1 => PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__qam64LowSE
  | _ => PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__qam256
  end.
Lemma PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F1F2 : forall x : PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Type, (PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F1 x <= 1) /\ PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F2 (PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F1 (PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Lemma PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__helper1 : (0 <= 2)%Z.  lia. Qed.
Lemma PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__helper2 : to_bit_sz (Z.to_nat (2 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__Type := Z.
Definition PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__cond := (fun z => (0 <= z <= 2)%Z).
Require Import NR.SetupRelease.
Require Import NR.PDSCH_TimeDomainResourceAllocationList_r16.
Definition PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__Type := SetupRelease__Type PDSCH_TimeDomainResourceAllocationList_r16__Type.
Definition PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__cond := SetupRelease__cond _ PDSCH_TimeDomainResourceAllocationList_r16__cond.
Definition PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__Type PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__cond := SetupRelease__Format _ _ PDSCH_TimeDomainResourceAllocationList_r16__Format.
Opaque PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__cond PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__Format.

Inductive PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Type : Set :=
 | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__n4
 | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__wideband
.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__cond := (fun (_ : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Type) => True).
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__nat__helper.

Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__n4 => 0
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__wideband => 1
  end.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__n4
  | 1 => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__wideband
  | _ => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__n4
  end.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F1F2 : forall x : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Type, (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F1 x <= 1) /\ PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F2 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F1 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type : Set :=
  make__PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type {
    PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16 : option PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Type ;
}.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list := (
 Opt PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__cond ::
 nil).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond z := 
  opt_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__cond (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16 z) /\
  True.

Inductive PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Type : Set :=
 | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n4
 | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__wideband
 | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n2_wideband
 | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n4_wideband
.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__cond := (fun (_ : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Type) => True).
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__nat__helper.

Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n4 => 0
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__wideband => 1
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n2_wideband => 2
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n4_wideband => 3
  end.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n4
  | 1 => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__wideband
  | 2 => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n2_wideband
  | 3 => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n4_wideband
  | _ => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__n4
  end.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F1F2 : forall x : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Type, (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F1 x <= 3) /\ PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F2 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F2F1 : forall (y : nat) (H : y <= 3), PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F1 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Type : Set :=
 | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__n4
 | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__wideband
.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__cond := (fun (_ : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__nat__helper.

Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__n4 => 0
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__wideband => 1
  end.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__n4
  | 1 => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__wideband
  | _ => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__n4
  end.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F1F2 : forall x : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Type, (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F1 x <= 1) /\ PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F2 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F1 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F2 y) = y. enum_solve H y. Qed.

Record PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type : Set :=
  make__PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type {
    PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16 : option PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Type ;
    PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16 : option PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Type ;
}.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list := (
 Opt PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__cond ::
 Opt PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__cond ::
 nil).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond z := 
  opt_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__cond (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16 z) /\
  opt_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__cond (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16 z) /\
  True.


Inductive PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type : Set :=
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16 : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type -> PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16 : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type -> PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type
.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list : list typ := (
typ_cons PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond ::
typ_cons PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond ::
 nil).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__cond (c : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type) := 
  match c with
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16 t => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond t 
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16 t => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond t 
  end.

Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__len_helper1 : to_bit_sz (length PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__len_helper2 : 2 <= length2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list.
 simpl. lia. Qed.
Inductive PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Type : Set :=
 | PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__enabled
.
Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__cond := (fun (_ : PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__nat__helper.

Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__enabled => 0
  end.
Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__enabled
  | _ => PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__enabled
  end.
Lemma PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F1F2 : forall x : PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Type, (PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F1 x <= 0) /\ PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F2 (PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F1 (PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RateMatchPatternGroup.

Opaque RateMatchPatternGroup__cond RateMatchPatternGroup__Format.

Require Import NR.RateMatchPatternGroup.

Opaque RateMatchPatternGroup__cond RateMatchPatternGroup__Format.

Inductive PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Type : Set :=
 | PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n2
 | PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n4
 | PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n8
 | PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n16
.
Definition PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__cond := (fun (_ : PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__nat__helper.

Definition PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n2 => 0
  | PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n4 => 1
  | PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n8 => 2
  | PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n16 => 3
  end.
Definition PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n2
  | 1 => PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n4
  | 2 => PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n8
  | 3 => PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n16
  | _ => PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__n2
  end.
Lemma PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F1F2 : forall x : PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Type, (PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F1 x <= 3) /\ PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F2 (PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 3), PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F1 (PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Type : Set :=
 | PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__n2
 | PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__n4
.
Definition PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__cond := (fun (_ : PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__nat__helper.

Definition PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__n2 => 0
  | PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__n4 => 1
  end.
Definition PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__n2
  | 1 => PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__n4
  | _ => PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__n2
  end.
Lemma PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F1F2 : forall x : PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Type, (PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F1 x <= 1) /\ PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F2 (PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 1), PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F1 (PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Type : Set :=
 | PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__enabled
.
Definition PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__cond := (fun (_ : PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__nat__helper.

Definition PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__enabled => 0
  end.
Definition PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__enabled
  | _ => PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__enabled
  end.
Lemma PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F1F2 : forall x : PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Type, (PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F1 x <= 0) /\ PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F2 (PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F1 (PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Type : Set :=
 | PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__resourceAllocationType0
 | PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__resourceAllocationType1
 | PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__dynamicSwitch
.
Definition PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__cond := (fun (_ : PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Type) => True).
Lemma PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__nat__helper.

Definition PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__resourceAllocationType0 => 0
  | PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__resourceAllocationType1 => 1
  | PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__dynamicSwitch => 2
  end.
Definition PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__resourceAllocationType0
  | 1 => PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__resourceAllocationType1
  | 2 => PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__dynamicSwitch
  | _ => PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__resourceAllocationType0
  end.
Lemma PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F1F2 : forall x : PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Type, (PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F1 x <= 2) /\ PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F2 (PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 2), PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F1 (PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Type : Set :=
 | PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__enabled
.
Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__cond := (fun (_ : PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Type) => True).
Lemma PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__nat__helper.

Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F1 t :=
  match t with
  | PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__enabled => 0
  end.
Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__enabled
  | _ => PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__enabled
  end.
Lemma PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F1F2 : forall x : PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Type, (PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F1 x <= 0) /\ PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F2 (PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F1 (PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F2 y) = y. enum_solve H y. Qed.

Lemma PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__Type := Z.
Definition PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__cond := (fun z => (0 <= z <= 1023)%Z).
Require Import NR.SetupRelease.
Require Import NR.PDSCH_TimeDomainResourceAllocationList_r16.
Definition PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__Type := SetupRelease__Type PDSCH_TimeDomainResourceAllocationList_r16__Type.
Definition PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__cond := SetupRelease__cond _ PDSCH_TimeDomainResourceAllocationList_r16__cond.
Definition PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__Format : T_Format PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__Type PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__cond := SetupRelease__Format _ _ PDSCH_TimeDomainResourceAllocationList_r16__Format.
Opaque PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__cond PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.RepetitionSchemeConfig_r16.
Definition PDSCH_Config__ext0O__repetitionSchemeConfig_r16__Type := SetupRelease__Type RepetitionSchemeConfig_r16__Type.
Definition PDSCH_Config__ext0O__repetitionSchemeConfig_r16__cond := SetupRelease__cond _ RepetitionSchemeConfig_r16__cond.
Definition PDSCH_Config__ext0O__repetitionSchemeConfig_r16__Format : T_Format PDSCH_Config__ext0O__repetitionSchemeConfig_r16__Type PDSCH_Config__ext0O__repetitionSchemeConfig_r16__cond := SetupRelease__Format _ _ RepetitionSchemeConfig_r16__Format.
Opaque PDSCH_Config__ext0O__repetitionSchemeConfig_r16__cond PDSCH_Config__ext0O__repetitionSchemeConfig_r16__Format.

Record PDSCH_Config__ext0O__Type : Set :=
  make__PDSCH_Config__ext0O__Type {
    PDSCH_Config__ext0O__maxMIMO_Layers_r16 : option PDSCH_Config__ext0O__maxMIMO_Layers_r16__Type ;
    PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16 : option PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__Type ;
    PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16 : option PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16 : option PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16 : option PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16 : option PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16 : option PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16 : option PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16 : option Z ;
    PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16 : option PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16 : option Z ;
    PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16 : option PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16 : option PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16 : option PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__rateMatchPatternGroup1DCI_1_2_r16 : option RateMatchPatternGroup__Type ;
    PDSCH_Config__ext0O__rateMatchPatternGroup2DCI_1_2_r16 : option RateMatchPatternGroup__Type ;
    PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16 : option PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16 : option PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16 : option PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16 : option PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Type ;
    PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16 : option PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Type ;
    PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16 : option Z ;
    PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16 : option PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__Type ;
    PDSCH_Config__ext0O__repetitionSchemeConfig_r16 : option PDSCH_Config__ext0O__repetitionSchemeConfig_r16__Type ;
}.
Definition PDSCH_Config__ext0O__list := (
 Opt PDSCH_Config__ext0O__maxMIMO_Layers_r16__Type PDSCH_Config__ext0O__maxMIMO_Layers_r16__cond ::
 Opt PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__Type PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__cond ::
 Opt PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Type PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__Type PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__Type PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__Type PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__Type PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Type PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__cond ::
 Opt Z PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Type PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__cond ::
 Opt Z PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__Type PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Type PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__cond ::
 Opt RateMatchPatternGroup__Type RateMatchPatternGroup__cond ::
 Opt RateMatchPatternGroup__Type RateMatchPatternGroup__cond ::
 Opt PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Type PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Type PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Type PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Type PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__cond ::
 Opt PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Type PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__cond ::
 Opt Z PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__cond ::
 Opt PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__Type PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__cond ::
 Opt PDSCH_Config__ext0O__repetitionSchemeConfig_r16__Type PDSCH_Config__ext0O__repetitionSchemeConfig_r16__cond ::
 nil).
Definition PDSCH_Config__ext0O__cond z := 
  opt_cond PDSCH_Config__ext0O__maxMIMO_Layers_r16__cond (PDSCH_Config__ext0O__maxMIMO_Layers_r16 z) /\
  opt_cond PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__cond (PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16 z) /\
  opt_cond PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__cond (PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__cond (PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__cond (PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__cond (PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__cond (PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__cond (PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__cond (PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__cond (PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__cond (PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__cond (PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__cond (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__cond (PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16 z) /\
  opt_cond RateMatchPatternGroup__cond (PDSCH_Config__ext0O__rateMatchPatternGroup1DCI_1_2_r16 z) /\
  opt_cond RateMatchPatternGroup__cond (PDSCH_Config__ext0O__rateMatchPatternGroup2DCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__cond (PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__cond (PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__cond (PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__cond (PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__cond (PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16 z) /\
  opt_cond PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__cond (PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16 z) /\
  opt_cond PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__cond (PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16 z) /\
  opt_cond PDSCH_Config__ext0O__repetitionSchemeConfig_r16__cond (PDSCH_Config__ext0O__repetitionSchemeConfig_r16 z) /\
  True.

Definition PDSCH_Config__ext0__Type := PDSCH_Config__ext0O__Type.
Definition PDSCH_Config__ext0__cond := PDSCH_Config__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.RepetitionSchemeConfig_v1630.
Definition PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__Type := SetupRelease__Type RepetitionSchemeConfig_v1630__Type.
Definition PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__cond := SetupRelease__cond _ RepetitionSchemeConfig_v1630__cond.
Definition PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__Format : T_Format PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__Type PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__cond := SetupRelease__Format _ _ RepetitionSchemeConfig_v1630__Format.
Opaque PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__cond PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__Format.

Record PDSCH_Config__ext1O__Type : Set :=
  make__PDSCH_Config__ext1O__Type {
    PDSCH_Config__ext1O__repetitionSchemeConfig_v1630 : option PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__Type ;
}.
Definition PDSCH_Config__ext1O__list := (
 Opt PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__Type PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__cond ::
 nil).
Definition PDSCH_Config__ext1O__cond z := 
  opt_cond PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__cond (PDSCH_Config__ext1O__repetitionSchemeConfig_v1630 z) /\
  True.

Definition PDSCH_Config__ext1__Type := PDSCH_Config__ext1O__Type.
Definition PDSCH_Config__ext1__cond := PDSCH_Config__ext1O__cond.

Inductive PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Type : Set :=
 | PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__enabled
.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__cond := (fun (_ : PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Type) => True).
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__nat__helper.

Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__enabled => 0
  end.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__enabled
  | _ => PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__enabled
  end.
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F1F2 : forall x : PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Type, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F2 (PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F1 (PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Type : Set :=
 | PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__enabled
.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__cond := (fun (_ : PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Type) => True).
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__nat__helper.

Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__enabled => 0
  end.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__enabled
  | _ => PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__enabled
  end.
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F1F2 : forall x : PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Type, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F2 (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F1 (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Type : Set :=
 | PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__enabled
.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__cond := (fun (_ : PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Type) => True).
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__nat__helper.

Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__enabled => 0
  end.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__enabled
  | _ => PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__enabled
  end.
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F1F2 : forall x : PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Type, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F2 (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F1 (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Type : Set :=
 | PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__enabled
.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__cond := (fun (_ : PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Type) => True).
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__nat__helper.

Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__enabled => 0
  end.
Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__enabled
  | _ => PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__enabled
  end.
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F1F2 : forall x : PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Type, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F2 (PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F1 (PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Type : Set :=
 | PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__enabled
.
Definition PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__cond := (fun (_ : PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Type) => True).
Lemma PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__nat__helper.

Definition PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__enabled => 0
  end.
Definition PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__enabled
  | _ => PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__enabled
  end.
Lemma PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F1F2 : forall x : PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Type, (PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F2 (PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F1 (PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.TCI_State.

Opaque TCI_State__cond TCI_State__Format.

Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__Type := list TCI_State__Type.

Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__helper1 : (0 <= 1 <= maxNrofTCI_States)%Z. unfold maxNrofTCI_States.
 lia. Qed.
Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofTCI_States - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTCI_States - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__cond (z : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofTCI_States)%Z /\ (list_and TCI_State__cond z) .

Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__Type := list TCI_StateId__Type.

Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofTCI_States)%Z. unfold maxNrofTCI_States.
 lia. Qed.
Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofTCI_States - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTCI_States - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__cond (z : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofTCI_States)%Z /\ (list_and TCI_StateId__cond z) .

Record PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type : Set :=
  make__PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type {
    PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17 : option PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__Type ;
    PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17 : option PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__Type ;
}.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list := (
 Opt PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__Type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__cond ::
 Opt PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__Type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__cond ::
 nil).
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond z := 
  opt_cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__cond (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17 z) /\
  opt_cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__cond (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17 z) /\
  True.

Require Import NR.ServingCellAndBWP_Id_r17.

Opaque ServingCellAndBWP_Id_r17__cond ServingCellAndBWP_Id_r17__Format.


Inductive PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type : Set :=
  | PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type -> PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type
  | PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__unifiedTCI_StateRef_r17 : ServingCellAndBWP_Id_r17__Type -> PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type
.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list : list typ := (
typ_cons PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond ::
typ_cons ServingCellAndBWP_Id_r17__Type ServingCellAndBWP_Id_r17__cond ::
 nil).
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__cond (c : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type) := 
  match c with
  | PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist t => PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond t 
  | PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__unifiedTCI_StateRef_r17 t => ServingCellAndBWP_Id_r17__cond t 
  end.

Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__len_helper1 : to_bit_sz (length PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__len_helper2 : 2 <= length2 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list.
 simpl. lia. Qed.
Inductive PDSCH_Config__ext2O__beamAppTime_r17__Type : Set :=
 | PDSCH_Config__ext2O__beamAppTime_r17__n1
 | PDSCH_Config__ext2O__beamAppTime_r17__n2
 | PDSCH_Config__ext2O__beamAppTime_r17__n4
 | PDSCH_Config__ext2O__beamAppTime_r17__n7
 | PDSCH_Config__ext2O__beamAppTime_r17__n14
 | PDSCH_Config__ext2O__beamAppTime_r17__n28
 | PDSCH_Config__ext2O__beamAppTime_r17__n42
 | PDSCH_Config__ext2O__beamAppTime_r17__n56
 | PDSCH_Config__ext2O__beamAppTime_r17__n70
 | PDSCH_Config__ext2O__beamAppTime_r17__n84
 | PDSCH_Config__ext2O__beamAppTime_r17__n98
 | PDSCH_Config__ext2O__beamAppTime_r17__n112
 | PDSCH_Config__ext2O__beamAppTime_r17__n224
 | PDSCH_Config__ext2O__beamAppTime_r17__n336
 | PDSCH_Config__ext2O__beamAppTime_r17__spare2
 | PDSCH_Config__ext2O__beamAppTime_r17__spare1
.
Definition PDSCH_Config__ext2O__beamAppTime_r17__cond := (fun (_ : PDSCH_Config__ext2O__beamAppTime_r17__Type) => True).
Lemma PDSCH_Config__ext2O__beamAppTime_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__beamAppTime_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 PDSCH_Config__ext2O__beamAppTime_r17__nat__helper.

Definition PDSCH_Config__ext2O__beamAppTime_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__beamAppTime_r17__n1 => 0
  | PDSCH_Config__ext2O__beamAppTime_r17__n2 => 1
  | PDSCH_Config__ext2O__beamAppTime_r17__n4 => 2
  | PDSCH_Config__ext2O__beamAppTime_r17__n7 => 3
  | PDSCH_Config__ext2O__beamAppTime_r17__n14 => 4
  | PDSCH_Config__ext2O__beamAppTime_r17__n28 => 5
  | PDSCH_Config__ext2O__beamAppTime_r17__n42 => 6
  | PDSCH_Config__ext2O__beamAppTime_r17__n56 => 7
  | PDSCH_Config__ext2O__beamAppTime_r17__n70 => 8
  | PDSCH_Config__ext2O__beamAppTime_r17__n84 => 9
  | PDSCH_Config__ext2O__beamAppTime_r17__n98 => 10
  | PDSCH_Config__ext2O__beamAppTime_r17__n112 => 11
  | PDSCH_Config__ext2O__beamAppTime_r17__n224 => 12
  | PDSCH_Config__ext2O__beamAppTime_r17__n336 => 13
  | PDSCH_Config__ext2O__beamAppTime_r17__spare2 => 14
  | PDSCH_Config__ext2O__beamAppTime_r17__spare1 => 15
  end.
Definition PDSCH_Config__ext2O__beamAppTime_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__beamAppTime_r17__n1
  | 1 => PDSCH_Config__ext2O__beamAppTime_r17__n2
  | 2 => PDSCH_Config__ext2O__beamAppTime_r17__n4
  | 3 => PDSCH_Config__ext2O__beamAppTime_r17__n7
  | 4 => PDSCH_Config__ext2O__beamAppTime_r17__n14
  | 5 => PDSCH_Config__ext2O__beamAppTime_r17__n28
  | 6 => PDSCH_Config__ext2O__beamAppTime_r17__n42
  | 7 => PDSCH_Config__ext2O__beamAppTime_r17__n56
  | 8 => PDSCH_Config__ext2O__beamAppTime_r17__n70
  | 9 => PDSCH_Config__ext2O__beamAppTime_r17__n84
  | 10 => PDSCH_Config__ext2O__beamAppTime_r17__n98
  | 11 => PDSCH_Config__ext2O__beamAppTime_r17__n112
  | 12 => PDSCH_Config__ext2O__beamAppTime_r17__n224
  | 13 => PDSCH_Config__ext2O__beamAppTime_r17__n336
  | 14 => PDSCH_Config__ext2O__beamAppTime_r17__spare2
  | 15 => PDSCH_Config__ext2O__beamAppTime_r17__spare1
  | _ => PDSCH_Config__ext2O__beamAppTime_r17__n1
  end.
Lemma PDSCH_Config__ext2O__beamAppTime_r17__F1F2 : forall x : PDSCH_Config__ext2O__beamAppTime_r17__Type, (PDSCH_Config__ext2O__beamAppTime_r17__F1 x <= 15) /\ PDSCH_Config__ext2O__beamAppTime_r17__F2 (PDSCH_Config__ext2O__beamAppTime_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__beamAppTime_r17__F2F1 : forall (y : nat) (H : y <= 15), PDSCH_Config__ext2O__beamAppTime_r17__F1 (PDSCH_Config__ext2O__beamAppTime_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.Dummy_TDRA_List.
Definition PDSCH_Config__ext2O__dummy__Type := SetupRelease__Type Dummy_TDRA_List__Type.
Definition PDSCH_Config__ext2O__dummy__cond := SetupRelease__cond _ Dummy_TDRA_List__cond.
Definition PDSCH_Config__ext2O__dummy__Format : T_Format PDSCH_Config__ext2O__dummy__Type PDSCH_Config__ext2O__dummy__cond := SetupRelease__Format _ _ Dummy_TDRA_List__Format.
Opaque PDSCH_Config__ext2O__dummy__cond PDSCH_Config__ext2O__dummy__Format.

Inductive PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Type : Set :=
 | PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__true
.
Definition PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__cond := (fun (_ : PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Type) => True).
Lemma PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__nat__helper.

Definition PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__true => 0
  end.
Definition PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__true
  | _ => PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__true
  end.
Lemma PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F1F2 : forall x : PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Type, (PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F2 (PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F1 (PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.MinSchedulingOffsetK0_Values_r17.
Definition PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__Type := SetupRelease__Type MinSchedulingOffsetK0_Values_r17__Type.
Definition PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__cond := SetupRelease__cond _ MinSchedulingOffsetK0_Values_r17__cond.
Definition PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__Format : T_Format PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__Type PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__cond := SetupRelease__Format _ _ MinSchedulingOffsetK0_Values_r17__Format.
Opaque PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__cond PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__Format.

Lemma PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__helper1 : (0 <= 5)%Z.  lia. Qed.
Lemma PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__helper2 : to_bit_sz (Z.to_nat (5 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__Type := Z.
Definition PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__cond := (fun z => (0 <= z <= 5)%Z).
Definition PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__Type := Z.
Definition PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__cond := (fun z : Z => z = 5)%Z.
Inductive PDSCH_Config__ext2O__mcs_Table_r17__Type : Set :=
 | PDSCH_Config__ext2O__mcs_Table_r17__qam1024
.
Definition PDSCH_Config__ext2O__mcs_Table_r17__cond := (fun (_ : PDSCH_Config__ext2O__mcs_Table_r17__Type) => True).
Lemma PDSCH_Config__ext2O__mcs_Table_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__mcs_Table_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__mcs_Table_r17__nat__helper.

Definition PDSCH_Config__ext2O__mcs_Table_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__mcs_Table_r17__qam1024 => 0
  end.
Definition PDSCH_Config__ext2O__mcs_Table_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__mcs_Table_r17__qam1024
  | _ => PDSCH_Config__ext2O__mcs_Table_r17__qam1024
  end.
Lemma PDSCH_Config__ext2O__mcs_Table_r17__F1F2 : forall x : PDSCH_Config__ext2O__mcs_Table_r17__Type, (PDSCH_Config__ext2O__mcs_Table_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__mcs_Table_r17__F2 (PDSCH_Config__ext2O__mcs_Table_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__mcs_Table_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__mcs_Table_r17__F1 (PDSCH_Config__ext2O__mcs_Table_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Type : Set :=
 | PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__qam1024
.
Definition PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__cond := (fun (_ : PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Type) => True).
Lemma PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__nat__helper.

Definition PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__qam1024 => 0
  end.
Definition PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__qam1024
  | _ => PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__qam1024
  end.
Lemma PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F1F2 : forall x : PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Type, (PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F2 (PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F1 (PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext2O__xOverheadMulticast_r17__Type : Set :=
 | PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh6
 | PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh12
 | PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh18
.
Definition PDSCH_Config__ext2O__xOverheadMulticast_r17__cond := (fun (_ : PDSCH_Config__ext2O__xOverheadMulticast_r17__Type) => True).
Lemma PDSCH_Config__ext2O__xOverheadMulticast_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__xOverheadMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PDSCH_Config__ext2O__xOverheadMulticast_r17__nat__helper.

Definition PDSCH_Config__ext2O__xOverheadMulticast_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh6 => 0
  | PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh12 => 1
  | PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh18 => 2
  end.
Definition PDSCH_Config__ext2O__xOverheadMulticast_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh6
  | 1 => PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh12
  | 2 => PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh18
  | _ => PDSCH_Config__ext2O__xOverheadMulticast_r17__xOh6
  end.
Lemma PDSCH_Config__ext2O__xOverheadMulticast_r17__F1F2 : forall x : PDSCH_Config__ext2O__xOverheadMulticast_r17__Type, (PDSCH_Config__ext2O__xOverheadMulticast_r17__F1 x <= 2) /\ PDSCH_Config__ext2O__xOverheadMulticast_r17__F2 (PDSCH_Config__ext2O__xOverheadMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__xOverheadMulticast_r17__F2F1 : forall (y : nat) (H : y <= 2), PDSCH_Config__ext2O__xOverheadMulticast_r17__F1 (PDSCH_Config__ext2O__xOverheadMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Type : Set :=
 | PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__enabled
.
Definition PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__cond := (fun (_ : PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Type) => True).
Lemma PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__nat__helper.

Definition PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F1 t :=
  match t with
  | PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__enabled => 0
  end.
Definition PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F2 n :=
  match n with
  | 0 => PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__enabled
  | _ => PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__enabled
  end.
Lemma PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F1F2 : forall x : PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Type, (PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F1 x <= 0) /\ PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F2 (PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F1 (PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F2 y) = y. enum_solve H y. Qed.

Lemma PDSCH_Config__ext2O__sizeDCI_4_2_r17__helper1 : (20 <= maxDCI_4_2_Size_r17)%Z. unfold maxDCI_4_2_Size_r17.
 lia. Qed.
Lemma PDSCH_Config__ext2O__sizeDCI_4_2_r17__helper2 : to_bit_sz (Z.to_nat (maxDCI_4_2_Size_r17 - 20)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDCI_4_2_Size_r17 - 20))%Z). { apply Zorder.Zle_minus_le_0. apply PDSCH_Config__ext2O__sizeDCI_4_2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PDSCH_Config__ext2O__sizeDCI_4_2_r17__Type := Z.
Definition PDSCH_Config__ext2O__sizeDCI_4_2_r17__cond := (fun z => (20 <= z <= maxDCI_4_2_Size_r17)%Z).
Record PDSCH_Config__ext2O__Type : Set :=
  make__PDSCH_Config__ext2O__Type {
    PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17 : option PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Type ;
    PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17 : option PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Type ;
    PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17 : option PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Type ;
    PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17 : option PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Type ;
    PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17 : option PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Type ;
    PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17 : option PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type ;
    PDSCH_Config__ext2O__beamAppTime_r17 : option PDSCH_Config__ext2O__beamAppTime_r17__Type ;
    PDSCH_Config__ext2O__dummy : option PDSCH_Config__ext2O__dummy__Type ;
    PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17 : option PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Type ;
    PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17 : option PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__Type ;
    PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700 : option Z ;
    PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17 : option Z ;
    PDSCH_Config__ext2O__mcs_Table_r17 : option PDSCH_Config__ext2O__mcs_Table_r17__Type ;
    PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17 : option PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Type ;
    PDSCH_Config__ext2O__xOverheadMulticast_r17 : option PDSCH_Config__ext2O__xOverheadMulticast_r17__Type ;
    PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17 : option PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Type ;
    PDSCH_Config__ext2O__sizeDCI_4_2_r17 : option Z ;
}.
Definition PDSCH_Config__ext2O__list := (
 Opt PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Type PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__cond ::
 Opt PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Type PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__cond ::
 Opt PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Type PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__cond ::
 Opt PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Type PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__cond ::
 Opt PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Type PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__cond ::
 Opt PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__cond ::
 Opt PDSCH_Config__ext2O__beamAppTime_r17__Type PDSCH_Config__ext2O__beamAppTime_r17__cond ::
 Opt PDSCH_Config__ext2O__dummy__Type PDSCH_Config__ext2O__dummy__cond ::
 Opt PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Type PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__cond ::
 Opt PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__Type PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__cond ::
 Opt Z PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__cond ::
 Opt Z PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__cond ::
 Opt PDSCH_Config__ext2O__mcs_Table_r17__Type PDSCH_Config__ext2O__mcs_Table_r17__cond ::
 Opt PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Type PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__cond ::
 Opt PDSCH_Config__ext2O__xOverheadMulticast_r17__Type PDSCH_Config__ext2O__xOverheadMulticast_r17__cond ::
 Opt PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Type PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__cond ::
 Opt Z PDSCH_Config__ext2O__sizeDCI_4_2_r17__cond ::
 nil).
Definition PDSCH_Config__ext2O__cond z := 
  opt_cond PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__cond (PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17 z) /\
  opt_cond PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__cond (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17 z) /\
  opt_cond PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__cond (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17 z) /\
  opt_cond PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__cond (PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17 z) /\
  opt_cond PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__cond (PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17 z) /\
  opt_cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__cond (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17 z) /\
  opt_cond PDSCH_Config__ext2O__beamAppTime_r17__cond (PDSCH_Config__ext2O__beamAppTime_r17 z) /\
  opt_cond PDSCH_Config__ext2O__dummy__cond (PDSCH_Config__ext2O__dummy z) /\
  opt_cond PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__cond (PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17 z) /\
  opt_cond PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__cond (PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17 z) /\
  opt_cond PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__cond (PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700 z) /\
  opt_cond PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__cond (PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17 z) /\
  opt_cond PDSCH_Config__ext2O__mcs_Table_r17__cond (PDSCH_Config__ext2O__mcs_Table_r17 z) /\
  opt_cond PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__cond (PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17 z) /\
  opt_cond PDSCH_Config__ext2O__xOverheadMulticast_r17__cond (PDSCH_Config__ext2O__xOverheadMulticast_r17 z) /\
  opt_cond PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__cond (PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17 z) /\
  opt_cond PDSCH_Config__ext2O__sizeDCI_4_2_r17__cond (PDSCH_Config__ext2O__sizeDCI_4_2_r17 z) /\
  True.

Definition PDSCH_Config__ext2__Type := PDSCH_Config__ext2O__Type.
Definition PDSCH_Config__ext2__cond := PDSCH_Config__ext2O__cond.

Require Import NR.SetupRelease.
Require Import NR.MultiPDSCH_TDRA_List_r17.
Definition PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__Type := SetupRelease__Type MultiPDSCH_TDRA_List_r17__Type.
Definition PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__cond := SetupRelease__cond _ MultiPDSCH_TDRA_List_r17__cond.
Definition PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__Format : T_Format PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__Type PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__cond := SetupRelease__Format _ _ MultiPDSCH_TDRA_List_r17__Format.
Opaque PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__cond PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__Format.

Record PDSCH_Config__ext3O__Type : Set :=
  make__PDSCH_Config__ext3O__Type {
    PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17 : option PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__Type ;
}.
Definition PDSCH_Config__ext3O__list := (
 Opt PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__Type PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__cond ::
 nil).
Definition PDSCH_Config__ext3O__cond z := 
  opt_cond PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__cond (PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17 z) /\
  True.

Definition PDSCH_Config__ext3__Type := PDSCH_Config__ext3O__Type.
Definition PDSCH_Config__ext3__cond := PDSCH_Config__ext3O__cond.

Record PDSCH_Config__Type : Set :=
  make__PDSCH_Config__Type {
    PDSCH_Config__dataScramblingIdentityPDSCH : option Z ;
    PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA : option PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__Type ;
    PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB : option PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__Type ;
    PDSCH_Config__tci_StatesToAddModList : option PDSCH_Config__tci_StatesToAddModList__Type ;
    PDSCH_Config__tci_StatesToReleaseList : option PDSCH_Config__tci_StatesToReleaseList__Type ;
    PDSCH_Config__vrb_ToPRB_Interleaver : option PDSCH_Config__vrb_ToPRB_Interleaver__Type ;
    PDSCH_Config__resourceAllocation : PDSCH_Config__resourceAllocation__Type ;
    PDSCH_Config__pdsch_TimeDomainAllocationList : option PDSCH_Config__pdsch_TimeDomainAllocationList__Type ;
    PDSCH_Config__pdsch_AggregationFactor : option PDSCH_Config__pdsch_AggregationFactor__Type ;
    PDSCH_Config__rateMatchPatternToAddModList : option PDSCH_Config__rateMatchPatternToAddModList__Type ;
    PDSCH_Config__rateMatchPatternToReleaseList : option PDSCH_Config__rateMatchPatternToReleaseList__Type ;
    PDSCH_Config__rateMatchPatternGroup1 : option RateMatchPatternGroup__Type ;
    PDSCH_Config__rateMatchPatternGroup2 : option RateMatchPatternGroup__Type ;
    PDSCH_Config__rbg_Size : PDSCH_Config__rbg_Size__Type ;
    PDSCH_Config__mcs_Table : option PDSCH_Config__mcs_Table__Type ;
    PDSCH_Config__maxNrofCodeWordsScheduledByDCI : option PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Type ;
    PDSCH_Config__prb_BundlingType : PDSCH_Config__prb_BundlingType__Type ;
    PDSCH_Config__zp_CSI_RS_ResourceToAddModList : option PDSCH_Config__zp_CSI_RS_ResourceToAddModList__Type ;
    PDSCH_Config__zp_CSI_RS_ResourceToReleaseList : option PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__Type ;
    PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList : option PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__Type ;
    PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList : option PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__Type ;
    PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList : option PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__Type ;
    PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList : option PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__Type ;
    PDSCH_Config__p_ZP_CSI_RS_ResourceSet : option PDSCH_Config__p_ZP_CSI_RS_ResourceSet__Type ;
    PDSCH_Config__ext0 : option PDSCH_Config__ext0__Type ;
    PDSCH_Config__ext1 : option PDSCH_Config__ext1__Type ;
    PDSCH_Config__ext2 : option PDSCH_Config__ext2__Type ;
    PDSCH_Config__ext3 : option PDSCH_Config__ext3__Type ;
}.
Definition PDSCH_Config__root_list : list seq_elem := (
 Opt Z PDSCH_Config__dataScramblingIdentityPDSCH__cond ::
 Opt PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__Type PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__cond ::
 Opt PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__Type PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__cond ::
 Opt PDSCH_Config__tci_StatesToAddModList__Type PDSCH_Config__tci_StatesToAddModList__cond ::
 Opt PDSCH_Config__tci_StatesToReleaseList__Type PDSCH_Config__tci_StatesToReleaseList__cond ::
 Opt PDSCH_Config__vrb_ToPRB_Interleaver__Type PDSCH_Config__vrb_ToPRB_Interleaver__cond ::
 Nor PDSCH_Config__resourceAllocation__Type PDSCH_Config__resourceAllocation__cond ::
 Opt PDSCH_Config__pdsch_TimeDomainAllocationList__Type PDSCH_Config__pdsch_TimeDomainAllocationList__cond ::
 Opt PDSCH_Config__pdsch_AggregationFactor__Type PDSCH_Config__pdsch_AggregationFactor__cond ::
 Opt PDSCH_Config__rateMatchPatternToAddModList__Type PDSCH_Config__rateMatchPatternToAddModList__cond ::
 Opt PDSCH_Config__rateMatchPatternToReleaseList__Type PDSCH_Config__rateMatchPatternToReleaseList__cond ::
 Opt RateMatchPatternGroup__Type RateMatchPatternGroup__cond ::
 Opt RateMatchPatternGroup__Type RateMatchPatternGroup__cond ::
 Nor PDSCH_Config__rbg_Size__Type PDSCH_Config__rbg_Size__cond ::
 Opt PDSCH_Config__mcs_Table__Type PDSCH_Config__mcs_Table__cond ::
 Opt PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Type PDSCH_Config__maxNrofCodeWordsScheduledByDCI__cond ::
 Nor PDSCH_Config__prb_BundlingType__Type PDSCH_Config__prb_BundlingType__cond ::
 Opt PDSCH_Config__zp_CSI_RS_ResourceToAddModList__Type PDSCH_Config__zp_CSI_RS_ResourceToAddModList__cond ::
 Opt PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__Type PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__cond ::
 Opt PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__Type PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__cond ::
 Opt PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__Type PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__cond ::
 Opt PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__Type PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__cond ::
 Opt PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__Type PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__cond ::
 Opt PDSCH_Config__p_ZP_CSI_RS_ResourceSet__Type PDSCH_Config__p_ZP_CSI_RS_ResourceSet__cond ::
 nil).
Definition PDSCH_Config__ext_list : list typ := (
  typ_cons PDSCH_Config__ext0__Type PDSCH_Config__ext0__cond ::
  typ_cons PDSCH_Config__ext1__Type PDSCH_Config__ext1__cond ::
  typ_cons PDSCH_Config__ext2__Type PDSCH_Config__ext2__cond ::
  typ_cons PDSCH_Config__ext3__Type PDSCH_Config__ext3__cond ::
  nil).
Definition PDSCH_Config__cond (z : PDSCH_Config__Type) := 
(  opt_cond PDSCH_Config__dataScramblingIdentityPDSCH__cond (PDSCH_Config__dataScramblingIdentityPDSCH z) /\
  opt_cond PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__cond (PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA z) /\
  opt_cond PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__cond (PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB z) /\
  opt_cond PDSCH_Config__tci_StatesToAddModList__cond (PDSCH_Config__tci_StatesToAddModList z) /\
  opt_cond PDSCH_Config__tci_StatesToReleaseList__cond (PDSCH_Config__tci_StatesToReleaseList z) /\
  opt_cond PDSCH_Config__vrb_ToPRB_Interleaver__cond (PDSCH_Config__vrb_ToPRB_Interleaver z) /\
  PDSCH_Config__resourceAllocation__cond (PDSCH_Config__resourceAllocation z) /\
  opt_cond PDSCH_Config__pdsch_TimeDomainAllocationList__cond (PDSCH_Config__pdsch_TimeDomainAllocationList z) /\
  opt_cond PDSCH_Config__pdsch_AggregationFactor__cond (PDSCH_Config__pdsch_AggregationFactor z) /\
  opt_cond PDSCH_Config__rateMatchPatternToAddModList__cond (PDSCH_Config__rateMatchPatternToAddModList z) /\
  opt_cond PDSCH_Config__rateMatchPatternToReleaseList__cond (PDSCH_Config__rateMatchPatternToReleaseList z) /\
  opt_cond RateMatchPatternGroup__cond (PDSCH_Config__rateMatchPatternGroup1 z) /\
  opt_cond RateMatchPatternGroup__cond (PDSCH_Config__rateMatchPatternGroup2 z) /\
  PDSCH_Config__rbg_Size__cond (PDSCH_Config__rbg_Size z) /\
  opt_cond PDSCH_Config__mcs_Table__cond (PDSCH_Config__mcs_Table z) /\
  opt_cond PDSCH_Config__maxNrofCodeWordsScheduledByDCI__cond (PDSCH_Config__maxNrofCodeWordsScheduledByDCI z) /\
  PDSCH_Config__prb_BundlingType__cond (PDSCH_Config__prb_BundlingType z) /\
  opt_cond PDSCH_Config__zp_CSI_RS_ResourceToAddModList__cond (PDSCH_Config__zp_CSI_RS_ResourceToAddModList z) /\
  opt_cond PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__cond (PDSCH_Config__zp_CSI_RS_ResourceToReleaseList z) /\
  opt_cond PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__cond (PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList z) /\
  opt_cond PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__cond (PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList z) /\
  opt_cond PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__cond (PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList z) /\
  opt_cond PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__cond (PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList z) /\
  opt_cond PDSCH_Config__p_ZP_CSI_RS_ResourceSet__cond (PDSCH_Config__p_ZP_CSI_RS_ResourceSet z) /\
  True) /\ 
(  opt_cond PDSCH_Config__ext0__cond (PDSCH_Config__ext0 z) /\
  opt_cond PDSCH_Config__ext1__cond (PDSCH_Config__ext1 z) /\
  opt_cond PDSCH_Config__ext2__cond (PDSCH_Config__ext2 z) /\
  opt_cond PDSCH_Config__ext3__cond (PDSCH_Config__ext3 z) /\
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
Definition PDSCH_Config__dataScramblingIdentityPDSCH__Format : T_Format Z PDSCH_Config__dataScramblingIdentityPDSCH__cond :=
 ranged_int_format (0) (1023) PDSCH_Config__dataScramblingIdentityPDSCH__helper1 PDSCH_Config__dataScramblingIdentityPDSCH__helper2.

Opaque PDSCH_Config__dataScramblingIdentityPDSCH__cond PDSCH_Config__dataScramblingIdentityPDSCH__Format.

Opaque PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__cond PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__Format.

Opaque PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__cond PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__Format.

Definition PDSCH_Config__tci_StatesToAddModList__Format : T_Format PDSCH_Config__tci_StatesToAddModList__Type PDSCH_Config__tci_StatesToAddModList__cond := seq_of_format TCI_State__Format 1 maxNrofTCI_States PDSCH_Config__tci_StatesToAddModList__helper1 PDSCH_Config__tci_StatesToAddModList__helper2.

Opaque PDSCH_Config__tci_StatesToAddModList__cond PDSCH_Config__tci_StatesToAddModList__Format.

Definition PDSCH_Config__tci_StatesToReleaseList__Format : T_Format PDSCH_Config__tci_StatesToReleaseList__Type PDSCH_Config__tci_StatesToReleaseList__cond := seq_of_format TCI_StateId__Format 1 maxNrofTCI_States PDSCH_Config__tci_StatesToReleaseList__helper1 PDSCH_Config__tci_StatesToReleaseList__helper2.

Opaque PDSCH_Config__tci_StatesToReleaseList__cond PDSCH_Config__tci_StatesToReleaseList__Format.

Definition PDSCH_Config__vrb_ToPRB_Interleaver__Format : T_Format PDSCH_Config__vrb_ToPRB_Interleaver__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__vrb_ToPRB_Interleaver__nat__Format PDSCH_Config__vrb_ToPRB_Interleaver__F1 PDSCH_Config__vrb_ToPRB_Interleaver__F2 PDSCH_Config__vrb_ToPRB_Interleaver__F1F2 PDSCH_Config__vrb_ToPRB_Interleaver__F2F1.

Opaque PDSCH_Config__vrb_ToPRB_Interleaver__cond PDSCH_Config__vrb_ToPRB_Interleaver__Format.

Definition PDSCH_Config__resourceAllocation__Format : T_Format PDSCH_Config__resourceAllocation__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__resourceAllocation__nat__Format PDSCH_Config__resourceAllocation__F1 PDSCH_Config__resourceAllocation__F2 PDSCH_Config__resourceAllocation__F1F2 PDSCH_Config__resourceAllocation__F2F1.

Opaque PDSCH_Config__resourceAllocation__cond PDSCH_Config__resourceAllocation__Format.

Opaque PDSCH_Config__pdsch_TimeDomainAllocationList__cond PDSCH_Config__pdsch_TimeDomainAllocationList__Format.

Definition PDSCH_Config__pdsch_AggregationFactor__Format : T_Format PDSCH_Config__pdsch_AggregationFactor__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__pdsch_AggregationFactor__nat__Format PDSCH_Config__pdsch_AggregationFactor__F1 PDSCH_Config__pdsch_AggregationFactor__F2 PDSCH_Config__pdsch_AggregationFactor__F1F2 PDSCH_Config__pdsch_AggregationFactor__F2F1.

Opaque PDSCH_Config__pdsch_AggregationFactor__cond PDSCH_Config__pdsch_AggregationFactor__Format.

Definition PDSCH_Config__rateMatchPatternToAddModList__Format : T_Format PDSCH_Config__rateMatchPatternToAddModList__Type PDSCH_Config__rateMatchPatternToAddModList__cond := seq_of_format RateMatchPattern__Format 1 maxNrofRateMatchPatterns PDSCH_Config__rateMatchPatternToAddModList__helper1 PDSCH_Config__rateMatchPatternToAddModList__helper2.

Opaque PDSCH_Config__rateMatchPatternToAddModList__cond PDSCH_Config__rateMatchPatternToAddModList__Format.

Definition PDSCH_Config__rateMatchPatternToReleaseList__Format : T_Format PDSCH_Config__rateMatchPatternToReleaseList__Type PDSCH_Config__rateMatchPatternToReleaseList__cond := seq_of_format RateMatchPatternId__Format 1 maxNrofRateMatchPatterns PDSCH_Config__rateMatchPatternToReleaseList__helper1 PDSCH_Config__rateMatchPatternToReleaseList__helper2.

Opaque PDSCH_Config__rateMatchPatternToReleaseList__cond PDSCH_Config__rateMatchPatternToReleaseList__Format.

Definition PDSCH_Config__rbg_Size__Format : T_Format PDSCH_Config__rbg_Size__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__rbg_Size__nat__Format PDSCH_Config__rbg_Size__F1 PDSCH_Config__rbg_Size__F2 PDSCH_Config__rbg_Size__F1F2 PDSCH_Config__rbg_Size__F2F1.

Opaque PDSCH_Config__rbg_Size__cond PDSCH_Config__rbg_Size__Format.

Definition PDSCH_Config__mcs_Table__Format : T_Format PDSCH_Config__mcs_Table__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__mcs_Table__nat__Format PDSCH_Config__mcs_Table__F1 PDSCH_Config__mcs_Table__F2 PDSCH_Config__mcs_Table__F1F2 PDSCH_Config__mcs_Table__F2F1.

Opaque PDSCH_Config__mcs_Table__cond PDSCH_Config__mcs_Table__Format.

Definition PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Format : T_Format PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__maxNrofCodeWordsScheduledByDCI__nat__Format PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F1 PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F2 PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F1F2 PDSCH_Config__maxNrofCodeWordsScheduledByDCI__F2F1.

Opaque PDSCH_Config__maxNrofCodeWordsScheduledByDCI__cond PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Format.

Definition PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Format : T_Format PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__nat__Format PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F1 PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F2 PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F1F2 PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__F2F1.

Opaque PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__cond PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Format.


Definition PDSCH_Config__prb_BundlingType__staticBundling__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__prb_BundlingType__staticBundling__list.
Definition PDSCH_Config__prb_BundlingType__staticBundling__Format_list : PDSCH_Config__prb_BundlingType__staticBundling__Format_Type :=
  (PDSCH_Config__prb_BundlingType__staticBundling__bundleSize__Format, unit_format).
Definition PDSCH_Config__prb_BundlingType__staticBundling__list__Format := (*Eval compute in *) seq_format PDSCH_Config__prb_BundlingType__staticBundling__list PDSCH_Config__prb_BundlingType__staticBundling__Format_list.
Definition PDSCH_Config__prb_BundlingType__staticBundling__F1 z :=
  (PDSCH_Config__prb_BundlingType__staticBundling__bundleSize z, tt).
Definition PDSCH_Config__prb_BundlingType__staticBundling__F2 (y : seq_type PDSCH_Config__prb_BundlingType__staticBundling__list) :=
  match y with
  | (i0, _)=>
    make__PDSCH_Config__prb_BundlingType__staticBundling__Type i0
  end.
Lemma PDSCH_Config__prb_BundlingType__staticBundling__F1F2_cond (z : PDSCH_Config__prb_BundlingType__staticBundling__Type)
  : PDSCH_Config__prb_BundlingType__staticBundling__cond z ->
  (seq_cond PDSCH_Config__prb_BundlingType__staticBundling__list (PDSCH_Config__prb_BundlingType__staticBundling__F1 z)).
intro H. unfold PDSCH_Config__prb_BundlingType__staticBundling__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__prb_BundlingType__staticBundling__F1F2_cond2 (z : PDSCH_Config__prb_BundlingType__staticBundling__Type)
 : PDSCH_Config__prb_BundlingType__staticBundling__F2 (PDSCH_Config__prb_BundlingType__staticBundling__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__prb_BundlingType__staticBundling__F2F1_cond (y : seq_type PDSCH_Config__prb_BundlingType__staticBundling__list)
  : seq_cond PDSCH_Config__prb_BundlingType__staticBundling__list y ->
 (PDSCH_Config__prb_BundlingType__staticBundling__cond (PDSCH_Config__prb_BundlingType__staticBundling__F2 y)) /\  PDSCH_Config__prb_BundlingType__staticBundling__F1 (PDSCH_Config__prb_BundlingType__staticBundling__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__prb_BundlingType__staticBundling__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__prb_BundlingType__staticBundling__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__prb_BundlingType__staticBundling__Format : T_Format PDSCH_Config__prb_BundlingType__staticBundling__Type PDSCH_Config__prb_BundlingType__staticBundling__cond :=
        proj2_format  PDSCH_Config__prb_BundlingType__staticBundling__cond PDSCH_Config__prb_BundlingType__staticBundling__list__Format
    PDSCH_Config__prb_BundlingType__staticBundling__F1 PDSCH_Config__prb_BundlingType__staticBundling__F2 PDSCH_Config__prb_BundlingType__staticBundling__F1F2_cond  PDSCH_Config__prb_BundlingType__staticBundling__F1F2_cond2 PDSCH_Config__prb_BundlingType__staticBundling__F2F1_cond.
Opaque PDSCH_Config__prb_BundlingType__staticBundling__cond PDSCH_Config__prb_BundlingType__staticBundling__Format.

Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Format : T_Format PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__nat__Format PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F1 PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F2 PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F1F2 PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__F2F1.

Opaque PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__cond PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Format.

Definition PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Format : T_Format PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__nat__Format PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F1 PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F2 PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F1F2 PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__F2F1.

Opaque PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__cond PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Format.


Definition PDSCH_Config__prb_BundlingType__dynamicBundling__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__prb_BundlingType__dynamicBundling__list.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__Format_list : PDSCH_Config__prb_BundlingType__dynamicBundling__Format_Type :=
  (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1__Format, (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2__Format, unit_format)).
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__list__Format := (*Eval compute in *) seq_format PDSCH_Config__prb_BundlingType__dynamicBundling__list PDSCH_Config__prb_BundlingType__dynamicBundling__Format_list.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__F1 z :=
  (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet1 z, (PDSCH_Config__prb_BundlingType__dynamicBundling__bundleSizeSet2 z, tt)).
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__F2 (y : seq_type PDSCH_Config__prb_BundlingType__dynamicBundling__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDSCH_Config__prb_BundlingType__dynamicBundling__Type i0 i1
  end.
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__F1F2_cond (z : PDSCH_Config__prb_BundlingType__dynamicBundling__Type)
  : PDSCH_Config__prb_BundlingType__dynamicBundling__cond z ->
  (seq_cond PDSCH_Config__prb_BundlingType__dynamicBundling__list (PDSCH_Config__prb_BundlingType__dynamicBundling__F1 z)).
intro H. unfold PDSCH_Config__prb_BundlingType__dynamicBundling__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__F1F2_cond2 (z : PDSCH_Config__prb_BundlingType__dynamicBundling__Type)
 : PDSCH_Config__prb_BundlingType__dynamicBundling__F2 (PDSCH_Config__prb_BundlingType__dynamicBundling__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__prb_BundlingType__dynamicBundling__F2F1_cond (y : seq_type PDSCH_Config__prb_BundlingType__dynamicBundling__list)
  : seq_cond PDSCH_Config__prb_BundlingType__dynamicBundling__list y ->
 (PDSCH_Config__prb_BundlingType__dynamicBundling__cond (PDSCH_Config__prb_BundlingType__dynamicBundling__F2 y)) /\  PDSCH_Config__prb_BundlingType__dynamicBundling__F1 (PDSCH_Config__prb_BundlingType__dynamicBundling__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__prb_BundlingType__dynamicBundling__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__prb_BundlingType__dynamicBundling__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__prb_BundlingType__dynamicBundling__Format : T_Format PDSCH_Config__prb_BundlingType__dynamicBundling__Type PDSCH_Config__prb_BundlingType__dynamicBundling__cond :=
        proj2_format  PDSCH_Config__prb_BundlingType__dynamicBundling__cond PDSCH_Config__prb_BundlingType__dynamicBundling__list__Format
    PDSCH_Config__prb_BundlingType__dynamicBundling__F1 PDSCH_Config__prb_BundlingType__dynamicBundling__F2 PDSCH_Config__prb_BundlingType__dynamicBundling__F1F2_cond  PDSCH_Config__prb_BundlingType__dynamicBundling__F1F2_cond2 PDSCH_Config__prb_BundlingType__dynamicBundling__F2F1_cond.
Opaque PDSCH_Config__prb_BundlingType__dynamicBundling__cond PDSCH_Config__prb_BundlingType__dynamicBundling__Format.


Definition PDSCH_Config__prb_BundlingType__Format_Type := Eval cbn in get_formats PDSCH_Config__prb_BundlingType__list.
Definition PDSCH_Config__prb_BundlingType__Format_list : PDSCH_Config__prb_BundlingType__Format_Type :=
  (PDSCH_Config__prb_BundlingType__staticBundling__Format, (PDSCH_Config__prb_BundlingType__dynamicBundling__Format, unit__Format)).
Definition PDSCH_Config__prb_BundlingType__list__Format := Eval compute in choice_format PDSCH_Config__prb_BundlingType__list PDSCH_Config__prb_BundlingType__len_helper1 PDSCH_Config__prb_BundlingType__len_helper2  PDSCH_Config__prb_BundlingType__Format_list.
Definition PDSCH_Config__prb_BundlingType__F1 (z : PDSCH_Config__prb_BundlingType__Type) : (choice PDSCH_Config__prb_BundlingType__list) :=
  match z with
   | PDSCH_Config__prb_BundlingType__staticBundling t => existT _ 0 t
  | PDSCH_Config__prb_BundlingType__dynamicBundling t => existT _ 1 t
  end.
Definition PDSCH_Config__prb_BundlingType__g := (fun n => typ_set (get_nth_typ PDSCH_Config__prb_BundlingType__list n)).
Definition PDSCH_Config__prb_BundlingType__F2 (y : choice PDSCH_Config__prb_BundlingType__list) : PDSCH_Config__prb_BundlingType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDSCH_Config__prb_BundlingType__g n -> PDSCH_Config__prb_BundlingType__Type) with
    | 0 => fun (t : PDSCH_Config__prb_BundlingType__staticBundling__Type) => PDSCH_Config__prb_BundlingType__staticBundling t 
    | 1 => fun (t : PDSCH_Config__prb_BundlingType__dynamicBundling__Type) => PDSCH_Config__prb_BundlingType__dynamicBundling t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PDSCH_Config__prb_BundlingType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PDSCH_Config__prb_BundlingType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDSCH_Config__prb_BundlingType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PDSCH_Config__prb_BundlingType__Type with end) n0
           end t0).

Lemma PDSCH_Config__prb_BundlingType__helper2 :  forall (y : PDSCH_Config__prb_BundlingType__Type), PDSCH_Config__prb_BundlingType__cond y -> choice_cond PDSCH_Config__prb_BundlingType__list (PDSCH_Config__prb_BundlingType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDSCH_Config__prb_BundlingType__helper3 :  forall (y : PDSCH_Config__prb_BundlingType__Type), PDSCH_Config__prb_BundlingType__F2 (PDSCH_Config__prb_BundlingType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDSCH_Config__prb_BundlingType__helper4 : (forall b : choice PDSCH_Config__prb_BundlingType__list, choice_cond PDSCH_Config__prb_BundlingType__list b -> PDSCH_Config__prb_BundlingType__cond (PDSCH_Config__prb_BundlingType__F2 b) /\ PDSCH_Config__prb_BundlingType__F1 (PDSCH_Config__prb_BundlingType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDSCH_Config__prb_BundlingType__F1 PDSCH_Config__prb_BundlingType__F2.
Definition PDSCH_Config__prb_BundlingType__Format : T_Format PDSCH_Config__prb_BundlingType__Type PDSCH_Config__prb_BundlingType__cond :=
  (* Eval compute in *) proj2_format PDSCH_Config__prb_BundlingType__cond PDSCH_Config__prb_BundlingType__list__Format PDSCH_Config__prb_BundlingType__F1 PDSCH_Config__prb_BundlingType__F2 PDSCH_Config__prb_BundlingType__helper2 PDSCH_Config__prb_BundlingType__helper3 PDSCH_Config__prb_BundlingType__helper4.
Opaque PDSCH_Config__prb_BundlingType__cond PDSCH_Config__prb_BundlingType__Format.

Definition PDSCH_Config__zp_CSI_RS_ResourceToAddModList__Format : T_Format PDSCH_Config__zp_CSI_RS_ResourceToAddModList__Type PDSCH_Config__zp_CSI_RS_ResourceToAddModList__cond := seq_of_format ZP_CSI_RS_Resource__Format 1 maxNrofZP_CSI_RS_Resources PDSCH_Config__zp_CSI_RS_ResourceToAddModList__helper1 PDSCH_Config__zp_CSI_RS_ResourceToAddModList__helper2.

Opaque PDSCH_Config__zp_CSI_RS_ResourceToAddModList__cond PDSCH_Config__zp_CSI_RS_ResourceToAddModList__Format.

Definition PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__Format : T_Format PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__Type PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__cond := seq_of_format ZP_CSI_RS_ResourceId__Format 1 maxNrofZP_CSI_RS_Resources PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__helper1 PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__helper2.

Opaque PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__cond PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__Format.

Definition PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__Format : T_Format PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__Type PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__cond := seq_of_format ZP_CSI_RS_ResourceSet__Format 1 maxNrofZP_CSI_RS_ResourceSets PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__helper1 PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__helper2.

Opaque PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__cond PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__Format.

Definition PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__Format : T_Format PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__Type PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__cond := seq_of_format ZP_CSI_RS_ResourceSetId__Format 1 maxNrofZP_CSI_RS_ResourceSets PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__helper1 PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__helper2.

Opaque PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__cond PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__Format.

Definition PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__Format : T_Format PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__Type PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__cond := seq_of_format ZP_CSI_RS_ResourceSet__Format 1 maxNrofZP_CSI_RS_ResourceSets PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__helper1 PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__helper2.

Opaque PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__cond PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__Format.

Definition PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__Format : T_Format PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__Type PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__cond := seq_of_format ZP_CSI_RS_ResourceSetId__Format 1 maxNrofZP_CSI_RS_ResourceSets PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__helper1 PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__helper2.

Opaque PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__cond PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__Format.

Opaque PDSCH_Config__p_ZP_CSI_RS_ResourceSet__cond PDSCH_Config__p_ZP_CSI_RS_ResourceSet__Format.

Opaque PDSCH_Config__ext0O__maxMIMO_Layers_r16__cond PDSCH_Config__ext0O__maxMIMO_Layers_r16__Format.

Opaque PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__cond PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__Format.

Definition PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__nat__Format PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F1 PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F2 PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F1F2 PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__F2F1.

Opaque PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__cond PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__Type PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__cond := seq_of_format ZP_CSI_RS_ResourceSet__Format 1 maxNrofZP_CSI_RS_ResourceSets PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__helper1 PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__helper2.

Opaque PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__cond PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__Type PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__cond := seq_of_format ZP_CSI_RS_ResourceSetId__Format 1 maxNrofZP_CSI_RS_ResourceSets PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__helper1 PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__helper2.

Opaque PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__cond PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__Format.

Opaque PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__cond PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__Format.

Opaque PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__cond PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__nat__Format PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F1 PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F2 PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F1F2 PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__F2F1.

Opaque PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__cond PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__Format : T_Format Z PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__cond :=
 ranged_int_format (0) (4) PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__helper1 PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__helper2.

Opaque PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__cond PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__nat__Format PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F1 PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F2 PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F1F2 PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__F2F1.

Opaque PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__cond PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__Format : T_Format Z PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__cond :=
 ranged_int_format (0) (2) PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__helper1 PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__helper2.

Opaque PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__cond PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__Format.

Opaque PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__cond PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Format : T_Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__nat__Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F1F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__F2F1.

Opaque PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Format.


Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Format_list : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Format_Type :=
  (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16__Format, unit_format).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list__Format := (*Eval compute in *) seq_format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Format_list.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1 z :=
  (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__bundleSize_r16 z, tt).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F2 (y : seq_type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list) :=
  match y with
  | (i0, _)=>
    make__PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type i0
  end.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1F2_cond (z : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type)
  : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond z ->
  (seq_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1 z)).
intro H. unfold PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1F2_cond2 (z : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type)
 : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F2 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F2F1_cond (y : seq_type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list)
  : seq_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list y ->
 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F2 y)) /\  PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Format : T_Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond :=
        proj2_format  PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__list__Format
    PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1F2_cond  PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F1F2_cond2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__F2F1_cond.
Opaque PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Format.

Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Format : T_Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__nat__Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F1F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__F2F1.

Opaque PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Format.

Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Format : T_Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__nat__Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F1F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__F2F1.

Opaque PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Format.


Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Format_list : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Format_Type :=
  (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16__Format, (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16__Format, unit_format)).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list__Format := (*Eval compute in *) seq_format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Format_list.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1 z :=
  (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet1_r16 z, (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__bundleSizeSet2_r16 z, tt)).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F2 (y : seq_type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type i0 i1
  end.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1F2_cond (z : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type)
  : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond z ->
  (seq_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1 z)).
intro H. unfold PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1F2_cond2 (z : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type)
 : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F2 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F2F1_cond (y : seq_type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list)
  : seq_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list y ->
 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F2 y)) /\  PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Format : T_Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond :=
        proj2_format  PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__list__Format
    PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1F2_cond  PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F1F2_cond2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__F2F1_cond.
Opaque PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Format.


Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Format_Type := Eval cbn in get_formats PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Format_list : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Format_Type :=
  (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Format, (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Format, unit__Format)).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list__Format := Eval compute in choice_format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__len_helper1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__len_helper2  PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Format_list.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F1 (z : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type) : (choice PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list) :=
  match z with
   | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16 t => existT _ 0 t
  | PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16 t => existT _ 1 t
  end.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__g := (fun n => typ_set (get_nth_typ PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list n)).
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F2 (y : choice PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list) : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__g n -> PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type) with
    | 0 => fun (t : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16__Type) => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__staticBundling_r16 t 
    | 1 => fun (t : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16__Type) => PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__dynamicBundling_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type with end) n0
           end t0).

Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__helper2 :  forall (y : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type), PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__cond y -> choice_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__helper3 :  forall (y : PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type), PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F2 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__helper4 : (forall b : choice PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list, choice_cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list b -> PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__cond (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F2 b) /\ PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F1 (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F2.
Definition PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Type PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__cond :=
  (* Eval compute in *) proj2_format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__list__Format PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F1 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__F2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__helper2 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__helper3 PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__helper4.
Opaque PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__cond PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__nat__Format PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F1 PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F2 PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F1F2 PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__F2F1.

Opaque PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__cond PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__nat__Format PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F1 PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F2 PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F1F2 PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__F2F1.

Opaque PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__cond PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__nat__Format PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F1 PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F2 PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F1F2 PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__F2F1.

Opaque PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__cond PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__nat__Format PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F1 PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F2 PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F1F2 PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__F2F1.

Opaque PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__cond PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Format : T_Format PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__nat__Format PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F1 PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F2 PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F1F2 PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__F2F1.

Opaque PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__cond PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Format.

Definition PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Format : T_Format PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__nat__Format PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F1 PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F2 PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F1F2 PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__F2F1.

Opaque PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__cond PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Format.

Definition PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__Format : T_Format Z PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__cond :=
 ranged_int_format (0) (1023) PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__helper1 PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__helper2.

Opaque PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__cond PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__Format.

Opaque PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__cond PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__Format.

Opaque PDSCH_Config__ext0O__repetitionSchemeConfig_r16__cond PDSCH_Config__ext0O__repetitionSchemeConfig_r16__Format.


Definition PDSCH_Config__ext0O__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__ext0O__list.
Definition PDSCH_Config__ext0O__Format_list : PDSCH_Config__ext0O__Format_Type :=
  (PDSCH_Config__ext0O__maxMIMO_Layers_r16__Format, (PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16__Format, (PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16__Format, (PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16__Format, (PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16__Format, (PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16__Format, (PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16__Format, (PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16__Format, (PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16__Format, (PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16__Format, (PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16__Format, (PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16__Format, (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16__Format, (PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16__Format, (RateMatchPatternGroup__Format, (RateMatchPatternGroup__Format, (PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16__Format, (PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16__Format, (PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16__Format, (PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16__Format, (PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16__Format, (PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16__Format, (PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16__Format, (PDSCH_Config__ext0O__repetitionSchemeConfig_r16__Format, unit_format)))))))))))))))))))))))).
Definition PDSCH_Config__ext0O__list__Format := (*Eval compute in *) seq_format PDSCH_Config__ext0O__list PDSCH_Config__ext0O__Format_list.
Definition PDSCH_Config__ext0O__F1 z :=
  (PDSCH_Config__ext0O__maxMIMO_Layers_r16 z, (PDSCH_Config__ext0O__minimumSchedulingOffsetK0_r16 z, (PDSCH_Config__ext0O__antennaPortsFieldPresenceDCI_1_2_r16 z, (PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToAddModListDCI_1_2_r16 z, (PDSCH_Config__ext0O__aperiodicZP_CSI_RS_ResourceSetsToReleaseListDCI_1_2_r16 z, (PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeA_DCI_1_2_r16 z, (PDSCH_Config__ext0O__dmrs_DownlinkForPDSCH_MappingTypeB_DCI_1_2_r16 z, (PDSCH_Config__ext0O__dmrs_SequenceInitializationDCI_1_2_r16 z, (PDSCH_Config__ext0O__harq_ProcessNumberSizeDCI_1_2_r16 z, (PDSCH_Config__ext0O__mcs_TableDCI_1_2_r16 z, (PDSCH_Config__ext0O__numberOfBitsForRV_DCI_1_2_r16 z, (PDSCH_Config__ext0O__pdsch_TimeDomainAllocationListDCI_1_2_r16 z, (PDSCH_Config__ext0O__prb_BundlingTypeDCI_1_2_r16 z, (PDSCH_Config__ext0O__priorityIndicatorDCI_1_2_r16 z, (PDSCH_Config__ext0O__rateMatchPatternGroup1DCI_1_2_r16 z, (PDSCH_Config__ext0O__rateMatchPatternGroup2DCI_1_2_r16 z, (PDSCH_Config__ext0O__resourceAllocationType1GranularityDCI_1_2_r16 z, (PDSCH_Config__ext0O__vrb_ToPRB_InterleaverDCI_1_2_r16 z, (PDSCH_Config__ext0O__referenceOfSLIVDCI_1_2_r16 z, (PDSCH_Config__ext0O__resourceAllocationDCI_1_2_r16 z, (PDSCH_Config__ext0O__priorityIndicatorDCI_1_1_r16 z, (PDSCH_Config__ext0O__dataScramblingIdentityPDSCH2_r16 z, (PDSCH_Config__ext0O__pdsch_TimeDomainAllocationList_r16 z, (PDSCH_Config__ext0O__repetitionSchemeConfig_r16 z, tt)))))))))))))))))))))))).
Definition PDSCH_Config__ext0O__F2 (y : seq_type PDSCH_Config__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, _))))))))))))))))))))))))=>
    make__PDSCH_Config__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23
  end.
Lemma PDSCH_Config__ext0O__F1F2_cond (z : PDSCH_Config__ext0O__Type)
  : PDSCH_Config__ext0O__cond z ->
  (seq_cond PDSCH_Config__ext0O__list (PDSCH_Config__ext0O__F1 z)).
intro H. unfold PDSCH_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__ext0O__F1F2_cond2 (z : PDSCH_Config__ext0O__Type)
 : PDSCH_Config__ext0O__F2 (PDSCH_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__ext0O__F2F1_cond (y : seq_type PDSCH_Config__ext0O__list)
  : seq_cond PDSCH_Config__ext0O__list y ->
 (PDSCH_Config__ext0O__cond (PDSCH_Config__ext0O__F2 y)) /\  PDSCH_Config__ext0O__F1 (PDSCH_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__ext0O__Format : T_Format PDSCH_Config__ext0O__Type PDSCH_Config__ext0O__cond :=
        proj2_format  PDSCH_Config__ext0O__cond PDSCH_Config__ext0O__list__Format
    PDSCH_Config__ext0O__F1 PDSCH_Config__ext0O__F2 PDSCH_Config__ext0O__F1F2_cond  PDSCH_Config__ext0O__F1F2_cond2 PDSCH_Config__ext0O__F2F1_cond.
Opaque PDSCH_Config__ext0O__cond PDSCH_Config__ext0O__Format.

Definition PDSCH_Config__ext0__check_all_none (b : PDSCH_Config__ext0O__Type) : bool :=
match b with 
  | make__PDSCH_Config__ext0O__Type None None None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition PDSCH_Config__ext0__Format : T_Format PDSCH_Config__ext0__Type PDSCH_Config__ext0__cond :=
  restrict_add_format PDSCH_Config__ext0__check_all_none PDSCH_Config__ext0O__Format.

Opaque PDSCH_Config__ext0__cond PDSCH_Config__ext0__Format.

Opaque PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__cond PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__Format.


Definition PDSCH_Config__ext1O__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__ext1O__list.
Definition PDSCH_Config__ext1O__Format_list : PDSCH_Config__ext1O__Format_Type :=
  (PDSCH_Config__ext1O__repetitionSchemeConfig_v1630__Format, unit_format).
Definition PDSCH_Config__ext1O__list__Format := (*Eval compute in *) seq_format PDSCH_Config__ext1O__list PDSCH_Config__ext1O__Format_list.
Definition PDSCH_Config__ext1O__F1 z :=
  (PDSCH_Config__ext1O__repetitionSchemeConfig_v1630 z, tt).
Definition PDSCH_Config__ext1O__F2 (y : seq_type PDSCH_Config__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__PDSCH_Config__ext1O__Type i0
  end.
Lemma PDSCH_Config__ext1O__F1F2_cond (z : PDSCH_Config__ext1O__Type)
  : PDSCH_Config__ext1O__cond z ->
  (seq_cond PDSCH_Config__ext1O__list (PDSCH_Config__ext1O__F1 z)).
intro H. unfold PDSCH_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__ext1O__F1F2_cond2 (z : PDSCH_Config__ext1O__Type)
 : PDSCH_Config__ext1O__F2 (PDSCH_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__ext1O__F2F1_cond (y : seq_type PDSCH_Config__ext1O__list)
  : seq_cond PDSCH_Config__ext1O__list y ->
 (PDSCH_Config__ext1O__cond (PDSCH_Config__ext1O__F2 y)) /\  PDSCH_Config__ext1O__F1 (PDSCH_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__ext1O__Format : T_Format PDSCH_Config__ext1O__Type PDSCH_Config__ext1O__cond :=
        proj2_format  PDSCH_Config__ext1O__cond PDSCH_Config__ext1O__list__Format
    PDSCH_Config__ext1O__F1 PDSCH_Config__ext1O__F2 PDSCH_Config__ext1O__F1F2_cond  PDSCH_Config__ext1O__F1F2_cond2 PDSCH_Config__ext1O__F2F1_cond.
Opaque PDSCH_Config__ext1O__cond PDSCH_Config__ext1O__Format.

Definition PDSCH_Config__ext1__check_all_none (b : PDSCH_Config__ext1O__Type) : bool :=
match b with 
  | make__PDSCH_Config__ext1O__Type None  => false 
  | _ => true 
 end.
Definition PDSCH_Config__ext1__Format : T_Format PDSCH_Config__ext1__Type PDSCH_Config__ext1__cond :=
  restrict_add_format PDSCH_Config__ext1__check_all_none PDSCH_Config__ext1O__Format.

Opaque PDSCH_Config__ext1__cond PDSCH_Config__ext1__Format.

Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Format : T_Format PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__nat__Format PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F1 PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F2 PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F1F2 PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__F2F1.

Opaque PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__cond PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Format.

Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Format : T_Format PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__nat__Format PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F1 PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F2 PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F1F2 PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__F2F1.

Opaque PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__cond PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Format.

Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Format : T_Format PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__nat__Format PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F1 PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F2 PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F1F2 PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__F2F1.

Opaque PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__cond PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Format.

Definition PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Format : T_Format PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__nat__Format PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F1 PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F2 PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F1F2 PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__F2F1.

Opaque PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__cond PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Format.

Definition PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Format : T_Format PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__nat__Format PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F1 PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F2 PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F1F2 PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__F2F1.

Opaque PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__cond PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Format.

Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__Format : T_Format PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__Type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__cond := seq_of_format TCI_State__Format 1 maxNrofTCI_States PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__helper1 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__helper2.

Opaque PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__Format.

Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__Format : T_Format PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__Type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__cond := seq_of_format TCI_StateId__Format 1 maxNrofTCI_States PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__helper1 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__helper2.

Opaque PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__Format.


Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Format_list : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Format_Type :=
  (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17__Format, (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17__Format, unit_format)).
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list__Format := (*Eval compute in *) seq_format PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Format_list.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1 z :=
  (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToAddModList_r17 z, (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__dl_OrJointTCI_StateToReleaseList_r17 z, tt)).
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F2 (y : seq_type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type i0 i1
  end.
Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1F2_cond (z : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type)
  : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond z ->
  (seq_cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1 z)).
intro H. unfold PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1F2_cond2 (z : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type)
 : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F2 (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F2F1_cond (y : seq_type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list)
  : seq_cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list y ->
 (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F2 y)) /\  PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1 (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Format : T_Format PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond :=
        proj2_format  PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__list__Format
    PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F2 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1F2_cond  PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F1F2_cond2 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__F2F1_cond.
Opaque PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Format.


Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Format_Type := Eval cbn in get_formats PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Format_list : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Format_Type :=
  (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Format, (ServingCellAndBWP_Id_r17__Format, unit__Format)).
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list__Format := Eval compute in choice_format PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__len_helper1 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__len_helper2  PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Format_list.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F1 (z : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type) : (choice PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list) :=
  match z with
   | PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist t => existT _ 0 t
  | PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__unifiedTCI_StateRef_r17 t => existT _ 1 t
  end.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__g := (fun n => typ_set (get_nth_typ PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list n)).
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F2 (y : choice PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list) : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__g n -> PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type) with
    | 0 => fun (t : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist__Type) => PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__explicitlist t 
    | 1 => fun (t : ServingCellAndBWP_Id_r17__Type) => PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__unifiedTCI_StateRef_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type with end) n0
           end t0).

Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__helper2 :  forall (y : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type), PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__cond y -> choice_cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__helper3 :  forall (y : PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type), PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F2 (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__helper4 : (forall b : choice PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list, choice_cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list b -> PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__cond (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F2 b) /\ PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F1 (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F1 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F2.
Definition PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Format : T_Format PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Type PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__cond :=
  (* Eval compute in *) proj2_format PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__list__Format PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F1 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__F2 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__helper2 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__helper3 PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__helper4.
Opaque PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__cond PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Format.

Definition PDSCH_Config__ext2O__beamAppTime_r17__Format : T_Format PDSCH_Config__ext2O__beamAppTime_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__beamAppTime_r17__nat__Format PDSCH_Config__ext2O__beamAppTime_r17__F1 PDSCH_Config__ext2O__beamAppTime_r17__F2 PDSCH_Config__ext2O__beamAppTime_r17__F1F2 PDSCH_Config__ext2O__beamAppTime_r17__F2F1.

Opaque PDSCH_Config__ext2O__beamAppTime_r17__cond PDSCH_Config__ext2O__beamAppTime_r17__Format.

Opaque PDSCH_Config__ext2O__dummy__cond PDSCH_Config__ext2O__dummy__Format.

Definition PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Format : T_Format PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__nat__Format PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F1 PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F2 PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F1F2 PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__F2F1.

Opaque PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__cond PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Format.

Opaque PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__cond PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__Format.

Definition PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__Format : T_Format Z PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__cond :=
 ranged_int_format (0) (5) PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__helper1 PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__helper2.

Opaque PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__cond PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__Format.

Definition PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__Format : T_Format Z PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__cond := fixed_int_format 5. Opaque PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__cond PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__Format.

Definition PDSCH_Config__ext2O__mcs_Table_r17__Format : T_Format PDSCH_Config__ext2O__mcs_Table_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__mcs_Table_r17__nat__Format PDSCH_Config__ext2O__mcs_Table_r17__F1 PDSCH_Config__ext2O__mcs_Table_r17__F2 PDSCH_Config__ext2O__mcs_Table_r17__F1F2 PDSCH_Config__ext2O__mcs_Table_r17__F2F1.

Opaque PDSCH_Config__ext2O__mcs_Table_r17__cond PDSCH_Config__ext2O__mcs_Table_r17__Format.

Definition PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Format : T_Format PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__nat__Format PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F1 PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F2 PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F1F2 PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__F2F1.

Opaque PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__cond PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Format.

Definition PDSCH_Config__ext2O__xOverheadMulticast_r17__Format : T_Format PDSCH_Config__ext2O__xOverheadMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__xOverheadMulticast_r17__nat__Format PDSCH_Config__ext2O__xOverheadMulticast_r17__F1 PDSCH_Config__ext2O__xOverheadMulticast_r17__F2 PDSCH_Config__ext2O__xOverheadMulticast_r17__F1F2 PDSCH_Config__ext2O__xOverheadMulticast_r17__F2F1.

Opaque PDSCH_Config__ext2O__xOverheadMulticast_r17__cond PDSCH_Config__ext2O__xOverheadMulticast_r17__Format.

Definition PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Format : T_Format PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__nat__Format PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F1 PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F2 PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F1F2 PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__F2F1.

Opaque PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__cond PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Format.

Definition PDSCH_Config__ext2O__sizeDCI_4_2_r17__Format : T_Format Z PDSCH_Config__ext2O__sizeDCI_4_2_r17__cond :=
 ranged_int_format (20) (maxDCI_4_2_Size_r17) PDSCH_Config__ext2O__sizeDCI_4_2_r17__helper1 PDSCH_Config__ext2O__sizeDCI_4_2_r17__helper2.

Opaque PDSCH_Config__ext2O__sizeDCI_4_2_r17__cond PDSCH_Config__ext2O__sizeDCI_4_2_r17__Format.


Definition PDSCH_Config__ext2O__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__ext2O__list.
Definition PDSCH_Config__ext2O__Format_list : PDSCH_Config__ext2O__Format_Type :=
  (PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17__Format, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17__Format, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17__Format, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17__Format, (PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17__Format, (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17__Format, (PDSCH_Config__ext2O__beamAppTime_r17__Format, (PDSCH_Config__ext2O__dummy__Format, (PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17__Format, (PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17__Format, (PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700__Format, (PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17__Format, (PDSCH_Config__ext2O__mcs_Table_r17__Format, (PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17__Format, (PDSCH_Config__ext2O__xOverheadMulticast_r17__Format, (PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17__Format, (PDSCH_Config__ext2O__sizeDCI_4_2_r17__Format, unit_format))))))))))))))))).
Definition PDSCH_Config__ext2O__list__Format := (*Eval compute in *) seq_format PDSCH_Config__ext2O__list PDSCH_Config__ext2O__Format_list.
Definition PDSCH_Config__ext2O__F1 z :=
  (PDSCH_Config__ext2O__pdsch_HARQ_ACK_OneShotFeedbackDCI_1_2_r17 z, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_1_2_r17 z, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_EnhType3DCI_Field_1_2_r17 z, (PDSCH_Config__ext2O__pdsch_HARQ_ACK_RetxDCI_1_2_r17 z, (PDSCH_Config__ext2O__pucch_sSCellDynDCI_1_2_r17 z, (PDSCH_Config__ext2O__dl_OrJointTCI_StateList_r17 z, (PDSCH_Config__ext2O__beamAppTime_r17 z, (PDSCH_Config__ext2O__dummy z, (PDSCH_Config__ext2O__dmrs_FD_OCC_DisabledForRank1_PDSCH_r17 z, (PDSCH_Config__ext2O__minimumSchedulingOffsetK0_r17 z, (PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_2_v1700 z, (PDSCH_Config__ext2O__harq_ProcessNumberSizeDCI_1_1_r17 z, (PDSCH_Config__ext2O__mcs_Table_r17 z, (PDSCH_Config__ext2O__mcs_TableDCI_1_2_r17 z, (PDSCH_Config__ext2O__xOverheadMulticast_r17 z, (PDSCH_Config__ext2O__priorityIndicatorDCI_4_2_r17 z, (PDSCH_Config__ext2O__sizeDCI_4_2_r17 z, tt))))))))))))))))).
Definition PDSCH_Config__ext2O__F2 (y : seq_type PDSCH_Config__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, _)))))))))))))))))=>
    make__PDSCH_Config__ext2O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16
  end.
Lemma PDSCH_Config__ext2O__F1F2_cond (z : PDSCH_Config__ext2O__Type)
  : PDSCH_Config__ext2O__cond z ->
  (seq_cond PDSCH_Config__ext2O__list (PDSCH_Config__ext2O__F1 z)).
intro H. unfold PDSCH_Config__ext2O__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__ext2O__F1F2_cond2 (z : PDSCH_Config__ext2O__Type)
 : PDSCH_Config__ext2O__F2 (PDSCH_Config__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__ext2O__F2F1_cond (y : seq_type PDSCH_Config__ext2O__list)
  : seq_cond PDSCH_Config__ext2O__list y ->
 (PDSCH_Config__ext2O__cond (PDSCH_Config__ext2O__F2 y)) /\  PDSCH_Config__ext2O__F1 (PDSCH_Config__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__ext2O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__ext2O__Format : T_Format PDSCH_Config__ext2O__Type PDSCH_Config__ext2O__cond :=
        proj2_format  PDSCH_Config__ext2O__cond PDSCH_Config__ext2O__list__Format
    PDSCH_Config__ext2O__F1 PDSCH_Config__ext2O__F2 PDSCH_Config__ext2O__F1F2_cond  PDSCH_Config__ext2O__F1F2_cond2 PDSCH_Config__ext2O__F2F1_cond.
Opaque PDSCH_Config__ext2O__cond PDSCH_Config__ext2O__Format.

Definition PDSCH_Config__ext2__check_all_none (b : PDSCH_Config__ext2O__Type) : bool :=
match b with 
  | make__PDSCH_Config__ext2O__Type None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition PDSCH_Config__ext2__Format : T_Format PDSCH_Config__ext2__Type PDSCH_Config__ext2__cond :=
  restrict_add_format PDSCH_Config__ext2__check_all_none PDSCH_Config__ext2O__Format.

Opaque PDSCH_Config__ext2__cond PDSCH_Config__ext2__Format.

Opaque PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__cond PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__Format.


Definition PDSCH_Config__ext3O__Format_Type := Eval cbn in seq_format_prod PDSCH_Config__ext3O__list.
Definition PDSCH_Config__ext3O__Format_list : PDSCH_Config__ext3O__Format_Type :=
  (PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17__Format, unit_format).
Definition PDSCH_Config__ext3O__list__Format := (*Eval compute in *) seq_format PDSCH_Config__ext3O__list PDSCH_Config__ext3O__Format_list.
Definition PDSCH_Config__ext3O__F1 z :=
  (PDSCH_Config__ext3O__pdsch_TimeDomainAllocationListForMultiPDSCH_r17 z, tt).
Definition PDSCH_Config__ext3O__F2 (y : seq_type PDSCH_Config__ext3O__list) :=
  match y with
  | (i0, _)=>
    make__PDSCH_Config__ext3O__Type i0
  end.
Lemma PDSCH_Config__ext3O__F1F2_cond (z : PDSCH_Config__ext3O__Type)
  : PDSCH_Config__ext3O__cond z ->
  (seq_cond PDSCH_Config__ext3O__list (PDSCH_Config__ext3O__F1 z)).
intro H. unfold PDSCH_Config__ext3O__cond in H. simpl. auto. Qed.
Lemma PDSCH_Config__ext3O__F1F2_cond2 (z : PDSCH_Config__ext3O__Type)
 : PDSCH_Config__ext3O__F2 (PDSCH_Config__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PDSCH_Config__ext3O__F2F1_cond (y : seq_type PDSCH_Config__ext3O__list)
  : seq_cond PDSCH_Config__ext3O__list y ->
 (PDSCH_Config__ext3O__cond (PDSCH_Config__ext3O__F2 y)) /\  PDSCH_Config__ext3O__F1 (PDSCH_Config__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PDSCH_Config__ext3O__cond. simpl in *. auto.
 - simpl. unfold PDSCH_Config__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PDSCH_Config__ext3O__Format : T_Format PDSCH_Config__ext3O__Type PDSCH_Config__ext3O__cond :=
        proj2_format  PDSCH_Config__ext3O__cond PDSCH_Config__ext3O__list__Format
    PDSCH_Config__ext3O__F1 PDSCH_Config__ext3O__F2 PDSCH_Config__ext3O__F1F2_cond  PDSCH_Config__ext3O__F1F2_cond2 PDSCH_Config__ext3O__F2F1_cond.
Opaque PDSCH_Config__ext3O__cond PDSCH_Config__ext3O__Format.

Definition PDSCH_Config__ext3__check_all_none (b : PDSCH_Config__ext3O__Type) : bool :=
match b with 
  | make__PDSCH_Config__ext3O__Type None  => false 
  | _ => true 
 end.
Definition PDSCH_Config__ext3__Format : T_Format PDSCH_Config__ext3__Type PDSCH_Config__ext3__cond :=
  restrict_add_format PDSCH_Config__ext3__check_all_none PDSCH_Config__ext3O__Format.

Opaque PDSCH_Config__ext3__cond PDSCH_Config__ext3__Format.


Definition PDSCH_Config__root_Format_Type := Eval cbn in seq_format_prod PDSCH_Config__root_list.
Definition PDSCH_Config__root_Format_list : PDSCH_Config__root_Format_Type :=
  (PDSCH_Config__dataScramblingIdentityPDSCH__Format, (PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA__Format, (PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB__Format, (PDSCH_Config__tci_StatesToAddModList__Format, (PDSCH_Config__tci_StatesToReleaseList__Format, (PDSCH_Config__vrb_ToPRB_Interleaver__Format, (PDSCH_Config__resourceAllocation__Format, (PDSCH_Config__pdsch_TimeDomainAllocationList__Format, (PDSCH_Config__pdsch_AggregationFactor__Format, (PDSCH_Config__rateMatchPatternToAddModList__Format, (PDSCH_Config__rateMatchPatternToReleaseList__Format, (RateMatchPatternGroup__Format, (RateMatchPatternGroup__Format, (PDSCH_Config__rbg_Size__Format, (PDSCH_Config__mcs_Table__Format, (PDSCH_Config__maxNrofCodeWordsScheduledByDCI__Format, (PDSCH_Config__prb_BundlingType__Format, (PDSCH_Config__zp_CSI_RS_ResourceToAddModList__Format, (PDSCH_Config__zp_CSI_RS_ResourceToReleaseList__Format, (PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList__Format, (PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList__Format, (PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList__Format, (PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList__Format, (PDSCH_Config__p_ZP_CSI_RS_ResourceSet__Format, unit_format)))))))))))))))))))))))).

Definition PDSCH_Config__ext_Format_Type := Eval cbn in get_formats PDSCH_Config__ext_list.
Definition PDSCH_Config__ext_Format_list : PDSCH_Config__ext_Format_Type :=
  (PDSCH_Config__ext0__Format, (PDSCH_Config__ext1__Format, (PDSCH_Config__ext2__Format, (PDSCH_Config__ext3__Format, unit__Format)))).

Definition PDSCH_Config__list_type : Set := (seq_type PDSCH_Config__root_list) * (seq_ext_type PDSCH_Config__ext_list).
Definition PDSCH_Config__list_cond (z : PDSCH_Config__list_type) : Prop :=
        (seq_cond PDSCH_Config__root_list (fst z)) /\ (seq_ext_cond PDSCH_Config__ext_list (snd z)).
Definition PDSCH_Config__list_format : T_Format PDSCH_Config__list_type PDSCH_Config__list_cond :=
 (* Eval compute in *) seq_ext_format PDSCH_Config__root_list PDSCH_Config__root_Format_list PDSCH_Config__ext_list PDSCH_Config__ext_Format_list.

Opaque PDSCH_Config__list_format.
Definition PDSCH_Config__F1 (z : PDSCH_Config__Type) : PDSCH_Config__list_type :=
  (((PDSCH_Config__dataScramblingIdentityPDSCH z, (PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeA z, (PDSCH_Config__dmrs_DownlinkForPDSCH_MappingTypeB z, (PDSCH_Config__tci_StatesToAddModList z, (PDSCH_Config__tci_StatesToReleaseList z, (PDSCH_Config__vrb_ToPRB_Interleaver z, (PDSCH_Config__resourceAllocation z, (PDSCH_Config__pdsch_TimeDomainAllocationList z, (PDSCH_Config__pdsch_AggregationFactor z, (PDSCH_Config__rateMatchPatternToAddModList z, (PDSCH_Config__rateMatchPatternToReleaseList z, (PDSCH_Config__rateMatchPatternGroup1 z, (PDSCH_Config__rateMatchPatternGroup2 z, (PDSCH_Config__rbg_Size z, (PDSCH_Config__mcs_Table z, (PDSCH_Config__maxNrofCodeWordsScheduledByDCI z, (PDSCH_Config__prb_BundlingType z, (PDSCH_Config__zp_CSI_RS_ResourceToAddModList z, (PDSCH_Config__zp_CSI_RS_ResourceToReleaseList z, (PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToAddModList z, (PDSCH_Config__aperiodic_ZP_CSI_RS_ResourceSetsToReleaseList z, (PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToAddModList z, (PDSCH_Config__sp_ZP_CSI_RS_ResourceSetsToReleaseList z, (PDSCH_Config__p_ZP_CSI_RS_ResourceSet z, tt))))))))))))))))))))))))), (
(PDSCH_Config__ext0 z, (PDSCH_Config__ext1 z, (PDSCH_Config__ext2 z, (PDSCH_Config__ext3 z, tt)))))).
Definition PDSCH_Config__F2 (y : PDSCH_Config__list_type) : PDSCH_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, (j18, (j19, (j20, (j21, (j22, (j23, _)))))))))))))))))))))))), (i0, (i1, (i2, (i3, _)))))=>
    make__PDSCH_Config__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j22 j23 i0 i1 i2 i3
  end.
Definition PDSCH_Config__helper1 : (forall a : PDSCH_Config__Type, PDSCH_Config__cond a -> PDSCH_Config__list_cond (PDSCH_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PDSCH_Config__helper2 : (forall a : PDSCH_Config__Type, PDSCH_Config__F2 (PDSCH_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PDSCH_Config__helper3 : (forall b : PDSCH_Config__list_type, PDSCH_Config__list_cond b -> PDSCH_Config__cond (PDSCH_Config__F2 b) /\ PDSCH_Config__F1 (PDSCH_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PDSCH_Config__cond, PDSCH_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PDSCH_Config__Format : T_Format PDSCH_Config__Type PDSCH_Config__cond :=
 proj2_format PDSCH_Config__cond PDSCH_Config__list_format  PDSCH_Config__F1 PDSCH_Config__F2 PDSCH_Config__helper1 PDSCH_Config__helper2 PDSCH_Config__helper3.

Opaque PDSCH_Config__cond PDSCH_Config__Format.

