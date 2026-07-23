Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PUSCH_Config__dataScramblingIdentityPUSCH__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma PUSCH_Config__dataScramblingIdentityPUSCH__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__dataScramblingIdentityPUSCH__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__dataScramblingIdentityPUSCH__Type := Z.
Definition PUSCH_Config__dataScramblingIdentityPUSCH__cond := (fun z => (0 <= z <= 1023)%Z).
Inductive PUSCH_Config__txConfig__Type : Set :=
 | PUSCH_Config__txConfig__codebook
 | PUSCH_Config__txConfig__nonCodebook
.
Definition PUSCH_Config__txConfig__cond := (fun (_ : PUSCH_Config__txConfig__Type) => True).
Lemma PUSCH_Config__txConfig__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__txConfig__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__txConfig__nat__helper.

Definition PUSCH_Config__txConfig__F1 t :=
  match t with
  | PUSCH_Config__txConfig__codebook => 0
  | PUSCH_Config__txConfig__nonCodebook => 1
  end.
Definition PUSCH_Config__txConfig__F2 n :=
  match n with
  | 0 => PUSCH_Config__txConfig__codebook
  | 1 => PUSCH_Config__txConfig__nonCodebook
  | _ => PUSCH_Config__txConfig__codebook
  end.
Lemma PUSCH_Config__txConfig__F1F2 : forall x : PUSCH_Config__txConfig__Type, (PUSCH_Config__txConfig__F1 x <= 1) /\ PUSCH_Config__txConfig__F2 (PUSCH_Config__txConfig__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__txConfig__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__txConfig__F1 (PUSCH_Config__txConfig__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.DMRS_UplinkConfig.
Definition PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__Type := SetupRelease__Type DMRS_UplinkConfig__Type.
Definition PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__cond := SetupRelease__cond _ DMRS_UplinkConfig__cond.
Definition PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__Format : T_Format PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__Type PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__cond := SetupRelease__Format _ _ DMRS_UplinkConfig__Format.
Opaque PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__cond PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__Format.

Require Import NR.SetupRelease.
Require Import NR.DMRS_UplinkConfig.
Definition PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__Type := SetupRelease__Type DMRS_UplinkConfig__Type.
Definition PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__cond := SetupRelease__cond _ DMRS_UplinkConfig__cond.
Definition PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__Format : T_Format PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__Type PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__cond := SetupRelease__Format _ _ DMRS_UplinkConfig__Format.
Opaque PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__cond PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__Format.

Require Import NR.PUSCH_PowerControl.

Opaque PUSCH_PowerControl__cond PUSCH_PowerControl__Format.

Inductive PUSCH_Config__frequencyHopping__Type : Set :=
 | PUSCH_Config__frequencyHopping__intraSlot
 | PUSCH_Config__frequencyHopping__interSlot
.
Definition PUSCH_Config__frequencyHopping__cond := (fun (_ : PUSCH_Config__frequencyHopping__Type) => True).
Lemma PUSCH_Config__frequencyHopping__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__frequencyHopping__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__frequencyHopping__nat__helper.

Definition PUSCH_Config__frequencyHopping__F1 t :=
  match t with
  | PUSCH_Config__frequencyHopping__intraSlot => 0
  | PUSCH_Config__frequencyHopping__interSlot => 1
  end.
Definition PUSCH_Config__frequencyHopping__F2 n :=
  match n with
  | 0 => PUSCH_Config__frequencyHopping__intraSlot
  | 1 => PUSCH_Config__frequencyHopping__interSlot
  | _ => PUSCH_Config__frequencyHopping__intraSlot
  end.
Lemma PUSCH_Config__frequencyHopping__F1F2 : forall x : PUSCH_Config__frequencyHopping__Type, (PUSCH_Config__frequencyHopping__F1 x <= 1) /\ PUSCH_Config__frequencyHopping__F2 (PUSCH_Config__frequencyHopping__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__frequencyHopping__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__frequencyHopping__F1 (PUSCH_Config__frequencyHopping__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_Config__frequencyHoppingOffsetLists__seq_of__helper1 : (1 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma PUSCH_Config__frequencyHoppingOffsetLists__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__frequencyHoppingOffsetLists__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__frequencyHoppingOffsetLists__seq_of__Type := Z.
Definition PUSCH_Config__frequencyHoppingOffsetLists__seq_of__cond := (fun z => (1 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Definition PUSCH_Config__frequencyHoppingOffsetLists__Type := list Z.

Lemma PUSCH_Config__frequencyHoppingOffsetLists__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma PUSCH_Config__frequencyHoppingOffsetLists__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__frequencyHoppingOffsetLists__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__frequencyHoppingOffsetLists__cond (z : PUSCH_Config__frequencyHoppingOffsetLists__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and PUSCH_Config__frequencyHoppingOffsetLists__seq_of__cond z) .

Inductive PUSCH_Config__resourceAllocation__Type : Set :=
 | PUSCH_Config__resourceAllocation__resourceAllocationType0
 | PUSCH_Config__resourceAllocation__resourceAllocationType1
 | PUSCH_Config__resourceAllocation__dynamicSwitch
.
Definition PUSCH_Config__resourceAllocation__cond := (fun (_ : PUSCH_Config__resourceAllocation__Type) => True).
Lemma PUSCH_Config__resourceAllocation__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__resourceAllocation__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUSCH_Config__resourceAllocation__nat__helper.

Definition PUSCH_Config__resourceAllocation__F1 t :=
  match t with
  | PUSCH_Config__resourceAllocation__resourceAllocationType0 => 0
  | PUSCH_Config__resourceAllocation__resourceAllocationType1 => 1
  | PUSCH_Config__resourceAllocation__dynamicSwitch => 2
  end.
Definition PUSCH_Config__resourceAllocation__F2 n :=
  match n with
  | 0 => PUSCH_Config__resourceAllocation__resourceAllocationType0
  | 1 => PUSCH_Config__resourceAllocation__resourceAllocationType1
  | 2 => PUSCH_Config__resourceAllocation__dynamicSwitch
  | _ => PUSCH_Config__resourceAllocation__resourceAllocationType0
  end.
Lemma PUSCH_Config__resourceAllocation__F1F2 : forall x : PUSCH_Config__resourceAllocation__Type, (PUSCH_Config__resourceAllocation__F1 x <= 2) /\ PUSCH_Config__resourceAllocation__F2 (PUSCH_Config__resourceAllocation__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__resourceAllocation__F2F1 : forall (y : nat) (H : y <= 2), PUSCH_Config__resourceAllocation__F1 (PUSCH_Config__resourceAllocation__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_TimeDomainResourceAllocationList.
Definition PUSCH_Config__pusch_TimeDomainAllocationList__Type := SetupRelease__Type PUSCH_TimeDomainResourceAllocationList__Type.
Definition PUSCH_Config__pusch_TimeDomainAllocationList__cond := SetupRelease__cond _ PUSCH_TimeDomainResourceAllocationList__cond.
Definition PUSCH_Config__pusch_TimeDomainAllocationList__Format : T_Format PUSCH_Config__pusch_TimeDomainAllocationList__Type PUSCH_Config__pusch_TimeDomainAllocationList__cond := SetupRelease__Format _ _ PUSCH_TimeDomainResourceAllocationList__Format.
Opaque PUSCH_Config__pusch_TimeDomainAllocationList__cond PUSCH_Config__pusch_TimeDomainAllocationList__Format.

Inductive PUSCH_Config__pusch_AggregationFactor__Type : Set :=
 | PUSCH_Config__pusch_AggregationFactor__n2
 | PUSCH_Config__pusch_AggregationFactor__n4
 | PUSCH_Config__pusch_AggregationFactor__n8
.
Definition PUSCH_Config__pusch_AggregationFactor__cond := (fun (_ : PUSCH_Config__pusch_AggregationFactor__Type) => True).
Lemma PUSCH_Config__pusch_AggregationFactor__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__pusch_AggregationFactor__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUSCH_Config__pusch_AggregationFactor__nat__helper.

Definition PUSCH_Config__pusch_AggregationFactor__F1 t :=
  match t with
  | PUSCH_Config__pusch_AggregationFactor__n2 => 0
  | PUSCH_Config__pusch_AggregationFactor__n4 => 1
  | PUSCH_Config__pusch_AggregationFactor__n8 => 2
  end.
Definition PUSCH_Config__pusch_AggregationFactor__F2 n :=
  match n with
  | 0 => PUSCH_Config__pusch_AggregationFactor__n2
  | 1 => PUSCH_Config__pusch_AggregationFactor__n4
  | 2 => PUSCH_Config__pusch_AggregationFactor__n8
  | _ => PUSCH_Config__pusch_AggregationFactor__n2
  end.
Lemma PUSCH_Config__pusch_AggregationFactor__F1F2 : forall x : PUSCH_Config__pusch_AggregationFactor__Type, (PUSCH_Config__pusch_AggregationFactor__F1 x <= 2) /\ PUSCH_Config__pusch_AggregationFactor__F2 (PUSCH_Config__pusch_AggregationFactor__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__pusch_AggregationFactor__F2F1 : forall (y : nat) (H : y <= 2), PUSCH_Config__pusch_AggregationFactor__F1 (PUSCH_Config__pusch_AggregationFactor__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__mcs_Table__Type : Set :=
 | PUSCH_Config__mcs_Table__qam256
 | PUSCH_Config__mcs_Table__qam64LowSE
.
Definition PUSCH_Config__mcs_Table__cond := (fun (_ : PUSCH_Config__mcs_Table__Type) => True).
Lemma PUSCH_Config__mcs_Table__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__mcs_Table__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__mcs_Table__nat__helper.

Definition PUSCH_Config__mcs_Table__F1 t :=
  match t with
  | PUSCH_Config__mcs_Table__qam256 => 0
  | PUSCH_Config__mcs_Table__qam64LowSE => 1
  end.
Definition PUSCH_Config__mcs_Table__F2 n :=
  match n with
  | 0 => PUSCH_Config__mcs_Table__qam256
  | 1 => PUSCH_Config__mcs_Table__qam64LowSE
  | _ => PUSCH_Config__mcs_Table__qam256
  end.
Lemma PUSCH_Config__mcs_Table__F1F2 : forall x : PUSCH_Config__mcs_Table__Type, (PUSCH_Config__mcs_Table__F1 x <= 1) /\ PUSCH_Config__mcs_Table__F2 (PUSCH_Config__mcs_Table__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__mcs_Table__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__mcs_Table__F1 (PUSCH_Config__mcs_Table__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__mcs_TableTransformPrecoder__Type : Set :=
 | PUSCH_Config__mcs_TableTransformPrecoder__qam256
 | PUSCH_Config__mcs_TableTransformPrecoder__qam64LowSE
.
Definition PUSCH_Config__mcs_TableTransformPrecoder__cond := (fun (_ : PUSCH_Config__mcs_TableTransformPrecoder__Type) => True).
Lemma PUSCH_Config__mcs_TableTransformPrecoder__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__mcs_TableTransformPrecoder__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__mcs_TableTransformPrecoder__nat__helper.

Definition PUSCH_Config__mcs_TableTransformPrecoder__F1 t :=
  match t with
  | PUSCH_Config__mcs_TableTransformPrecoder__qam256 => 0
  | PUSCH_Config__mcs_TableTransformPrecoder__qam64LowSE => 1
  end.
Definition PUSCH_Config__mcs_TableTransformPrecoder__F2 n :=
  match n with
  | 0 => PUSCH_Config__mcs_TableTransformPrecoder__qam256
  | 1 => PUSCH_Config__mcs_TableTransformPrecoder__qam64LowSE
  | _ => PUSCH_Config__mcs_TableTransformPrecoder__qam256
  end.
Lemma PUSCH_Config__mcs_TableTransformPrecoder__F1F2 : forall x : PUSCH_Config__mcs_TableTransformPrecoder__Type, (PUSCH_Config__mcs_TableTransformPrecoder__F1 x <= 1) /\ PUSCH_Config__mcs_TableTransformPrecoder__F2 (PUSCH_Config__mcs_TableTransformPrecoder__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__mcs_TableTransformPrecoder__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__mcs_TableTransformPrecoder__F1 (PUSCH_Config__mcs_TableTransformPrecoder__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__transformPrecoder__Type : Set :=
 | PUSCH_Config__transformPrecoder__enabled
 | PUSCH_Config__transformPrecoder__disabled
.
Definition PUSCH_Config__transformPrecoder__cond := (fun (_ : PUSCH_Config__transformPrecoder__Type) => True).
Lemma PUSCH_Config__transformPrecoder__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__transformPrecoder__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__transformPrecoder__nat__helper.

Definition PUSCH_Config__transformPrecoder__F1 t :=
  match t with
  | PUSCH_Config__transformPrecoder__enabled => 0
  | PUSCH_Config__transformPrecoder__disabled => 1
  end.
Definition PUSCH_Config__transformPrecoder__F2 n :=
  match n with
  | 0 => PUSCH_Config__transformPrecoder__enabled
  | 1 => PUSCH_Config__transformPrecoder__disabled
  | _ => PUSCH_Config__transformPrecoder__enabled
  end.
Lemma PUSCH_Config__transformPrecoder__F1F2 : forall x : PUSCH_Config__transformPrecoder__Type, (PUSCH_Config__transformPrecoder__F1 x <= 1) /\ PUSCH_Config__transformPrecoder__F2 (PUSCH_Config__transformPrecoder__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__transformPrecoder__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__transformPrecoder__F1 (PUSCH_Config__transformPrecoder__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__codebookSubset__Type : Set :=
 | PUSCH_Config__codebookSubset__fullyAndPartialAndNonCoherent
 | PUSCH_Config__codebookSubset__partialAndNonCoherent
 | PUSCH_Config__codebookSubset__nonCoherent
.
Definition PUSCH_Config__codebookSubset__cond := (fun (_ : PUSCH_Config__codebookSubset__Type) => True).
Lemma PUSCH_Config__codebookSubset__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__codebookSubset__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUSCH_Config__codebookSubset__nat__helper.

Definition PUSCH_Config__codebookSubset__F1 t :=
  match t with
  | PUSCH_Config__codebookSubset__fullyAndPartialAndNonCoherent => 0
  | PUSCH_Config__codebookSubset__partialAndNonCoherent => 1
  | PUSCH_Config__codebookSubset__nonCoherent => 2
  end.
Definition PUSCH_Config__codebookSubset__F2 n :=
  match n with
  | 0 => PUSCH_Config__codebookSubset__fullyAndPartialAndNonCoherent
  | 1 => PUSCH_Config__codebookSubset__partialAndNonCoherent
  | 2 => PUSCH_Config__codebookSubset__nonCoherent
  | _ => PUSCH_Config__codebookSubset__fullyAndPartialAndNonCoherent
  end.
Lemma PUSCH_Config__codebookSubset__F1F2 : forall x : PUSCH_Config__codebookSubset__Type, (PUSCH_Config__codebookSubset__F1 x <= 2) /\ PUSCH_Config__codebookSubset__F2 (PUSCH_Config__codebookSubset__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__codebookSubset__F2F1 : forall (y : nat) (H : y <= 2), PUSCH_Config__codebookSubset__F1 (PUSCH_Config__codebookSubset__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_Config__maxRank__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma PUSCH_Config__maxRank__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__maxRank__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__maxRank__Type := Z.
Definition PUSCH_Config__maxRank__cond := (fun z => (1 <= z <= 4)%Z).
Inductive PUSCH_Config__rbg_Size__Type : Set :=
 | PUSCH_Config__rbg_Size__config2
.
Definition PUSCH_Config__rbg_Size__cond := (fun (_ : PUSCH_Config__rbg_Size__Type) => True).
Lemma PUSCH_Config__rbg_Size__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__rbg_Size__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__rbg_Size__nat__helper.

Definition PUSCH_Config__rbg_Size__F1 t :=
  match t with
  | PUSCH_Config__rbg_Size__config2 => 0
  end.
Definition PUSCH_Config__rbg_Size__F2 n :=
  match n with
  | 0 => PUSCH_Config__rbg_Size__config2
  | _ => PUSCH_Config__rbg_Size__config2
  end.
Lemma PUSCH_Config__rbg_Size__F1F2 : forall x : PUSCH_Config__rbg_Size__Type, (PUSCH_Config__rbg_Size__F1 x <= 0) /\ PUSCH_Config__rbg_Size__F2 (PUSCH_Config__rbg_Size__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__rbg_Size__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__rbg_Size__F1 (PUSCH_Config__rbg_Size__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.UCI_OnPUSCH.
Definition PUSCH_Config__uci_OnPUSCH__Type := SetupRelease__Type UCI_OnPUSCH__Type.
Definition PUSCH_Config__uci_OnPUSCH__cond := SetupRelease__cond _ UCI_OnPUSCH__cond.
Definition PUSCH_Config__uci_OnPUSCH__Format : T_Format PUSCH_Config__uci_OnPUSCH__Type PUSCH_Config__uci_OnPUSCH__cond := SetupRelease__Format _ _ UCI_OnPUSCH__Format.
Opaque PUSCH_Config__uci_OnPUSCH__cond PUSCH_Config__uci_OnPUSCH__Format.

Inductive PUSCH_Config__tp_pi2BPSK__Type : Set :=
 | PUSCH_Config__tp_pi2BPSK__enabled
.
Definition PUSCH_Config__tp_pi2BPSK__cond := (fun (_ : PUSCH_Config__tp_pi2BPSK__Type) => True).
Lemma PUSCH_Config__tp_pi2BPSK__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__tp_pi2BPSK__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__tp_pi2BPSK__nat__helper.

Definition PUSCH_Config__tp_pi2BPSK__F1 t :=
  match t with
  | PUSCH_Config__tp_pi2BPSK__enabled => 0
  end.
Definition PUSCH_Config__tp_pi2BPSK__F2 n :=
  match n with
  | 0 => PUSCH_Config__tp_pi2BPSK__enabled
  | _ => PUSCH_Config__tp_pi2BPSK__enabled
  end.
Lemma PUSCH_Config__tp_pi2BPSK__F1F2 : forall x : PUSCH_Config__tp_pi2BPSK__Type, (PUSCH_Config__tp_pi2BPSK__F1 x <= 0) /\ PUSCH_Config__tp_pi2BPSK__F2 (PUSCH_Config__tp_pi2BPSK__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__tp_pi2BPSK__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__tp_pi2BPSK__F1 (PUSCH_Config__tp_pi2BPSK__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.MinSchedulingOffsetK2_Values_r16.
Definition PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__Type := SetupRelease__Type MinSchedulingOffsetK2_Values_r16__Type.
Definition PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__cond := SetupRelease__cond _ MinSchedulingOffsetK2_Values_r16__cond.
Definition PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__Format : T_Format PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__Type PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__cond := SetupRelease__Format _ _ MinSchedulingOffsetK2_Values_r16__Format.
Opaque PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__cond PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.UL_AccessConfigListDCI_0_1_r16.
Definition PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__Type := SetupRelease__Type UL_AccessConfigListDCI_0_1_r16__Type.
Definition PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__cond := SetupRelease__cond _ UL_AccessConfigListDCI_0_1_r16__cond.
Definition PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__Format : T_Format PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__Type PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__cond := SetupRelease__Format _ _ UL_AccessConfigListDCI_0_1_r16__Format.
Opaque PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__cond PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__Format.

Lemma PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__Type := Z.
Definition PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__cond := (fun z => (0 <= z <= 4)%Z).
Inductive PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__enabled
.
Definition PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__enabled => 0
  end.
Definition PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__enabled
  | _ => PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__enabled
  end.
Lemma PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Type, (PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F1 x <= 0) /\ PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F2 (PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F1 (PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__helper1 : (0 <= 2)%Z.  lia. Qed.
Lemma PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (2 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__Type := Z.
Definition PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__cond := (fun z => (0 <= z <= 2)%Z).
Inductive PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__enabled
.
Definition PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__enabled => 0
  end.
Definition PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__enabled
  | _ => PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__enabled
  end.
Lemma PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Type, (PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F1 x <= 0) /\ PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F2 (PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F1 (PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.DMRS_UplinkConfig.
Definition PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__Type := SetupRelease__Type DMRS_UplinkConfig__Type.
Definition PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__cond := SetupRelease__cond _ DMRS_UplinkConfig__cond.
Definition PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__Type PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__cond := SetupRelease__Format _ _ DMRS_UplinkConfig__Format.
Opaque PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__cond PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.DMRS_UplinkConfig.
Definition PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__Type := SetupRelease__Type DMRS_UplinkConfig__Type.
Definition PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__cond := SetupRelease__cond _ DMRS_UplinkConfig__cond.
Definition PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__Type PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__cond := SetupRelease__Format _ _ DMRS_UplinkConfig__Format.
Opaque PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__cond PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__Format.

Inductive PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Type : Set :=
 | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__intraSlot
 | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__interSlot
.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__cond := (fun (_ : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Type) => True).
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__nat__helper.

Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F1 t :=
  match t with
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__intraSlot => 0
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__interSlot => 1
  end.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__intraSlot
  | 1 => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__interSlot
  | _ => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__intraSlot
  end.
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F1F2 : forall x : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Type, (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F1 x <= 1) /\ PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F2 (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F1 (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Type : Set :=
 | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__interRepetition
 | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__interSlot
.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__cond := (fun (_ : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Type) => True).
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__nat__helper.

Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F1 t :=
  match t with
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__interRepetition => 0
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__interSlot => 1
  end.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__interRepetition
  | 1 => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__interSlot
  | _ => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__interRepetition
  end.
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F1F2 : forall x : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Type, (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F1 x <= 1) /\ PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F2 (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F1 (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F2 y) = y. enum_solve H y. Qed.


Inductive PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type : Set :=
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Type -> PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Type -> PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type
.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list : list typ := (
typ_cons PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Type PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__cond ::
typ_cons PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Type PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__cond ::
 nil).
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__cond (c : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type) := 
  match c with
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA t => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__cond t 
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB t => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__cond t 
  end.

Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__len_helper1 : to_bit_sz (length PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__len_helper2 : 2 <= length2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list.
 simpl. lia. Qed.
Require Import NR.SetupRelease.
Require Import NR.FrequencyHoppingOffsetListsDCI_0_2_r16.
Definition PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__Type := SetupRelease__Type FrequencyHoppingOffsetListsDCI_0_2_r16__Type.
Definition PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__cond := SetupRelease__cond _ FrequencyHoppingOffsetListsDCI_0_2_r16__cond.
Definition PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__Type PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__cond := SetupRelease__Format _ _ FrequencyHoppingOffsetListsDCI_0_2_r16__Format.
Opaque PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__cond PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__Format.

Inductive PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__fullyAndPartialAndNonCoherent
 | PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__partialAndNonCoherent
 | PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__nonCoherent
.
Definition PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__fullyAndPartialAndNonCoherent => 0
  | PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__partialAndNonCoherent => 1
  | PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__nonCoherent => 2
  end.
Definition PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__fullyAndPartialAndNonCoherent
  | 1 => PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__partialAndNonCoherent
  | 2 => PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__nonCoherent
  | _ => PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__fullyAndPartialAndNonCoherent
  end.
Lemma PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Type, (PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F1 x <= 2) /\ PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F2 (PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 2), PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F1 (PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__enabled
.
Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__enabled => 0
  end.
Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__enabled
  | _ => PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__enabled
  end.
Lemma PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Type, (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F1 x <= 0) /\ PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F2 (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F1 (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_Config__ext0O__maxRankDCI_0_2_r16__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma PUSCH_Config__ext0O__maxRankDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__ext0O__maxRankDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__ext0O__maxRankDCI_0_2_r16__Type := Z.
Definition PUSCH_Config__ext0O__maxRankDCI_0_2_r16__cond := (fun z => (1 <= z <= 4)%Z).
Inductive PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__qam256
 | PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__qam64LowSE
.
Definition PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__qam256 => 0
  | PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__qam64LowSE => 1
  end.
Definition PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__qam256
  | 1 => PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__qam64LowSE
  | _ => PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__qam256
  end.
Lemma PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Type, (PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F1 x <= 1) /\ PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F2 (PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F1 (PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__qam256
 | PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__qam64LowSE
.
Definition PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__qam256 => 0
  | PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__qam64LowSE => 1
  end.
Definition PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__qam256
  | 1 => PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__qam64LowSE
  | _ => PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__qam256
  end.
Lemma PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Type, (PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F1 x <= 1) /\ PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F2 (PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F1 (PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__enabled
.
Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__enabled => 0
  end.
Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__enabled
  | _ => PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__enabled
  end.
Lemma PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Type, (PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F1 x <= 0) /\ PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F2 (PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F1 (PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__pusch_RepTypeA
 | PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__pusch_RepTypeB
.
Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__pusch_RepTypeA => 0
  | PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__pusch_RepTypeB => 1
  end.
Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__pusch_RepTypeA
  | 1 => PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__pusch_RepTypeB
  | _ => PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__pusch_RepTypeA
  end.
Lemma PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Type, (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F1 x <= 1) /\ PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F2 (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F1 (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__resourceAllocationType0
 | PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__resourceAllocationType1
 | PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__dynamicSwitch
.
Definition PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__resourceAllocationType0 => 0
  | PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__resourceAllocationType1 => 1
  | PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__dynamicSwitch => 2
  end.
Definition PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__resourceAllocationType0
  | 1 => PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__resourceAllocationType1
  | 2 => PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__dynamicSwitch
  | _ => PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__resourceAllocationType0
  end.
Lemma PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Type, (PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F1 x <= 2) /\ PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F2 (PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 2), PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F1 (PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Type : Set :=
 | PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n2
 | PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n4
 | PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n8
 | PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n16
.
Definition PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__cond := (fun (_ : PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Type) => True).
Lemma PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__nat__helper.

Definition PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n2 => 0
  | PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n4 => 1
  | PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n8 => 2
  | PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n16 => 3
  end.
Definition PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n2
  | 1 => PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n4
  | 2 => PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n8
  | 3 => PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n16
  | _ => PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__n2
  end.
Lemma PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F1F2 : forall x : PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Type, (PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F1 x <= 3) /\ PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F2 (PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 3), PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F1 (PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.UCI_OnPUSCH_ListDCI_0_2_r16.
Definition PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__Type := SetupRelease__Type UCI_OnPUSCH_ListDCI_0_2_r16__Type.
Definition PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__cond := SetupRelease__cond _ UCI_OnPUSCH_ListDCI_0_2_r16__cond.
Definition PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__Type PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__cond := SetupRelease__Format _ _ UCI_OnPUSCH_ListDCI_0_2_r16__Format.
Opaque PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__cond PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_TimeDomainResourceAllocationList_r16.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__Type := SetupRelease__Type PUSCH_TimeDomainResourceAllocationList_r16__Type.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__cond := SetupRelease__cond _ PUSCH_TimeDomainResourceAllocationList_r16__cond.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__Type PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__cond := SetupRelease__Format _ _ PUSCH_TimeDomainResourceAllocationList_r16__Format.
Opaque PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_TimeDomainResourceAllocationList_r16.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__Type := SetupRelease__Type PUSCH_TimeDomainResourceAllocationList_r16__Type.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__cond := SetupRelease__cond _ PUSCH_TimeDomainResourceAllocationList_r16__cond.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__Format : T_Format PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__Type PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__cond := SetupRelease__Format _ _ PUSCH_TimeDomainResourceAllocationList_r16__Format.
Opaque PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__Format.

Inductive PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Type : Set :=
 | PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__enabled
.
Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__cond := (fun (_ : PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Type) => True).
Lemma PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__nat__helper.

Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__enabled => 0
  end.
Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__enabled
  | _ => PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__enabled
  end.
Lemma PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F1F2 : forall x : PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Type, (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F1 x <= 0) /\ PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F2 (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F1 (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Type : Set :=
 | PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__enabled
.
Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__cond := (fun (_ : PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Type) => True).
Lemma PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__nat__helper.

Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__enabled => 0
  end.
Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__enabled
  | _ => PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__enabled
  end.
Lemma PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F1F2 : forall x : PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Type, (PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F1 x <= 0) /\ PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F2 (PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F1 (PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Type : Set :=
 | PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__pusch_RepTypeA
 | PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__pusch_RepTypeB
.
Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__cond := (fun (_ : PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Type) => True).
Lemma PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__nat__helper.

Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__pusch_RepTypeA => 0
  | PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__pusch_RepTypeB => 1
  end.
Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__pusch_RepTypeA
  | 1 => PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__pusch_RepTypeB
  | _ => PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__pusch_RepTypeA
  end.
Lemma PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F1F2 : forall x : PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Type, (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F1 x <= 1) /\ PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F2 (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F1 (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Type : Set :=
 | PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__interRepetition
 | PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__interSlot
.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__cond := (fun (_ : PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Type) => True).
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__nat__helper.

Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__interRepetition => 0
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__interSlot => 1
  end.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__interRepetition
  | 1 => PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__interSlot
  | _ => PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__interRepetition
  end.
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F1F2 : forall x : PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Type, (PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F1 x <= 1) /\ PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F2 (PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F1 (PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.UCI_OnPUSCH_ListDCI_0_1_r16.
Definition PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__Type := SetupRelease__Type UCI_OnPUSCH_ListDCI_0_1_r16__Type.
Definition PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__cond := SetupRelease__cond _ UCI_OnPUSCH_ListDCI_0_1_r16__cond.
Definition PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__Format : T_Format PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__Type PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__cond := SetupRelease__Format _ _ UCI_OnPUSCH_ListDCI_0_1_r16__Format.
Opaque PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__cond PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__Format.

Require Import NR.InvalidSymbolPattern_r16.

Opaque InvalidSymbolPattern_r16__cond InvalidSymbolPattern_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_PowerControl_v1610.
Definition PUSCH_Config__ext0O__pusch_PowerControl_v1610__Type := SetupRelease__Type PUSCH_PowerControl_v1610__Type.
Definition PUSCH_Config__ext0O__pusch_PowerControl_v1610__cond := SetupRelease__cond _ PUSCH_PowerControl_v1610__cond.
Definition PUSCH_Config__ext0O__pusch_PowerControl_v1610__Format : T_Format PUSCH_Config__ext0O__pusch_PowerControl_v1610__Type PUSCH_Config__ext0O__pusch_PowerControl_v1610__cond := SetupRelease__Format _ _ PUSCH_PowerControl_v1610__Format.
Opaque PUSCH_Config__ext0O__pusch_PowerControl_v1610__cond PUSCH_Config__ext0O__pusch_PowerControl_v1610__Format.

Inductive PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Type : Set :=
 | PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpower
 | PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpowerMode1
 | PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpowerMode2
.
Definition PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__cond := (fun (_ : PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Type) => True).
Lemma PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__nat__helper.

Definition PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F1 t :=
  match t with
  | PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpower => 0
  | PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpowerMode1 => 1
  | PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpowerMode2 => 2
  end.
Definition PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpower
  | 1 => PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpowerMode1
  | 2 => PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpowerMode2
  | _ => PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__fullpower
  end.
Lemma PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F1F2 : forall x : PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Type, (PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F1 x <= 2) /\ PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F2 (PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F2F1 : forall (y : nat) (H : y <= 2), PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F1 (PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_TimeDomainResourceAllocationList_r16.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__Type := SetupRelease__Type PUSCH_TimeDomainResourceAllocationList_r16__Type.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__cond := SetupRelease__cond _ PUSCH_TimeDomainResourceAllocationList_r16__cond.
Definition PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__Format : T_Format PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__Type PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__cond := SetupRelease__Format _ _ PUSCH_TimeDomainResourceAllocationList_r16__Format.
Opaque PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__Format.

Lemma PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__Type := Z.
Definition PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__cond := (fun z => (1 <= z <= 4)%Z).
Record PUSCH_Config__ext0O__Type : Set :=
  make__PUSCH_Config__ext0O__Type {
    PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16 : option PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__Type ;
    PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16 : option PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__Type ;
    PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16 : option Z ;
    PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16 : option PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16 : option Z ;
    PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16 : option PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16 : option PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16 : option PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16 : option PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16 : option PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16 : option PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16 : option PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__maxRankDCI_0_2_r16 : option Z ;
    PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16 : option PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16 : option PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16 : option PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16 : option PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16 : option PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16 : option PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16 : option PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16 : option PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__Type ;
    PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16 : option PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__Type ;
    PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16 : option PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Type ;
    PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16 : option PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Type ;
    PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16 : option PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Type ;
    PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16 : option PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Type ;
    PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16 : option PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__Type ;
    PUSCH_Config__ext0O__invalidSymbolPattern_r16 : option InvalidSymbolPattern_r16__Type ;
    PUSCH_Config__ext0O__pusch_PowerControl_v1610 : option PUSCH_Config__ext0O__pusch_PowerControl_v1610__Type ;
    PUSCH_Config__ext0O__ul_FullPowerTransmission_r16 : option PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Type ;
    PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16 : option PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__Type ;
    PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16 : option Z ;
}.
Definition PUSCH_Config__ext0O__list := (
 Opt PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__Type PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__cond ::
 Opt PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__Type PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__cond ::
 Opt Z PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Type PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__cond ::
 Opt Z PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Type PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__Type PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__Type PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__Type PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Type PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Type PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__cond ::
 Opt Z PUSCH_Config__ext0O__maxRankDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Type PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Type PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Type PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Type PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Type PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Type PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__Type PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__Type PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__cond ::
 Opt PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__Type PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__cond ::
 Opt PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Type PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__cond ::
 Opt PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Type PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__cond ::
 Opt PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Type PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__cond ::
 Opt PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Type PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__cond ::
 Opt PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__Type PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__cond ::
 Opt InvalidSymbolPattern_r16__Type InvalidSymbolPattern_r16__cond ::
 Opt PUSCH_Config__ext0O__pusch_PowerControl_v1610__Type PUSCH_Config__ext0O__pusch_PowerControl_v1610__cond ::
 Opt PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Type PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__cond ::
 Opt PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__Type PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__cond ::
 Opt Z PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__cond ::
 nil).
Definition PUSCH_Config__ext0O__cond z := 
  opt_cond PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__cond (PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__cond (PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16 z) /\
  opt_cond PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__cond (PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__cond (PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__cond (PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__cond (PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__cond (PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__cond (PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__cond (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__cond (PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__cond (PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__cond (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__maxRankDCI_0_2_r16__cond (PUSCH_Config__ext0O__maxRankDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__cond (PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__cond (PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__cond (PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__cond (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__cond (PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__cond (PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__cond (PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__cond (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16 z) /\
  opt_cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__cond (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16 z) /\
  opt_cond PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__cond (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16 z) /\
  opt_cond PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__cond (PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16 z) /\
  opt_cond PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__cond (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16 z) /\
  opt_cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__cond (PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16 z) /\
  opt_cond PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__cond (PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16 z) /\
  opt_cond InvalidSymbolPattern_r16__cond (PUSCH_Config__ext0O__invalidSymbolPattern_r16 z) /\
  opt_cond PUSCH_Config__ext0O__pusch_PowerControl_v1610__cond (PUSCH_Config__ext0O__pusch_PowerControl_v1610 z) /\
  opt_cond PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__cond (PUSCH_Config__ext0O__ul_FullPowerTransmission_r16 z) /\
  opt_cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__cond (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16 z) /\
  opt_cond PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__cond (PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16 z) /\
  True.

Definition PUSCH_Config__ext0__Type := PUSCH_Config__ext0O__Type.
Definition PUSCH_Config__ext0__cond := PUSCH_Config__ext0O__cond.

Require Import NR.SetupRelease.
Require Import NR.UL_AccessConfigListDCI_0_2_r17.
Definition PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__Type := SetupRelease__Type UL_AccessConfigListDCI_0_2_r17__Type.
Definition PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__cond := SetupRelease__cond _ UL_AccessConfigListDCI_0_2_r17__cond.
Definition PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__Format : T_Format PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__Type PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__cond := SetupRelease__Format _ _ UL_AccessConfigListDCI_0_2_r17__Format.
Opaque PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__cond PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.BetaOffsetsCrossPriSel_r17.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__Type := SetupRelease__Type BetaOffsetsCrossPriSel_r17__Type.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__cond := SetupRelease__cond _ BetaOffsetsCrossPriSel_r17__cond.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__Format : T_Format PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__Type PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__cond := SetupRelease__Format _ _ BetaOffsetsCrossPriSel_r17__Format.
Opaque PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__cond PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.BetaOffsetsCrossPriSel_r17.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__Type := SetupRelease__Type BetaOffsetsCrossPriSel_r17__Type.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__cond := SetupRelease__cond _ BetaOffsetsCrossPriSel_r17__cond.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__Format : T_Format PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__Type PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__cond := SetupRelease__Format _ _ BetaOffsetsCrossPriSel_r17__Format.
Opaque PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__cond PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.BetaOffsetsCrossPriSelDCI_0_2_r17.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__Type := SetupRelease__Type BetaOffsetsCrossPriSelDCI_0_2_r17__Type.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__cond := SetupRelease__cond _ BetaOffsetsCrossPriSelDCI_0_2_r17__cond.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__Format : T_Format PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__Type PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__cond := SetupRelease__Format _ _ BetaOffsetsCrossPriSelDCI_0_2_r17__Format.
Opaque PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__cond PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.BetaOffsetsCrossPriSelDCI_0_2_r17.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__Type := SetupRelease__Type BetaOffsetsCrossPriSelDCI_0_2_r17__Type.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__cond := SetupRelease__cond _ BetaOffsetsCrossPriSelDCI_0_2_r17__cond.
Definition PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__Format : T_Format PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__Type PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__cond := SetupRelease__Format _ _ BetaOffsetsCrossPriSelDCI_0_2_r17__Format.
Opaque PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__cond PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__Format.

Inductive PUSCH_Config__ext1O__mappingPattern_r17__Type : Set :=
 | PUSCH_Config__ext1O__mappingPattern_r17__cyclicMapping
 | PUSCH_Config__ext1O__mappingPattern_r17__sequentialMapping
.
Definition PUSCH_Config__ext1O__mappingPattern_r17__cond := (fun (_ : PUSCH_Config__ext1O__mappingPattern_r17__Type) => True).
Lemma PUSCH_Config__ext1O__mappingPattern_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext1O__mappingPattern_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PUSCH_Config__ext1O__mappingPattern_r17__nat__helper.

Definition PUSCH_Config__ext1O__mappingPattern_r17__F1 t :=
  match t with
  | PUSCH_Config__ext1O__mappingPattern_r17__cyclicMapping => 0
  | PUSCH_Config__ext1O__mappingPattern_r17__sequentialMapping => 1
  end.
Definition PUSCH_Config__ext1O__mappingPattern_r17__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext1O__mappingPattern_r17__cyclicMapping
  | 1 => PUSCH_Config__ext1O__mappingPattern_r17__sequentialMapping
  | _ => PUSCH_Config__ext1O__mappingPattern_r17__cyclicMapping
  end.
Lemma PUSCH_Config__ext1O__mappingPattern_r17__F1F2 : forall x : PUSCH_Config__ext1O__mappingPattern_r17__Type, (PUSCH_Config__ext1O__mappingPattern_r17__F1 x <= 1) /\ PUSCH_Config__ext1O__mappingPattern_r17__F2 (PUSCH_Config__ext1O__mappingPattern_r17__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext1O__mappingPattern_r17__F2F1 : forall (y : nat) (H : y <= 1), PUSCH_Config__ext1O__mappingPattern_r17__F1 (PUSCH_Config__ext1O__mappingPattern_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Type : Set :=
 | PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__enabled
.
Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__cond := (fun (_ : PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Type) => True).
Lemma PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__nat__helper.

Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F1 t :=
  match t with
  | PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__enabled => 0
  end.
Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__enabled
  | _ => PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__enabled
  end.
Lemma PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F1F2 : forall x : PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Type, (PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F1 x <= 0) /\ PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F2 (PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F1 (PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Type : Set :=
 | PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__enabled
.
Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__cond := (fun (_ : PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Type) => True).
Lemma PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__nat__helper.

Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F1 t :=
  match t with
  | PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__enabled => 0
  end.
Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__enabled
  | _ => PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__enabled
  end.
Lemma PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F1F2 : forall x : PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Type, (PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F1 x <= 0) /\ PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F2 (PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F1 (PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F2 y) = y. enum_solve H y. Qed.

Lemma PUSCH_Config__ext1O__sequenceOffsetForRV_r17__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma PUSCH_Config__ext1O__sequenceOffsetForRV_r17__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__ext1O__sequenceOffsetForRV_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__ext1O__sequenceOffsetForRV_r17__Type := Z.
Definition PUSCH_Config__ext1O__sequenceOffsetForRV_r17__cond := (fun z => (0 <= z <= 3)%Z).
Require Import NR.SetupRelease.
Require Import NR.UL_AccessConfigListDCI_0_1_r17.
Definition PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__Type := SetupRelease__Type UL_AccessConfigListDCI_0_1_r17__Type.
Definition PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__cond := SetupRelease__cond _ UL_AccessConfigListDCI_0_1_r17__cond.
Definition PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__Format : T_Format PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__Type PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__cond := SetupRelease__Format _ _ UL_AccessConfigListDCI_0_1_r17__Format.
Opaque PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__cond PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.MinSchedulingOffsetK2_Values_r17.
Definition PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__Type := SetupRelease__Type MinSchedulingOffsetK2_Values_r17__Type.
Definition PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__cond := SetupRelease__cond _ MinSchedulingOffsetK2_Values_r17__cond.
Definition PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__Format : T_Format PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__Type PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__cond := SetupRelease__Format _ _ MinSchedulingOffsetK2_Values_r17__Format.
Opaque PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__cond PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__Format.

Inductive PUSCH_Config__ext1O__availableSlotCounting_r17__Type : Set :=
 | PUSCH_Config__ext1O__availableSlotCounting_r17__enabled
.
Definition PUSCH_Config__ext1O__availableSlotCounting_r17__cond := (fun (_ : PUSCH_Config__ext1O__availableSlotCounting_r17__Type) => True).
Lemma PUSCH_Config__ext1O__availableSlotCounting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUSCH_Config__ext1O__availableSlotCounting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUSCH_Config__ext1O__availableSlotCounting_r17__nat__helper.

Definition PUSCH_Config__ext1O__availableSlotCounting_r17__F1 t :=
  match t with
  | PUSCH_Config__ext1O__availableSlotCounting_r17__enabled => 0
  end.
Definition PUSCH_Config__ext1O__availableSlotCounting_r17__F2 n :=
  match n with
  | 0 => PUSCH_Config__ext1O__availableSlotCounting_r17__enabled
  | _ => PUSCH_Config__ext1O__availableSlotCounting_r17__enabled
  end.
Lemma PUSCH_Config__ext1O__availableSlotCounting_r17__F1F2 : forall x : PUSCH_Config__ext1O__availableSlotCounting_r17__Type, (PUSCH_Config__ext1O__availableSlotCounting_r17__F1 x <= 0) /\ PUSCH_Config__ext1O__availableSlotCounting_r17__F2 (PUSCH_Config__ext1O__availableSlotCounting_r17__F1 x) = x. imp_solve. Qed.
Lemma PUSCH_Config__ext1O__availableSlotCounting_r17__F2F1 : forall (y : nat) (H : y <= 0), PUSCH_Config__ext1O__availableSlotCounting_r17__F1 (PUSCH_Config__ext1O__availableSlotCounting_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.DMRS_BundlingPUSCH_Config_r17.
Definition PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__Type := SetupRelease__Type DMRS_BundlingPUSCH_Config_r17__Type.
Definition PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__cond := SetupRelease__cond _ DMRS_BundlingPUSCH_Config_r17__cond.
Definition PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__Format : T_Format PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__Type PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__cond := SetupRelease__Format _ _ DMRS_BundlingPUSCH_Config_r17__Format.
Opaque PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__cond PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__Format.

Definition PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__Type := Z.
Definition PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__cond := (fun z : Z => z = 5)%Z.
Definition PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__Type := Z.
Definition PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__cond := (fun z : Z => z = 5)%Z.
Require Import NR.MPE_Resource_r17.

Opaque MPE_Resource_r17__cond MPE_Resource_r17__Format.

Definition PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__Type := list MPE_Resource_r17__Type.

Lemma PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__helper1 : (0 <= 1 <= maxMPE_Resources_r17)%Z. unfold maxMPE_Resources_r17.
 lia. Qed.
Lemma PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxMPE_Resources_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMPE_Resources_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__cond (z : PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxMPE_Resources_r17)%Z /\ (list_and MPE_Resource_r17__cond z) .

Require Import NR.MPE_ResourceId_r17.

Opaque MPE_ResourceId_r17__cond MPE_ResourceId_r17__Format.

Definition PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__Type := list MPE_ResourceId_r17__Type.

Lemma PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__helper1 : (0 <= 1 <= maxMPE_Resources_r17)%Z. unfold maxMPE_Resources_r17.
 lia. Qed.
Lemma PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxMPE_Resources_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMPE_Resources_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__cond (z : PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxMPE_Resources_r17)%Z /\ (list_and MPE_ResourceId_r17__cond z) .

Record PUSCH_Config__ext1O__Type : Set :=
  make__PUSCH_Config__ext1O__Type {
    PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17 : option PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__Type ;
    PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17 : option PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__Type ;
    PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17 : option PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__Type ;
    PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17 : option PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__Type ;
    PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17 : option PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__Type ;
    PUSCH_Config__ext1O__mappingPattern_r17 : option PUSCH_Config__ext1O__mappingPattern_r17__Type ;
    PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17 : option PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Type ;
    PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17 : option PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Type ;
    PUSCH_Config__ext1O__sequenceOffsetForRV_r17 : option Z ;
    PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17 : option PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__Type ;
    PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17 : option PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__Type ;
    PUSCH_Config__ext1O__availableSlotCounting_r17 : option PUSCH_Config__ext1O__availableSlotCounting_r17__Type ;
    PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17 : option PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__Type ;
    PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700 : option Z ;
    PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17 : option Z ;
    PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17 : option PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__Type ;
    PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17 : option PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__Type ;
}.
Definition PUSCH_Config__ext1O__list := (
 Opt PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__Type PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__cond ::
 Opt PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__Type PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__cond ::
 Opt PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__Type PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__cond ::
 Opt PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__Type PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__cond ::
 Opt PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__Type PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__cond ::
 Opt PUSCH_Config__ext1O__mappingPattern_r17__Type PUSCH_Config__ext1O__mappingPattern_r17__cond ::
 Opt PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Type PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__cond ::
 Opt PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Type PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__cond ::
 Opt Z PUSCH_Config__ext1O__sequenceOffsetForRV_r17__cond ::
 Opt PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__Type PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__cond ::
 Opt PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__Type PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__cond ::
 Opt PUSCH_Config__ext1O__availableSlotCounting_r17__Type PUSCH_Config__ext1O__availableSlotCounting_r17__cond ::
 Opt PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__Type PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__cond ::
 Opt Z PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__cond ::
 Opt Z PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__cond ::
 Opt PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__Type PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__cond ::
 Opt PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__Type PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__cond ::
 nil).
Definition PUSCH_Config__ext1O__cond z := 
  opt_cond PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__cond (PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17 z) /\
  opt_cond PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__cond (PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17 z) /\
  opt_cond PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__cond (PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17 z) /\
  opt_cond PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__cond (PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17 z) /\
  opt_cond PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__cond (PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17 z) /\
  opt_cond PUSCH_Config__ext1O__mappingPattern_r17__cond (PUSCH_Config__ext1O__mappingPattern_r17 z) /\
  opt_cond PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__cond (PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17 z) /\
  opt_cond PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__cond (PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17 z) /\
  opt_cond PUSCH_Config__ext1O__sequenceOffsetForRV_r17__cond (PUSCH_Config__ext1O__sequenceOffsetForRV_r17 z) /\
  opt_cond PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__cond (PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17 z) /\
  opt_cond PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__cond (PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17 z) /\
  opt_cond PUSCH_Config__ext1O__availableSlotCounting_r17__cond (PUSCH_Config__ext1O__availableSlotCounting_r17 z) /\
  opt_cond PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__cond (PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17 z) /\
  opt_cond PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__cond (PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700 z) /\
  opt_cond PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__cond (PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17 z) /\
  opt_cond PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__cond (PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17 z) /\
  opt_cond PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__cond (PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17 z) /\
  True.

Definition PUSCH_Config__ext1__Type := PUSCH_Config__ext1O__Type.
Definition PUSCH_Config__ext1__cond := PUSCH_Config__ext1O__cond.

Record PUSCH_Config__Type : Set :=
  make__PUSCH_Config__Type {
    PUSCH_Config__dataScramblingIdentityPUSCH : option Z ;
    PUSCH_Config__txConfig : option PUSCH_Config__txConfig__Type ;
    PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA : option PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__Type ;
    PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB : option PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__Type ;
    PUSCH_Config__pusch_PowerControl : option PUSCH_PowerControl__Type ;
    PUSCH_Config__frequencyHopping : option PUSCH_Config__frequencyHopping__Type ;
    PUSCH_Config__frequencyHoppingOffsetLists : option PUSCH_Config__frequencyHoppingOffsetLists__Type ;
    PUSCH_Config__resourceAllocation : PUSCH_Config__resourceAllocation__Type ;
    PUSCH_Config__pusch_TimeDomainAllocationList : option PUSCH_Config__pusch_TimeDomainAllocationList__Type ;
    PUSCH_Config__pusch_AggregationFactor : option PUSCH_Config__pusch_AggregationFactor__Type ;
    PUSCH_Config__mcs_Table : option PUSCH_Config__mcs_Table__Type ;
    PUSCH_Config__mcs_TableTransformPrecoder : option PUSCH_Config__mcs_TableTransformPrecoder__Type ;
    PUSCH_Config__transformPrecoder : option PUSCH_Config__transformPrecoder__Type ;
    PUSCH_Config__codebookSubset : option PUSCH_Config__codebookSubset__Type ;
    PUSCH_Config__maxRank : option Z ;
    PUSCH_Config__rbg_Size : option PUSCH_Config__rbg_Size__Type ;
    PUSCH_Config__uci_OnPUSCH : option PUSCH_Config__uci_OnPUSCH__Type ;
    PUSCH_Config__tp_pi2BPSK : option PUSCH_Config__tp_pi2BPSK__Type ;
    PUSCH_Config__ext0 : option PUSCH_Config__ext0__Type ;
    PUSCH_Config__ext1 : option PUSCH_Config__ext1__Type ;
}.
Definition PUSCH_Config__root_list : list seq_elem := (
 Opt Z PUSCH_Config__dataScramblingIdentityPUSCH__cond ::
 Opt PUSCH_Config__txConfig__Type PUSCH_Config__txConfig__cond ::
 Opt PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__Type PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__cond ::
 Opt PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__Type PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__cond ::
 Opt PUSCH_PowerControl__Type PUSCH_PowerControl__cond ::
 Opt PUSCH_Config__frequencyHopping__Type PUSCH_Config__frequencyHopping__cond ::
 Opt PUSCH_Config__frequencyHoppingOffsetLists__Type PUSCH_Config__frequencyHoppingOffsetLists__cond ::
 Nor PUSCH_Config__resourceAllocation__Type PUSCH_Config__resourceAllocation__cond ::
 Opt PUSCH_Config__pusch_TimeDomainAllocationList__Type PUSCH_Config__pusch_TimeDomainAllocationList__cond ::
 Opt PUSCH_Config__pusch_AggregationFactor__Type PUSCH_Config__pusch_AggregationFactor__cond ::
 Opt PUSCH_Config__mcs_Table__Type PUSCH_Config__mcs_Table__cond ::
 Opt PUSCH_Config__mcs_TableTransformPrecoder__Type PUSCH_Config__mcs_TableTransformPrecoder__cond ::
 Opt PUSCH_Config__transformPrecoder__Type PUSCH_Config__transformPrecoder__cond ::
 Opt PUSCH_Config__codebookSubset__Type PUSCH_Config__codebookSubset__cond ::
 Opt Z PUSCH_Config__maxRank__cond ::
 Opt PUSCH_Config__rbg_Size__Type PUSCH_Config__rbg_Size__cond ::
 Opt PUSCH_Config__uci_OnPUSCH__Type PUSCH_Config__uci_OnPUSCH__cond ::
 Opt PUSCH_Config__tp_pi2BPSK__Type PUSCH_Config__tp_pi2BPSK__cond ::
 nil).
Definition PUSCH_Config__ext_list : list typ := (
  typ_cons PUSCH_Config__ext0__Type PUSCH_Config__ext0__cond ::
  typ_cons PUSCH_Config__ext1__Type PUSCH_Config__ext1__cond ::
  nil).
Definition PUSCH_Config__cond (z : PUSCH_Config__Type) := 
(  opt_cond PUSCH_Config__dataScramblingIdentityPUSCH__cond (PUSCH_Config__dataScramblingIdentityPUSCH z) /\
  opt_cond PUSCH_Config__txConfig__cond (PUSCH_Config__txConfig z) /\
  opt_cond PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__cond (PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA z) /\
  opt_cond PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__cond (PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB z) /\
  opt_cond PUSCH_PowerControl__cond (PUSCH_Config__pusch_PowerControl z) /\
  opt_cond PUSCH_Config__frequencyHopping__cond (PUSCH_Config__frequencyHopping z) /\
  opt_cond PUSCH_Config__frequencyHoppingOffsetLists__cond (PUSCH_Config__frequencyHoppingOffsetLists z) /\
  PUSCH_Config__resourceAllocation__cond (PUSCH_Config__resourceAllocation z) /\
  opt_cond PUSCH_Config__pusch_TimeDomainAllocationList__cond (PUSCH_Config__pusch_TimeDomainAllocationList z) /\
  opt_cond PUSCH_Config__pusch_AggregationFactor__cond (PUSCH_Config__pusch_AggregationFactor z) /\
  opt_cond PUSCH_Config__mcs_Table__cond (PUSCH_Config__mcs_Table z) /\
  opt_cond PUSCH_Config__mcs_TableTransformPrecoder__cond (PUSCH_Config__mcs_TableTransformPrecoder z) /\
  opt_cond PUSCH_Config__transformPrecoder__cond (PUSCH_Config__transformPrecoder z) /\
  opt_cond PUSCH_Config__codebookSubset__cond (PUSCH_Config__codebookSubset z) /\
  opt_cond PUSCH_Config__maxRank__cond (PUSCH_Config__maxRank z) /\
  opt_cond PUSCH_Config__rbg_Size__cond (PUSCH_Config__rbg_Size z) /\
  opt_cond PUSCH_Config__uci_OnPUSCH__cond (PUSCH_Config__uci_OnPUSCH z) /\
  opt_cond PUSCH_Config__tp_pi2BPSK__cond (PUSCH_Config__tp_pi2BPSK z) /\
  True) /\ 
(  opt_cond PUSCH_Config__ext0__cond (PUSCH_Config__ext0 z) /\
  opt_cond PUSCH_Config__ext1__cond (PUSCH_Config__ext1 z) /\
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
Definition PUSCH_Config__dataScramblingIdentityPUSCH__Format : T_Format Z PUSCH_Config__dataScramblingIdentityPUSCH__cond :=
 ranged_int_format (0) (1023) PUSCH_Config__dataScramblingIdentityPUSCH__helper1 PUSCH_Config__dataScramblingIdentityPUSCH__helper2.

Opaque PUSCH_Config__dataScramblingIdentityPUSCH__cond PUSCH_Config__dataScramblingIdentityPUSCH__Format.

Definition PUSCH_Config__txConfig__Format : T_Format PUSCH_Config__txConfig__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__txConfig__nat__Format PUSCH_Config__txConfig__F1 PUSCH_Config__txConfig__F2 PUSCH_Config__txConfig__F1F2 PUSCH_Config__txConfig__F2F1.

Opaque PUSCH_Config__txConfig__cond PUSCH_Config__txConfig__Format.

Opaque PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__cond PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__Format.

Opaque PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__cond PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__Format.

Definition PUSCH_Config__frequencyHopping__Format : T_Format PUSCH_Config__frequencyHopping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__frequencyHopping__nat__Format PUSCH_Config__frequencyHopping__F1 PUSCH_Config__frequencyHopping__F2 PUSCH_Config__frequencyHopping__F1F2 PUSCH_Config__frequencyHopping__F2F1.

Opaque PUSCH_Config__frequencyHopping__cond PUSCH_Config__frequencyHopping__Format.

Definition PUSCH_Config__frequencyHoppingOffsetLists__seq_of__Format : T_Format Z PUSCH_Config__frequencyHoppingOffsetLists__seq_of__cond :=
 ranged_int_format (1) (maxNrofPhysicalResourceBlocks_1) PUSCH_Config__frequencyHoppingOffsetLists__seq_of__helper1 PUSCH_Config__frequencyHoppingOffsetLists__seq_of__helper2.

Opaque PUSCH_Config__frequencyHoppingOffsetLists__seq_of__cond PUSCH_Config__frequencyHoppingOffsetLists__seq_of__Format.

Definition PUSCH_Config__frequencyHoppingOffsetLists__Format : T_Format PUSCH_Config__frequencyHoppingOffsetLists__Type PUSCH_Config__frequencyHoppingOffsetLists__cond := seq_of_format PUSCH_Config__frequencyHoppingOffsetLists__seq_of__Format 1 4 PUSCH_Config__frequencyHoppingOffsetLists__helper1 PUSCH_Config__frequencyHoppingOffsetLists__helper2.

Opaque PUSCH_Config__frequencyHoppingOffsetLists__cond PUSCH_Config__frequencyHoppingOffsetLists__Format.

Definition PUSCH_Config__resourceAllocation__Format : T_Format PUSCH_Config__resourceAllocation__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__resourceAllocation__nat__Format PUSCH_Config__resourceAllocation__F1 PUSCH_Config__resourceAllocation__F2 PUSCH_Config__resourceAllocation__F1F2 PUSCH_Config__resourceAllocation__F2F1.

Opaque PUSCH_Config__resourceAllocation__cond PUSCH_Config__resourceAllocation__Format.

Opaque PUSCH_Config__pusch_TimeDomainAllocationList__cond PUSCH_Config__pusch_TimeDomainAllocationList__Format.

Definition PUSCH_Config__pusch_AggregationFactor__Format : T_Format PUSCH_Config__pusch_AggregationFactor__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__pusch_AggregationFactor__nat__Format PUSCH_Config__pusch_AggregationFactor__F1 PUSCH_Config__pusch_AggregationFactor__F2 PUSCH_Config__pusch_AggregationFactor__F1F2 PUSCH_Config__pusch_AggregationFactor__F2F1.

Opaque PUSCH_Config__pusch_AggregationFactor__cond PUSCH_Config__pusch_AggregationFactor__Format.

Definition PUSCH_Config__mcs_Table__Format : T_Format PUSCH_Config__mcs_Table__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__mcs_Table__nat__Format PUSCH_Config__mcs_Table__F1 PUSCH_Config__mcs_Table__F2 PUSCH_Config__mcs_Table__F1F2 PUSCH_Config__mcs_Table__F2F1.

Opaque PUSCH_Config__mcs_Table__cond PUSCH_Config__mcs_Table__Format.

Definition PUSCH_Config__mcs_TableTransformPrecoder__Format : T_Format PUSCH_Config__mcs_TableTransformPrecoder__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__mcs_TableTransformPrecoder__nat__Format PUSCH_Config__mcs_TableTransformPrecoder__F1 PUSCH_Config__mcs_TableTransformPrecoder__F2 PUSCH_Config__mcs_TableTransformPrecoder__F1F2 PUSCH_Config__mcs_TableTransformPrecoder__F2F1.

Opaque PUSCH_Config__mcs_TableTransformPrecoder__cond PUSCH_Config__mcs_TableTransformPrecoder__Format.

Definition PUSCH_Config__transformPrecoder__Format : T_Format PUSCH_Config__transformPrecoder__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__transformPrecoder__nat__Format PUSCH_Config__transformPrecoder__F1 PUSCH_Config__transformPrecoder__F2 PUSCH_Config__transformPrecoder__F1F2 PUSCH_Config__transformPrecoder__F2F1.

Opaque PUSCH_Config__transformPrecoder__cond PUSCH_Config__transformPrecoder__Format.

Definition PUSCH_Config__codebookSubset__Format : T_Format PUSCH_Config__codebookSubset__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__codebookSubset__nat__Format PUSCH_Config__codebookSubset__F1 PUSCH_Config__codebookSubset__F2 PUSCH_Config__codebookSubset__F1F2 PUSCH_Config__codebookSubset__F2F1.

Opaque PUSCH_Config__codebookSubset__cond PUSCH_Config__codebookSubset__Format.

Definition PUSCH_Config__maxRank__Format : T_Format Z PUSCH_Config__maxRank__cond :=
 ranged_int_format (1) (4) PUSCH_Config__maxRank__helper1 PUSCH_Config__maxRank__helper2.

Opaque PUSCH_Config__maxRank__cond PUSCH_Config__maxRank__Format.

Definition PUSCH_Config__rbg_Size__Format : T_Format PUSCH_Config__rbg_Size__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__rbg_Size__nat__Format PUSCH_Config__rbg_Size__F1 PUSCH_Config__rbg_Size__F2 PUSCH_Config__rbg_Size__F1F2 PUSCH_Config__rbg_Size__F2F1.

Opaque PUSCH_Config__rbg_Size__cond PUSCH_Config__rbg_Size__Format.

Opaque PUSCH_Config__uci_OnPUSCH__cond PUSCH_Config__uci_OnPUSCH__Format.

Definition PUSCH_Config__tp_pi2BPSK__Format : T_Format PUSCH_Config__tp_pi2BPSK__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__tp_pi2BPSK__nat__Format PUSCH_Config__tp_pi2BPSK__F1 PUSCH_Config__tp_pi2BPSK__F2 PUSCH_Config__tp_pi2BPSK__F1F2 PUSCH_Config__tp_pi2BPSK__F2F1.

Opaque PUSCH_Config__tp_pi2BPSK__cond PUSCH_Config__tp_pi2BPSK__Format.

Opaque PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__cond PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__Format.

Opaque PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__cond PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__Format.

Definition PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__Format : T_Format Z PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__cond :=
 ranged_int_format (0) (4) PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__helper1 PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__helper2.

Opaque PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__cond PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F1 PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F2 PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__cond PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__Format : T_Format Z PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__cond :=
 ranged_int_format (0) (2) PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__helper1 PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__helper2.

Opaque PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__cond PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F1 PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F2 PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__cond PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Format.

Opaque PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__cond PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__Format.

Opaque PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__cond PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Format : T_Format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__nat__Format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F1F2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__F2F1.

Opaque PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Format.

Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Format : T_Format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__nat__Format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F1F2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__F2F1.

Opaque PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Format.


Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Format_Type := Eval cbn in get_formats PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Format_list : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Format_Type :=
  (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Format, (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Format, unit__Format)).
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list__Format := Eval compute in choice_format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__len_helper1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__len_helper2  PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Format_list.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F1 (z : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type) : (choice PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list) :=
  match z with
   | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA t => existT _ 0 t
  | PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB t => existT _ 1 t
  end.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__g := (fun n => typ_set (get_nth_typ PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list n)).
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F2 (y : choice PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list) : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__g n -> PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type) with
    | 0 => fun (t : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA__Type) => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeA t 
    | 1 => fun (t : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB__Type) => PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__pusch_RepTypeB t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type with end) n0
           end t0).

Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__helper2 :  forall (y : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type), PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__cond y -> choice_cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__helper3 :  forall (y : PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type), PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F2 (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__helper4 : (forall b : choice PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list, choice_cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list b -> PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__cond (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F2 b) /\ PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F1 (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F2.
Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Type PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__cond :=
  (* Eval compute in *) proj2_format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__list__Format PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__F2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__helper2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__helper3 PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__helper4.
Opaque PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Format.

Opaque PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__cond PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F1 PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F2 PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__cond PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F1 PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F2 PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__cond PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__maxRankDCI_0_2_r16__Format : T_Format Z PUSCH_Config__ext0O__maxRankDCI_0_2_r16__cond :=
 ranged_int_format (1) (4) PUSCH_Config__ext0O__maxRankDCI_0_2_r16__helper1 PUSCH_Config__ext0O__maxRankDCI_0_2_r16__helper2.

Opaque PUSCH_Config__ext0O__maxRankDCI_0_2_r16__cond PUSCH_Config__ext0O__maxRankDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F1 PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F2 PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__cond PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F1 PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F2 PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__cond PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F1 PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F2 PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__cond PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F1 PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F2 PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__cond PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F1 PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F2 PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__cond PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Format.

Definition PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Format : T_Format PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__nat__Format PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F1 PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F2 PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F1F2 PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__F2F1.

Opaque PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__cond PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Format.

Opaque PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__cond PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__Format.

Opaque PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__Format.

Opaque PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__Format.

Definition PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Format : T_Format PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__nat__Format PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F1 PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F2 PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F1F2 PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__F2F1.

Opaque PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__cond PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Format.

Definition PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Format : T_Format PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__nat__Format PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F1 PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F2 PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F1F2 PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__F2F1.

Opaque PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__cond PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Format.

Definition PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Format : T_Format PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__nat__Format PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F1 PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F2 PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F1F2 PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__F2F1.

Opaque PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__cond PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Format.

Definition PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Format : T_Format PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__nat__Format PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F1 PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F1F2 PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__F2F1.

Opaque PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__cond PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Format.

Opaque PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__cond PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__Format.

Opaque PUSCH_Config__ext0O__pusch_PowerControl_v1610__cond PUSCH_Config__ext0O__pusch_PowerControl_v1610__Format.

Definition PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Format : T_Format PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__nat__Format PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F1 PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F2 PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F1F2 PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__F2F1.

Opaque PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__cond PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Format.

Opaque PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__cond PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__Format.

Definition PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__Format : T_Format Z PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__cond :=
 ranged_int_format (1) (4) PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__helper1 PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__helper2.

Opaque PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__cond PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__Format.


Definition PUSCH_Config__ext0O__Format_Type := Eval cbn in seq_format_prod PUSCH_Config__ext0O__list.
Definition PUSCH_Config__ext0O__Format_list : PUSCH_Config__ext0O__Format_Type :=
  (PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16__Format, (PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16__Format, (PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16__Format, (PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16__Format, (PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16__Format, (PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16__Format, (PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16__Format, (PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16__Format, (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16__Format, (PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16__Format, (PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16__Format, (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16__Format, (PUSCH_Config__ext0O__maxRankDCI_0_2_r16__Format, (PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16__Format, (PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16__Format, (PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16__Format, (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16__Format, (PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16__Format, (PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16__Format, (PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16__Format, (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16__Format, (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16__Format, (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16__Format, (PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16__Format, (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16__Format, (PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16__Format, (PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16__Format, (InvalidSymbolPattern_r16__Format, (PUSCH_Config__ext0O__pusch_PowerControl_v1610__Format, (PUSCH_Config__ext0O__ul_FullPowerTransmission_r16__Format, (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16__Format, (PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16__Format, unit_format)))))))))))))))))))))))))))))))).
Definition PUSCH_Config__ext0O__list__Format := (*Eval compute in *) seq_format PUSCH_Config__ext0O__list PUSCH_Config__ext0O__Format_list.
Definition PUSCH_Config__ext0O__F1 z :=
  (PUSCH_Config__ext0O__minimumSchedulingOffsetK2_r16 z, (PUSCH_Config__ext0O__ul_AccessConfigListDCI_0_1_r16 z, (PUSCH_Config__ext0O__harq_ProcessNumberSizeDCI_0_2_r16 z, (PUSCH_Config__ext0O__dmrs_SequenceInitializationDCI_0_2_r16 z, (PUSCH_Config__ext0O__numberOfBitsForRV_DCI_0_2_r16 z, (PUSCH_Config__ext0O__antennaPortsFieldPresenceDCI_0_2_r16 z, (PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeA_DCI_0_2_r16 z, (PUSCH_Config__ext0O__dmrs_UplinkForPUSCH_MappingTypeB_DCI_0_2_r16 z, (PUSCH_Config__ext0O__frequencyHoppingDCI_0_2_r16 z, (PUSCH_Config__ext0O__frequencyHoppingOffsetListsDCI_0_2_r16 z, (PUSCH_Config__ext0O__codebookSubsetDCI_0_2_r16 z, (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_2_r16 z, (PUSCH_Config__ext0O__maxRankDCI_0_2_r16 z, (PUSCH_Config__ext0O__mcs_TableDCI_0_2_r16 z, (PUSCH_Config__ext0O__mcs_TableTransformPrecoderDCI_0_2_r16 z, (PUSCH_Config__ext0O__priorityIndicatorDCI_0_2_r16 z, (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_2_r16 z, (PUSCH_Config__ext0O__resourceAllocationDCI_0_2_r16 z, (PUSCH_Config__ext0O__resourceAllocationType1GranularityDCI_0_2_r16 z, (PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_2_r16 z, (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_2_r16 z, (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListDCI_0_1_r16 z, (PUSCH_Config__ext0O__invalidSymbolPatternIndicatorDCI_0_1_r16 z, (PUSCH_Config__ext0O__priorityIndicatorDCI_0_1_r16 z, (PUSCH_Config__ext0O__pusch_RepTypeIndicatorDCI_0_1_r16 z, (PUSCH_Config__ext0O__frequencyHoppingDCI_0_1_r16 z, (PUSCH_Config__ext0O__uci_OnPUSCH_ListDCI_0_1_r16 z, (PUSCH_Config__ext0O__invalidSymbolPattern_r16 z, (PUSCH_Config__ext0O__pusch_PowerControl_v1610 z, (PUSCH_Config__ext0O__ul_FullPowerTransmission_r16 z, (PUSCH_Config__ext0O__pusch_TimeDomainAllocationListForMultiPUSCH_r16 z, (PUSCH_Config__ext0O__numberOfInvalidSymbolsForDL_UL_Switching_r16 z, tt)))))))))))))))))))))))))))))))).
Definition PUSCH_Config__ext0O__F2 (y : seq_type PUSCH_Config__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, (i24, (i25, (i26, (i27, (i28, (i29, (i30, (i31, _))))))))))))))))))))))))))))))))=>
    make__PUSCH_Config__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31
  end.
Lemma PUSCH_Config__ext0O__F1F2_cond (z : PUSCH_Config__ext0O__Type)
  : PUSCH_Config__ext0O__cond z ->
  (seq_cond PUSCH_Config__ext0O__list (PUSCH_Config__ext0O__F1 z)).
intro H. unfold PUSCH_Config__ext0O__cond in H. simpl. auto. Qed.
Lemma PUSCH_Config__ext0O__F1F2_cond2 (z : PUSCH_Config__ext0O__Type)
 : PUSCH_Config__ext0O__F2 (PUSCH_Config__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_Config__ext0O__F2F1_cond (y : seq_type PUSCH_Config__ext0O__list)
  : seq_cond PUSCH_Config__ext0O__list y ->
 (PUSCH_Config__ext0O__cond (PUSCH_Config__ext0O__F2 y)) /\  PUSCH_Config__ext0O__F1 (PUSCH_Config__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_Config__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUSCH_Config__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_Config__ext0O__Format : T_Format PUSCH_Config__ext0O__Type PUSCH_Config__ext0O__cond :=
        proj2_format  PUSCH_Config__ext0O__cond PUSCH_Config__ext0O__list__Format
    PUSCH_Config__ext0O__F1 PUSCH_Config__ext0O__F2 PUSCH_Config__ext0O__F1F2_cond  PUSCH_Config__ext0O__F1F2_cond2 PUSCH_Config__ext0O__F2F1_cond.
Opaque PUSCH_Config__ext0O__cond PUSCH_Config__ext0O__Format.

Definition PUSCH_Config__ext0__check_all_none (b : PUSCH_Config__ext0O__Type) : bool :=
match b with 
  | make__PUSCH_Config__ext0O__Type None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition PUSCH_Config__ext0__Format : T_Format PUSCH_Config__ext0__Type PUSCH_Config__ext0__cond :=
  restrict_add_format PUSCH_Config__ext0__check_all_none PUSCH_Config__ext0O__Format.

Opaque PUSCH_Config__ext0__cond PUSCH_Config__ext0__Format.

Opaque PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__cond PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__Format.

Opaque PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__cond PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__Format.

Opaque PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__cond PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__Format.

Opaque PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__cond PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__Format.

Opaque PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__cond PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__Format.

Definition PUSCH_Config__ext1O__mappingPattern_r17__Format : T_Format PUSCH_Config__ext1O__mappingPattern_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext1O__mappingPattern_r17__nat__Format PUSCH_Config__ext1O__mappingPattern_r17__F1 PUSCH_Config__ext1O__mappingPattern_r17__F2 PUSCH_Config__ext1O__mappingPattern_r17__F1F2 PUSCH_Config__ext1O__mappingPattern_r17__F2F1.

Opaque PUSCH_Config__ext1O__mappingPattern_r17__cond PUSCH_Config__ext1O__mappingPattern_r17__Format.

Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Format : T_Format PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__nat__Format PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F1 PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F2 PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F1F2 PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__F2F1.

Opaque PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__cond PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Format.

Definition PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Format : T_Format PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__nat__Format PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F1 PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F2 PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F1F2 PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__F2F1.

Opaque PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__cond PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Format.

Definition PUSCH_Config__ext1O__sequenceOffsetForRV_r17__Format : T_Format Z PUSCH_Config__ext1O__sequenceOffsetForRV_r17__cond :=
 ranged_int_format (0) (3) PUSCH_Config__ext1O__sequenceOffsetForRV_r17__helper1 PUSCH_Config__ext1O__sequenceOffsetForRV_r17__helper2.

Opaque PUSCH_Config__ext1O__sequenceOffsetForRV_r17__cond PUSCH_Config__ext1O__sequenceOffsetForRV_r17__Format.

Opaque PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__cond PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__Format.

Opaque PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__cond PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__Format.

Definition PUSCH_Config__ext1O__availableSlotCounting_r17__Format : T_Format PUSCH_Config__ext1O__availableSlotCounting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUSCH_Config__ext1O__availableSlotCounting_r17__nat__Format PUSCH_Config__ext1O__availableSlotCounting_r17__F1 PUSCH_Config__ext1O__availableSlotCounting_r17__F2 PUSCH_Config__ext1O__availableSlotCounting_r17__F1F2 PUSCH_Config__ext1O__availableSlotCounting_r17__F2F1.

Opaque PUSCH_Config__ext1O__availableSlotCounting_r17__cond PUSCH_Config__ext1O__availableSlotCounting_r17__Format.

Opaque PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__cond PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__Format.

Definition PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__Format : T_Format Z PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__cond := fixed_int_format 5. Opaque PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__cond PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__Format.

Definition PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__Format : T_Format Z PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__cond := fixed_int_format 5. Opaque PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__cond PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__Format.

Definition PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__Format : T_Format PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__Type PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__cond := seq_of_format MPE_Resource_r17__Format 1 maxMPE_Resources_r17 PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__helper1 PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__helper2.

Opaque PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__cond PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__Format.

Definition PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__Format : T_Format PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__Type PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__cond := seq_of_format MPE_ResourceId_r17__Format 1 maxMPE_Resources_r17 PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__helper1 PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__helper2.

Opaque PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__cond PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__Format.


Definition PUSCH_Config__ext1O__Format_Type := Eval cbn in seq_format_prod PUSCH_Config__ext1O__list.
Definition PUSCH_Config__ext1O__Format_list : PUSCH_Config__ext1O__Format_Type :=
  (PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17__Format, (PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17__Format, (PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17__Format, (PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17__Format, (PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17__Format, (PUSCH_Config__ext1O__mappingPattern_r17__Format, (PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17__Format, (PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17__Format, (PUSCH_Config__ext1O__sequenceOffsetForRV_r17__Format, (PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17__Format, (PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17__Format, (PUSCH_Config__ext1O__availableSlotCounting_r17__Format, (PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17__Format, (PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700__Format, (PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17__Format, (PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17__Format, (PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17__Format, unit_format))))))))))))))))).
Definition PUSCH_Config__ext1O__list__Format := (*Eval compute in *) seq_format PUSCH_Config__ext1O__list PUSCH_Config__ext1O__Format_list.
Definition PUSCH_Config__ext1O__F1 z :=
  (PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_2_r17 z, (PUSCH_Config__ext1O__betaOffsetsCrossPri0_r17 z, (PUSCH_Config__ext1O__betaOffsetsCrossPri1_r17 z, (PUSCH_Config__ext1O__betaOffsetsCrossPri0DCI_0_2_r17 z, (PUSCH_Config__ext1O__betaOffsetsCrossPri1DCI_0_2_r17 z, (PUSCH_Config__ext1O__mappingPattern_r17 z, (PUSCH_Config__ext1O__secondTPCFieldDCI_0_1_r17 z, (PUSCH_Config__ext1O__secondTPCFieldDCI_0_2_r17 z, (PUSCH_Config__ext1O__sequenceOffsetForRV_r17 z, (PUSCH_Config__ext1O__ul_AccessConfigListDCI_0_1_r17 z, (PUSCH_Config__ext1O__minimumSchedulingOffsetK2_r17 z, (PUSCH_Config__ext1O__availableSlotCounting_r17 z, (PUSCH_Config__ext1O__dmrs_BundlingPUSCH_Config_r17 z, (PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_2_v1700 z, (PUSCH_Config__ext1O__harq_ProcessNumberSizeDCI_0_1_r17 z, (PUSCH_Config__ext1O__mpe_ResourcePoolToAddModList_r17 z, (PUSCH_Config__ext1O__mpe_ResourcePoolToReleaseList_r17 z, tt))))))))))))))))).
Definition PUSCH_Config__ext1O__F2 (y : seq_type PUSCH_Config__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, _)))))))))))))))))=>
    make__PUSCH_Config__ext1O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16
  end.
Lemma PUSCH_Config__ext1O__F1F2_cond (z : PUSCH_Config__ext1O__Type)
  : PUSCH_Config__ext1O__cond z ->
  (seq_cond PUSCH_Config__ext1O__list (PUSCH_Config__ext1O__F1 z)).
intro H. unfold PUSCH_Config__ext1O__cond in H. simpl. auto. Qed.
Lemma PUSCH_Config__ext1O__F1F2_cond2 (z : PUSCH_Config__ext1O__Type)
 : PUSCH_Config__ext1O__F2 (PUSCH_Config__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_Config__ext1O__F2F1_cond (y : seq_type PUSCH_Config__ext1O__list)
  : seq_cond PUSCH_Config__ext1O__list y ->
 (PUSCH_Config__ext1O__cond (PUSCH_Config__ext1O__F2 y)) /\  PUSCH_Config__ext1O__F1 (PUSCH_Config__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_Config__ext1O__cond. simpl in *. auto.
 - simpl. unfold PUSCH_Config__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_Config__ext1O__Format : T_Format PUSCH_Config__ext1O__Type PUSCH_Config__ext1O__cond :=
        proj2_format  PUSCH_Config__ext1O__cond PUSCH_Config__ext1O__list__Format
    PUSCH_Config__ext1O__F1 PUSCH_Config__ext1O__F2 PUSCH_Config__ext1O__F1F2_cond  PUSCH_Config__ext1O__F1F2_cond2 PUSCH_Config__ext1O__F2F1_cond.
Opaque PUSCH_Config__ext1O__cond PUSCH_Config__ext1O__Format.

Definition PUSCH_Config__ext1__check_all_none (b : PUSCH_Config__ext1O__Type) : bool :=
match b with 
  | make__PUSCH_Config__ext1O__Type None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition PUSCH_Config__ext1__Format : T_Format PUSCH_Config__ext1__Type PUSCH_Config__ext1__cond :=
  restrict_add_format PUSCH_Config__ext1__check_all_none PUSCH_Config__ext1O__Format.

Opaque PUSCH_Config__ext1__cond PUSCH_Config__ext1__Format.


Definition PUSCH_Config__root_Format_Type := Eval cbn in seq_format_prod PUSCH_Config__root_list.
Definition PUSCH_Config__root_Format_list : PUSCH_Config__root_Format_Type :=
  (PUSCH_Config__dataScramblingIdentityPUSCH__Format, (PUSCH_Config__txConfig__Format, (PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA__Format, (PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB__Format, (PUSCH_PowerControl__Format, (PUSCH_Config__frequencyHopping__Format, (PUSCH_Config__frequencyHoppingOffsetLists__Format, (PUSCH_Config__resourceAllocation__Format, (PUSCH_Config__pusch_TimeDomainAllocationList__Format, (PUSCH_Config__pusch_AggregationFactor__Format, (PUSCH_Config__mcs_Table__Format, (PUSCH_Config__mcs_TableTransformPrecoder__Format, (PUSCH_Config__transformPrecoder__Format, (PUSCH_Config__codebookSubset__Format, (PUSCH_Config__maxRank__Format, (PUSCH_Config__rbg_Size__Format, (PUSCH_Config__uci_OnPUSCH__Format, (PUSCH_Config__tp_pi2BPSK__Format, unit_format)))))))))))))))))).

Definition PUSCH_Config__ext_Format_Type := Eval cbn in get_formats PUSCH_Config__ext_list.
Definition PUSCH_Config__ext_Format_list : PUSCH_Config__ext_Format_Type :=
  (PUSCH_Config__ext0__Format, (PUSCH_Config__ext1__Format, unit__Format)).

Definition PUSCH_Config__list_type : Set := (seq_type PUSCH_Config__root_list) * (seq_ext_type PUSCH_Config__ext_list).
Definition PUSCH_Config__list_cond (z : PUSCH_Config__list_type) : Prop :=
        (seq_cond PUSCH_Config__root_list (fst z)) /\ (seq_ext_cond PUSCH_Config__ext_list (snd z)).
Definition PUSCH_Config__list_format : T_Format PUSCH_Config__list_type PUSCH_Config__list_cond :=
 (* Eval compute in *) seq_ext_format PUSCH_Config__root_list PUSCH_Config__root_Format_list PUSCH_Config__ext_list PUSCH_Config__ext_Format_list.

Opaque PUSCH_Config__list_format.
Definition PUSCH_Config__F1 (z : PUSCH_Config__Type) : PUSCH_Config__list_type :=
  (((PUSCH_Config__dataScramblingIdentityPUSCH z, (PUSCH_Config__txConfig z, (PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeA z, (PUSCH_Config__dmrs_UplinkForPUSCH_MappingTypeB z, (PUSCH_Config__pusch_PowerControl z, (PUSCH_Config__frequencyHopping z, (PUSCH_Config__frequencyHoppingOffsetLists z, (PUSCH_Config__resourceAllocation z, (PUSCH_Config__pusch_TimeDomainAllocationList z, (PUSCH_Config__pusch_AggregationFactor z, (PUSCH_Config__mcs_Table z, (PUSCH_Config__mcs_TableTransformPrecoder z, (PUSCH_Config__transformPrecoder z, (PUSCH_Config__codebookSubset z, (PUSCH_Config__maxRank z, (PUSCH_Config__rbg_Size z, (PUSCH_Config__uci_OnPUSCH z, (PUSCH_Config__tp_pi2BPSK z, tt))))))))))))))))))), (
(PUSCH_Config__ext0 z, (PUSCH_Config__ext1 z, tt)))).
Definition PUSCH_Config__F2 (y : PUSCH_Config__list_type) : PUSCH_Config__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, _)))))))))))))))))), (i0, (i1, _)))=>
    make__PUSCH_Config__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 i0 i1
  end.
Definition PUSCH_Config__helper1 : (forall a : PUSCH_Config__Type, PUSCH_Config__cond a -> PUSCH_Config__list_cond (PUSCH_Config__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUSCH_Config__helper2 : (forall a : PUSCH_Config__Type, PUSCH_Config__F2 (PUSCH_Config__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUSCH_Config__helper3 : (forall b : PUSCH_Config__list_type, PUSCH_Config__list_cond b -> PUSCH_Config__cond (PUSCH_Config__F2 b) /\ PUSCH_Config__F1 (PUSCH_Config__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUSCH_Config__cond, PUSCH_Config__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUSCH_Config__Format : T_Format PUSCH_Config__Type PUSCH_Config__cond :=
 proj2_format PUSCH_Config__cond PUSCH_Config__list_format  PUSCH_Config__F1 PUSCH_Config__F2 PUSCH_Config__helper1 PUSCH_Config__helper2 PUSCH_Config__helper3.

Opaque PUSCH_Config__cond PUSCH_Config__Format.

