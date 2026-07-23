Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma MsgA_PUSCH_Resource_r16__msgA_MCS_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__msgA_MCS_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__msgA_MCS_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__msgA_MCS_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__msgA_MCS_r16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__cond := (fun z => (1 <= z <= 4)%Z).
Inductive MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Type : Set :=
 | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__one
 | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__two
 | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__three
 | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__six
.
Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__cond := (fun (_ : MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Type) => True).
Lemma MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__nat__helper.

Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F1 t :=
  match t with
  | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__one => 0
  | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__two => 1
  | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__three => 2
  | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__six => 3
  end.
Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F2 n :=
  match n with
  | 0 => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__one
  | 1 => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__two
  | 2 => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__three
  | 3 => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__six
  | _ => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__one
  end.
Lemma MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F1F2 : forall x : MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Type, (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F1 x <= 3) /\ MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F2 (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F1 x) = x. imp_solve. Qed.
Lemma MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F2F1 : forall (y : nat) (H : y <= 3), MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F1 (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F2 y) = y. enum_solve H y. Qed.

Lemma MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__cond := (fun z => (1 <= z <= 32)%Z).
Lemma MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__helper1 : (1 <= maxNrofUL_Allocations)%Z. unfold maxNrofUL_Allocations.
 lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__cond := (fun z => (1 <= z <= maxNrofUL_Allocations)%Z).
Lemma MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__cond := (fun z => (0 <= z <= 127)%Z).
Inductive MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Type : Set :=
 | MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__typeA
 | MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__typeB
.
Definition MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__cond := (fun (_ : MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Type) => True).
Lemma MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__nat__helper.

Definition MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F1 t :=
  match t with
  | MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__typeA => 0
  | MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__typeB => 1
  end.
Definition MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F2 n :=
  match n with
  | 0 => MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__typeA
  | 1 => MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__typeB
  | _ => MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__typeA
  end.
Lemma MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F1F2 : forall x : MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Type, (MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F1 x <= 1) /\ MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F2 (MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F2F1 : forall (y : nat) (H : y <= 1), MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F1 (MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Lemma MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__cond := (fun z => (0 <= z <= 3)%Z).
Lemma MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__cond := (fun z => (0 <= z <= 1)%Z).
Lemma MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Lemma MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__cond := (fun z => (1 <= z <= 32)%Z).
Inductive MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Type : Set :=
 | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__one
 | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__two
 | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__four
 | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__eight
.
Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__cond := (fun (_ : MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Type) => True).
Lemma MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__nat__helper.

Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F1 t :=
  match t with
  | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__one => 0
  | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__two => 1
  | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__four => 2
  | MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__eight => 3
  end.
Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F2 n :=
  match n with
  | 0 => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__one
  | 1 => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__two
  | 2 => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__four
  | 3 => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__eight
  | _ => MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__one
  end.
Lemma MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F1F2 : forall x : MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Type, (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F1 x <= 3) /\ MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F2 (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F1 x) = x. imp_solve. Qed.
Lemma MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F2F1 : forall (y : nat) (H : y <= 3), MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F1 (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Type : Set :=
 | MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__enabled
.
Definition MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__cond := (fun (_ : MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Type) => True).
Lemma MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__nat__helper.

Definition MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F1 t :=
  match t with
  | MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__enabled => 0
  end.
Definition MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F2 n :=
  match n with
  | 0 => MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__enabled
  | _ => MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__enabled
  end.
Lemma MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F1F2 : forall x : MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Type, (MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F1 x <= 0) /\ MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F2 (MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F1 x) = x. imp_solve. Qed.
Lemma MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F2F1 : forall (y : nat) (H : y <= 0), MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F1 (MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F2 y) = y. enum_solve H y. Qed.

Definition MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__Type := bit_string_fixed.
Definition MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.MsgA_DMRS_Config_r16.

Opaque MsgA_DMRS_Config_r16__cond MsgA_DMRS_Config_r16__Format.

Lemma MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__cond := (fun z => (1 <= z <= 2)%Z).
Inductive MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Type : Set :=
 | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha0
 | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha04
 | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha05
 | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha06
 | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha07
 | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha08
 | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha09
 | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha1
.
Definition MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__cond := (fun (_ : MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Type) => True).
Lemma MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__nat__helper.

Definition MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F1 t :=
  match t with
  | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha0 => 0
  | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha04 => 1
  | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha05 => 2
  | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha06 => 3
  | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha07 => 4
  | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha08 => 5
  | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha09 => 6
  | MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha1 => 7
  end.
Definition MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F2 n :=
  match n with
  | 0 => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha0
  | 1 => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha04
  | 2 => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha05
  | 3 => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha06
  | 4 => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha07
  | 5 => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha08
  | 6 => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha09
  | 7 => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha1
  | _ => MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__alpha0
  end.
Lemma MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F1F2 : forall x : MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Type, (MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F1 x <= 7) /\ MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F2 (MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F1 x) = x. imp_solve. Qed.
Lemma MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F2F1 : forall (y : nat) (H : y <= 7), MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F1 (MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F2 y) = y. enum_solve H y. Qed.

Lemma MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__helper1 : (1 <= 10)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__helper2 : to_bit_sz (Z.to_nat (10 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__cond := (fun z => (1 <= z <= 10)%Z).
Lemma MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__helper1 : (1 <= 10)%Z.  lia. Qed.
Lemma MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__helper2 : to_bit_sz (Z.to_nat (10 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__Type := Z.
Definition MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__cond := (fun z => (1 <= z <= 10)%Z).
Record MsgA_PUSCH_Resource_r16__Type : Set :=
  make__MsgA_PUSCH_Resource_r16__Type {
    MsgA_PUSCH_Resource_r16__msgA_MCS_r16 : Z ;
    MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16 : Z ;
    MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16 : MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Type ;
    MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16 : Z ;
    MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16 : option Z ;
    MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16 : option Z ;
    MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16 : option MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Type ;
    MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16 : option Z ;
    MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16 : Z ;
    MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16 : Z ;
    MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16 : Z ;
    MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16 : MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Type ;
    MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16 : option MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Type ;
    MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16 : option MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__Type ;
    MsgA_PUSCH_Resource_r16__msgA_DMRS_Config_r16 : MsgA_DMRS_Config_r16__Type ;
    MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16 : Z ;
    MsgA_PUSCH_Resource_r16__msgA_Alpha_r16 : option MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Type ;
    MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16 : option Z ;
    MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16 : option Z ;
}.
Definition MsgA_PUSCH_Resource_r16__root_list : list seq_elem := (
 Nor Z MsgA_PUSCH_Resource_r16__msgA_MCS_r16__cond ::
 Nor Z MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__cond ::
 Nor MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Type MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__cond ::
 Nor Z MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__cond ::
 Opt Z MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__cond ::
 Opt Z MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__cond ::
 Opt MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Type MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__cond ::
 Opt Z MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__cond ::
 Nor Z MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__cond ::
 Nor Z MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__cond ::
 Nor Z MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__cond ::
 Nor MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Type MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__cond ::
 Opt MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Type MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__cond ::
 Opt MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__Type MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__cond ::
 Nor MsgA_DMRS_Config_r16__Type MsgA_DMRS_Config_r16__cond ::
 Nor Z MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__cond ::
 Opt MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Type MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__cond ::
 Opt Z MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__cond ::
 Opt Z MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__cond ::
 nil).
Definition MsgA_PUSCH_Resource_r16__ext_list : list typ := (
  nil).
Definition MsgA_PUSCH_Resource_r16__cond (z : MsgA_PUSCH_Resource_r16__Type) := 
(  MsgA_PUSCH_Resource_r16__msgA_MCS_r16__cond (MsgA_PUSCH_Resource_r16__msgA_MCS_r16 z) /\
  MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__cond (MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16 z) /\
  MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__cond (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16 z) /\
  MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__cond (MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__cond (MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__cond (MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__cond (MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__cond (MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16 z) /\
  MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__cond (MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16 z) /\
  MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__cond (MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16 z) /\
  MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__cond (MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16 z) /\
  MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__cond (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__cond (MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__cond (MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16 z) /\
  MsgA_DMRS_Config_r16__cond (MsgA_PUSCH_Resource_r16__msgA_DMRS_Config_r16 z) /\
  MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__cond (MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__cond (MsgA_PUSCH_Resource_r16__msgA_Alpha_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__cond (MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16 z) /\
  opt_cond MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__cond (MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16 z) /\
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
Definition MsgA_PUSCH_Resource_r16__msgA_MCS_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__msgA_MCS_r16__cond :=
 ranged_int_format (0) (15) MsgA_PUSCH_Resource_r16__msgA_MCS_r16__helper1 MsgA_PUSCH_Resource_r16__msgA_MCS_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__msgA_MCS_r16__cond MsgA_PUSCH_Resource_r16__msgA_MCS_r16__Format.

Definition MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__cond :=
 ranged_int_format (1) (4) MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__helper1 MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__cond MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__Format.

Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Format : T_Format MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__nat__Format MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F1 MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F2 MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F1F2 MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__F2F1.

Opaque MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__cond MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Format.

Definition MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__cond :=
 ranged_int_format (1) (32) MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__helper1 MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__cond MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__Format.

Definition MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__cond :=
 ranged_int_format (1) (maxNrofUL_Allocations) MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__helper1 MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__cond MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__Format.

Definition MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__cond :=
 ranged_int_format (0) (127) MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__helper1 MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__cond MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__Format.

Definition MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Format : T_Format MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__nat__Format MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F1 MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F2 MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F1F2 MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__F2F1.

Opaque MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__cond MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Format.

Definition MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__cond :=
 ranged_int_format (0) (3) MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__helper1 MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__cond MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__Format.

Definition MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__cond :=
 ranged_int_format (0) (1) MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__helper1 MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__cond MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__Format.

Definition MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__helper1 MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__cond MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__Format.

Definition MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__cond :=
 ranged_int_format (1) (32) MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__helper1 MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__cond MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__Format.

Definition MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Format : T_Format MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__nat__Format MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F1 MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F2 MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F1F2 MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__F2F1.

Opaque MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__cond MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Format.

Definition MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Format : T_Format MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__nat__Format MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F1 MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F2 MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F1F2 MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__F2F1.

Opaque MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__cond MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Format.

Definition MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__Format : T_Format MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__Type MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__cond MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__Format.

Definition MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__cond :=
 ranged_int_format (1) (2) MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__helper1 MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__cond MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__Format.

Definition MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Format : T_Format MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__nat__Format MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F1 MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F2 MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F1F2 MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__F2F1.

Opaque MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__cond MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Format.

Definition MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__cond :=
 ranged_int_format (1) (10) MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__helper1 MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__cond MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__Format.

Definition MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__Format : T_Format Z MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__cond :=
 ranged_int_format (1) (10) MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__helper1 MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__helper2.

Opaque MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__cond MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__Format.


Definition MsgA_PUSCH_Resource_r16__root_Format_Type := Eval cbn in seq_format_prod MsgA_PUSCH_Resource_r16__root_list.
Definition MsgA_PUSCH_Resource_r16__root_Format_list : MsgA_PUSCH_Resource_r16__root_Format_Type :=
  (MsgA_PUSCH_Resource_r16__msgA_MCS_r16__Format, (MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16__Format, (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16__Format, (MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16__Format, (MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16__Format, (MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16__Format, (MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16__Format, (MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16__Format, (MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16__Format, (MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16__Format, (MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16__Format, (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16__Format, (MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16__Format, (MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16__Format, (MsgA_DMRS_Config_r16__Format, (MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16__Format, (MsgA_PUSCH_Resource_r16__msgA_Alpha_r16__Format, (MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16__Format, (MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16__Format, unit_format))))))))))))))))))).

Definition MsgA_PUSCH_Resource_r16__ext_Format_Type := Eval cbn in get_formats MsgA_PUSCH_Resource_r16__ext_list.
Definition MsgA_PUSCH_Resource_r16__ext_Format_list : MsgA_PUSCH_Resource_r16__ext_Format_Type :=
  unit__Format.

Definition MsgA_PUSCH_Resource_r16__list_type : Set := (seq_type MsgA_PUSCH_Resource_r16__root_list) * (seq_ext_type MsgA_PUSCH_Resource_r16__ext_list).
Definition MsgA_PUSCH_Resource_r16__list_cond (z : MsgA_PUSCH_Resource_r16__list_type) : Prop :=
        (seq_cond MsgA_PUSCH_Resource_r16__root_list (fst z)) /\ (seq_ext_cond MsgA_PUSCH_Resource_r16__ext_list (snd z)).
Definition MsgA_PUSCH_Resource_r16__list_format : T_Format MsgA_PUSCH_Resource_r16__list_type MsgA_PUSCH_Resource_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MsgA_PUSCH_Resource_r16__root_list MsgA_PUSCH_Resource_r16__root_Format_list MsgA_PUSCH_Resource_r16__ext_list MsgA_PUSCH_Resource_r16__ext_Format_list.

Opaque MsgA_PUSCH_Resource_r16__list_format.
Definition MsgA_PUSCH_Resource_r16__F1 (z : MsgA_PUSCH_Resource_r16__Type) : MsgA_PUSCH_Resource_r16__list_type :=
  (((MsgA_PUSCH_Resource_r16__msgA_MCS_r16 z, (MsgA_PUSCH_Resource_r16__nrofSlotsMsgA_PUSCH_r16 z, (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_PerSlot_r16 z, (MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainOffset_r16 z, (MsgA_PUSCH_Resource_r16__msgA_PUSCH_TimeDomainAllocation_r16 z, (MsgA_PUSCH_Resource_r16__startSymbolAndLengthMsgA_PO_r16 z, (MsgA_PUSCH_Resource_r16__mappingTypeMsgA_PUSCH_r16 z, (MsgA_PUSCH_Resource_r16__guardPeriodMsgA_PUSCH_r16 z, (MsgA_PUSCH_Resource_r16__guardBandMsgA_PUSCH_r16 z, (MsgA_PUSCH_Resource_r16__frequencyStartMsgA_PUSCH_r16 z, (MsgA_PUSCH_Resource_r16__nrofPRBs_PerMsgA_PO_r16 z, (MsgA_PUSCH_Resource_r16__nrofMsgA_PO_FDM_r16 z, (MsgA_PUSCH_Resource_r16__msgA_IntraSlotFrequencyHopping_r16 z, (MsgA_PUSCH_Resource_r16__msgA_HoppingBits_r16 z, (MsgA_PUSCH_Resource_r16__msgA_DMRS_Config_r16 z, (MsgA_PUSCH_Resource_r16__nrofDMRS_Sequences_r16 z, (MsgA_PUSCH_Resource_r16__msgA_Alpha_r16 z, (MsgA_PUSCH_Resource_r16__interlaceIndexFirstPO_MsgA_PUSCH_r16 z, (MsgA_PUSCH_Resource_r16__nrofInterlacesPerMsgA_PO_r16 z, tt)))))))))))))))))))), (
tt)).
Definition MsgA_PUSCH_Resource_r16__F2 (y : MsgA_PUSCH_Resource_r16__list_type) : MsgA_PUSCH_Resource_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, (j18, _))))))))))))))))))), _)=>
    make__MsgA_PUSCH_Resource_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18
  end.
Definition MsgA_PUSCH_Resource_r16__helper1 : (forall a : MsgA_PUSCH_Resource_r16__Type, MsgA_PUSCH_Resource_r16__cond a -> MsgA_PUSCH_Resource_r16__list_cond (MsgA_PUSCH_Resource_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MsgA_PUSCH_Resource_r16__helper2 : (forall a : MsgA_PUSCH_Resource_r16__Type, MsgA_PUSCH_Resource_r16__F2 (MsgA_PUSCH_Resource_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MsgA_PUSCH_Resource_r16__helper3 : (forall b : MsgA_PUSCH_Resource_r16__list_type, MsgA_PUSCH_Resource_r16__list_cond b -> MsgA_PUSCH_Resource_r16__cond (MsgA_PUSCH_Resource_r16__F2 b) /\ MsgA_PUSCH_Resource_r16__F1 (MsgA_PUSCH_Resource_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MsgA_PUSCH_Resource_r16__cond, MsgA_PUSCH_Resource_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MsgA_PUSCH_Resource_r16__Format : T_Format MsgA_PUSCH_Resource_r16__Type MsgA_PUSCH_Resource_r16__cond :=
 proj2_format MsgA_PUSCH_Resource_r16__cond MsgA_PUSCH_Resource_r16__list_format  MsgA_PUSCH_Resource_r16__F1 MsgA_PUSCH_Resource_r16__F2 MsgA_PUSCH_Resource_r16__helper1 MsgA_PUSCH_Resource_r16__helper2 MsgA_PUSCH_Resource_r16__helper3.

Opaque MsgA_PUSCH_Resource_r16__cond MsgA_PUSCH_Resource_r16__Format.

