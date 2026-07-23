Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SL_ScheduledConfig_r16.
Definition SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__Type := SetupRelease__Type SL_ScheduledConfig_r16__Type.
Definition SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__cond := SetupRelease__cond _ SL_ScheduledConfig_r16__cond.
Definition SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__cond := SetupRelease__Format _ _ SL_ScheduledConfig_r16__Format.
Opaque SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_UE_SelectedConfig_r16.
Definition SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__Type := SetupRelease__Type SL_UE_SelectedConfig_r16__Type.
Definition SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__cond := SetupRelease__cond _ SL_UE_SelectedConfig_r16__cond.
Definition SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__cond := SetupRelease__Format _ _ SL_UE_SelectedConfig_r16__Format.
Opaque SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__Format.

Require Import NR.SL_Freq_Id_r16.

Opaque SL_Freq_Id_r16__cond SL_Freq_Id_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__Type := list SL_Freq_Id_r16__Type.

Lemma SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__helper1 : (0 <= 1 <= maxNrofFreqSL_r16)%Z. unfold maxNrofFreqSL_r16.
 lia. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofFreqSL_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofFreqSL_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__cond (z : SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofFreqSL_r16)%Z /\ (list_and SL_Freq_Id_r16__cond z) .

Require Import NR.SL_FreqConfig_r16.

Opaque SL_FreqConfig_r16__cond SL_FreqConfig_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__Type := list SL_FreqConfig_r16__Type.

Lemma SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__helper1 : (0 <= 1 <= maxNrofFreqSL_r16)%Z. unfold maxNrofFreqSL_r16.
 lia. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofFreqSL_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofFreqSL_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__cond (z : SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofFreqSL_r16)%Z /\ (list_and SL_FreqConfig_r16__cond z) .

Require Import NR.SL_RLC_BearerConfigIndex_r16.

Opaque SL_RLC_BearerConfigIndex_r16__cond SL_RLC_BearerConfigIndex_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__Type := list SL_RLC_BearerConfigIndex_r16__Type.

Lemma SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__helper1 : (0 <= 1 <= maxSL_LCID_r16)%Z. unfold maxSL_LCID_r16.
 lia. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxSL_LCID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSL_LCID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__cond (z : SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSL_LCID_r16)%Z /\ (list_and SL_RLC_BearerConfigIndex_r16__cond z) .

Require Import NR.SL_RLC_BearerConfig_r16.

Opaque SL_RLC_BearerConfig_r16__cond SL_RLC_BearerConfig_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__Type := list SL_RLC_BearerConfig_r16__Type.

Lemma SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__helper1 : (0 <= 1 <= maxSL_LCID_r16)%Z. unfold maxSL_LCID_r16.
 lia. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxSL_LCID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSL_LCID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__cond (z : SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSL_LCID_r16)%Z /\ (list_and SL_RLC_BearerConfig_r16__cond z) .

Inductive SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Type : Set :=
 | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n1
 | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n2
 | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n3
 | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n4
 | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n6
 | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n8
 | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n16
 | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n32
.
Definition SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__cond := (fun (_ : SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Type) => True).
Lemma SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__nat__helper.

Definition SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F1 t :=
  match t with
  | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n1 => 0
  | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n2 => 1
  | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n3 => 2
  | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n4 => 3
  | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n6 => 4
  | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n8 => 5
  | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n16 => 6
  | SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n32 => 7
  end.
Definition SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F2 n :=
  match n with
  | 0 => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n1
  | 1 => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n2
  | 2 => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n3
  | 3 => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n4
  | 4 => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n6
  | 5 => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n8
  | 6 => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n16
  | 7 => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n32
  | _ => SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__n1
  end.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F1F2 : forall x : SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Type, (SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F1 x <= 7) /\ SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F2 (SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F1 (SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Type : Set :=
 | SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__enabled
.
Definition SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__cond := (fun (_ : SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Type) => True).
Lemma SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__nat__helper.

Definition SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F1 t :=
  match t with
  | SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__enabled => 0
  end.
Definition SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F2 n :=
  match n with
  | 0 => SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__enabled
  | _ => SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__enabled
  end.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F1F2 : forall x : SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Type, (SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F1 x <= 0) /\ SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F2 (SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F1 (SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.SchedulingRequestId.
Definition SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__Type := SetupRelease__Type SchedulingRequestId__Type.
Definition SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__cond := SetupRelease__cond _ SchedulingRequestId__cond.
Definition SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__cond := SetupRelease__Format _ _ SchedulingRequestId__Format.
Opaque SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__Format.

Lemma SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__Type := Z.
Definition SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__cond := (fun z => (1 <= z <= 8)%Z).
Inductive SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Type : Set :=
 | SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__on
 | SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__off
.
Definition SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__cond := (fun (_ : SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Type) => True).
Lemma SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__nat__helper.

Definition SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F1 t :=
  match t with
  | SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__on => 0
  | SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__off => 1
  end.
Definition SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F2 n :=
  match n with
  | 0 => SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__on
  | 1 => SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__off
  | _ => SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__on
  end.
Lemma SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F1F2 : forall x : SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Type, (SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F1 x <= 1) /\ SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F2 (SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F1 (SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F2 y) = y. enum_solve H y. Qed.

Record SL_PHY_MAC_RLC_Config_r16__Type : Set :=
  make__SL_PHY_MAC_RLC_Config_r16__Type {
    SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16 : option SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__Type ;
    SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16 : option Z ;
    SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16 : option SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Type ;
}.
Definition SL_PHY_MAC_RLC_Config_r16__list := (
 Opt SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__cond ::
 Opt Z SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__cond ::
 Opt SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Type SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__cond ::
 nil).
Definition SL_PHY_MAC_RLC_Config_r16__cond z := 
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__cond (SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__cond (SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16 z) /\
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
Opaque SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__Format.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__cond := seq_of_format SL_Freq_Id_r16__Format 1 maxNrofFreqSL_r16 SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__helper1 SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__helper2.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__cond := seq_of_format SL_FreqConfig_r16__Format 1 maxNrofFreqSL_r16 SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__helper1 SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__helper2.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__cond := seq_of_format SL_RLC_BearerConfigIndex_r16__Format 1 maxSL_LCID_r16 SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__helper1 SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__helper2.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__Type SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__cond := seq_of_format SL_RLC_BearerConfig_r16__Format 1 maxSL_LCID_r16 SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__helper1 SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__helper2.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__nat__Format SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F1 SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F2 SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F1F2 SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__F2F1.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__nat__Format SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F1 SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F2 SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F1F2 SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__F2F1.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Format.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__Format : T_Format Z SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__cond :=
 ranged_int_format (1) (8) SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__helper1 SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__helper2.

Opaque SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__cond SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__Format.

Definition SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__nat__Format SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F1 SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F2 SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F1F2 SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__F2F1.

Opaque SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__cond SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Format.


Definition SL_PHY_MAC_RLC_Config_r16__Format_Type := Eval cbn in seq_format_prod SL_PHY_MAC_RLC_Config_r16__list.
Definition SL_PHY_MAC_RLC_Config_r16__Format_list : SL_PHY_MAC_RLC_Config_r16__Format_Type :=
  (SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16__Format, (SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16__Format, (SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16__Format, unit_format))))))))))).
Definition SL_PHY_MAC_RLC_Config_r16__list__Format := (*Eval compute in *) seq_format SL_PHY_MAC_RLC_Config_r16__list SL_PHY_MAC_RLC_Config_r16__Format_list.
Definition SL_PHY_MAC_RLC_Config_r16__F1 z :=
  (SL_PHY_MAC_RLC_Config_r16__sl_ScheduledConfig_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_UE_SelectedConfig_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToReleaseList_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_FreqInfoToAddModList_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToReleaseList_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_RLC_BearerToAddModList_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_MaxNumConsecutiveDTX_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_CSI_Acquisition_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_CSI_SchedulingRequestId_r16 z, (SL_PHY_MAC_RLC_Config_r16__sl_SSB_PriorityNR_r16 z, (SL_PHY_MAC_RLC_Config_r16__networkControlledSyncTx_r16 z, tt))))))))))).
Definition SL_PHY_MAC_RLC_Config_r16__F2 (y : seq_type SL_PHY_MAC_RLC_Config_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, _)))))))))))=>
    make__SL_PHY_MAC_RLC_Config_r16__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10
  end.
Lemma SL_PHY_MAC_RLC_Config_r16__F1F2_cond (z : SL_PHY_MAC_RLC_Config_r16__Type)
  : SL_PHY_MAC_RLC_Config_r16__cond z ->
  (seq_cond SL_PHY_MAC_RLC_Config_r16__list (SL_PHY_MAC_RLC_Config_r16__F1 z)).
intro H. unfold SL_PHY_MAC_RLC_Config_r16__cond in H. simpl. auto. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__F1F2_cond2 (z : SL_PHY_MAC_RLC_Config_r16__Type)
 : SL_PHY_MAC_RLC_Config_r16__F2 (SL_PHY_MAC_RLC_Config_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SL_PHY_MAC_RLC_Config_r16__F2F1_cond (y : seq_type SL_PHY_MAC_RLC_Config_r16__list)
  : seq_cond SL_PHY_MAC_RLC_Config_r16__list y ->
 (SL_PHY_MAC_RLC_Config_r16__cond (SL_PHY_MAC_RLC_Config_r16__F2 y)) /\  SL_PHY_MAC_RLC_Config_r16__F1 (SL_PHY_MAC_RLC_Config_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SL_PHY_MAC_RLC_Config_r16__cond. simpl in *. auto.
 - simpl. unfold SL_PHY_MAC_RLC_Config_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SL_PHY_MAC_RLC_Config_r16__Format : T_Format SL_PHY_MAC_RLC_Config_r16__Type SL_PHY_MAC_RLC_Config_r16__cond :=
        proj2_format  SL_PHY_MAC_RLC_Config_r16__cond SL_PHY_MAC_RLC_Config_r16__list__Format
    SL_PHY_MAC_RLC_Config_r16__F1 SL_PHY_MAC_RLC_Config_r16__F2 SL_PHY_MAC_RLC_Config_r16__F1F2_cond  SL_PHY_MAC_RLC_Config_r16__F1F2_cond2 SL_PHY_MAC_RLC_Config_r16__F2F1_cond.
Opaque SL_PHY_MAC_RLC_Config_r16__cond SL_PHY_MAC_RLC_Config_r16__Format.

