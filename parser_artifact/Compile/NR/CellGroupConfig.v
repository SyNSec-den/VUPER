Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CellGroupId.

Opaque CellGroupId__cond CellGroupId__Format.

Require Import NR.RLC_BearerConfig.

Opaque RLC_BearerConfig__cond RLC_BearerConfig__Format.

Definition CellGroupConfig__rlc_BearerToAddModList__Type := list RLC_BearerConfig__Type.

Lemma CellGroupConfig__rlc_BearerToAddModList__helper1 : (0 <= 1 <= maxLC_ID)%Z. unfold maxLC_ID.
 lia. Qed.
Lemma CellGroupConfig__rlc_BearerToAddModList__helper2 : to_bit_sz (Z.to_nat (maxLC_ID - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxLC_ID - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__rlc_BearerToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__rlc_BearerToAddModList__cond (z : CellGroupConfig__rlc_BearerToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxLC_ID)%Z /\ (list_and RLC_BearerConfig__cond z) .

Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Definition CellGroupConfig__rlc_BearerToReleaseList__Type := list LogicalChannelIdentity__Type.

Lemma CellGroupConfig__rlc_BearerToReleaseList__helper1 : (0 <= 1 <= maxLC_ID)%Z. unfold maxLC_ID.
 lia. Qed.
Lemma CellGroupConfig__rlc_BearerToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxLC_ID - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxLC_ID - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__rlc_BearerToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__rlc_BearerToReleaseList__cond (z : CellGroupConfig__rlc_BearerToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxLC_ID)%Z /\ (list_and LogicalChannelIdentity__cond z) .

Require Import NR.MAC_CellGroupConfig.

Opaque MAC_CellGroupConfig__cond MAC_CellGroupConfig__Format.

Require Import NR.PhysicalCellGroupConfig.

Opaque PhysicalCellGroupConfig__cond PhysicalCellGroupConfig__Format.

Require Import NR.SpCellConfig.

Opaque SpCellConfig__cond SpCellConfig__Format.

Require Import NR.SCellConfig.

Opaque SCellConfig__cond SCellConfig__Format.

Definition CellGroupConfig__sCellToAddModList__Type := list SCellConfig__Type.

Lemma CellGroupConfig__sCellToAddModList__helper1 : (0 <= 1 <= maxNrofSCells)%Z. unfold maxNrofSCells.
 lia. Qed.
Lemma CellGroupConfig__sCellToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofSCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__sCellToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__sCellToAddModList__cond (z : CellGroupConfig__sCellToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSCells)%Z /\ (list_and SCellConfig__cond z) .

Require Import NR.SCellIndex.

Opaque SCellIndex__cond SCellIndex__Format.

Definition CellGroupConfig__sCellToReleaseList__Type := list SCellIndex__Type.

Lemma CellGroupConfig__sCellToReleaseList__helper1 : (0 <= 1 <= maxNrofSCells)%Z. unfold maxNrofSCells.
 lia. Qed.
Lemma CellGroupConfig__sCellToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofSCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__sCellToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__sCellToReleaseList__cond (z : CellGroupConfig__sCellToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSCells)%Z /\ (list_and SCellIndex__cond z) .

Inductive CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Type : Set :=
 | CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__true
.
Definition CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__cond := (fun (_ : CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Type) => True).
Lemma CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__nat__helper.

Definition CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F1 t :=
  match t with
  | CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__true => 0
  end.
Definition CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F2 n :=
  match n with
  | 0 => CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__true
  | _ => CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__true
  end.
Lemma CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F1F2 : forall x : CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Type, (CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F1 x <= 0) /\ CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F2 (CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F1 x) = x. imp_solve. Qed.
Lemma CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F2F1 : forall (y : nat) (H : y <= 0), CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F1 (CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F2 y) = y. enum_solve H y. Qed.

Record CellGroupConfig__ext0O__Type : Set :=
  make__CellGroupConfig__ext0O__Type {
    CellGroupConfig__ext0O__reportUplinkTxDirectCurrent : option CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Type ;
}.
Definition CellGroupConfig__ext0O__list := (
 Opt CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Type CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__cond ::
 nil).
Definition CellGroupConfig__ext0O__cond z := 
  opt_cond CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__cond (CellGroupConfig__ext0O__reportUplinkTxDirectCurrent z) /\
  True.

Definition CellGroupConfig__ext0__Type := CellGroupConfig__ext0O__Type.
Definition CellGroupConfig__ext0__cond := CellGroupConfig__ext0O__cond.

Definition CellGroupConfig__ext1O__bap_Address_r16__Type := bit_string_fixed.
Definition CellGroupConfig__ext1O__bap_Address_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.BH_RLC_ChannelConfig_r16.

Opaque BH_RLC_ChannelConfig_r16__cond BH_RLC_ChannelConfig_r16__Format.

Definition CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__Type := list BH_RLC_ChannelConfig_r16__Type.

Lemma CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__helper1 : (0 <= 1 <= maxBH_RLC_ChannelID_r16)%Z. unfold maxBH_RLC_ChannelID_r16.
 lia. Qed.
Lemma CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__helper2 : to_bit_sz (Z.to_nat (maxBH_RLC_ChannelID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBH_RLC_ChannelID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__cond (z : CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxBH_RLC_ChannelID_r16)%Z /\ (list_and BH_RLC_ChannelConfig_r16__cond z) .

Require Import NR.BH_RLC_ChannelID_r16.

Opaque BH_RLC_ChannelID_r16__cond BH_RLC_ChannelID_r16__Format.

Definition CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__Type := list BH_RLC_ChannelID_r16__Type.

Lemma CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__helper1 : (0 <= 1 <= maxBH_RLC_ChannelID_r16)%Z. unfold maxBH_RLC_ChannelID_r16.
 lia. Qed.
Lemma CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__helper2 : to_bit_sz (Z.to_nat (maxBH_RLC_ChannelID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBH_RLC_ChannelID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__cond (z : CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxBH_RLC_ChannelID_r16)%Z /\ (list_and BH_RLC_ChannelID_r16__cond z) .

Inductive CellGroupConfig__ext1O__f1c_TransferPath_r16__Type : Set :=
 | CellGroupConfig__ext1O__f1c_TransferPath_r16__lte
 | CellGroupConfig__ext1O__f1c_TransferPath_r16__nr
 | CellGroupConfig__ext1O__f1c_TransferPath_r16__both
.
Definition CellGroupConfig__ext1O__f1c_TransferPath_r16__cond := (fun (_ : CellGroupConfig__ext1O__f1c_TransferPath_r16__Type) => True).
Lemma CellGroupConfig__ext1O__f1c_TransferPath_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGroupConfig__ext1O__f1c_TransferPath_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CellGroupConfig__ext1O__f1c_TransferPath_r16__nat__helper.

Definition CellGroupConfig__ext1O__f1c_TransferPath_r16__F1 t :=
  match t with
  | CellGroupConfig__ext1O__f1c_TransferPath_r16__lte => 0
  | CellGroupConfig__ext1O__f1c_TransferPath_r16__nr => 1
  | CellGroupConfig__ext1O__f1c_TransferPath_r16__both => 2
  end.
Definition CellGroupConfig__ext1O__f1c_TransferPath_r16__F2 n :=
  match n with
  | 0 => CellGroupConfig__ext1O__f1c_TransferPath_r16__lte
  | 1 => CellGroupConfig__ext1O__f1c_TransferPath_r16__nr
  | 2 => CellGroupConfig__ext1O__f1c_TransferPath_r16__both
  | _ => CellGroupConfig__ext1O__f1c_TransferPath_r16__lte
  end.
Lemma CellGroupConfig__ext1O__f1c_TransferPath_r16__F1F2 : forall x : CellGroupConfig__ext1O__f1c_TransferPath_r16__Type, (CellGroupConfig__ext1O__f1c_TransferPath_r16__F1 x <= 2) /\ CellGroupConfig__ext1O__f1c_TransferPath_r16__F2 (CellGroupConfig__ext1O__f1c_TransferPath_r16__F1 x) = x. imp_solve. Qed.
Lemma CellGroupConfig__ext1O__f1c_TransferPath_r16__F2F1 : forall (y : nat) (H : y <= 2), CellGroupConfig__ext1O__f1c_TransferPath_r16__F1 (CellGroupConfig__ext1O__f1c_TransferPath_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__Type := list ServCellIndex__Type.

Lemma CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__helper1 : (0 <= 1 <= maxNrofServingCellsTCI_r16)%Z. unfold maxNrofServingCellsTCI_r16.
 lia. Qed.
Lemma CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCellsTCI_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCellsTCI_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__cond (z : CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCellsTCI_r16)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__Type := list ServCellIndex__Type.

Lemma CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__helper1 : (0 <= 1 <= maxNrofServingCellsTCI_r16)%Z. unfold maxNrofServingCellsTCI_r16.
 lia. Qed.
Lemma CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCellsTCI_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCellsTCI_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__cond (z : CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCellsTCI_r16)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__Type := list ServCellIndex__Type.

Lemma CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__helper1 : (0 <= 1 <= maxNrofServingCellsTCI_r16)%Z. unfold maxNrofServingCellsTCI_r16.
 lia. Qed.
Lemma CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCellsTCI_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCellsTCI_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__cond (z : CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCellsTCI_r16)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__Type := list ServCellIndex__Type.

Lemma CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__helper1 : (0 <= 1 <= maxNrofServingCellsTCI_r16)%Z. unfold maxNrofServingCellsTCI_r16.
 lia. Qed.
Lemma CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCellsTCI_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCellsTCI_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__cond (z : CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCellsTCI_r16)%Z /\ (list_and ServCellIndex__cond z) .

Inductive CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Type : Set :=
 | CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__switchedUL
 | CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__dualUL
.
Definition CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__cond := (fun (_ : CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Type) => True).
Lemma CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__nat__helper.

Definition CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F1 t :=
  match t with
  | CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__switchedUL => 0
  | CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__dualUL => 1
  end.
Definition CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F2 n :=
  match n with
  | 0 => CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__switchedUL
  | 1 => CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__dualUL
  | _ => CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__switchedUL
  end.
Lemma CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F1F2 : forall x : CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Type, (CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F1 x <= 1) /\ CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F2 (CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F1 x) = x. imp_solve. Qed.
Lemma CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F2F1 : forall (y : nat) (H : y <= 1), CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F1 (CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Type : Set :=
 | CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__enabled
.
Definition CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__cond := (fun (_ : CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Type) => True).
Lemma CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__nat__helper.

Definition CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F1 t :=
  match t with
  | CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__enabled => 0
  end.
Definition CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F2 n :=
  match n with
  | 0 => CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__enabled
  | _ => CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__enabled
  end.
Lemma CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F1F2 : forall x : CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Type, (CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F1 x <= 0) /\ CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F2 (CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F1 x) = x. imp_solve. Qed.
Lemma CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F2F1 : forall (y : nat) (H : y <= 0), CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F1 (CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F2 y) = y. enum_solve H y. Qed.

Record CellGroupConfig__ext1O__Type : Set :=
  make__CellGroupConfig__ext1O__Type {
    CellGroupConfig__ext1O__bap_Address_r16 : option CellGroupConfig__ext1O__bap_Address_r16__Type ;
    CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16 : option CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__Type ;
    CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16 : option CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__Type ;
    CellGroupConfig__ext1O__f1c_TransferPath_r16 : option CellGroupConfig__ext1O__f1c_TransferPath_r16__Type ;
    CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16 : option CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__Type ;
    CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16 : option CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__Type ;
    CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16 : option CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__Type ;
    CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16 : option CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__Type ;
    CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16 : option CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Type ;
    CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16 : option CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Type ;
}.
Definition CellGroupConfig__ext1O__list := (
 Opt CellGroupConfig__ext1O__bap_Address_r16__Type CellGroupConfig__ext1O__bap_Address_r16__cond ::
 Opt CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__Type CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__cond ::
 Opt CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__Type CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__cond ::
 Opt CellGroupConfig__ext1O__f1c_TransferPath_r16__Type CellGroupConfig__ext1O__f1c_TransferPath_r16__cond ::
 Opt CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__Type CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__cond ::
 Opt CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__Type CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__cond ::
 Opt CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__Type CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__cond ::
 Opt CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__Type CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__cond ::
 Opt CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Type CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__cond ::
 Opt CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Type CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__cond ::
 nil).
Definition CellGroupConfig__ext1O__cond z := 
  opt_cond CellGroupConfig__ext1O__bap_Address_r16__cond (CellGroupConfig__ext1O__bap_Address_r16 z) /\
  opt_cond CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__cond (CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16 z) /\
  opt_cond CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__cond (CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16 z) /\
  opt_cond CellGroupConfig__ext1O__f1c_TransferPath_r16__cond (CellGroupConfig__ext1O__f1c_TransferPath_r16 z) /\
  opt_cond CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__cond (CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16 z) /\
  opt_cond CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__cond (CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16 z) /\
  opt_cond CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__cond (CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16 z) /\
  opt_cond CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__cond (CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16 z) /\
  opt_cond CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__cond (CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16 z) /\
  opt_cond CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__cond (CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16 z) /\
  True.

Definition CellGroupConfig__ext1__Type := CellGroupConfig__ext1O__Type.
Definition CellGroupConfig__ext1__cond := CellGroupConfig__ext1O__cond.

Inductive CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Type : Set :=
 | CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__true
.
Definition CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__cond := (fun (_ : CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Type) => True).
Lemma CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__nat__helper.

Definition CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F1 t :=
  match t with
  | CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__true => 0
  end.
Definition CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F2 n :=
  match n with
  | 0 => CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__true
  | _ => CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__true
  end.
Lemma CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F1F2 : forall x : CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Type, (CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F1 x <= 0) /\ CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F2 (CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F1 x) = x. imp_solve. Qed.
Lemma CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F2F1 : forall (y : nat) (H : y <= 0), CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F1 (CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F2 y) = y. enum_solve H y. Qed.

Record CellGroupConfig__ext2O__Type : Set :=
  make__CellGroupConfig__ext2O__Type {
    CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16 : option CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Type ;
}.
Definition CellGroupConfig__ext2O__list := (
 Opt CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Type CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__cond ::
 nil).
Definition CellGroupConfig__ext2O__cond z := 
  opt_cond CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__cond (CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16 z) /\
  True.

Definition CellGroupConfig__ext2__Type := CellGroupConfig__ext2O__Type.
Definition CellGroupConfig__ext2__cond := CellGroupConfig__ext2O__cond.

Inductive CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Type : Set :=
 | CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__mcg
 | CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__scg
 | CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__both
.
Definition CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__cond := (fun (_ : CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Type) => True).
Lemma CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__nat__helper.

Definition CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F1 t :=
  match t with
  | CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__mcg => 0
  | CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__scg => 1
  | CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__both => 2
  end.
Definition CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F2 n :=
  match n with
  | 0 => CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__mcg
  | 1 => CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__scg
  | 2 => CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__both
  | _ => CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__mcg
  end.
Lemma CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F1F2 : forall x : CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Type, (CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F1 x <= 2) /\ CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F2 (CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F1 x) = x. imp_solve. Qed.
Lemma CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F2F1 : forall (y : nat) (H : y <= 2), CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F1 (CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Type : Set :=
 | CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__enabled
.
Definition CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__cond := (fun (_ : CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Type) => True).
Lemma CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__nat__helper.

Definition CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F1 t :=
  match t with
  | CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__enabled => 0
  end.
Definition CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F2 n :=
  match n with
  | 0 => CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__enabled
  | _ => CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__enabled
  end.
Lemma CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F1F2 : forall x : CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Type, (CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F1 x <= 0) /\ CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F2 (CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F1 x) = x. imp_solve. Qed.
Lemma CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F2F1 : forall (y : nat) (H : y <= 0), CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F1 (CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Type : Set :=
 | CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__oneT
 | CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__twoT
.
Definition CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__cond := (fun (_ : CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Type) => True).
Lemma CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__nat__helper.

Definition CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F1 t :=
  match t with
  | CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__oneT => 0
  | CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__twoT => 1
  end.
Definition CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F2 n :=
  match n with
  | 0 => CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__oneT
  | 1 => CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__twoT
  | _ => CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__oneT
  end.
Lemma CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F1F2 : forall x : CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Type, (CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F1 x <= 1) /\ CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F2 (CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F1 x) = x. imp_solve. Qed.
Lemma CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F2F1 : forall (y : nat) (H : y <= 1), CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F1 (CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.Uu_RelayRLC_ChannelConfig_r17.

Opaque Uu_RelayRLC_ChannelConfig_r17__cond Uu_RelayRLC_ChannelConfig_r17__Format.

Definition CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__Type := list Uu_RelayRLC_ChannelConfig_r17__Type.

Lemma CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__helper1 : (0 <= 1 <= maxUu_RelayRLC_ChannelID_r17)%Z. unfold maxUu_RelayRLC_ChannelID_r17.
 lia. Qed.
Lemma CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxUu_RelayRLC_ChannelID_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUu_RelayRLC_ChannelID_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__cond (z : CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxUu_RelayRLC_ChannelID_r17)%Z /\ (list_and Uu_RelayRLC_ChannelConfig_r17__cond z) .

Require Import NR.Uu_RelayRLC_ChannelID_r17.

Opaque Uu_RelayRLC_ChannelID_r17__cond Uu_RelayRLC_ChannelID_r17__Format.

Definition CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__Type := list Uu_RelayRLC_ChannelID_r17__Type.

Lemma CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__helper1 : (0 <= 1 <= maxUu_RelayRLC_ChannelID_r17)%Z. unfold maxUu_RelayRLC_ChannelID_r17.
 lia. Qed.
Lemma CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxUu_RelayRLC_ChannelID_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxUu_RelayRLC_ChannelID_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__cond (z : CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxUu_RelayRLC_ChannelID_r17)%Z /\ (list_and Uu_RelayRLC_ChannelID_r17__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__Type := list ServCellIndex__Type.

Lemma CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__helper1 : (0 <= 1 <= maxNrofServingCellsTCI_r16)%Z. unfold maxNrofServingCellsTCI_r16.
 lia. Qed.
Lemma CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCellsTCI_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCellsTCI_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__cond (z : CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCellsTCI_r16)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__Type := list ServCellIndex__Type.

Lemma CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__helper1 : (0 <= 1 <= maxNrofServingCellsTCI_r16)%Z. unfold maxNrofServingCellsTCI_r16.
 lia. Qed.
Lemma CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCellsTCI_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCellsTCI_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__cond (z : CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCellsTCI_r16)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__Type := list ServCellIndex__Type.

Lemma CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__helper1 : (0 <= 1 <= maxNrofServingCellsTCI_r16)%Z. unfold maxNrofServingCellsTCI_r16.
 lia. Qed.
Lemma CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCellsTCI_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCellsTCI_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__cond (z : CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCellsTCI_r16)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__Type := list ServCellIndex__Type.

Lemma CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__helper1 : (0 <= 1 <= maxNrofServingCellsTCI_r16)%Z. unfold maxNrofServingCellsTCI_r16.
 lia. Qed.
Lemma CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCellsTCI_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCellsTCI_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__cond (z : CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCellsTCI_r16)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.LogicalChannelIdentityExt_r17.

Opaque LogicalChannelIdentityExt_r17__cond LogicalChannelIdentityExt_r17__Format.

Definition CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__Type := list LogicalChannelIdentityExt_r17__Type.

Lemma CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__helper1 : (0 <= 1 <= maxLC_ID)%Z. unfold maxLC_ID.
 lia. Qed.
Lemma CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__helper2 : to_bit_sz (Z.to_nat (maxLC_ID - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxLC_ID - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__cond (z : CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxLC_ID)%Z /\ (list_and LogicalChannelIdentityExt_r17__cond z) .

Require Import NR.IAB_ResourceConfig_r17.

Opaque IAB_ResourceConfig_r17__cond IAB_ResourceConfig_r17__Format.

Definition CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__Type := list IAB_ResourceConfig_r17__Type.

Lemma CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__helper1 : (0 <= 1 <= maxNrofIABResourceConfig_r17)%Z. unfold maxNrofIABResourceConfig_r17.
 lia. Qed.
Lemma CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofIABResourceConfig_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofIABResourceConfig_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__cond (z : CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofIABResourceConfig_r17)%Z /\ (list_and IAB_ResourceConfig_r17__cond z) .

Require Import NR.IAB_ResourceConfigID_r17.

Opaque IAB_ResourceConfigID_r17__cond IAB_ResourceConfigID_r17__Format.

Definition CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__Type := list IAB_ResourceConfigID_r17__Type.

Lemma CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofIABResourceConfig_r17)%Z. unfold maxNrofIABResourceConfig_r17.
 lia. Qed.
Lemma CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofIABResourceConfig_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofIABResourceConfig_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__cond (z : CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofIABResourceConfig_r17)%Z /\ (list_and IAB_ResourceConfigID_r17__cond z) .

Record CellGroupConfig__ext3O__Type : Set :=
  make__CellGroupConfig__ext3O__Type {
    CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17 : option CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Type ;
    CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17 : option CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Type ;
    CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17 : option CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Type ;
    CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17 : option CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__Type ;
    CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17 : option CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__Type ;
    CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17 : option CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__Type ;
    CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17 : option CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__Type ;
    CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17 : option CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__Type ;
    CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17 : option CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__Type ;
    CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17 : option CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__Type ;
    CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17 : option CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__Type ;
    CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17 : option CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__Type ;
}.
Definition CellGroupConfig__ext3O__list := (
 Opt CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Type CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__cond ::
 Opt CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Type CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__cond ::
 Opt CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Type CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__cond ::
 Opt CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__Type CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__cond ::
 Opt CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__Type CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__cond ::
 Opt CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__Type CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__cond ::
 Opt CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__Type CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__cond ::
 Opt CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__Type CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__cond ::
 Opt CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__Type CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__cond ::
 Opt CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__Type CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__cond ::
 Opt CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__Type CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__cond ::
 Opt CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__Type CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__cond ::
 nil).
Definition CellGroupConfig__ext3O__cond z := 
  opt_cond CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__cond (CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17 z) /\
  opt_cond CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__cond (CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17 z) /\
  opt_cond CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__cond (CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17 z) /\
  opt_cond CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__cond (CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17 z) /\
  opt_cond CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__cond (CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17 z) /\
  opt_cond CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__cond (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17 z) /\
  opt_cond CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__cond (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17 z) /\
  opt_cond CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__cond (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17 z) /\
  opt_cond CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__cond (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17 z) /\
  opt_cond CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__cond (CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17 z) /\
  opt_cond CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__cond (CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17 z) /\
  opt_cond CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__cond (CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17 z) /\
  True.

Definition CellGroupConfig__ext3__Type := CellGroupConfig__ext3O__Type.
Definition CellGroupConfig__ext3__cond := CellGroupConfig__ext3O__cond.

Require Import NR.ReportUplinkTxDirectCurrentMoreCarrier_r17.

Opaque ReportUplinkTxDirectCurrentMoreCarrier_r17__cond ReportUplinkTxDirectCurrentMoreCarrier_r17__Format.

Record CellGroupConfig__ext4O__Type : Set :=
  make__CellGroupConfig__ext4O__Type {
    CellGroupConfig__ext4O__reportUplinkTxDirectCurrentMoreCarrier_r17 : option ReportUplinkTxDirectCurrentMoreCarrier_r17__Type ;
}.
Definition CellGroupConfig__ext4O__list := (
 Opt ReportUplinkTxDirectCurrentMoreCarrier_r17__Type ReportUplinkTxDirectCurrentMoreCarrier_r17__cond ::
 nil).
Definition CellGroupConfig__ext4O__cond z := 
  opt_cond ReportUplinkTxDirectCurrentMoreCarrier_r17__cond (CellGroupConfig__ext4O__reportUplinkTxDirectCurrentMoreCarrier_r17 z) /\
  True.

Definition CellGroupConfig__ext4__Type := CellGroupConfig__ext4O__Type.
Definition CellGroupConfig__ext4__cond := CellGroupConfig__ext4O__cond.

Record CellGroupConfig__Type : Set :=
  make__CellGroupConfig__Type {
    CellGroupConfig__cellGroupId : CellGroupId__Type ;
    CellGroupConfig__rlc_BearerToAddModList : option CellGroupConfig__rlc_BearerToAddModList__Type ;
    CellGroupConfig__rlc_BearerToReleaseList : option CellGroupConfig__rlc_BearerToReleaseList__Type ;
    CellGroupConfig__mac_CellGroupConfig : option MAC_CellGroupConfig__Type ;
    CellGroupConfig__physicalCellGroupConfig : option PhysicalCellGroupConfig__Type ;
    CellGroupConfig__spCellConfig : option SpCellConfig__Type ;
    CellGroupConfig__sCellToAddModList : option CellGroupConfig__sCellToAddModList__Type ;
    CellGroupConfig__sCellToReleaseList : option CellGroupConfig__sCellToReleaseList__Type ;
    CellGroupConfig__ext0 : option CellGroupConfig__ext0__Type ;
    CellGroupConfig__ext1 : option CellGroupConfig__ext1__Type ;
    CellGroupConfig__ext2 : option CellGroupConfig__ext2__Type ;
    CellGroupConfig__ext3 : option CellGroupConfig__ext3__Type ;
    CellGroupConfig__ext4 : option CellGroupConfig__ext4__Type ;
}.
Definition CellGroupConfig__root_list : list seq_elem := (
 Nor CellGroupId__Type CellGroupId__cond ::
 Opt CellGroupConfig__rlc_BearerToAddModList__Type CellGroupConfig__rlc_BearerToAddModList__cond ::
 Opt CellGroupConfig__rlc_BearerToReleaseList__Type CellGroupConfig__rlc_BearerToReleaseList__cond ::
 Opt MAC_CellGroupConfig__Type MAC_CellGroupConfig__cond ::
 Opt PhysicalCellGroupConfig__Type PhysicalCellGroupConfig__cond ::
 Opt SpCellConfig__Type SpCellConfig__cond ::
 Opt CellGroupConfig__sCellToAddModList__Type CellGroupConfig__sCellToAddModList__cond ::
 Opt CellGroupConfig__sCellToReleaseList__Type CellGroupConfig__sCellToReleaseList__cond ::
 nil).
Definition CellGroupConfig__ext_list : list typ := (
  typ_cons CellGroupConfig__ext0__Type CellGroupConfig__ext0__cond ::
  typ_cons CellGroupConfig__ext1__Type CellGroupConfig__ext1__cond ::
  typ_cons CellGroupConfig__ext2__Type CellGroupConfig__ext2__cond ::
  typ_cons CellGroupConfig__ext3__Type CellGroupConfig__ext3__cond ::
  typ_cons CellGroupConfig__ext4__Type CellGroupConfig__ext4__cond ::
  nil).
Definition CellGroupConfig__cond (z : CellGroupConfig__Type) := 
(  CellGroupId__cond (CellGroupConfig__cellGroupId z) /\
  opt_cond CellGroupConfig__rlc_BearerToAddModList__cond (CellGroupConfig__rlc_BearerToAddModList z) /\
  opt_cond CellGroupConfig__rlc_BearerToReleaseList__cond (CellGroupConfig__rlc_BearerToReleaseList z) /\
  opt_cond MAC_CellGroupConfig__cond (CellGroupConfig__mac_CellGroupConfig z) /\
  opt_cond PhysicalCellGroupConfig__cond (CellGroupConfig__physicalCellGroupConfig z) /\
  opt_cond SpCellConfig__cond (CellGroupConfig__spCellConfig z) /\
  opt_cond CellGroupConfig__sCellToAddModList__cond (CellGroupConfig__sCellToAddModList z) /\
  opt_cond CellGroupConfig__sCellToReleaseList__cond (CellGroupConfig__sCellToReleaseList z) /\
  True) /\ 
(  opt_cond CellGroupConfig__ext0__cond (CellGroupConfig__ext0 z) /\
  opt_cond CellGroupConfig__ext1__cond (CellGroupConfig__ext1 z) /\
  opt_cond CellGroupConfig__ext2__cond (CellGroupConfig__ext2 z) /\
  opt_cond CellGroupConfig__ext3__cond (CellGroupConfig__ext3 z) /\
  opt_cond CellGroupConfig__ext4__cond (CellGroupConfig__ext4 z) /\
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
Definition CellGroupConfig__rlc_BearerToAddModList__Format : T_Format CellGroupConfig__rlc_BearerToAddModList__Type CellGroupConfig__rlc_BearerToAddModList__cond := seq_of_format RLC_BearerConfig__Format 1 maxLC_ID CellGroupConfig__rlc_BearerToAddModList__helper1 CellGroupConfig__rlc_BearerToAddModList__helper2.

Opaque CellGroupConfig__rlc_BearerToAddModList__cond CellGroupConfig__rlc_BearerToAddModList__Format.

Definition CellGroupConfig__rlc_BearerToReleaseList__Format : T_Format CellGroupConfig__rlc_BearerToReleaseList__Type CellGroupConfig__rlc_BearerToReleaseList__cond := seq_of_format LogicalChannelIdentity__Format 1 maxLC_ID CellGroupConfig__rlc_BearerToReleaseList__helper1 CellGroupConfig__rlc_BearerToReleaseList__helper2.

Opaque CellGroupConfig__rlc_BearerToReleaseList__cond CellGroupConfig__rlc_BearerToReleaseList__Format.

Definition CellGroupConfig__sCellToAddModList__Format : T_Format CellGroupConfig__sCellToAddModList__Type CellGroupConfig__sCellToAddModList__cond := seq_of_format SCellConfig__Format 1 maxNrofSCells CellGroupConfig__sCellToAddModList__helper1 CellGroupConfig__sCellToAddModList__helper2.

Opaque CellGroupConfig__sCellToAddModList__cond CellGroupConfig__sCellToAddModList__Format.

Definition CellGroupConfig__sCellToReleaseList__Format : T_Format CellGroupConfig__sCellToReleaseList__Type CellGroupConfig__sCellToReleaseList__cond := seq_of_format SCellIndex__Format 1 maxNrofSCells CellGroupConfig__sCellToReleaseList__helper1 CellGroupConfig__sCellToReleaseList__helper2.

Opaque CellGroupConfig__sCellToReleaseList__cond CellGroupConfig__sCellToReleaseList__Format.

Definition CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Format : T_Format CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__nat__Format CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F1 CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F2 CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F1F2 CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__F2F1.

Opaque CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__cond CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Format.


Definition CellGroupConfig__ext0O__Format_Type := Eval cbn in seq_format_prod CellGroupConfig__ext0O__list.
Definition CellGroupConfig__ext0O__Format_list : CellGroupConfig__ext0O__Format_Type :=
  (CellGroupConfig__ext0O__reportUplinkTxDirectCurrent__Format, unit_format).
Definition CellGroupConfig__ext0O__list__Format := (*Eval compute in *) seq_format CellGroupConfig__ext0O__list CellGroupConfig__ext0O__Format_list.
Definition CellGroupConfig__ext0O__F1 z :=
  (CellGroupConfig__ext0O__reportUplinkTxDirectCurrent z, tt).
Definition CellGroupConfig__ext0O__F2 (y : seq_type CellGroupConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CellGroupConfig__ext0O__Type i0
  end.
Lemma CellGroupConfig__ext0O__F1F2_cond (z : CellGroupConfig__ext0O__Type)
  : CellGroupConfig__ext0O__cond z ->
  (seq_cond CellGroupConfig__ext0O__list (CellGroupConfig__ext0O__F1 z)).
intro H. unfold CellGroupConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma CellGroupConfig__ext0O__F1F2_cond2 (z : CellGroupConfig__ext0O__Type)
 : CellGroupConfig__ext0O__F2 (CellGroupConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellGroupConfig__ext0O__F2F1_cond (y : seq_type CellGroupConfig__ext0O__list)
  : seq_cond CellGroupConfig__ext0O__list y ->
 (CellGroupConfig__ext0O__cond (CellGroupConfig__ext0O__F2 y)) /\  CellGroupConfig__ext0O__F1 (CellGroupConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellGroupConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold CellGroupConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellGroupConfig__ext0O__Format : T_Format CellGroupConfig__ext0O__Type CellGroupConfig__ext0O__cond :=
        proj2_format  CellGroupConfig__ext0O__cond CellGroupConfig__ext0O__list__Format
    CellGroupConfig__ext0O__F1 CellGroupConfig__ext0O__F2 CellGroupConfig__ext0O__F1F2_cond  CellGroupConfig__ext0O__F1F2_cond2 CellGroupConfig__ext0O__F2F1_cond.
Opaque CellGroupConfig__ext0O__cond CellGroupConfig__ext0O__Format.

Definition CellGroupConfig__ext0__check_all_none (b : CellGroupConfig__ext0O__Type) : bool :=
match b with 
  | make__CellGroupConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CellGroupConfig__ext0__Format : T_Format CellGroupConfig__ext0__Type CellGroupConfig__ext0__cond :=
  restrict_add_format CellGroupConfig__ext0__check_all_none CellGroupConfig__ext0O__Format.

Opaque CellGroupConfig__ext0__cond CellGroupConfig__ext0__Format.

Definition CellGroupConfig__ext1O__bap_Address_r16__Format : T_Format CellGroupConfig__ext1O__bap_Address_r16__Type CellGroupConfig__ext1O__bap_Address_r16__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque CellGroupConfig__ext1O__bap_Address_r16__cond CellGroupConfig__ext1O__bap_Address_r16__Format.

Definition CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__Format : T_Format CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__Type CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__cond := seq_of_format BH_RLC_ChannelConfig_r16__Format 1 maxBH_RLC_ChannelID_r16 CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__helper1 CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__helper2.

Opaque CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__cond CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__Format.

Definition CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__Format : T_Format CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__Type CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__cond := seq_of_format BH_RLC_ChannelID_r16__Format 1 maxBH_RLC_ChannelID_r16 CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__helper1 CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__helper2.

Opaque CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__cond CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__Format.

Definition CellGroupConfig__ext1O__f1c_TransferPath_r16__Format : T_Format CellGroupConfig__ext1O__f1c_TransferPath_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGroupConfig__ext1O__f1c_TransferPath_r16__nat__Format CellGroupConfig__ext1O__f1c_TransferPath_r16__F1 CellGroupConfig__ext1O__f1c_TransferPath_r16__F2 CellGroupConfig__ext1O__f1c_TransferPath_r16__F1F2 CellGroupConfig__ext1O__f1c_TransferPath_r16__F2F1.

Opaque CellGroupConfig__ext1O__f1c_TransferPath_r16__cond CellGroupConfig__ext1O__f1c_TransferPath_r16__Format.

Definition CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__Format : T_Format CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__Type CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCellsTCI_r16 CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__helper1 CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__helper2.

Opaque CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__cond CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__Format.

Definition CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__Format : T_Format CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__Type CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCellsTCI_r16 CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__helper1 CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__helper2.

Opaque CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__cond CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__Format.

Definition CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__Format : T_Format CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__Type CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCellsTCI_r16 CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__helper1 CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__helper2.

Opaque CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__cond CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__Format.

Definition CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__Format : T_Format CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__Type CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCellsTCI_r16 CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__helper1 CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__helper2.

Opaque CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__cond CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__Format.

Definition CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Format : T_Format CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__nat__Format CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F1 CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F2 CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F1F2 CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__F2F1.

Opaque CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__cond CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Format.

Definition CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Format : T_Format CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__nat__Format CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F1 CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F2 CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F1F2 CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__F2F1.

Opaque CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__cond CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Format.


Definition CellGroupConfig__ext1O__Format_Type := Eval cbn in seq_format_prod CellGroupConfig__ext1O__list.
Definition CellGroupConfig__ext1O__Format_list : CellGroupConfig__ext1O__Format_Type :=
  (CellGroupConfig__ext1O__bap_Address_r16__Format, (CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16__Format, (CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16__Format, (CellGroupConfig__ext1O__f1c_TransferPath_r16__Format, (CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16__Format, (CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16__Format, (CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16__Format, (CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16__Format, (CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16__Format, (CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16__Format, unit_format)))))))))).
Definition CellGroupConfig__ext1O__list__Format := (*Eval compute in *) seq_format CellGroupConfig__ext1O__list CellGroupConfig__ext1O__Format_list.
Definition CellGroupConfig__ext1O__F1 z :=
  (CellGroupConfig__ext1O__bap_Address_r16 z, (CellGroupConfig__ext1O__bh_RLC_ChannelToAddModList_r16 z, (CellGroupConfig__ext1O__bh_RLC_ChannelToReleaseList_r16 z, (CellGroupConfig__ext1O__f1c_TransferPath_r16 z, (CellGroupConfig__ext1O__simultaneousTCI_UpdateList1_r16 z, (CellGroupConfig__ext1O__simultaneousTCI_UpdateList2_r16 z, (CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList1_r16 z, (CellGroupConfig__ext1O__simultaneousSpatial_UpdatedList2_r16 z, (CellGroupConfig__ext1O__uplinkTxSwitchingOption_r16 z, (CellGroupConfig__ext1O__uplinkTxSwitchingPowerBoosting_r16 z, tt)))))))))).
Definition CellGroupConfig__ext1O__F2 (y : seq_type CellGroupConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__CellGroupConfig__ext1O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma CellGroupConfig__ext1O__F1F2_cond (z : CellGroupConfig__ext1O__Type)
  : CellGroupConfig__ext1O__cond z ->
  (seq_cond CellGroupConfig__ext1O__list (CellGroupConfig__ext1O__F1 z)).
intro H. unfold CellGroupConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma CellGroupConfig__ext1O__F1F2_cond2 (z : CellGroupConfig__ext1O__Type)
 : CellGroupConfig__ext1O__F2 (CellGroupConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellGroupConfig__ext1O__F2F1_cond (y : seq_type CellGroupConfig__ext1O__list)
  : seq_cond CellGroupConfig__ext1O__list y ->
 (CellGroupConfig__ext1O__cond (CellGroupConfig__ext1O__F2 y)) /\  CellGroupConfig__ext1O__F1 (CellGroupConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellGroupConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold CellGroupConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellGroupConfig__ext1O__Format : T_Format CellGroupConfig__ext1O__Type CellGroupConfig__ext1O__cond :=
        proj2_format  CellGroupConfig__ext1O__cond CellGroupConfig__ext1O__list__Format
    CellGroupConfig__ext1O__F1 CellGroupConfig__ext1O__F2 CellGroupConfig__ext1O__F1F2_cond  CellGroupConfig__ext1O__F1F2_cond2 CellGroupConfig__ext1O__F2F1_cond.
Opaque CellGroupConfig__ext1O__cond CellGroupConfig__ext1O__Format.

Definition CellGroupConfig__ext1__check_all_none (b : CellGroupConfig__ext1O__Type) : bool :=
match b with 
  | make__CellGroupConfig__ext1O__Type None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition CellGroupConfig__ext1__Format : T_Format CellGroupConfig__ext1__Type CellGroupConfig__ext1__cond :=
  restrict_add_format CellGroupConfig__ext1__check_all_none CellGroupConfig__ext1O__Format.

Opaque CellGroupConfig__ext1__cond CellGroupConfig__ext1__Format.

Definition CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Format : T_Format CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__nat__Format CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F1 CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F2 CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F1F2 CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__F2F1.

Opaque CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__cond CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Format.


Definition CellGroupConfig__ext2O__Format_Type := Eval cbn in seq_format_prod CellGroupConfig__ext2O__list.
Definition CellGroupConfig__ext2O__Format_list : CellGroupConfig__ext2O__Format_Type :=
  (CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16__Format, unit_format).
Definition CellGroupConfig__ext2O__list__Format := (*Eval compute in *) seq_format CellGroupConfig__ext2O__list CellGroupConfig__ext2O__Format_list.
Definition CellGroupConfig__ext2O__F1 z :=
  (CellGroupConfig__ext2O__reportUplinkTxDirectCurrentTwoCarrier_r16 z, tt).
Definition CellGroupConfig__ext2O__F2 (y : seq_type CellGroupConfig__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__CellGroupConfig__ext2O__Type i0
  end.
Lemma CellGroupConfig__ext2O__F1F2_cond (z : CellGroupConfig__ext2O__Type)
  : CellGroupConfig__ext2O__cond z ->
  (seq_cond CellGroupConfig__ext2O__list (CellGroupConfig__ext2O__F1 z)).
intro H. unfold CellGroupConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma CellGroupConfig__ext2O__F1F2_cond2 (z : CellGroupConfig__ext2O__Type)
 : CellGroupConfig__ext2O__F2 (CellGroupConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellGroupConfig__ext2O__F2F1_cond (y : seq_type CellGroupConfig__ext2O__list)
  : seq_cond CellGroupConfig__ext2O__list y ->
 (CellGroupConfig__ext2O__cond (CellGroupConfig__ext2O__F2 y)) /\  CellGroupConfig__ext2O__F1 (CellGroupConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellGroupConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold CellGroupConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellGroupConfig__ext2O__Format : T_Format CellGroupConfig__ext2O__Type CellGroupConfig__ext2O__cond :=
        proj2_format  CellGroupConfig__ext2O__cond CellGroupConfig__ext2O__list__Format
    CellGroupConfig__ext2O__F1 CellGroupConfig__ext2O__F2 CellGroupConfig__ext2O__F1F2_cond  CellGroupConfig__ext2O__F1F2_cond2 CellGroupConfig__ext2O__F2F1_cond.
Opaque CellGroupConfig__ext2O__cond CellGroupConfig__ext2O__Format.

Definition CellGroupConfig__ext2__check_all_none (b : CellGroupConfig__ext2O__Type) : bool :=
match b with 
  | make__CellGroupConfig__ext2O__Type None  => false 
  | _ => true 
 end.
Definition CellGroupConfig__ext2__Format : T_Format CellGroupConfig__ext2__Type CellGroupConfig__ext2__cond :=
  restrict_add_format CellGroupConfig__ext2__check_all_none CellGroupConfig__ext2O__Format.

Opaque CellGroupConfig__ext2__cond CellGroupConfig__ext2__Format.

Definition CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Format : T_Format CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__nat__Format CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F1 CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F2 CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F1F2 CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__F2F1.

Opaque CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__cond CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Format.

Definition CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Format : T_Format CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__nat__Format CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F1 CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F2 CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F1F2 CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__F2F1.

Opaque CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__cond CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Format.

Definition CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Format : T_Format CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__nat__Format CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F1 CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F2 CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F1F2 CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__F2F1.

Opaque CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__cond CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Format.

Definition CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__Format : T_Format CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__Type CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__cond := seq_of_format Uu_RelayRLC_ChannelConfig_r17__Format 1 maxUu_RelayRLC_ChannelID_r17 CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__helper1 CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__helper2.

Opaque CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__cond CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__Format.

Definition CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__Format : T_Format CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__Type CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__cond := seq_of_format Uu_RelayRLC_ChannelID_r17__Format 1 maxUu_RelayRLC_ChannelID_r17 CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__helper1 CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__helper2.

Opaque CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__cond CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__Format.

Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__Format : T_Format CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__Type CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCellsTCI_r16 CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__helper1 CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__helper2.

Opaque CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__cond CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__Format.

Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__Format : T_Format CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__Type CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCellsTCI_r16 CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__helper1 CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__helper2.

Opaque CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__cond CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__Format.

Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__Format : T_Format CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__Type CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCellsTCI_r16 CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__helper1 CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__helper2.

Opaque CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__cond CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__Format.

Definition CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__Format : T_Format CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__Type CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCellsTCI_r16 CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__helper1 CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__helper2.

Opaque CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__cond CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__Format.

Definition CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__Format : T_Format CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__Type CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__cond := seq_of_format LogicalChannelIdentityExt_r17__Format 1 maxLC_ID CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__helper1 CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__helper2.

Opaque CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__cond CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__Format.

Definition CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__Format : T_Format CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__Type CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__cond := seq_of_format IAB_ResourceConfig_r17__Format 1 maxNrofIABResourceConfig_r17 CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__helper1 CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__helper2.

Opaque CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__cond CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__Format.

Definition CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__Format : T_Format CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__Type CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__cond := seq_of_format IAB_ResourceConfigID_r17__Format 1 maxNrofIABResourceConfig_r17 CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__helper1 CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__helper2.

Opaque CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__cond CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__Format.


Definition CellGroupConfig__ext3O__Format_Type := Eval cbn in seq_format_prod CellGroupConfig__ext3O__list.
Definition CellGroupConfig__ext3O__Format_list : CellGroupConfig__ext3O__Format_Type :=
  (CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17__Format, (CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17__Format, (CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17__Format, (CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17__Format, (CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17__Format, (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17__Format, (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17__Format, (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17__Format, (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17__Format, (CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17__Format, (CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17__Format, (CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17__Format, unit_format)))))))))))).
Definition CellGroupConfig__ext3O__list__Format := (*Eval compute in *) seq_format CellGroupConfig__ext3O__list CellGroupConfig__ext3O__Format_list.
Definition CellGroupConfig__ext3O__F1 z :=
  (CellGroupConfig__ext3O__f1c_TransferPathNRDC_r17 z, (CellGroupConfig__ext3O__uplinkTxSwitching_2T_Mode_r17 z, (CellGroupConfig__ext3O__uplinkTxSwitching_DualUL_TxState_r17 z, (CellGroupConfig__ext3O__uu_RelayRLC_ChannelToAddModList_r17 z, (CellGroupConfig__ext3O__uu_RelayRLC_ChannelToReleaseList_r17 z, (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList1_r17 z, (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList2_r17 z, (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList3_r17 z, (CellGroupConfig__ext3O__simultaneousU_TCI_UpdateList4_r17 z, (CellGroupConfig__ext3O__rlc_BearerToReleaseListExt_r17 z, (CellGroupConfig__ext3O__iab_ResourceConfigToAddModList_r17 z, (CellGroupConfig__ext3O__iab_ResourceConfigToReleaseList_r17 z, tt)))))))))))).
Definition CellGroupConfig__ext3O__F2 (y : seq_type CellGroupConfig__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, _))))))))))))=>
    make__CellGroupConfig__ext3O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  end.
Lemma CellGroupConfig__ext3O__F1F2_cond (z : CellGroupConfig__ext3O__Type)
  : CellGroupConfig__ext3O__cond z ->
  (seq_cond CellGroupConfig__ext3O__list (CellGroupConfig__ext3O__F1 z)).
intro H. unfold CellGroupConfig__ext3O__cond in H. simpl. auto. Qed.
Lemma CellGroupConfig__ext3O__F1F2_cond2 (z : CellGroupConfig__ext3O__Type)
 : CellGroupConfig__ext3O__F2 (CellGroupConfig__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellGroupConfig__ext3O__F2F1_cond (y : seq_type CellGroupConfig__ext3O__list)
  : seq_cond CellGroupConfig__ext3O__list y ->
 (CellGroupConfig__ext3O__cond (CellGroupConfig__ext3O__F2 y)) /\  CellGroupConfig__ext3O__F1 (CellGroupConfig__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellGroupConfig__ext3O__cond. simpl in *. auto.
 - simpl. unfold CellGroupConfig__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellGroupConfig__ext3O__Format : T_Format CellGroupConfig__ext3O__Type CellGroupConfig__ext3O__cond :=
        proj2_format  CellGroupConfig__ext3O__cond CellGroupConfig__ext3O__list__Format
    CellGroupConfig__ext3O__F1 CellGroupConfig__ext3O__F2 CellGroupConfig__ext3O__F1F2_cond  CellGroupConfig__ext3O__F1F2_cond2 CellGroupConfig__ext3O__F2F1_cond.
Opaque CellGroupConfig__ext3O__cond CellGroupConfig__ext3O__Format.

Definition CellGroupConfig__ext3__check_all_none (b : CellGroupConfig__ext3O__Type) : bool :=
match b with 
  | make__CellGroupConfig__ext3O__Type None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition CellGroupConfig__ext3__Format : T_Format CellGroupConfig__ext3__Type CellGroupConfig__ext3__cond :=
  restrict_add_format CellGroupConfig__ext3__check_all_none CellGroupConfig__ext3O__Format.

Opaque CellGroupConfig__ext3__cond CellGroupConfig__ext3__Format.


Definition CellGroupConfig__ext4O__Format_Type := Eval cbn in seq_format_prod CellGroupConfig__ext4O__list.
Definition CellGroupConfig__ext4O__Format_list : CellGroupConfig__ext4O__Format_Type :=
  (ReportUplinkTxDirectCurrentMoreCarrier_r17__Format, unit_format).
Definition CellGroupConfig__ext4O__list__Format := (*Eval compute in *) seq_format CellGroupConfig__ext4O__list CellGroupConfig__ext4O__Format_list.
Definition CellGroupConfig__ext4O__F1 z :=
  (CellGroupConfig__ext4O__reportUplinkTxDirectCurrentMoreCarrier_r17 z, tt).
Definition CellGroupConfig__ext4O__F2 (y : seq_type CellGroupConfig__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__CellGroupConfig__ext4O__Type i0
  end.
Lemma CellGroupConfig__ext4O__F1F2_cond (z : CellGroupConfig__ext4O__Type)
  : CellGroupConfig__ext4O__cond z ->
  (seq_cond CellGroupConfig__ext4O__list (CellGroupConfig__ext4O__F1 z)).
intro H. unfold CellGroupConfig__ext4O__cond in H. simpl. auto. Qed.
Lemma CellGroupConfig__ext4O__F1F2_cond2 (z : CellGroupConfig__ext4O__Type)
 : CellGroupConfig__ext4O__F2 (CellGroupConfig__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellGroupConfig__ext4O__F2F1_cond (y : seq_type CellGroupConfig__ext4O__list)
  : seq_cond CellGroupConfig__ext4O__list y ->
 (CellGroupConfig__ext4O__cond (CellGroupConfig__ext4O__F2 y)) /\  CellGroupConfig__ext4O__F1 (CellGroupConfig__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellGroupConfig__ext4O__cond. simpl in *. auto.
 - simpl. unfold CellGroupConfig__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellGroupConfig__ext4O__Format : T_Format CellGroupConfig__ext4O__Type CellGroupConfig__ext4O__cond :=
        proj2_format  CellGroupConfig__ext4O__cond CellGroupConfig__ext4O__list__Format
    CellGroupConfig__ext4O__F1 CellGroupConfig__ext4O__F2 CellGroupConfig__ext4O__F1F2_cond  CellGroupConfig__ext4O__F1F2_cond2 CellGroupConfig__ext4O__F2F1_cond.
Opaque CellGroupConfig__ext4O__cond CellGroupConfig__ext4O__Format.

Definition CellGroupConfig__ext4__check_all_none (b : CellGroupConfig__ext4O__Type) : bool :=
match b with 
  | make__CellGroupConfig__ext4O__Type None  => false 
  | _ => true 
 end.
Definition CellGroupConfig__ext4__Format : T_Format CellGroupConfig__ext4__Type CellGroupConfig__ext4__cond :=
  restrict_add_format CellGroupConfig__ext4__check_all_none CellGroupConfig__ext4O__Format.

Opaque CellGroupConfig__ext4__cond CellGroupConfig__ext4__Format.


Definition CellGroupConfig__root_Format_Type := Eval cbn in seq_format_prod CellGroupConfig__root_list.
Definition CellGroupConfig__root_Format_list : CellGroupConfig__root_Format_Type :=
  (CellGroupId__Format, (CellGroupConfig__rlc_BearerToAddModList__Format, (CellGroupConfig__rlc_BearerToReleaseList__Format, (MAC_CellGroupConfig__Format, (PhysicalCellGroupConfig__Format, (SpCellConfig__Format, (CellGroupConfig__sCellToAddModList__Format, (CellGroupConfig__sCellToReleaseList__Format, unit_format)))))))).

Definition CellGroupConfig__ext_Format_Type := Eval cbn in get_formats CellGroupConfig__ext_list.
Definition CellGroupConfig__ext_Format_list : CellGroupConfig__ext_Format_Type :=
  (CellGroupConfig__ext0__Format, (CellGroupConfig__ext1__Format, (CellGroupConfig__ext2__Format, (CellGroupConfig__ext3__Format, (CellGroupConfig__ext4__Format, unit__Format))))).

Definition CellGroupConfig__list_type : Set := (seq_type CellGroupConfig__root_list) * (seq_ext_type CellGroupConfig__ext_list).
Definition CellGroupConfig__list_cond (z : CellGroupConfig__list_type) : Prop :=
        (seq_cond CellGroupConfig__root_list (fst z)) /\ (seq_ext_cond CellGroupConfig__ext_list (snd z)).
Definition CellGroupConfig__list_format : T_Format CellGroupConfig__list_type CellGroupConfig__list_cond :=
 (* Eval compute in *) seq_ext_format CellGroupConfig__root_list CellGroupConfig__root_Format_list CellGroupConfig__ext_list CellGroupConfig__ext_Format_list.

Opaque CellGroupConfig__list_format.
Definition CellGroupConfig__F1 (z : CellGroupConfig__Type) : CellGroupConfig__list_type :=
  (((CellGroupConfig__cellGroupId z, (CellGroupConfig__rlc_BearerToAddModList z, (CellGroupConfig__rlc_BearerToReleaseList z, (CellGroupConfig__mac_CellGroupConfig z, (CellGroupConfig__physicalCellGroupConfig z, (CellGroupConfig__spCellConfig z, (CellGroupConfig__sCellToAddModList z, (CellGroupConfig__sCellToReleaseList z, tt))))))))), (
(CellGroupConfig__ext0 z, (CellGroupConfig__ext1 z, (CellGroupConfig__ext2 z, (CellGroupConfig__ext3 z, (CellGroupConfig__ext4 z, tt))))))).
Definition CellGroupConfig__F2 (y : CellGroupConfig__list_type) : CellGroupConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, (i1, (i2, (i3, (i4, _))))))=>
    make__CellGroupConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 i0 i1 i2 i3 i4
  end.
Definition CellGroupConfig__helper1 : (forall a : CellGroupConfig__Type, CellGroupConfig__cond a -> CellGroupConfig__list_cond (CellGroupConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CellGroupConfig__helper2 : (forall a : CellGroupConfig__Type, CellGroupConfig__F2 (CellGroupConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CellGroupConfig__helper3 : (forall b : CellGroupConfig__list_type, CellGroupConfig__list_cond b -> CellGroupConfig__cond (CellGroupConfig__F2 b) /\ CellGroupConfig__F1 (CellGroupConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CellGroupConfig__cond, CellGroupConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CellGroupConfig__Format : T_Format CellGroupConfig__Type CellGroupConfig__cond :=
 proj2_format CellGroupConfig__cond CellGroupConfig__list_format  CellGroupConfig__F1 CellGroupConfig__F2 CellGroupConfig__helper1 CellGroupConfig__helper2 CellGroupConfig__helper3.

Opaque CellGroupConfig__cond CellGroupConfig__Format.

