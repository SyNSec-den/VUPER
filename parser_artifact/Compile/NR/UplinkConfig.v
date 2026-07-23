Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BWP_UplinkDedicated.

Opaque BWP_UplinkDedicated__cond BWP_UplinkDedicated__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Definition UplinkConfig__uplinkBWP_ToReleaseList__Type := list BWP_Id__Type.

Lemma UplinkConfig__uplinkBWP_ToReleaseList__helper1 : (0 <= 1 <= maxNrofBWPs)%Z. unfold maxNrofBWPs.
 lia. Qed.
Lemma UplinkConfig__uplinkBWP_ToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofBWPs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofBWPs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UplinkConfig__uplinkBWP_ToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UplinkConfig__uplinkBWP_ToReleaseList__cond (z : UplinkConfig__uplinkBWP_ToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofBWPs)%Z /\ (list_and BWP_Id__cond z) .

Require Import NR.BWP_Uplink.

Opaque BWP_Uplink__cond BWP_Uplink__Format.

Definition UplinkConfig__uplinkBWP_ToAddModList__Type := list BWP_Uplink__Type.

Lemma UplinkConfig__uplinkBWP_ToAddModList__helper1 : (0 <= 1 <= maxNrofBWPs)%Z. unfold maxNrofBWPs.
 lia. Qed.
Lemma UplinkConfig__uplinkBWP_ToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofBWPs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofBWPs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UplinkConfig__uplinkBWP_ToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UplinkConfig__uplinkBWP_ToAddModList__cond (z : UplinkConfig__uplinkBWP_ToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofBWPs)%Z /\ (list_and BWP_Uplink__cond z) .

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Require Import NR.SetupRelease.
Require Import NR.PUSCH_ServingCellConfig.
Definition UplinkConfig__pusch_ServingCellConfig__Type := SetupRelease__Type PUSCH_ServingCellConfig__Type.
Definition UplinkConfig__pusch_ServingCellConfig__cond := SetupRelease__cond _ PUSCH_ServingCellConfig__cond.
Definition UplinkConfig__pusch_ServingCellConfig__Format : T_Format UplinkConfig__pusch_ServingCellConfig__Type UplinkConfig__pusch_ServingCellConfig__cond := SetupRelease__Format _ _ PUSCH_ServingCellConfig__Format.
Opaque UplinkConfig__pusch_ServingCellConfig__cond UplinkConfig__pusch_ServingCellConfig__Format.

Require Import NR.SetupRelease.
Require Import NR.SRS_CarrierSwitching.
Definition UplinkConfig__carrierSwitching__Type := SetupRelease__Type SRS_CarrierSwitching__Type.
Definition UplinkConfig__carrierSwitching__cond := SetupRelease__cond _ SRS_CarrierSwitching__cond.
Definition UplinkConfig__carrierSwitching__Format : T_Format UplinkConfig__carrierSwitching__Type UplinkConfig__carrierSwitching__cond := SetupRelease__Format _ _ SRS_CarrierSwitching__Format.
Opaque UplinkConfig__carrierSwitching__cond UplinkConfig__carrierSwitching__Format.

Require Import NR.SCS_SpecificCarrier.

Opaque SCS_SpecificCarrier__cond SCS_SpecificCarrier__Format.

Definition UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__Type := list SCS_SpecificCarrier__Type.

Lemma UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__cond (z : UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SCS_SpecificCarrier__cond z) .

Record UplinkConfig__ext0O__Type : Set :=
  make__UplinkConfig__ext0O__Type {
    UplinkConfig__ext0O__powerBoostPi2BPSK : option bool ;
    UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List : option UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__Type ;
}.
Definition UplinkConfig__ext0O__list := (
 Opt bool (fun _ => True) ::
 Opt UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__Type UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__cond ::
 nil).
Definition UplinkConfig__ext0O__cond z := 
  opt_cond (fun _ => True) (UplinkConfig__ext0O__powerBoostPi2BPSK z) /\
  opt_cond UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__cond (UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List z) /\
  True.

Definition UplinkConfig__ext0__Type := UplinkConfig__ext0O__Type.
Definition UplinkConfig__ext0__cond := UplinkConfig__ext0O__cond.

Inductive UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Type : Set :=
 | UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__enabled
.
Definition UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__cond := (fun (_ : UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Type) => True).
Lemma UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__nat__helper.

Definition UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F1 t :=
  match t with
  | UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__enabled => 0
  end.
Definition UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F2 n :=
  match n with
  | 0 => UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__enabled
  | _ => UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__enabled
  end.
Lemma UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F1F2 : forall x : UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Type, (UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F1 x <= 0) /\ UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F2 (UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F1 x) = x. imp_solve. Qed.
Lemma UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F2F1 : forall (y : nat) (H : y <= 0), UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F1 (UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Type : Set :=
 | UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__enabled
.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__cond := (fun (_ : UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Type) => True).
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__nat__helper.

Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F1 t :=
  match t with
  | UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__enabled => 0
  end.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F2 n :=
  match n with
  | 0 => UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__enabled
  | _ => UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__enabled
  end.
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F1F2 : forall x : UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Type, (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F1 x <= 0) /\ UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F2 (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F1 x) = x. imp_solve. Qed.
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F2F1 : forall (y : nat) (H : y <= 0), UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F1 (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Type : Set :=
 | UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__enabled
.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__cond := (fun (_ : UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Type) => True).
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__nat__helper.

Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F1 t :=
  match t with
  | UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__enabled => 0
  end.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F2 n :=
  match n with
  | 0 => UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__enabled
  | _ => UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__enabled
  end.
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F1F2 : forall x : UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Type, (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F1 x <= 0) /\ UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F2 (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F1 x) = x. imp_solve. Qed.
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F2F1 : forall (y : nat) (H : y <= 0), UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F1 (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Type : Set :=
 | UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__enabled
.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__cond := (fun (_ : UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Type) => True).
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__nat__helper.

Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F1 t :=
  match t with
  | UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__enabled => 0
  end.
Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F2 n :=
  match n with
  | 0 => UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__enabled
  | _ => UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__enabled
  end.
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F1F2 : forall x : UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Type, (UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F1 x <= 0) /\ UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F2 (UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F1 x) = x. imp_solve. Qed.
Lemma UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F2F1 : forall (y : nat) (H : y <= 0), UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F1 (UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.UplinkTxSwitching_r16.
Definition UplinkConfig__ext1O__uplinkTxSwitching_r16__Type := SetupRelease__Type UplinkTxSwitching_r16__Type.
Definition UplinkConfig__ext1O__uplinkTxSwitching_r16__cond := SetupRelease__cond _ UplinkTxSwitching_r16__cond.
Definition UplinkConfig__ext1O__uplinkTxSwitching_r16__Format : T_Format UplinkConfig__ext1O__uplinkTxSwitching_r16__Type UplinkConfig__ext1O__uplinkTxSwitching_r16__cond := SetupRelease__Format _ _ UplinkTxSwitching_r16__Format.
Opaque UplinkConfig__ext1O__uplinkTxSwitching_r16__cond UplinkConfig__ext1O__uplinkTxSwitching_r16__Format.

Inductive UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Type : Set :=
 | UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__true
.
Definition UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__cond := (fun (_ : UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Type) => True).
Lemma UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__nat__helper.

Definition UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F1 t :=
  match t with
  | UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__true => 0
  end.
Definition UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F2 n :=
  match n with
  | 0 => UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__true
  | _ => UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__true
  end.
Lemma UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F1F2 : forall x : UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Type, (UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F1 x <= 0) /\ UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F2 (UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F1 x) = x. imp_solve. Qed.
Lemma UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F2F1 : forall (y : nat) (H : y <= 0), UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F1 (UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F2 y) = y. enum_solve H y. Qed.

Record UplinkConfig__ext1O__Type : Set :=
  make__UplinkConfig__ext1O__Type {
    UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16 : option UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Type ;
    UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16 : option UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Type ;
    UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16 : option UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Type ;
    UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16 : option UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Type ;
    UplinkConfig__ext1O__uplinkTxSwitching_r16 : option UplinkConfig__ext1O__uplinkTxSwitching_r16__Type ;
    UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16 : option UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Type ;
}.
Definition UplinkConfig__ext1O__list := (
 Opt UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Type UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__cond ::
 Opt UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Type UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__cond ::
 Opt UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Type UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__cond ::
 Opt UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Type UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__cond ::
 Opt UplinkConfig__ext1O__uplinkTxSwitching_r16__Type UplinkConfig__ext1O__uplinkTxSwitching_r16__cond ::
 Opt UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Type UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__cond ::
 nil).
Definition UplinkConfig__ext1O__cond z := 
  opt_cond UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__cond (UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16 z) /\
  opt_cond UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__cond (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16 z) /\
  opt_cond UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__cond (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16 z) /\
  opt_cond UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__cond (UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16 z) /\
  opt_cond UplinkConfig__ext1O__uplinkTxSwitching_r16__cond (UplinkConfig__ext1O__uplinkTxSwitching_r16 z) /\
  opt_cond UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__cond (UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16 z) /\
  True.

Definition UplinkConfig__ext1__Type := UplinkConfig__ext1O__Type.
Definition UplinkConfig__ext1__cond := UplinkConfig__ext1O__cond.

Record UplinkConfig__Type : Set :=
  make__UplinkConfig__Type {
    UplinkConfig__initialUplinkBWP : option BWP_UplinkDedicated__Type ;
    UplinkConfig__uplinkBWP_ToReleaseList : option UplinkConfig__uplinkBWP_ToReleaseList__Type ;
    UplinkConfig__uplinkBWP_ToAddModList : option UplinkConfig__uplinkBWP_ToAddModList__Type ;
    UplinkConfig__firstActiveUplinkBWP_Id : option BWP_Id__Type ;
    UplinkConfig__pusch_ServingCellConfig : option UplinkConfig__pusch_ServingCellConfig__Type ;
    UplinkConfig__carrierSwitching : option UplinkConfig__carrierSwitching__Type ;
    UplinkConfig__ext0 : option UplinkConfig__ext0__Type ;
    UplinkConfig__ext1 : option UplinkConfig__ext1__Type ;
}.
Definition UplinkConfig__root_list : list seq_elem := (
 Opt BWP_UplinkDedicated__Type BWP_UplinkDedicated__cond ::
 Opt UplinkConfig__uplinkBWP_ToReleaseList__Type UplinkConfig__uplinkBWP_ToReleaseList__cond ::
 Opt UplinkConfig__uplinkBWP_ToAddModList__Type UplinkConfig__uplinkBWP_ToAddModList__cond ::
 Opt BWP_Id__Type BWP_Id__cond ::
 Opt UplinkConfig__pusch_ServingCellConfig__Type UplinkConfig__pusch_ServingCellConfig__cond ::
 Opt UplinkConfig__carrierSwitching__Type UplinkConfig__carrierSwitching__cond ::
 nil).
Definition UplinkConfig__ext_list : list typ := (
  typ_cons UplinkConfig__ext0__Type UplinkConfig__ext0__cond ::
  typ_cons UplinkConfig__ext1__Type UplinkConfig__ext1__cond ::
  nil).
Definition UplinkConfig__cond (z : UplinkConfig__Type) := 
(  opt_cond BWP_UplinkDedicated__cond (UplinkConfig__initialUplinkBWP z) /\
  opt_cond UplinkConfig__uplinkBWP_ToReleaseList__cond (UplinkConfig__uplinkBWP_ToReleaseList z) /\
  opt_cond UplinkConfig__uplinkBWP_ToAddModList__cond (UplinkConfig__uplinkBWP_ToAddModList z) /\
  opt_cond BWP_Id__cond (UplinkConfig__firstActiveUplinkBWP_Id z) /\
  opt_cond UplinkConfig__pusch_ServingCellConfig__cond (UplinkConfig__pusch_ServingCellConfig z) /\
  opt_cond UplinkConfig__carrierSwitching__cond (UplinkConfig__carrierSwitching z) /\
  True) /\ 
(  opt_cond UplinkConfig__ext0__cond (UplinkConfig__ext0 z) /\
  opt_cond UplinkConfig__ext1__cond (UplinkConfig__ext1 z) /\
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
Definition UplinkConfig__uplinkBWP_ToReleaseList__Format : T_Format UplinkConfig__uplinkBWP_ToReleaseList__Type UplinkConfig__uplinkBWP_ToReleaseList__cond := seq_of_format BWP_Id__Format 1 maxNrofBWPs UplinkConfig__uplinkBWP_ToReleaseList__helper1 UplinkConfig__uplinkBWP_ToReleaseList__helper2.

Opaque UplinkConfig__uplinkBWP_ToReleaseList__cond UplinkConfig__uplinkBWP_ToReleaseList__Format.

Definition UplinkConfig__uplinkBWP_ToAddModList__Format : T_Format UplinkConfig__uplinkBWP_ToAddModList__Type UplinkConfig__uplinkBWP_ToAddModList__cond := seq_of_format BWP_Uplink__Format 1 maxNrofBWPs UplinkConfig__uplinkBWP_ToAddModList__helper1 UplinkConfig__uplinkBWP_ToAddModList__helper2.

Opaque UplinkConfig__uplinkBWP_ToAddModList__cond UplinkConfig__uplinkBWP_ToAddModList__Format.

Opaque UplinkConfig__pusch_ServingCellConfig__cond UplinkConfig__pusch_ServingCellConfig__Format.

Opaque UplinkConfig__carrierSwitching__cond UplinkConfig__carrierSwitching__Format.

Definition UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__Format : T_Format UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__Type UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__cond := seq_of_format SCS_SpecificCarrier__Format 1 maxSCSs UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__helper1 UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__helper2.

Opaque UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__cond UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__Format.


Definition UplinkConfig__ext0O__Format_Type := Eval cbn in seq_format_prod UplinkConfig__ext0O__list.
Definition UplinkConfig__ext0O__Format_list : UplinkConfig__ext0O__Format_Type :=
  (bool__Format, (UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List__Format, unit_format)).
Definition UplinkConfig__ext0O__list__Format := (*Eval compute in *) seq_format UplinkConfig__ext0O__list UplinkConfig__ext0O__Format_list.
Definition UplinkConfig__ext0O__F1 z :=
  (UplinkConfig__ext0O__powerBoostPi2BPSK z, (UplinkConfig__ext0O__uplinkChannelBW_PerSCS_List z, tt)).
Definition UplinkConfig__ext0O__F2 (y : seq_type UplinkConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UplinkConfig__ext0O__Type i0 i1
  end.
Lemma UplinkConfig__ext0O__F1F2_cond (z : UplinkConfig__ext0O__Type)
  : UplinkConfig__ext0O__cond z ->
  (seq_cond UplinkConfig__ext0O__list (UplinkConfig__ext0O__F1 z)).
intro H. unfold UplinkConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma UplinkConfig__ext0O__F1F2_cond2 (z : UplinkConfig__ext0O__Type)
 : UplinkConfig__ext0O__F2 (UplinkConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkConfig__ext0O__F2F1_cond (y : seq_type UplinkConfig__ext0O__list)
  : seq_cond UplinkConfig__ext0O__list y ->
 (UplinkConfig__ext0O__cond (UplinkConfig__ext0O__F2 y)) /\  UplinkConfig__ext0O__F1 (UplinkConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold UplinkConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkConfig__ext0O__Format : T_Format UplinkConfig__ext0O__Type UplinkConfig__ext0O__cond :=
        proj2_format  UplinkConfig__ext0O__cond UplinkConfig__ext0O__list__Format
    UplinkConfig__ext0O__F1 UplinkConfig__ext0O__F2 UplinkConfig__ext0O__F1F2_cond  UplinkConfig__ext0O__F1F2_cond2 UplinkConfig__ext0O__F2F1_cond.
Opaque UplinkConfig__ext0O__cond UplinkConfig__ext0O__Format.

Definition UplinkConfig__ext0__check_all_none (b : UplinkConfig__ext0O__Type) : bool :=
match b with 
  | make__UplinkConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition UplinkConfig__ext0__Format : T_Format UplinkConfig__ext0__Type UplinkConfig__ext0__cond :=
  restrict_add_format UplinkConfig__ext0__check_all_none UplinkConfig__ext0O__Format.

Opaque UplinkConfig__ext0__cond UplinkConfig__ext0__Format.

Definition UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Format : T_Format UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__nat__Format UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F1 UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F2 UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F1F2 UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__F2F1.

Opaque UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__cond UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Format.

Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Format : T_Format UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__nat__Format UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F1 UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F2 UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F1F2 UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__F2F1.

Opaque UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__cond UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Format.

Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Format : T_Format UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__nat__Format UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F1 UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F2 UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F1F2 UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__F2F1.

Opaque UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__cond UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Format.

Definition UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Format : T_Format UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__nat__Format UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F1 UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F2 UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F1F2 UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__F2F1.

Opaque UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__cond UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Format.

Opaque UplinkConfig__ext1O__uplinkTxSwitching_r16__cond UplinkConfig__ext1O__uplinkTxSwitching_r16__Format.

Definition UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Format : T_Format UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__nat__Format UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F1 UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F2 UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F1F2 UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__F2F1.

Opaque UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__cond UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Format.


Definition UplinkConfig__ext1O__Format_Type := Eval cbn in seq_format_prod UplinkConfig__ext1O__list.
Definition UplinkConfig__ext1O__Format_list : UplinkConfig__ext1O__Format_Type :=
  (UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16__Format, (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16__Format, (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16__Format, (UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16__Format, (UplinkConfig__ext1O__uplinkTxSwitching_r16__Format, (UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16__Format, unit_format)))))).
Definition UplinkConfig__ext1O__list__Format := (*Eval compute in *) seq_format UplinkConfig__ext1O__list UplinkConfig__ext1O__Format_list.
Definition UplinkConfig__ext1O__F1 z :=
  (UplinkConfig__ext1O__enablePL_RS_UpdateForPUSCH_SRS_r16 z, (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUSCH0_0_r16 z, (UplinkConfig__ext1O__enableDefaultBeamPL_ForPUCCH_r16 z, (UplinkConfig__ext1O__enableDefaultBeamPL_ForSRS_r16 z, (UplinkConfig__ext1O__uplinkTxSwitching_r16 z, (UplinkConfig__ext1O__mpr_PowerBoost_FR2_r16 z, tt)))))).
Definition UplinkConfig__ext1O__F2 (y : seq_type UplinkConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__UplinkConfig__ext1O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma UplinkConfig__ext1O__F1F2_cond (z : UplinkConfig__ext1O__Type)
  : UplinkConfig__ext1O__cond z ->
  (seq_cond UplinkConfig__ext1O__list (UplinkConfig__ext1O__F1 z)).
intro H. unfold UplinkConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma UplinkConfig__ext1O__F1F2_cond2 (z : UplinkConfig__ext1O__Type)
 : UplinkConfig__ext1O__F2 (UplinkConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UplinkConfig__ext1O__F2F1_cond (y : seq_type UplinkConfig__ext1O__list)
  : seq_cond UplinkConfig__ext1O__list y ->
 (UplinkConfig__ext1O__cond (UplinkConfig__ext1O__F2 y)) /\  UplinkConfig__ext1O__F1 (UplinkConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UplinkConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold UplinkConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UplinkConfig__ext1O__Format : T_Format UplinkConfig__ext1O__Type UplinkConfig__ext1O__cond :=
        proj2_format  UplinkConfig__ext1O__cond UplinkConfig__ext1O__list__Format
    UplinkConfig__ext1O__F1 UplinkConfig__ext1O__F2 UplinkConfig__ext1O__F1F2_cond  UplinkConfig__ext1O__F1F2_cond2 UplinkConfig__ext1O__F2F1_cond.
Opaque UplinkConfig__ext1O__cond UplinkConfig__ext1O__Format.

Definition UplinkConfig__ext1__check_all_none (b : UplinkConfig__ext1O__Type) : bool :=
match b with 
  | make__UplinkConfig__ext1O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition UplinkConfig__ext1__Format : T_Format UplinkConfig__ext1__Type UplinkConfig__ext1__cond :=
  restrict_add_format UplinkConfig__ext1__check_all_none UplinkConfig__ext1O__Format.

Opaque UplinkConfig__ext1__cond UplinkConfig__ext1__Format.


Definition UplinkConfig__root_Format_Type := Eval cbn in seq_format_prod UplinkConfig__root_list.
Definition UplinkConfig__root_Format_list : UplinkConfig__root_Format_Type :=
  (BWP_UplinkDedicated__Format, (UplinkConfig__uplinkBWP_ToReleaseList__Format, (UplinkConfig__uplinkBWP_ToAddModList__Format, (BWP_Id__Format, (UplinkConfig__pusch_ServingCellConfig__Format, (UplinkConfig__carrierSwitching__Format, unit_format)))))).

Definition UplinkConfig__ext_Format_Type := Eval cbn in get_formats UplinkConfig__ext_list.
Definition UplinkConfig__ext_Format_list : UplinkConfig__ext_Format_Type :=
  (UplinkConfig__ext0__Format, (UplinkConfig__ext1__Format, unit__Format)).

Definition UplinkConfig__list_type : Set := (seq_type UplinkConfig__root_list) * (seq_ext_type UplinkConfig__ext_list).
Definition UplinkConfig__list_cond (z : UplinkConfig__list_type) : Prop :=
        (seq_cond UplinkConfig__root_list (fst z)) /\ (seq_ext_cond UplinkConfig__ext_list (snd z)).
Definition UplinkConfig__list_format : T_Format UplinkConfig__list_type UplinkConfig__list_cond :=
 (* Eval compute in *) seq_ext_format UplinkConfig__root_list UplinkConfig__root_Format_list UplinkConfig__ext_list UplinkConfig__ext_Format_list.

Opaque UplinkConfig__list_format.
Definition UplinkConfig__F1 (z : UplinkConfig__Type) : UplinkConfig__list_type :=
  (((UplinkConfig__initialUplinkBWP z, (UplinkConfig__uplinkBWP_ToReleaseList z, (UplinkConfig__uplinkBWP_ToAddModList z, (UplinkConfig__firstActiveUplinkBWP_Id z, (UplinkConfig__pusch_ServingCellConfig z, (UplinkConfig__carrierSwitching z, tt))))))), (
(UplinkConfig__ext0 z, (UplinkConfig__ext1 z, tt)))).
Definition UplinkConfig__F2 (y : UplinkConfig__list_type) : UplinkConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, (i1, _)))=>
    make__UplinkConfig__Type j0 j1 j2 j3 j4 j5 i0 i1
  end.
Definition UplinkConfig__helper1 : (forall a : UplinkConfig__Type, UplinkConfig__cond a -> UplinkConfig__list_cond (UplinkConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition UplinkConfig__helper2 : (forall a : UplinkConfig__Type, UplinkConfig__F2 (UplinkConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition UplinkConfig__helper3 : (forall b : UplinkConfig__list_type, UplinkConfig__list_cond b -> UplinkConfig__cond (UplinkConfig__F2 b) /\ UplinkConfig__F1 (UplinkConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold UplinkConfig__cond, UplinkConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition UplinkConfig__Format : T_Format UplinkConfig__Type UplinkConfig__cond :=
 proj2_format UplinkConfig__cond UplinkConfig__list_format  UplinkConfig__F1 UplinkConfig__F2 UplinkConfig__helper1 UplinkConfig__helper2 UplinkConfig__helper3.

Opaque UplinkConfig__cond UplinkConfig__Format.

