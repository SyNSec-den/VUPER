Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TDD_UL_DL_ConfigDedicated.

Opaque TDD_UL_DL_ConfigDedicated__cond TDD_UL_DL_ConfigDedicated__Format.

Require Import NR.BWP_DownlinkDedicated.

Opaque BWP_DownlinkDedicated__cond BWP_DownlinkDedicated__Format.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Definition ServingCellConfig__downlinkBWP_ToReleaseList__Type := list BWP_Id__Type.

Lemma ServingCellConfig__downlinkBWP_ToReleaseList__helper1 : (0 <= 1 <= maxNrofBWPs)%Z. unfold maxNrofBWPs.
 lia. Qed.
Lemma ServingCellConfig__downlinkBWP_ToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofBWPs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofBWPs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__downlinkBWP_ToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__downlinkBWP_ToReleaseList__cond (z : ServingCellConfig__downlinkBWP_ToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofBWPs)%Z /\ (list_and BWP_Id__cond z) .

Require Import NR.BWP_Downlink.

Opaque BWP_Downlink__cond BWP_Downlink__Format.

Definition ServingCellConfig__downlinkBWP_ToAddModList__Type := list BWP_Downlink__Type.

Lemma ServingCellConfig__downlinkBWP_ToAddModList__helper1 : (0 <= 1 <= maxNrofBWPs)%Z. unfold maxNrofBWPs.
 lia. Qed.
Lemma ServingCellConfig__downlinkBWP_ToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofBWPs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofBWPs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__downlinkBWP_ToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__downlinkBWP_ToAddModList__cond (z : ServingCellConfig__downlinkBWP_ToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofBWPs)%Z /\ (list_and BWP_Downlink__cond z) .

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Inductive ServingCellConfig__bwp_InactivityTimer__Type : Set :=
 | ServingCellConfig__bwp_InactivityTimer__ms2
 | ServingCellConfig__bwp_InactivityTimer__ms3
 | ServingCellConfig__bwp_InactivityTimer__ms4
 | ServingCellConfig__bwp_InactivityTimer__ms5
 | ServingCellConfig__bwp_InactivityTimer__ms6
 | ServingCellConfig__bwp_InactivityTimer__ms8
 | ServingCellConfig__bwp_InactivityTimer__ms10
 | ServingCellConfig__bwp_InactivityTimer__ms20
 | ServingCellConfig__bwp_InactivityTimer__ms30
 | ServingCellConfig__bwp_InactivityTimer__ms40
 | ServingCellConfig__bwp_InactivityTimer__ms50
 | ServingCellConfig__bwp_InactivityTimer__ms60
 | ServingCellConfig__bwp_InactivityTimer__ms80
 | ServingCellConfig__bwp_InactivityTimer__ms100
 | ServingCellConfig__bwp_InactivityTimer__ms200
 | ServingCellConfig__bwp_InactivityTimer__ms300
 | ServingCellConfig__bwp_InactivityTimer__ms500
 | ServingCellConfig__bwp_InactivityTimer__ms750
 | ServingCellConfig__bwp_InactivityTimer__ms1280
 | ServingCellConfig__bwp_InactivityTimer__ms1920
 | ServingCellConfig__bwp_InactivityTimer__ms2560
 | ServingCellConfig__bwp_InactivityTimer__spare10
 | ServingCellConfig__bwp_InactivityTimer__spare9
 | ServingCellConfig__bwp_InactivityTimer__spare8
 | ServingCellConfig__bwp_InactivityTimer__spare7
 | ServingCellConfig__bwp_InactivityTimer__spare6
 | ServingCellConfig__bwp_InactivityTimer__spare5
 | ServingCellConfig__bwp_InactivityTimer__spare4
 | ServingCellConfig__bwp_InactivityTimer__spare3
 | ServingCellConfig__bwp_InactivityTimer__spare2
 | ServingCellConfig__bwp_InactivityTimer__spare1
.
Definition ServingCellConfig__bwp_InactivityTimer__cond := (fun (_ : ServingCellConfig__bwp_InactivityTimer__Type) => True).
Lemma ServingCellConfig__bwp_InactivityTimer__nat__helper : to_bit_sz 30 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__bwp_InactivityTimer__nat__Format : T_Format nat (fun z => (z <= 30)) :=
  nat_enum_format 30 ServingCellConfig__bwp_InactivityTimer__nat__helper.

Definition ServingCellConfig__bwp_InactivityTimer__F1 t :=
  match t with
  | ServingCellConfig__bwp_InactivityTimer__ms2 => 0
  | ServingCellConfig__bwp_InactivityTimer__ms3 => 1
  | ServingCellConfig__bwp_InactivityTimer__ms4 => 2
  | ServingCellConfig__bwp_InactivityTimer__ms5 => 3
  | ServingCellConfig__bwp_InactivityTimer__ms6 => 4
  | ServingCellConfig__bwp_InactivityTimer__ms8 => 5
  | ServingCellConfig__bwp_InactivityTimer__ms10 => 6
  | ServingCellConfig__bwp_InactivityTimer__ms20 => 7
  | ServingCellConfig__bwp_InactivityTimer__ms30 => 8
  | ServingCellConfig__bwp_InactivityTimer__ms40 => 9
  | ServingCellConfig__bwp_InactivityTimer__ms50 => 10
  | ServingCellConfig__bwp_InactivityTimer__ms60 => 11
  | ServingCellConfig__bwp_InactivityTimer__ms80 => 12
  | ServingCellConfig__bwp_InactivityTimer__ms100 => 13
  | ServingCellConfig__bwp_InactivityTimer__ms200 => 14
  | ServingCellConfig__bwp_InactivityTimer__ms300 => 15
  | ServingCellConfig__bwp_InactivityTimer__ms500 => 16
  | ServingCellConfig__bwp_InactivityTimer__ms750 => 17
  | ServingCellConfig__bwp_InactivityTimer__ms1280 => 18
  | ServingCellConfig__bwp_InactivityTimer__ms1920 => 19
  | ServingCellConfig__bwp_InactivityTimer__ms2560 => 20
  | ServingCellConfig__bwp_InactivityTimer__spare10 => 21
  | ServingCellConfig__bwp_InactivityTimer__spare9 => 22
  | ServingCellConfig__bwp_InactivityTimer__spare8 => 23
  | ServingCellConfig__bwp_InactivityTimer__spare7 => 24
  | ServingCellConfig__bwp_InactivityTimer__spare6 => 25
  | ServingCellConfig__bwp_InactivityTimer__spare5 => 26
  | ServingCellConfig__bwp_InactivityTimer__spare4 => 27
  | ServingCellConfig__bwp_InactivityTimer__spare3 => 28
  | ServingCellConfig__bwp_InactivityTimer__spare2 => 29
  | ServingCellConfig__bwp_InactivityTimer__spare1 => 30
  end.
Definition ServingCellConfig__bwp_InactivityTimer__F2 n :=
  match n with
  | 0 => ServingCellConfig__bwp_InactivityTimer__ms2
  | 1 => ServingCellConfig__bwp_InactivityTimer__ms3
  | 2 => ServingCellConfig__bwp_InactivityTimer__ms4
  | 3 => ServingCellConfig__bwp_InactivityTimer__ms5
  | 4 => ServingCellConfig__bwp_InactivityTimer__ms6
  | 5 => ServingCellConfig__bwp_InactivityTimer__ms8
  | 6 => ServingCellConfig__bwp_InactivityTimer__ms10
  | 7 => ServingCellConfig__bwp_InactivityTimer__ms20
  | 8 => ServingCellConfig__bwp_InactivityTimer__ms30
  | 9 => ServingCellConfig__bwp_InactivityTimer__ms40
  | 10 => ServingCellConfig__bwp_InactivityTimer__ms50
  | 11 => ServingCellConfig__bwp_InactivityTimer__ms60
  | 12 => ServingCellConfig__bwp_InactivityTimer__ms80
  | 13 => ServingCellConfig__bwp_InactivityTimer__ms100
  | 14 => ServingCellConfig__bwp_InactivityTimer__ms200
  | 15 => ServingCellConfig__bwp_InactivityTimer__ms300
  | 16 => ServingCellConfig__bwp_InactivityTimer__ms500
  | 17 => ServingCellConfig__bwp_InactivityTimer__ms750
  | 18 => ServingCellConfig__bwp_InactivityTimer__ms1280
  | 19 => ServingCellConfig__bwp_InactivityTimer__ms1920
  | 20 => ServingCellConfig__bwp_InactivityTimer__ms2560
  | 21 => ServingCellConfig__bwp_InactivityTimer__spare10
  | 22 => ServingCellConfig__bwp_InactivityTimer__spare9
  | 23 => ServingCellConfig__bwp_InactivityTimer__spare8
  | 24 => ServingCellConfig__bwp_InactivityTimer__spare7
  | 25 => ServingCellConfig__bwp_InactivityTimer__spare6
  | 26 => ServingCellConfig__bwp_InactivityTimer__spare5
  | 27 => ServingCellConfig__bwp_InactivityTimer__spare4
  | 28 => ServingCellConfig__bwp_InactivityTimer__spare3
  | 29 => ServingCellConfig__bwp_InactivityTimer__spare2
  | 30 => ServingCellConfig__bwp_InactivityTimer__spare1
  | _ => ServingCellConfig__bwp_InactivityTimer__ms2
  end.
Lemma ServingCellConfig__bwp_InactivityTimer__F1F2 : forall x : ServingCellConfig__bwp_InactivityTimer__Type, (ServingCellConfig__bwp_InactivityTimer__F1 x <= 30) /\ ServingCellConfig__bwp_InactivityTimer__F2 (ServingCellConfig__bwp_InactivityTimer__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__bwp_InactivityTimer__F2F1 : forall (y : nat) (H : y <= 30), ServingCellConfig__bwp_InactivityTimer__F1 (ServingCellConfig__bwp_InactivityTimer__F2 y) = y. enum_solve H y. Qed.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Require Import NR.UplinkConfig.

Opaque UplinkConfig__cond UplinkConfig__Format.

Require Import NR.UplinkConfig.

Opaque UplinkConfig__cond UplinkConfig__Format.

Require Import NR.SetupRelease.
Require Import NR.PDCCH_ServingCellConfig.
Definition ServingCellConfig__pdcch_ServingCellConfig__Type := SetupRelease__Type PDCCH_ServingCellConfig__Type.
Definition ServingCellConfig__pdcch_ServingCellConfig__cond := SetupRelease__cond _ PDCCH_ServingCellConfig__cond.
Definition ServingCellConfig__pdcch_ServingCellConfig__Format : T_Format ServingCellConfig__pdcch_ServingCellConfig__Type ServingCellConfig__pdcch_ServingCellConfig__cond := SetupRelease__Format _ _ PDCCH_ServingCellConfig__Format.
Opaque ServingCellConfig__pdcch_ServingCellConfig__cond ServingCellConfig__pdcch_ServingCellConfig__Format.

Require Import NR.SetupRelease.
Require Import NR.PDSCH_ServingCellConfig.
Definition ServingCellConfig__pdsch_ServingCellConfig__Type := SetupRelease__Type PDSCH_ServingCellConfig__Type.
Definition ServingCellConfig__pdsch_ServingCellConfig__cond := SetupRelease__cond _ PDSCH_ServingCellConfig__cond.
Definition ServingCellConfig__pdsch_ServingCellConfig__Format : T_Format ServingCellConfig__pdsch_ServingCellConfig__Type ServingCellConfig__pdsch_ServingCellConfig__cond := SetupRelease__Format _ _ PDSCH_ServingCellConfig__Format.
Opaque ServingCellConfig__pdsch_ServingCellConfig__cond ServingCellConfig__pdsch_ServingCellConfig__Format.

Require Import NR.SetupRelease.
Require Import NR.CSI_MeasConfig.
Definition ServingCellConfig__csi_MeasConfig__Type := SetupRelease__Type CSI_MeasConfig__Type.
Definition ServingCellConfig__csi_MeasConfig__cond := SetupRelease__cond _ CSI_MeasConfig__cond.
Definition ServingCellConfig__csi_MeasConfig__Format : T_Format ServingCellConfig__csi_MeasConfig__Type ServingCellConfig__csi_MeasConfig__cond := SetupRelease__Format _ _ CSI_MeasConfig__Format.
Opaque ServingCellConfig__csi_MeasConfig__cond ServingCellConfig__csi_MeasConfig__Format.

Inductive ServingCellConfig__sCellDeactivationTimer__Type : Set :=
 | ServingCellConfig__sCellDeactivationTimer__ms20
 | ServingCellConfig__sCellDeactivationTimer__ms40
 | ServingCellConfig__sCellDeactivationTimer__ms80
 | ServingCellConfig__sCellDeactivationTimer__ms160
 | ServingCellConfig__sCellDeactivationTimer__ms200
 | ServingCellConfig__sCellDeactivationTimer__ms240
 | ServingCellConfig__sCellDeactivationTimer__ms320
 | ServingCellConfig__sCellDeactivationTimer__ms400
 | ServingCellConfig__sCellDeactivationTimer__ms480
 | ServingCellConfig__sCellDeactivationTimer__ms520
 | ServingCellConfig__sCellDeactivationTimer__ms640
 | ServingCellConfig__sCellDeactivationTimer__ms720
 | ServingCellConfig__sCellDeactivationTimer__ms840
 | ServingCellConfig__sCellDeactivationTimer__ms1280
 | ServingCellConfig__sCellDeactivationTimer__spare2
 | ServingCellConfig__sCellDeactivationTimer__spare1
.
Definition ServingCellConfig__sCellDeactivationTimer__cond := (fun (_ : ServingCellConfig__sCellDeactivationTimer__Type) => True).
Lemma ServingCellConfig__sCellDeactivationTimer__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__sCellDeactivationTimer__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 ServingCellConfig__sCellDeactivationTimer__nat__helper.

Definition ServingCellConfig__sCellDeactivationTimer__F1 t :=
  match t with
  | ServingCellConfig__sCellDeactivationTimer__ms20 => 0
  | ServingCellConfig__sCellDeactivationTimer__ms40 => 1
  | ServingCellConfig__sCellDeactivationTimer__ms80 => 2
  | ServingCellConfig__sCellDeactivationTimer__ms160 => 3
  | ServingCellConfig__sCellDeactivationTimer__ms200 => 4
  | ServingCellConfig__sCellDeactivationTimer__ms240 => 5
  | ServingCellConfig__sCellDeactivationTimer__ms320 => 6
  | ServingCellConfig__sCellDeactivationTimer__ms400 => 7
  | ServingCellConfig__sCellDeactivationTimer__ms480 => 8
  | ServingCellConfig__sCellDeactivationTimer__ms520 => 9
  | ServingCellConfig__sCellDeactivationTimer__ms640 => 10
  | ServingCellConfig__sCellDeactivationTimer__ms720 => 11
  | ServingCellConfig__sCellDeactivationTimer__ms840 => 12
  | ServingCellConfig__sCellDeactivationTimer__ms1280 => 13
  | ServingCellConfig__sCellDeactivationTimer__spare2 => 14
  | ServingCellConfig__sCellDeactivationTimer__spare1 => 15
  end.
Definition ServingCellConfig__sCellDeactivationTimer__F2 n :=
  match n with
  | 0 => ServingCellConfig__sCellDeactivationTimer__ms20
  | 1 => ServingCellConfig__sCellDeactivationTimer__ms40
  | 2 => ServingCellConfig__sCellDeactivationTimer__ms80
  | 3 => ServingCellConfig__sCellDeactivationTimer__ms160
  | 4 => ServingCellConfig__sCellDeactivationTimer__ms200
  | 5 => ServingCellConfig__sCellDeactivationTimer__ms240
  | 6 => ServingCellConfig__sCellDeactivationTimer__ms320
  | 7 => ServingCellConfig__sCellDeactivationTimer__ms400
  | 8 => ServingCellConfig__sCellDeactivationTimer__ms480
  | 9 => ServingCellConfig__sCellDeactivationTimer__ms520
  | 10 => ServingCellConfig__sCellDeactivationTimer__ms640
  | 11 => ServingCellConfig__sCellDeactivationTimer__ms720
  | 12 => ServingCellConfig__sCellDeactivationTimer__ms840
  | 13 => ServingCellConfig__sCellDeactivationTimer__ms1280
  | 14 => ServingCellConfig__sCellDeactivationTimer__spare2
  | 15 => ServingCellConfig__sCellDeactivationTimer__spare1
  | _ => ServingCellConfig__sCellDeactivationTimer__ms20
  end.
Lemma ServingCellConfig__sCellDeactivationTimer__F1F2 : forall x : ServingCellConfig__sCellDeactivationTimer__Type, (ServingCellConfig__sCellDeactivationTimer__F1 x <= 15) /\ ServingCellConfig__sCellDeactivationTimer__F2 (ServingCellConfig__sCellDeactivationTimer__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__sCellDeactivationTimer__F2F1 : forall (y : nat) (H : y <= 15), ServingCellConfig__sCellDeactivationTimer__F1 (ServingCellConfig__sCellDeactivationTimer__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CrossCarrierSchedulingConfig.

Opaque CrossCarrierSchedulingConfig__cond CrossCarrierSchedulingConfig__Format.

Require Import NR.TAG_Id.

Opaque TAG_Id__cond TAG_Id__Format.

Inductive ServingCellConfig__dummy1__Type : Set :=
 | ServingCellConfig__dummy1__enabled
.
Definition ServingCellConfig__dummy1__cond := (fun (_ : ServingCellConfig__dummy1__Type) => True).
Lemma ServingCellConfig__dummy1__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__dummy1__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__dummy1__nat__helper.

Definition ServingCellConfig__dummy1__F1 t :=
  match t with
  | ServingCellConfig__dummy1__enabled => 0
  end.
Definition ServingCellConfig__dummy1__F2 n :=
  match n with
  | 0 => ServingCellConfig__dummy1__enabled
  | _ => ServingCellConfig__dummy1__enabled
  end.
Lemma ServingCellConfig__dummy1__F1F2 : forall x : ServingCellConfig__dummy1__Type, (ServingCellConfig__dummy1__F1 x <= 0) /\ ServingCellConfig__dummy1__F2 (ServingCellConfig__dummy1__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__dummy1__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__dummy1__F1 (ServingCellConfig__dummy1__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__pathlossReferenceLinking__Type : Set :=
 | ServingCellConfig__pathlossReferenceLinking__spCell
 | ServingCellConfig__pathlossReferenceLinking__sCell
.
Definition ServingCellConfig__pathlossReferenceLinking__cond := (fun (_ : ServingCellConfig__pathlossReferenceLinking__Type) => True).
Lemma ServingCellConfig__pathlossReferenceLinking__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__pathlossReferenceLinking__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ServingCellConfig__pathlossReferenceLinking__nat__helper.

Definition ServingCellConfig__pathlossReferenceLinking__F1 t :=
  match t with
  | ServingCellConfig__pathlossReferenceLinking__spCell => 0
  | ServingCellConfig__pathlossReferenceLinking__sCell => 1
  end.
Definition ServingCellConfig__pathlossReferenceLinking__F2 n :=
  match n with
  | 0 => ServingCellConfig__pathlossReferenceLinking__spCell
  | 1 => ServingCellConfig__pathlossReferenceLinking__sCell
  | _ => ServingCellConfig__pathlossReferenceLinking__spCell
  end.
Lemma ServingCellConfig__pathlossReferenceLinking__F1F2 : forall x : ServingCellConfig__pathlossReferenceLinking__Type, (ServingCellConfig__pathlossReferenceLinking__F1 x <= 1) /\ ServingCellConfig__pathlossReferenceLinking__F2 (ServingCellConfig__pathlossReferenceLinking__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__pathlossReferenceLinking__F2F1 : forall (y : nat) (H : y <= 1), ServingCellConfig__pathlossReferenceLinking__F1 (ServingCellConfig__pathlossReferenceLinking__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasObjectId.

Opaque MeasObjectId__cond MeasObjectId__Format.

Require Import NR.SetupRelease.
Require Import NR.RateMatchPatternLTE_CRS.
Definition ServingCellConfig__ext0O__lte_CRS_ToMatchAround__Type := SetupRelease__Type RateMatchPatternLTE_CRS__Type.
Definition ServingCellConfig__ext0O__lte_CRS_ToMatchAround__cond := SetupRelease__cond _ RateMatchPatternLTE_CRS__cond.
Definition ServingCellConfig__ext0O__lte_CRS_ToMatchAround__Format : T_Format ServingCellConfig__ext0O__lte_CRS_ToMatchAround__Type ServingCellConfig__ext0O__lte_CRS_ToMatchAround__cond := SetupRelease__Format _ _ RateMatchPatternLTE_CRS__Format.
Opaque ServingCellConfig__ext0O__lte_CRS_ToMatchAround__cond ServingCellConfig__ext0O__lte_CRS_ToMatchAround__Format.

Require Import NR.RateMatchPattern.

Opaque RateMatchPattern__cond RateMatchPattern__Format.

Definition ServingCellConfig__ext0O__rateMatchPatternToAddModList__Type := list RateMatchPattern__Type.

Lemma ServingCellConfig__ext0O__rateMatchPatternToAddModList__helper1 : (0 <= 1 <= maxNrofRateMatchPatterns)%Z. unfold maxNrofRateMatchPatterns.
 lia. Qed.
Lemma ServingCellConfig__ext0O__rateMatchPatternToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofRateMatchPatterns - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRateMatchPatterns - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext0O__rateMatchPatternToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext0O__rateMatchPatternToAddModList__cond (z : ServingCellConfig__ext0O__rateMatchPatternToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRateMatchPatterns)%Z /\ (list_and RateMatchPattern__cond z) .

Require Import NR.RateMatchPatternId.

Opaque RateMatchPatternId__cond RateMatchPatternId__Format.

Definition ServingCellConfig__ext0O__rateMatchPatternToReleaseList__Type := list RateMatchPatternId__Type.

Lemma ServingCellConfig__ext0O__rateMatchPatternToReleaseList__helper1 : (0 <= 1 <= maxNrofRateMatchPatterns)%Z. unfold maxNrofRateMatchPatterns.
 lia. Qed.
Lemma ServingCellConfig__ext0O__rateMatchPatternToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofRateMatchPatterns - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRateMatchPatterns - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext0O__rateMatchPatternToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext0O__rateMatchPatternToReleaseList__cond (z : ServingCellConfig__ext0O__rateMatchPatternToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRateMatchPatterns)%Z /\ (list_and RateMatchPatternId__cond z) .

Require Import NR.SCS_SpecificCarrier.

Opaque SCS_SpecificCarrier__cond SCS_SpecificCarrier__Format.

Definition ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__Type := list SCS_SpecificCarrier__Type.

Lemma ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__cond (z : ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SCS_SpecificCarrier__cond z) .

Record ServingCellConfig__ext0O__Type : Set :=
  make__ServingCellConfig__ext0O__Type {
    ServingCellConfig__ext0O__lte_CRS_ToMatchAround : option ServingCellConfig__ext0O__lte_CRS_ToMatchAround__Type ;
    ServingCellConfig__ext0O__rateMatchPatternToAddModList : option ServingCellConfig__ext0O__rateMatchPatternToAddModList__Type ;
    ServingCellConfig__ext0O__rateMatchPatternToReleaseList : option ServingCellConfig__ext0O__rateMatchPatternToReleaseList__Type ;
    ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List : option ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__Type ;
}.
Definition ServingCellConfig__ext0O__list := (
 Opt ServingCellConfig__ext0O__lte_CRS_ToMatchAround__Type ServingCellConfig__ext0O__lte_CRS_ToMatchAround__cond ::
 Opt ServingCellConfig__ext0O__rateMatchPatternToAddModList__Type ServingCellConfig__ext0O__rateMatchPatternToAddModList__cond ::
 Opt ServingCellConfig__ext0O__rateMatchPatternToReleaseList__Type ServingCellConfig__ext0O__rateMatchPatternToReleaseList__cond ::
 Opt ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__Type ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__cond ::
 nil).
Definition ServingCellConfig__ext0O__cond z := 
  opt_cond ServingCellConfig__ext0O__lte_CRS_ToMatchAround__cond (ServingCellConfig__ext0O__lte_CRS_ToMatchAround z) /\
  opt_cond ServingCellConfig__ext0O__rateMatchPatternToAddModList__cond (ServingCellConfig__ext0O__rateMatchPatternToAddModList z) /\
  opt_cond ServingCellConfig__ext0O__rateMatchPatternToReleaseList__cond (ServingCellConfig__ext0O__rateMatchPatternToReleaseList z) /\
  opt_cond ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__cond (ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List z) /\
  True.

Definition ServingCellConfig__ext0__Type := ServingCellConfig__ext0O__Type.
Definition ServingCellConfig__ext0__cond := ServingCellConfig__ext0O__cond.

Inductive ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Type : Set :=
 | ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__true
.
Definition ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__cond := (fun (_ : ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Type) => True).
Lemma ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__nat__helper.

Definition ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F1 t :=
  match t with
  | ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__true => 0
  end.
Definition ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__true
  | _ => ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__true
  end.
Lemma ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F1F2 : forall x : ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Type, (ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F1 x <= 0) /\ ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F2 (ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F1 (ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.TDD_UL_DL_ConfigDedicated_IAB_MT_r16.

Opaque TDD_UL_DL_ConfigDedicated_IAB_MT_r16__cond TDD_UL_DL_ConfigDedicated_IAB_MT_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.DormantBWP_Config_r16.
Definition ServingCellConfig__ext1O__dormantBWP_Config_r16__Type := SetupRelease__Type DormantBWP_Config_r16__Type.
Definition ServingCellConfig__ext1O__dormantBWP_Config_r16__cond := SetupRelease__cond _ DormantBWP_Config_r16__cond.
Definition ServingCellConfig__ext1O__dormantBWP_Config_r16__Format : T_Format ServingCellConfig__ext1O__dormantBWP_Config_r16__Type ServingCellConfig__ext1O__dormantBWP_Config_r16__cond := SetupRelease__Format _ _ DormantBWP_Config_r16__Format.
Opaque ServingCellConfig__ext1O__dormantBWP_Config_r16__cond ServingCellConfig__ext1O__dormantBWP_Config_r16__Format.

Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__helper1 : (-2 <= 2)%Z.  lia. Qed.
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__helper2 : to_bit_sz (Z.to_nat (2 - -2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - -2))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__Type := Z.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__cond := (fun z => (-2 <= z <= 2)%Z).
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__helper1 : (-5 <= 5)%Z.  lia. Qed.
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__helper2 : to_bit_sz (Z.to_nat (5 - -5)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - -5))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__Type := Z.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__cond := (fun z => (-5 <= z <= 5)%Z).
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__helper1 : (-10 <= 10)%Z.  lia. Qed.
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__helper2 : to_bit_sz (Z.to_nat (10 - -10)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10 - -10))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__Type := Z.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__cond := (fun z => (-10 <= z <= 10)%Z).
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__helper1 : (-20 <= 20)%Z.  lia. Qed.
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__helper2 : to_bit_sz (Z.to_nat (20 - -20)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (20 - -20))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__Type := Z.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__cond := (fun z => (-20 <= z <= 20)%Z).

Inductive ServingCellConfig__ext1O__ca_SlotOffset_r16__Type : Set :=
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz : Z -> ServingCellConfig__ext1O__ca_SlotOffset_r16__Type
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz : Z -> ServingCellConfig__ext1O__ca_SlotOffset_r16__Type
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz : Z -> ServingCellConfig__ext1O__ca_SlotOffset_r16__Type
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz : Z -> ServingCellConfig__ext1O__ca_SlotOffset_r16__Type
.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__list : list typ := (
typ_cons Z ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__cond ::
typ_cons Z ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__cond ::
typ_cons Z ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__cond ::
typ_cons Z ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__cond ::
 nil).
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__cond (c : ServingCellConfig__ext1O__ca_SlotOffset_r16__Type) := 
  match c with
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz t => ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__cond t 
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz t => ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__cond t 
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz t => ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__cond t 
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz t => ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__cond t 
  end.

Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__len_helper1 : to_bit_sz (length ServingCellConfig__ext1O__ca_SlotOffset_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__len_helper2 : 2 <= length2 ServingCellConfig__ext1O__ca_SlotOffset_r16__list.
 simpl. lia. Qed.
Require Import NR.SetupRelease.
Require Import NR.DummyJ.
Definition ServingCellConfig__ext1O__dummy2__Type := SetupRelease__Type DummyJ__Type.
Definition ServingCellConfig__ext1O__dummy2__cond := SetupRelease__cond _ DummyJ__cond.
Definition ServingCellConfig__ext1O__dummy2__Format : T_Format ServingCellConfig__ext1O__dummy2__Type ServingCellConfig__ext1O__dummy2__cond := SetupRelease__Format _ _ DummyJ__Format.
Opaque ServingCellConfig__ext1O__dummy2__cond ServingCellConfig__ext1O__dummy2__Format.

Require Import NR.IntraCellGuardBandsPerSCS_r16.

Opaque IntraCellGuardBandsPerSCS_r16__cond IntraCellGuardBandsPerSCS_r16__Format.

Definition ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__Type := list IntraCellGuardBandsPerSCS_r16__Type.

Lemma ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__cond (z : ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and IntraCellGuardBandsPerSCS_r16__cond z) .

Require Import NR.IntraCellGuardBandsPerSCS_r16.

Opaque IntraCellGuardBandsPerSCS_r16__cond IntraCellGuardBandsPerSCS_r16__Format.

Definition ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__Type := list IntraCellGuardBandsPerSCS_r16__Type.

Lemma ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__cond (z : ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and IntraCellGuardBandsPerSCS_r16__cond z) .

Inductive ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Type : Set :=
 | ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__enabled
.
Definition ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__cond := (fun (_ : ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Type) => True).
Lemma ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__nat__helper.

Definition ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F1 t :=
  match t with
  | ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__enabled => 0
  end.
Definition ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__enabled
  | _ => ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__enabled
  end.
Lemma ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F1F2 : forall x : ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Type, (ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F1 x <= 0) /\ ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F2 (ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F1 (ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.LTE_CRS_PatternList_r16.
Definition ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__Type := SetupRelease__Type LTE_CRS_PatternList_r16__Type.
Definition ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__cond := SetupRelease__cond _ LTE_CRS_PatternList_r16__cond.
Definition ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__Format : T_Format ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__Type ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__cond := SetupRelease__Format _ _ LTE_CRS_PatternList_r16__Format.
Opaque ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__cond ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.LTE_CRS_PatternList_r16.
Definition ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__Type := SetupRelease__Type LTE_CRS_PatternList_r16__Type.
Definition ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__cond := SetupRelease__cond _ LTE_CRS_PatternList_r16__cond.
Definition ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__Format : T_Format ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__Type ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__cond := SetupRelease__Format _ _ LTE_CRS_PatternList_r16__Format.
Opaque ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__cond ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__Format.

Inductive ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Type : Set :=
 | ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__enabled
.
Definition ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__cond := (fun (_ : ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Type) => True).
Lemma ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__nat__helper.

Definition ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F1 t :=
  match t with
  | ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__enabled => 0
  end.
Definition ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__enabled
  | _ => ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__enabled
  end.
Lemma ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F1F2 : forall x : ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Type, (ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F1 x <= 0) /\ ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F2 (ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F1 (ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Type : Set :=
 | ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__enabled
.
Definition ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__cond := (fun (_ : ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Type) => True).
Lemma ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__nat__helper.

Definition ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F1 t :=
  match t with
  | ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__enabled => 0
  end.
Definition ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__enabled
  | _ => ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__enabled
  end.
Lemma ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F1F2 : forall x : ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Type, (ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F1 x <= 0) /\ ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F2 (ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F1 (ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Type : Set :=
 | ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__enabled
.
Definition ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__cond := (fun (_ : ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Type) => True).
Lemma ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__nat__helper.

Definition ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F1 t :=
  match t with
  | ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__enabled => 0
  end.
Definition ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__enabled
  | _ => ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__enabled
  end.
Lemma ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F1F2 : forall x : ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Type, (ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F1 x <= 0) /\ ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F2 (ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F1 (ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Type : Set :=
 | ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__true
.
Definition ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__cond := (fun (_ : ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Type) => True).
Lemma ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__nat__helper.

Definition ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F1 t :=
  match t with
  | ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__true => 0
  end.
Definition ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__true
  | _ => ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__true
  end.
Lemma ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F1F2 : forall x : ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Type, (ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F1 x <= 0) /\ ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F2 (ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F1 (ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Type : Set :=
 | ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__enabled
.
Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__cond := (fun (_ : ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Type) => True).
Lemma ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__nat__helper.

Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F1 t :=
  match t with
  | ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__enabled => 0
  end.
Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__enabled
  | _ => ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__enabled
  end.
Lemma ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F1F2 : forall x : ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Type, (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F1 x <= 0) /\ ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F2 (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F1 (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Type : Set :=
 | ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__enabled
.
Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__cond := (fun (_ : ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Type) => True).
Lemma ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__nat__helper.

Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F1 t :=
  match t with
  | ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__enabled => 0
  end.
Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__enabled
  | _ => ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__enabled
  end.
Lemma ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F1F2 : forall x : ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Type, (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F1 x <= 0) /\ ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F2 (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F1 (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F2 y) = y. enum_solve H y. Qed.

Record ServingCellConfig__ext1O__Type : Set :=
  make__ServingCellConfig__ext1O__Type {
    ServingCellConfig__ext1O__supplementaryUplinkRelease_r16 : option ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Type ;
    ServingCellConfig__ext1O__tdd_UL_DL_ConfigurationDedicated_IAB_MT_r16 : option TDD_UL_DL_ConfigDedicated_IAB_MT_r16__Type ;
    ServingCellConfig__ext1O__dormantBWP_Config_r16 : option ServingCellConfig__ext1O__dormantBWP_Config_r16__Type ;
    ServingCellConfig__ext1O__ca_SlotOffset_r16 : option ServingCellConfig__ext1O__ca_SlotOffset_r16__Type ;
    ServingCellConfig__ext1O__dummy2 : option ServingCellConfig__ext1O__dummy2__Type ;
    ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16 : option ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__Type ;
    ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16 : option ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__Type ;
    ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16 : option ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Type ;
    ServingCellConfig__ext1O__lte_CRS_PatternList1_r16 : option ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__Type ;
    ServingCellConfig__ext1O__lte_CRS_PatternList2_r16 : option ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__Type ;
    ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16 : option ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Type ;
    ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16 : option ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Type ;
    ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16 : option ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Type ;
    ServingCellConfig__ext1O__enableBeamSwitchTiming_r16 : option ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Type ;
    ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16 : option ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Type ;
    ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16 : option ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Type ;
}.
Definition ServingCellConfig__ext1O__list := (
 Opt ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Type ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__cond ::
 Opt TDD_UL_DL_ConfigDedicated_IAB_MT_r16__Type TDD_UL_DL_ConfigDedicated_IAB_MT_r16__cond ::
 Opt ServingCellConfig__ext1O__dormantBWP_Config_r16__Type ServingCellConfig__ext1O__dormantBWP_Config_r16__cond ::
 Opt ServingCellConfig__ext1O__ca_SlotOffset_r16__Type ServingCellConfig__ext1O__ca_SlotOffset_r16__cond ::
 Opt ServingCellConfig__ext1O__dummy2__Type ServingCellConfig__ext1O__dummy2__cond ::
 Opt ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__Type ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__cond ::
 Opt ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__Type ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__cond ::
 Opt ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Type ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__cond ::
 Opt ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__Type ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__cond ::
 Opt ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__Type ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__cond ::
 Opt ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Type ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__cond ::
 Opt ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Type ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__cond ::
 Opt ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Type ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__cond ::
 Opt ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Type ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__cond ::
 Opt ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Type ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__cond ::
 Opt ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Type ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__cond ::
 nil).
Definition ServingCellConfig__ext1O__cond z := 
  opt_cond ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__cond (ServingCellConfig__ext1O__supplementaryUplinkRelease_r16 z) /\
  opt_cond TDD_UL_DL_ConfigDedicated_IAB_MT_r16__cond (ServingCellConfig__ext1O__tdd_UL_DL_ConfigurationDedicated_IAB_MT_r16 z) /\
  opt_cond ServingCellConfig__ext1O__dormantBWP_Config_r16__cond (ServingCellConfig__ext1O__dormantBWP_Config_r16 z) /\
  opt_cond ServingCellConfig__ext1O__ca_SlotOffset_r16__cond (ServingCellConfig__ext1O__ca_SlotOffset_r16 z) /\
  opt_cond ServingCellConfig__ext1O__dummy2__cond (ServingCellConfig__ext1O__dummy2 z) /\
  opt_cond ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__cond (ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16 z) /\
  opt_cond ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__cond (ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16 z) /\
  opt_cond ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__cond (ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16 z) /\
  opt_cond ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__cond (ServingCellConfig__ext1O__lte_CRS_PatternList1_r16 z) /\
  opt_cond ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__cond (ServingCellConfig__ext1O__lte_CRS_PatternList2_r16 z) /\
  opt_cond ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__cond (ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16 z) /\
  opt_cond ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__cond (ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16 z) /\
  opt_cond ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__cond (ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16 z) /\
  opt_cond ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__cond (ServingCellConfig__ext1O__enableBeamSwitchTiming_r16 z) /\
  opt_cond ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__cond (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16 z) /\
  opt_cond ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__cond (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16 z) /\
  True.

Definition ServingCellConfig__ext1__Type := ServingCellConfig__ext1O__Type.
Definition ServingCellConfig__ext1__cond := ServingCellConfig__ext1O__cond.

Inductive ServingCellConfig__ext2O__directionalCollisionHandling_r16__Type : Set :=
 | ServingCellConfig__ext2O__directionalCollisionHandling_r16__enabled
.
Definition ServingCellConfig__ext2O__directionalCollisionHandling_r16__cond := (fun (_ : ServingCellConfig__ext2O__directionalCollisionHandling_r16__Type) => True).
Lemma ServingCellConfig__ext2O__directionalCollisionHandling_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext2O__directionalCollisionHandling_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext2O__directionalCollisionHandling_r16__nat__helper.

Definition ServingCellConfig__ext2O__directionalCollisionHandling_r16__F1 t :=
  match t with
  | ServingCellConfig__ext2O__directionalCollisionHandling_r16__enabled => 0
  end.
Definition ServingCellConfig__ext2O__directionalCollisionHandling_r16__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext2O__directionalCollisionHandling_r16__enabled
  | _ => ServingCellConfig__ext2O__directionalCollisionHandling_r16__enabled
  end.
Lemma ServingCellConfig__ext2O__directionalCollisionHandling_r16__F1F2 : forall x : ServingCellConfig__ext2O__directionalCollisionHandling_r16__Type, (ServingCellConfig__ext2O__directionalCollisionHandling_r16__F1 x <= 0) /\ ServingCellConfig__ext2O__directionalCollisionHandling_r16__F2 (ServingCellConfig__ext2O__directionalCollisionHandling_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext2O__directionalCollisionHandling_r16__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext2O__directionalCollisionHandling_r16__F1 (ServingCellConfig__ext2O__directionalCollisionHandling_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.ChannelAccessConfig_r16.
Definition ServingCellConfig__ext2O__channelAccessConfig_r16__Type := SetupRelease__Type ChannelAccessConfig_r16__Type.
Definition ServingCellConfig__ext2O__channelAccessConfig_r16__cond := SetupRelease__cond _ ChannelAccessConfig_r16__cond.
Definition ServingCellConfig__ext2O__channelAccessConfig_r16__Format : T_Format ServingCellConfig__ext2O__channelAccessConfig_r16__Type ServingCellConfig__ext2O__channelAccessConfig_r16__cond := SetupRelease__Format _ _ ChannelAccessConfig_r16__Format.
Opaque ServingCellConfig__ext2O__channelAccessConfig_r16__cond ServingCellConfig__ext2O__channelAccessConfig_r16__Format.

Record ServingCellConfig__ext2O__Type : Set :=
  make__ServingCellConfig__ext2O__Type {
    ServingCellConfig__ext2O__directionalCollisionHandling_r16 : option ServingCellConfig__ext2O__directionalCollisionHandling_r16__Type ;
    ServingCellConfig__ext2O__channelAccessConfig_r16 : option ServingCellConfig__ext2O__channelAccessConfig_r16__Type ;
}.
Definition ServingCellConfig__ext2O__list := (
 Opt ServingCellConfig__ext2O__directionalCollisionHandling_r16__Type ServingCellConfig__ext2O__directionalCollisionHandling_r16__cond ::
 Opt ServingCellConfig__ext2O__channelAccessConfig_r16__Type ServingCellConfig__ext2O__channelAccessConfig_r16__cond ::
 nil).
Definition ServingCellConfig__ext2O__cond z := 
  opt_cond ServingCellConfig__ext2O__directionalCollisionHandling_r16__cond (ServingCellConfig__ext2O__directionalCollisionHandling_r16 z) /\
  opt_cond ServingCellConfig__ext2O__channelAccessConfig_r16__cond (ServingCellConfig__ext2O__channelAccessConfig_r16 z) /\
  True.

Definition ServingCellConfig__ext2__Type := ServingCellConfig__ext2O__Type.
Definition ServingCellConfig__ext2__cond := ServingCellConfig__ext2O__cond.

Require Import NR.SetupRelease.
Require Import NR.NR_DL_PRS_PDC_Info_r17.
Definition ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__Type := SetupRelease__Type NR_DL_PRS_PDC_Info_r17__Type.
Definition ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__cond := SetupRelease__cond _ NR_DL_PRS_PDC_Info_r17__cond.
Definition ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__Format : T_Format ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__Type ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__cond := SetupRelease__Format _ _ NR_DL_PRS_PDC_Info_r17__Format.
Opaque ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__cond ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SemiStaticChannelAccessConfigUE_r17.
Definition ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__Type := SetupRelease__Type SemiStaticChannelAccessConfigUE_r17__Type.
Definition ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__cond := SetupRelease__cond _ SemiStaticChannelAccessConfigUE_r17__cond.
Definition ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__Format : T_Format ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__Type ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__cond := SetupRelease__Format _ _ SemiStaticChannelAccessConfigUE_r17__Format.
Opaque ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__cond ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.MIMOParam_r17.
Definition ServingCellConfig__ext3O__mimoParam_r17__Type := SetupRelease__Type MIMOParam_r17__Type.
Definition ServingCellConfig__ext3O__mimoParam_r17__cond := SetupRelease__cond _ MIMOParam_r17__cond.
Definition ServingCellConfig__ext3O__mimoParam_r17__Format : T_Format ServingCellConfig__ext3O__mimoParam_r17__Type ServingCellConfig__ext3O__mimoParam_r17__cond := SetupRelease__Format _ _ MIMOParam_r17__Format.
Opaque ServingCellConfig__ext3O__mimoParam_r17__cond ServingCellConfig__ext3O__mimoParam_r17__Format.

Inductive ServingCellConfig__ext3O__channelAccessMode2_r17__Type : Set :=
 | ServingCellConfig__ext3O__channelAccessMode2_r17__enabled
.
Definition ServingCellConfig__ext3O__channelAccessMode2_r17__cond := (fun (_ : ServingCellConfig__ext3O__channelAccessMode2_r17__Type) => True).
Lemma ServingCellConfig__ext3O__channelAccessMode2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext3O__channelAccessMode2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext3O__channelAccessMode2_r17__nat__helper.

Definition ServingCellConfig__ext3O__channelAccessMode2_r17__F1 t :=
  match t with
  | ServingCellConfig__ext3O__channelAccessMode2_r17__enabled => 0
  end.
Definition ServingCellConfig__ext3O__channelAccessMode2_r17__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext3O__channelAccessMode2_r17__enabled
  | _ => ServingCellConfig__ext3O__channelAccessMode2_r17__enabled
  end.
Lemma ServingCellConfig__ext3O__channelAccessMode2_r17__F1F2 : forall x : ServingCellConfig__ext3O__channelAccessMode2_r17__Type, (ServingCellConfig__ext3O__channelAccessMode2_r17__F1 x <= 0) /\ ServingCellConfig__ext3O__channelAccessMode2_r17__F2 (ServingCellConfig__ext3O__channelAccessMode2_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext3O__channelAccessMode2_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext3O__channelAccessMode2_r17__F1 (ServingCellConfig__ext3O__channelAccessMode2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Type : Set :=
 | ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__enabled
.
Definition ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__cond := (fun (_ : ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Type) => True).
Lemma ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__nat__helper.

Definition ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F1 t :=
  match t with
  | ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__enabled => 0
  end.
Definition ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__enabled
  | _ => ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__enabled
  end.
Lemma ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F1F2 : forall x : ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Type, (ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F1 x <= 0) /\ ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F2 (ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F1 (ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Type : Set :=
 | ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n1
 | ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n2
 | ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n4
.
Definition ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__cond := (fun (_ : ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Type) => True).
Lemma ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__nat__helper.

Definition ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F1 t :=
  match t with
  | ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n1 => 0
  | ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n2 => 1
  | ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n4 => 2
  end.
Definition ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n1
  | 1 => ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n2
  | 2 => ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n4
  | _ => ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__n1
  end.
Lemma ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F1F2 : forall x : ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Type, (ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F1 x <= 2) /\ ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F2 (ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F2F1 : forall (y : nat) (H : y <= 2), ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F1 (ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Type : Set :=
 | ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__true
.
Definition ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__cond := (fun (_ : ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Type) => True).
Lemma ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__nat__helper.

Definition ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F1 t :=
  match t with
  | ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__true => 0
  end.
Definition ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__true
  | _ => ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__true
  end.
Lemma ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F1F2 : forall x : ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Type, (ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F1 x <= 0) /\ ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F2 (ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F1 (ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Type : Set :=
 | ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__mode2
.
Definition ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__cond := (fun (_ : ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Type) => True).
Lemma ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__nat__helper.

Definition ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F1 t :=
  match t with
  | ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__mode2 => 0
  end.
Definition ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__mode2
  | _ => ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__mode2
  end.
Lemma ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F1F2 : forall x : ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Type, (ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F1 x <= 0) /\ ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F2 (ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F1 (ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.TCI_ActivatedConfig_r17.

Opaque TCI_ActivatedConfig_r17__cond TCI_ActivatedConfig_r17__Format.

Inductive ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Type : Set :=
 | ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__enabled
.
Definition ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__cond := (fun (_ : ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Type) => True).
Lemma ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__nat__helper.

Definition ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F1 t :=
  match t with
  | ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__enabled => 0
  end.
Definition ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__enabled
  | _ => ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__enabled
  end.
Lemma ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F1F2 : forall x : ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Type, (ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F1 x <= 0) /\ ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F2 (ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F1 (ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.LTE_NeighCellsCRS_AssistInfoList_r17.
Definition ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__Type := SetupRelease__Type LTE_NeighCellsCRS_AssistInfoList_r17__Type.
Definition ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__cond := SetupRelease__cond _ LTE_NeighCellsCRS_AssistInfoList_r17__cond.
Definition ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__Format : T_Format ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__Type ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__cond := SetupRelease__Format _ _ LTE_NeighCellsCRS_AssistInfoList_r17__Format.
Opaque ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__cond ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__Format.

Record ServingCellConfig__ext3O__Type : Set :=
  make__ServingCellConfig__ext3O__Type {
    ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17 : option ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__Type ;
    ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17 : option ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__Type ;
    ServingCellConfig__ext3O__mimoParam_r17 : option ServingCellConfig__ext3O__mimoParam_r17__Type ;
    ServingCellConfig__ext3O__channelAccessMode2_r17 : option ServingCellConfig__ext3O__channelAccessMode2_r17__Type ;
    ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17 : option ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Type ;
    ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17 : option ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Type ;
    ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17 : option ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Type ;
    ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17 : option ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Type ;
    ServingCellConfig__ext3O__tci_ActivatedConfig_r17 : option TCI_ActivatedConfig_r17__Type ;
    ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17 : option ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Type ;
    ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17 : option ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__Type ;
}.
Definition ServingCellConfig__ext3O__list := (
 Opt ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__Type ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__cond ::
 Opt ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__Type ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__cond ::
 Opt ServingCellConfig__ext3O__mimoParam_r17__Type ServingCellConfig__ext3O__mimoParam_r17__cond ::
 Opt ServingCellConfig__ext3O__channelAccessMode2_r17__Type ServingCellConfig__ext3O__channelAccessMode2_r17__cond ::
 Opt ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Type ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__cond ::
 Opt ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Type ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__cond ::
 Opt ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Type ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__cond ::
 Opt ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Type ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__cond ::
 Opt TCI_ActivatedConfig_r17__Type TCI_ActivatedConfig_r17__cond ::
 Opt ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Type ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__cond ::
 Opt ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__Type ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__cond ::
 nil).
Definition ServingCellConfig__ext3O__cond z := 
  opt_cond ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__cond (ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17 z) /\
  opt_cond ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__cond (ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17 z) /\
  opt_cond ServingCellConfig__ext3O__mimoParam_r17__cond (ServingCellConfig__ext3O__mimoParam_r17 z) /\
  opt_cond ServingCellConfig__ext3O__channelAccessMode2_r17__cond (ServingCellConfig__ext3O__channelAccessMode2_r17 z) /\
  opt_cond ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__cond (ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17 z) /\
  opt_cond ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__cond (ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17 z) /\
  opt_cond ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__cond (ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17 z) /\
  opt_cond ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__cond (ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17 z) /\
  opt_cond TCI_ActivatedConfig_r17__cond (ServingCellConfig__ext3O__tci_ActivatedConfig_r17 z) /\
  opt_cond ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__cond (ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17 z) /\
  opt_cond ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__cond (ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17 z) /\
  True.

Definition ServingCellConfig__ext3__Type := ServingCellConfig__ext3O__Type.
Definition ServingCellConfig__ext3__cond := ServingCellConfig__ext3O__cond.

Inductive ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Type : Set :=
 | ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__false
.
Definition ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__cond := (fun (_ : ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Type) => True).
Lemma ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__nat__helper.

Definition ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F1 t :=
  match t with
  | ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__false => 0
  end.
Definition ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F2 n :=
  match n with
  | 0 => ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__false
  | _ => ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__false
  end.
Lemma ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F1F2 : forall x : ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Type, (ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F1 x <= 0) /\ ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F2 (ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F1 (ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F2 y) = y. enum_solve H y. Qed.

Record ServingCellConfig__ext4O__Type : Set :=
  make__ServingCellConfig__ext4O__Type {
    ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17 : option ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Type ;
}.
Definition ServingCellConfig__ext4O__list := (
 Opt ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Type ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__cond ::
 nil).
Definition ServingCellConfig__ext4O__cond z := 
  opt_cond ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__cond (ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17 z) /\
  True.

Definition ServingCellConfig__ext4__Type := ServingCellConfig__ext4O__Type.
Definition ServingCellConfig__ext4__cond := ServingCellConfig__ext4O__cond.

Record ServingCellConfig__Type : Set :=
  make__ServingCellConfig__Type {
    ServingCellConfig__tdd_UL_DL_ConfigurationDedicated : option TDD_UL_DL_ConfigDedicated__Type ;
    ServingCellConfig__initialDownlinkBWP : option BWP_DownlinkDedicated__Type ;
    ServingCellConfig__downlinkBWP_ToReleaseList : option ServingCellConfig__downlinkBWP_ToReleaseList__Type ;
    ServingCellConfig__downlinkBWP_ToAddModList : option ServingCellConfig__downlinkBWP_ToAddModList__Type ;
    ServingCellConfig__firstActiveDownlinkBWP_Id : option BWP_Id__Type ;
    ServingCellConfig__bwp_InactivityTimer : option ServingCellConfig__bwp_InactivityTimer__Type ;
    ServingCellConfig__defaultDownlinkBWP_Id : option BWP_Id__Type ;
    ServingCellConfig__uplinkConfig : option UplinkConfig__Type ;
    ServingCellConfig__supplementaryUplink : option UplinkConfig__Type ;
    ServingCellConfig__pdcch_ServingCellConfig : option ServingCellConfig__pdcch_ServingCellConfig__Type ;
    ServingCellConfig__pdsch_ServingCellConfig : option ServingCellConfig__pdsch_ServingCellConfig__Type ;
    ServingCellConfig__csi_MeasConfig : option ServingCellConfig__csi_MeasConfig__Type ;
    ServingCellConfig__sCellDeactivationTimer : option ServingCellConfig__sCellDeactivationTimer__Type ;
    ServingCellConfig__crossCarrierSchedulingConfig : option CrossCarrierSchedulingConfig__Type ;
    ServingCellConfig__tag_Id : TAG_Id__Type ;
    ServingCellConfig__dummy1 : option ServingCellConfig__dummy1__Type ;
    ServingCellConfig__pathlossReferenceLinking : option ServingCellConfig__pathlossReferenceLinking__Type ;
    ServingCellConfig__servingCellMO : option MeasObjectId__Type ;
    ServingCellConfig__ext0 : option ServingCellConfig__ext0__Type ;
    ServingCellConfig__ext1 : option ServingCellConfig__ext1__Type ;
    ServingCellConfig__ext2 : option ServingCellConfig__ext2__Type ;
    ServingCellConfig__ext3 : option ServingCellConfig__ext3__Type ;
    ServingCellConfig__ext4 : option ServingCellConfig__ext4__Type ;
}.
Definition ServingCellConfig__root_list : list seq_elem := (
 Opt TDD_UL_DL_ConfigDedicated__Type TDD_UL_DL_ConfigDedicated__cond ::
 Opt BWP_DownlinkDedicated__Type BWP_DownlinkDedicated__cond ::
 Opt ServingCellConfig__downlinkBWP_ToReleaseList__Type ServingCellConfig__downlinkBWP_ToReleaseList__cond ::
 Opt ServingCellConfig__downlinkBWP_ToAddModList__Type ServingCellConfig__downlinkBWP_ToAddModList__cond ::
 Opt BWP_Id__Type BWP_Id__cond ::
 Opt ServingCellConfig__bwp_InactivityTimer__Type ServingCellConfig__bwp_InactivityTimer__cond ::
 Opt BWP_Id__Type BWP_Id__cond ::
 Opt UplinkConfig__Type UplinkConfig__cond ::
 Opt UplinkConfig__Type UplinkConfig__cond ::
 Opt ServingCellConfig__pdcch_ServingCellConfig__Type ServingCellConfig__pdcch_ServingCellConfig__cond ::
 Opt ServingCellConfig__pdsch_ServingCellConfig__Type ServingCellConfig__pdsch_ServingCellConfig__cond ::
 Opt ServingCellConfig__csi_MeasConfig__Type ServingCellConfig__csi_MeasConfig__cond ::
 Opt ServingCellConfig__sCellDeactivationTimer__Type ServingCellConfig__sCellDeactivationTimer__cond ::
 Opt CrossCarrierSchedulingConfig__Type CrossCarrierSchedulingConfig__cond ::
 Nor TAG_Id__Type TAG_Id__cond ::
 Opt ServingCellConfig__dummy1__Type ServingCellConfig__dummy1__cond ::
 Opt ServingCellConfig__pathlossReferenceLinking__Type ServingCellConfig__pathlossReferenceLinking__cond ::
 Opt MeasObjectId__Type MeasObjectId__cond ::
 nil).
Definition ServingCellConfig__ext_list : list typ := (
  typ_cons ServingCellConfig__ext0__Type ServingCellConfig__ext0__cond ::
  typ_cons ServingCellConfig__ext1__Type ServingCellConfig__ext1__cond ::
  typ_cons ServingCellConfig__ext2__Type ServingCellConfig__ext2__cond ::
  typ_cons ServingCellConfig__ext3__Type ServingCellConfig__ext3__cond ::
  typ_cons ServingCellConfig__ext4__Type ServingCellConfig__ext4__cond ::
  nil).
Definition ServingCellConfig__cond (z : ServingCellConfig__Type) := 
(  opt_cond TDD_UL_DL_ConfigDedicated__cond (ServingCellConfig__tdd_UL_DL_ConfigurationDedicated z) /\
  opt_cond BWP_DownlinkDedicated__cond (ServingCellConfig__initialDownlinkBWP z) /\
  opt_cond ServingCellConfig__downlinkBWP_ToReleaseList__cond (ServingCellConfig__downlinkBWP_ToReleaseList z) /\
  opt_cond ServingCellConfig__downlinkBWP_ToAddModList__cond (ServingCellConfig__downlinkBWP_ToAddModList z) /\
  opt_cond BWP_Id__cond (ServingCellConfig__firstActiveDownlinkBWP_Id z) /\
  opt_cond ServingCellConfig__bwp_InactivityTimer__cond (ServingCellConfig__bwp_InactivityTimer z) /\
  opt_cond BWP_Id__cond (ServingCellConfig__defaultDownlinkBWP_Id z) /\
  opt_cond UplinkConfig__cond (ServingCellConfig__uplinkConfig z) /\
  opt_cond UplinkConfig__cond (ServingCellConfig__supplementaryUplink z) /\
  opt_cond ServingCellConfig__pdcch_ServingCellConfig__cond (ServingCellConfig__pdcch_ServingCellConfig z) /\
  opt_cond ServingCellConfig__pdsch_ServingCellConfig__cond (ServingCellConfig__pdsch_ServingCellConfig z) /\
  opt_cond ServingCellConfig__csi_MeasConfig__cond (ServingCellConfig__csi_MeasConfig z) /\
  opt_cond ServingCellConfig__sCellDeactivationTimer__cond (ServingCellConfig__sCellDeactivationTimer z) /\
  opt_cond CrossCarrierSchedulingConfig__cond (ServingCellConfig__crossCarrierSchedulingConfig z) /\
  TAG_Id__cond (ServingCellConfig__tag_Id z) /\
  opt_cond ServingCellConfig__dummy1__cond (ServingCellConfig__dummy1 z) /\
  opt_cond ServingCellConfig__pathlossReferenceLinking__cond (ServingCellConfig__pathlossReferenceLinking z) /\
  opt_cond MeasObjectId__cond (ServingCellConfig__servingCellMO z) /\
  True) /\ 
(  opt_cond ServingCellConfig__ext0__cond (ServingCellConfig__ext0 z) /\
  opt_cond ServingCellConfig__ext1__cond (ServingCellConfig__ext1 z) /\
  opt_cond ServingCellConfig__ext2__cond (ServingCellConfig__ext2 z) /\
  opt_cond ServingCellConfig__ext3__cond (ServingCellConfig__ext3 z) /\
  opt_cond ServingCellConfig__ext4__cond (ServingCellConfig__ext4 z) /\
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
Definition ServingCellConfig__downlinkBWP_ToReleaseList__Format : T_Format ServingCellConfig__downlinkBWP_ToReleaseList__Type ServingCellConfig__downlinkBWP_ToReleaseList__cond := seq_of_format BWP_Id__Format 1 maxNrofBWPs ServingCellConfig__downlinkBWP_ToReleaseList__helper1 ServingCellConfig__downlinkBWP_ToReleaseList__helper2.

Opaque ServingCellConfig__downlinkBWP_ToReleaseList__cond ServingCellConfig__downlinkBWP_ToReleaseList__Format.

Definition ServingCellConfig__downlinkBWP_ToAddModList__Format : T_Format ServingCellConfig__downlinkBWP_ToAddModList__Type ServingCellConfig__downlinkBWP_ToAddModList__cond := seq_of_format BWP_Downlink__Format 1 maxNrofBWPs ServingCellConfig__downlinkBWP_ToAddModList__helper1 ServingCellConfig__downlinkBWP_ToAddModList__helper2.

Opaque ServingCellConfig__downlinkBWP_ToAddModList__cond ServingCellConfig__downlinkBWP_ToAddModList__Format.

Definition ServingCellConfig__bwp_InactivityTimer__Format : T_Format ServingCellConfig__bwp_InactivityTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__bwp_InactivityTimer__nat__Format ServingCellConfig__bwp_InactivityTimer__F1 ServingCellConfig__bwp_InactivityTimer__F2 ServingCellConfig__bwp_InactivityTimer__F1F2 ServingCellConfig__bwp_InactivityTimer__F2F1.

Opaque ServingCellConfig__bwp_InactivityTimer__cond ServingCellConfig__bwp_InactivityTimer__Format.

Opaque ServingCellConfig__pdcch_ServingCellConfig__cond ServingCellConfig__pdcch_ServingCellConfig__Format.

Opaque ServingCellConfig__pdsch_ServingCellConfig__cond ServingCellConfig__pdsch_ServingCellConfig__Format.

Opaque ServingCellConfig__csi_MeasConfig__cond ServingCellConfig__csi_MeasConfig__Format.

Definition ServingCellConfig__sCellDeactivationTimer__Format : T_Format ServingCellConfig__sCellDeactivationTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__sCellDeactivationTimer__nat__Format ServingCellConfig__sCellDeactivationTimer__F1 ServingCellConfig__sCellDeactivationTimer__F2 ServingCellConfig__sCellDeactivationTimer__F1F2 ServingCellConfig__sCellDeactivationTimer__F2F1.

Opaque ServingCellConfig__sCellDeactivationTimer__cond ServingCellConfig__sCellDeactivationTimer__Format.

Definition ServingCellConfig__dummy1__Format : T_Format ServingCellConfig__dummy1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__dummy1__nat__Format ServingCellConfig__dummy1__F1 ServingCellConfig__dummy1__F2 ServingCellConfig__dummy1__F1F2 ServingCellConfig__dummy1__F2F1.

Opaque ServingCellConfig__dummy1__cond ServingCellConfig__dummy1__Format.

Definition ServingCellConfig__pathlossReferenceLinking__Format : T_Format ServingCellConfig__pathlossReferenceLinking__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__pathlossReferenceLinking__nat__Format ServingCellConfig__pathlossReferenceLinking__F1 ServingCellConfig__pathlossReferenceLinking__F2 ServingCellConfig__pathlossReferenceLinking__F1F2 ServingCellConfig__pathlossReferenceLinking__F2F1.

Opaque ServingCellConfig__pathlossReferenceLinking__cond ServingCellConfig__pathlossReferenceLinking__Format.

Opaque ServingCellConfig__ext0O__lte_CRS_ToMatchAround__cond ServingCellConfig__ext0O__lte_CRS_ToMatchAround__Format.

Definition ServingCellConfig__ext0O__rateMatchPatternToAddModList__Format : T_Format ServingCellConfig__ext0O__rateMatchPatternToAddModList__Type ServingCellConfig__ext0O__rateMatchPatternToAddModList__cond := seq_of_format RateMatchPattern__Format 1 maxNrofRateMatchPatterns ServingCellConfig__ext0O__rateMatchPatternToAddModList__helper1 ServingCellConfig__ext0O__rateMatchPatternToAddModList__helper2.

Opaque ServingCellConfig__ext0O__rateMatchPatternToAddModList__cond ServingCellConfig__ext0O__rateMatchPatternToAddModList__Format.

Definition ServingCellConfig__ext0O__rateMatchPatternToReleaseList__Format : T_Format ServingCellConfig__ext0O__rateMatchPatternToReleaseList__Type ServingCellConfig__ext0O__rateMatchPatternToReleaseList__cond := seq_of_format RateMatchPatternId__Format 1 maxNrofRateMatchPatterns ServingCellConfig__ext0O__rateMatchPatternToReleaseList__helper1 ServingCellConfig__ext0O__rateMatchPatternToReleaseList__helper2.

Opaque ServingCellConfig__ext0O__rateMatchPatternToReleaseList__cond ServingCellConfig__ext0O__rateMatchPatternToReleaseList__Format.

Definition ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__Format : T_Format ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__Type ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__cond := seq_of_format SCS_SpecificCarrier__Format 1 maxSCSs ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__helper1 ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__helper2.

Opaque ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__cond ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__Format.


Definition ServingCellConfig__ext0O__Format_Type := Eval cbn in seq_format_prod ServingCellConfig__ext0O__list.
Definition ServingCellConfig__ext0O__Format_list : ServingCellConfig__ext0O__Format_Type :=
  (ServingCellConfig__ext0O__lte_CRS_ToMatchAround__Format, (ServingCellConfig__ext0O__rateMatchPatternToAddModList__Format, (ServingCellConfig__ext0O__rateMatchPatternToReleaseList__Format, (ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List__Format, unit_format)))).
Definition ServingCellConfig__ext0O__list__Format := (*Eval compute in *) seq_format ServingCellConfig__ext0O__list ServingCellConfig__ext0O__Format_list.
Definition ServingCellConfig__ext0O__F1 z :=
  (ServingCellConfig__ext0O__lte_CRS_ToMatchAround z, (ServingCellConfig__ext0O__rateMatchPatternToAddModList z, (ServingCellConfig__ext0O__rateMatchPatternToReleaseList z, (ServingCellConfig__ext0O__downlinkChannelBW_PerSCS_List z, tt)))).
Definition ServingCellConfig__ext0O__F2 (y : seq_type ServingCellConfig__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ServingCellConfig__ext0O__Type i0 i1 i2 i3
  end.
Lemma ServingCellConfig__ext0O__F1F2_cond (z : ServingCellConfig__ext0O__Type)
  : ServingCellConfig__ext0O__cond z ->
  (seq_cond ServingCellConfig__ext0O__list (ServingCellConfig__ext0O__F1 z)).
intro H. unfold ServingCellConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfig__ext0O__F1F2_cond2 (z : ServingCellConfig__ext0O__Type)
 : ServingCellConfig__ext0O__F2 (ServingCellConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfig__ext0O__F2F1_cond (y : seq_type ServingCellConfig__ext0O__list)
  : seq_cond ServingCellConfig__ext0O__list y ->
 (ServingCellConfig__ext0O__cond (ServingCellConfig__ext0O__F2 y)) /\  ServingCellConfig__ext0O__F1 (ServingCellConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfig__ext0O__Format : T_Format ServingCellConfig__ext0O__Type ServingCellConfig__ext0O__cond :=
        proj2_format  ServingCellConfig__ext0O__cond ServingCellConfig__ext0O__list__Format
    ServingCellConfig__ext0O__F1 ServingCellConfig__ext0O__F2 ServingCellConfig__ext0O__F1F2_cond  ServingCellConfig__ext0O__F1F2_cond2 ServingCellConfig__ext0O__F2F1_cond.
Opaque ServingCellConfig__ext0O__cond ServingCellConfig__ext0O__Format.

Definition ServingCellConfig__ext0__check_all_none (b : ServingCellConfig__ext0O__Type) : bool :=
match b with 
  | make__ServingCellConfig__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition ServingCellConfig__ext0__Format : T_Format ServingCellConfig__ext0__Type ServingCellConfig__ext0__cond :=
  restrict_add_format ServingCellConfig__ext0__check_all_none ServingCellConfig__ext0O__Format.

Opaque ServingCellConfig__ext0__cond ServingCellConfig__ext0__Format.

Definition ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Format : T_Format ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__nat__Format ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F1 ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F2 ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F1F2 ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__F2F1.

Opaque ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__cond ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Format.

Opaque ServingCellConfig__ext1O__dormantBWP_Config_r16__cond ServingCellConfig__ext1O__dormantBWP_Config_r16__Format.

Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__Format : T_Format Z ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__cond :=
 ranged_int_format (-2) (2) ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__helper1 ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__helper2.

Opaque ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__cond ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__Format.

Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__Format : T_Format Z ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__cond :=
 ranged_int_format (-5) (5) ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__helper1 ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__helper2.

Opaque ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__cond ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__Format.

Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__Format : T_Format Z ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__cond :=
 ranged_int_format (-10) (10) ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__helper1 ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__helper2.

Opaque ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__cond ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__Format.

Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__Format : T_Format Z ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__cond :=
 ranged_int_format (-20) (20) ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__helper1 ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__helper2.

Opaque ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__cond ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__Format.


Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__Format_Type := Eval cbn in get_formats ServingCellConfig__ext1O__ca_SlotOffset_r16__list.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__Format_list : ServingCellConfig__ext1O__ca_SlotOffset_r16__Format_Type :=
  (ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz__Format, (ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz__Format, (ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz__Format, (ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz__Format, unit__Format)))).
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__list__Format := Eval compute in choice_format ServingCellConfig__ext1O__ca_SlotOffset_r16__list ServingCellConfig__ext1O__ca_SlotOffset_r16__len_helper1 ServingCellConfig__ext1O__ca_SlotOffset_r16__len_helper2  ServingCellConfig__ext1O__ca_SlotOffset_r16__Format_list.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__F1 (z : ServingCellConfig__ext1O__ca_SlotOffset_r16__Type) : (choice ServingCellConfig__ext1O__ca_SlotOffset_r16__list) :=
  match z with
   | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz t => existT _ 0 t
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz t => existT _ 1 t
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz t => existT _ 2 t
  | ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz t => existT _ 3 t
  end.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__g := (fun n => typ_set (get_nth_typ ServingCellConfig__ext1O__ca_SlotOffset_r16__list n)).
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__F2 (y : choice ServingCellConfig__ext1O__ca_SlotOffset_r16__list) : ServingCellConfig__ext1O__ca_SlotOffset_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ServingCellConfig__ext1O__ca_SlotOffset_r16__g n -> ServingCellConfig__ext1O__ca_SlotOffset_r16__Type) with
    | 0 => fun (t : Z) => ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS15kHz t 
    | 1 => fun (t : Z) => ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS30KHz t 
    | 2 => fun (t : Z) => ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS60KHz t 
    | 3 => fun (t : Z) => ServingCellConfig__ext1O__ca_SlotOffset_r16__refSCS120KHz t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : ServingCellConfig__ext1O__ca_SlotOffset_r16__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ ServingCellConfig__ext1O__ca_SlotOffset_r16__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ServingCellConfig__ext1O__ca_SlotOffset_r16__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return ServingCellConfig__ext1O__ca_SlotOffset_r16__Type with end) n0
           end t0).

Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__helper2 :  forall (y : ServingCellConfig__ext1O__ca_SlotOffset_r16__Type), ServingCellConfig__ext1O__ca_SlotOffset_r16__cond y -> choice_cond ServingCellConfig__ext1O__ca_SlotOffset_r16__list (ServingCellConfig__ext1O__ca_SlotOffset_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__helper3 :  forall (y : ServingCellConfig__ext1O__ca_SlotOffset_r16__Type), ServingCellConfig__ext1O__ca_SlotOffset_r16__F2 (ServingCellConfig__ext1O__ca_SlotOffset_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ServingCellConfig__ext1O__ca_SlotOffset_r16__helper4 : (forall b : choice ServingCellConfig__ext1O__ca_SlotOffset_r16__list, choice_cond ServingCellConfig__ext1O__ca_SlotOffset_r16__list b -> ServingCellConfig__ext1O__ca_SlotOffset_r16__cond (ServingCellConfig__ext1O__ca_SlotOffset_r16__F2 b) /\ ServingCellConfig__ext1O__ca_SlotOffset_r16__F1 (ServingCellConfig__ext1O__ca_SlotOffset_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ServingCellConfig__ext1O__ca_SlotOffset_r16__F1 ServingCellConfig__ext1O__ca_SlotOffset_r16__F2.
Definition ServingCellConfig__ext1O__ca_SlotOffset_r16__Format : T_Format ServingCellConfig__ext1O__ca_SlotOffset_r16__Type ServingCellConfig__ext1O__ca_SlotOffset_r16__cond :=
  (* Eval compute in *) proj2_format ServingCellConfig__ext1O__ca_SlotOffset_r16__cond ServingCellConfig__ext1O__ca_SlotOffset_r16__list__Format ServingCellConfig__ext1O__ca_SlotOffset_r16__F1 ServingCellConfig__ext1O__ca_SlotOffset_r16__F2 ServingCellConfig__ext1O__ca_SlotOffset_r16__helper2 ServingCellConfig__ext1O__ca_SlotOffset_r16__helper3 ServingCellConfig__ext1O__ca_SlotOffset_r16__helper4.
Opaque ServingCellConfig__ext1O__ca_SlotOffset_r16__cond ServingCellConfig__ext1O__ca_SlotOffset_r16__Format.

Opaque ServingCellConfig__ext1O__dummy2__cond ServingCellConfig__ext1O__dummy2__Format.

Definition ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__Format : T_Format ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__Type ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__cond := seq_of_format IntraCellGuardBandsPerSCS_r16__Format 1 maxSCSs ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__helper1 ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__helper2.

Opaque ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__cond ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__Format.

Definition ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__Format : T_Format ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__Type ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__cond := seq_of_format IntraCellGuardBandsPerSCS_r16__Format 1 maxSCSs ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__helper1 ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__helper2.

Opaque ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__cond ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__Format.

Definition ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Format : T_Format ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__nat__Format ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F1 ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F2 ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F1F2 ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__F2F1.

Opaque ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__cond ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Format.

Opaque ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__cond ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__Format.

Opaque ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__cond ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__Format.

Definition ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Format : T_Format ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__nat__Format ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F1 ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F2 ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F1F2 ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__F2F1.

Opaque ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__cond ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Format.

Definition ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Format : T_Format ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__nat__Format ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F1 ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F2 ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F1F2 ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__F2F1.

Opaque ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__cond ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Format.

Definition ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Format : T_Format ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__nat__Format ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F1 ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F2 ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F1F2 ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__F2F1.

Opaque ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__cond ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Format.

Definition ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Format : T_Format ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__nat__Format ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F1 ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F2 ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F1F2 ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__F2F1.

Opaque ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__cond ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Format.

Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Format : T_Format ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__nat__Format ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F1 ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F2 ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F1F2 ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__F2F1.

Opaque ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__cond ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Format.

Definition ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Format : T_Format ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__nat__Format ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F1 ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F2 ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F1F2 ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__F2F1.

Opaque ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__cond ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Format.


Definition ServingCellConfig__ext1O__Format_Type := Eval cbn in seq_format_prod ServingCellConfig__ext1O__list.
Definition ServingCellConfig__ext1O__Format_list : ServingCellConfig__ext1O__Format_Type :=
  (ServingCellConfig__ext1O__supplementaryUplinkRelease_r16__Format, (TDD_UL_DL_ConfigDedicated_IAB_MT_r16__Format, (ServingCellConfig__ext1O__dormantBWP_Config_r16__Format, (ServingCellConfig__ext1O__ca_SlotOffset_r16__Format, (ServingCellConfig__ext1O__dummy2__Format, (ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16__Format, (ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16__Format, (ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16__Format, (ServingCellConfig__ext1O__lte_CRS_PatternList1_r16__Format, (ServingCellConfig__ext1O__lte_CRS_PatternList2_r16__Format, (ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16__Format, (ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16__Format, (ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16__Format, (ServingCellConfig__ext1O__enableBeamSwitchTiming_r16__Format, (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16__Format, (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16__Format, unit_format)))))))))))))))).
Definition ServingCellConfig__ext1O__list__Format := (*Eval compute in *) seq_format ServingCellConfig__ext1O__list ServingCellConfig__ext1O__Format_list.
Definition ServingCellConfig__ext1O__F1 z :=
  (ServingCellConfig__ext1O__supplementaryUplinkRelease_r16 z, (ServingCellConfig__ext1O__tdd_UL_DL_ConfigurationDedicated_IAB_MT_r16 z, (ServingCellConfig__ext1O__dormantBWP_Config_r16 z, (ServingCellConfig__ext1O__ca_SlotOffset_r16 z, (ServingCellConfig__ext1O__dummy2 z, (ServingCellConfig__ext1O__intraCellGuardBandsDL_List_r16 z, (ServingCellConfig__ext1O__intraCellGuardBandsUL_List_r16 z, (ServingCellConfig__ext1O__csi_RS_ValidationWithDCI_r16 z, (ServingCellConfig__ext1O__lte_CRS_PatternList1_r16 z, (ServingCellConfig__ext1O__lte_CRS_PatternList2_r16 z, (ServingCellConfig__ext1O__crs_RateMatch_PerCORESETPoolIndex_r16 z, (ServingCellConfig__ext1O__enableTwoDefaultTCI_States_r16 z, (ServingCellConfig__ext1O__enableDefaultTCI_StatePerCoresetPoolIndex_r16 z, (ServingCellConfig__ext1O__enableBeamSwitchTiming_r16 z, (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType1_r16 z, (ServingCellConfig__ext1O__cbg_TxDiffTBsProcessingType2_r16 z, tt)))))))))))))))).
Definition ServingCellConfig__ext1O__F2 (y : seq_type ServingCellConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, _))))))))))))))))=>
    make__ServingCellConfig__ext1O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
  end.
Lemma ServingCellConfig__ext1O__F1F2_cond (z : ServingCellConfig__ext1O__Type)
  : ServingCellConfig__ext1O__cond z ->
  (seq_cond ServingCellConfig__ext1O__list (ServingCellConfig__ext1O__F1 z)).
intro H. unfold ServingCellConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfig__ext1O__F1F2_cond2 (z : ServingCellConfig__ext1O__Type)
 : ServingCellConfig__ext1O__F2 (ServingCellConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfig__ext1O__F2F1_cond (y : seq_type ServingCellConfig__ext1O__list)
  : seq_cond ServingCellConfig__ext1O__list y ->
 (ServingCellConfig__ext1O__cond (ServingCellConfig__ext1O__F2 y)) /\  ServingCellConfig__ext1O__F1 (ServingCellConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfig__ext1O__Format : T_Format ServingCellConfig__ext1O__Type ServingCellConfig__ext1O__cond :=
        proj2_format  ServingCellConfig__ext1O__cond ServingCellConfig__ext1O__list__Format
    ServingCellConfig__ext1O__F1 ServingCellConfig__ext1O__F2 ServingCellConfig__ext1O__F1F2_cond  ServingCellConfig__ext1O__F1F2_cond2 ServingCellConfig__ext1O__F2F1_cond.
Opaque ServingCellConfig__ext1O__cond ServingCellConfig__ext1O__Format.

Definition ServingCellConfig__ext1__check_all_none (b : ServingCellConfig__ext1O__Type) : bool :=
match b with 
  | make__ServingCellConfig__ext1O__Type None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition ServingCellConfig__ext1__Format : T_Format ServingCellConfig__ext1__Type ServingCellConfig__ext1__cond :=
  restrict_add_format ServingCellConfig__ext1__check_all_none ServingCellConfig__ext1O__Format.

Opaque ServingCellConfig__ext1__cond ServingCellConfig__ext1__Format.

Definition ServingCellConfig__ext2O__directionalCollisionHandling_r16__Format : T_Format ServingCellConfig__ext2O__directionalCollisionHandling_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext2O__directionalCollisionHandling_r16__nat__Format ServingCellConfig__ext2O__directionalCollisionHandling_r16__F1 ServingCellConfig__ext2O__directionalCollisionHandling_r16__F2 ServingCellConfig__ext2O__directionalCollisionHandling_r16__F1F2 ServingCellConfig__ext2O__directionalCollisionHandling_r16__F2F1.

Opaque ServingCellConfig__ext2O__directionalCollisionHandling_r16__cond ServingCellConfig__ext2O__directionalCollisionHandling_r16__Format.

Opaque ServingCellConfig__ext2O__channelAccessConfig_r16__cond ServingCellConfig__ext2O__channelAccessConfig_r16__Format.


Definition ServingCellConfig__ext2O__Format_Type := Eval cbn in seq_format_prod ServingCellConfig__ext2O__list.
Definition ServingCellConfig__ext2O__Format_list : ServingCellConfig__ext2O__Format_Type :=
  (ServingCellConfig__ext2O__directionalCollisionHandling_r16__Format, (ServingCellConfig__ext2O__channelAccessConfig_r16__Format, unit_format)).
Definition ServingCellConfig__ext2O__list__Format := (*Eval compute in *) seq_format ServingCellConfig__ext2O__list ServingCellConfig__ext2O__Format_list.
Definition ServingCellConfig__ext2O__F1 z :=
  (ServingCellConfig__ext2O__directionalCollisionHandling_r16 z, (ServingCellConfig__ext2O__channelAccessConfig_r16 z, tt)).
Definition ServingCellConfig__ext2O__F2 (y : seq_type ServingCellConfig__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ServingCellConfig__ext2O__Type i0 i1
  end.
Lemma ServingCellConfig__ext2O__F1F2_cond (z : ServingCellConfig__ext2O__Type)
  : ServingCellConfig__ext2O__cond z ->
  (seq_cond ServingCellConfig__ext2O__list (ServingCellConfig__ext2O__F1 z)).
intro H. unfold ServingCellConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfig__ext2O__F1F2_cond2 (z : ServingCellConfig__ext2O__Type)
 : ServingCellConfig__ext2O__F2 (ServingCellConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfig__ext2O__F2F1_cond (y : seq_type ServingCellConfig__ext2O__list)
  : seq_cond ServingCellConfig__ext2O__list y ->
 (ServingCellConfig__ext2O__cond (ServingCellConfig__ext2O__F2 y)) /\  ServingCellConfig__ext2O__F1 (ServingCellConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfig__ext2O__Format : T_Format ServingCellConfig__ext2O__Type ServingCellConfig__ext2O__cond :=
        proj2_format  ServingCellConfig__ext2O__cond ServingCellConfig__ext2O__list__Format
    ServingCellConfig__ext2O__F1 ServingCellConfig__ext2O__F2 ServingCellConfig__ext2O__F1F2_cond  ServingCellConfig__ext2O__F1F2_cond2 ServingCellConfig__ext2O__F2F1_cond.
Opaque ServingCellConfig__ext2O__cond ServingCellConfig__ext2O__Format.

Definition ServingCellConfig__ext2__check_all_none (b : ServingCellConfig__ext2O__Type) : bool :=
match b with 
  | make__ServingCellConfig__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition ServingCellConfig__ext2__Format : T_Format ServingCellConfig__ext2__Type ServingCellConfig__ext2__cond :=
  restrict_add_format ServingCellConfig__ext2__check_all_none ServingCellConfig__ext2O__Format.

Opaque ServingCellConfig__ext2__cond ServingCellConfig__ext2__Format.

Opaque ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__cond ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__Format.

Opaque ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__cond ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__Format.

Opaque ServingCellConfig__ext3O__mimoParam_r17__cond ServingCellConfig__ext3O__mimoParam_r17__Format.

Definition ServingCellConfig__ext3O__channelAccessMode2_r17__Format : T_Format ServingCellConfig__ext3O__channelAccessMode2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext3O__channelAccessMode2_r17__nat__Format ServingCellConfig__ext3O__channelAccessMode2_r17__F1 ServingCellConfig__ext3O__channelAccessMode2_r17__F2 ServingCellConfig__ext3O__channelAccessMode2_r17__F1F2 ServingCellConfig__ext3O__channelAccessMode2_r17__F2F1.

Opaque ServingCellConfig__ext3O__channelAccessMode2_r17__cond ServingCellConfig__ext3O__channelAccessMode2_r17__Format.

Definition ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Format : T_Format ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__nat__Format ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F1 ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F2 ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F1F2 ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__F2F1.

Opaque ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__cond ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Format.

Definition ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Format : T_Format ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__nat__Format ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F1 ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F2 ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F1F2 ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__F2F1.

Opaque ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__cond ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Format.

Definition ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Format : T_Format ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__nat__Format ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F1 ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F2 ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F1F2 ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__F2F1.

Opaque ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__cond ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Format.

Definition ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Format : T_Format ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__nat__Format ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F1 ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F2 ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F1F2 ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__F2F1.

Opaque ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__cond ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Format.

Definition ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Format : T_Format ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__nat__Format ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F1 ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F2 ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F1F2 ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__F2F1.

Opaque ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__cond ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Format.

Opaque ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__cond ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__Format.


Definition ServingCellConfig__ext3O__Format_Type := Eval cbn in seq_format_prod ServingCellConfig__ext3O__list.
Definition ServingCellConfig__ext3O__Format_list : ServingCellConfig__ext3O__Format_Type :=
  (ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17__Format, (ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17__Format, (ServingCellConfig__ext3O__mimoParam_r17__Format, (ServingCellConfig__ext3O__channelAccessMode2_r17__Format, (ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17__Format, (ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17__Format, (ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17__Format, (ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17__Format, (TCI_ActivatedConfig_r17__Format, (ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17__Format, (ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17__Format, unit_format))))))))))).
Definition ServingCellConfig__ext3O__list__Format := (*Eval compute in *) seq_format ServingCellConfig__ext3O__list ServingCellConfig__ext3O__Format_list.
Definition ServingCellConfig__ext3O__F1 z :=
  (ServingCellConfig__ext3O__nr_dl_PRS_PDC_Info_r17 z, (ServingCellConfig__ext3O__semiStaticChannelAccessConfigUE_r17 z, (ServingCellConfig__ext3O__mimoParam_r17 z, (ServingCellConfig__ext3O__channelAccessMode2_r17 z, (ServingCellConfig__ext3O__timeDomainHARQ_BundlingType1_r17 z, (ServingCellConfig__ext3O__nrofHARQ_BundlingGroups_r17 z, (ServingCellConfig__ext3O__fdmed_ReceptionMulticast_r17 z, (ServingCellConfig__ext3O__moreThanOneNackOnlyMode_r17 z, (ServingCellConfig__ext3O__tci_ActivatedConfig_r17 z, (ServingCellConfig__ext3O__directionalCollisionHandling_DC_r17 z, (ServingCellConfig__ext3O__lte_NeighCellsCRS_AssistInfoList_r17 z, tt))))))))))).
Definition ServingCellConfig__ext3O__F2 (y : seq_type ServingCellConfig__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, _)))))))))))=>
    make__ServingCellConfig__ext3O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10
  end.
Lemma ServingCellConfig__ext3O__F1F2_cond (z : ServingCellConfig__ext3O__Type)
  : ServingCellConfig__ext3O__cond z ->
  (seq_cond ServingCellConfig__ext3O__list (ServingCellConfig__ext3O__F1 z)).
intro H. unfold ServingCellConfig__ext3O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfig__ext3O__F1F2_cond2 (z : ServingCellConfig__ext3O__Type)
 : ServingCellConfig__ext3O__F2 (ServingCellConfig__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfig__ext3O__F2F1_cond (y : seq_type ServingCellConfig__ext3O__list)
  : seq_cond ServingCellConfig__ext3O__list y ->
 (ServingCellConfig__ext3O__cond (ServingCellConfig__ext3O__F2 y)) /\  ServingCellConfig__ext3O__F1 (ServingCellConfig__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfig__ext3O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfig__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfig__ext3O__Format : T_Format ServingCellConfig__ext3O__Type ServingCellConfig__ext3O__cond :=
        proj2_format  ServingCellConfig__ext3O__cond ServingCellConfig__ext3O__list__Format
    ServingCellConfig__ext3O__F1 ServingCellConfig__ext3O__F2 ServingCellConfig__ext3O__F1F2_cond  ServingCellConfig__ext3O__F1F2_cond2 ServingCellConfig__ext3O__F2F1_cond.
Opaque ServingCellConfig__ext3O__cond ServingCellConfig__ext3O__Format.

Definition ServingCellConfig__ext3__check_all_none (b : ServingCellConfig__ext3O__Type) : bool :=
match b with 
  | make__ServingCellConfig__ext3O__Type None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition ServingCellConfig__ext3__Format : T_Format ServingCellConfig__ext3__Type ServingCellConfig__ext3__cond :=
  restrict_add_format ServingCellConfig__ext3__check_all_none ServingCellConfig__ext3O__Format.

Opaque ServingCellConfig__ext3__cond ServingCellConfig__ext3__Format.

Definition ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Format : T_Format ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__nat__Format ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F1 ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F2 ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F1F2 ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__F2F1.

Opaque ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__cond ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Format.


Definition ServingCellConfig__ext4O__Format_Type := Eval cbn in seq_format_prod ServingCellConfig__ext4O__list.
Definition ServingCellConfig__ext4O__Format_list : ServingCellConfig__ext4O__Format_Type :=
  (ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17__Format, unit_format).
Definition ServingCellConfig__ext4O__list__Format := (*Eval compute in *) seq_format ServingCellConfig__ext4O__list ServingCellConfig__ext4O__Format_list.
Definition ServingCellConfig__ext4O__F1 z :=
  (ServingCellConfig__ext4O__lte_NeighCellsCRS_Assumptions_r17 z, tt).
Definition ServingCellConfig__ext4O__F2 (y : seq_type ServingCellConfig__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__ServingCellConfig__ext4O__Type i0
  end.
Lemma ServingCellConfig__ext4O__F1F2_cond (z : ServingCellConfig__ext4O__Type)
  : ServingCellConfig__ext4O__cond z ->
  (seq_cond ServingCellConfig__ext4O__list (ServingCellConfig__ext4O__F1 z)).
intro H. unfold ServingCellConfig__ext4O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfig__ext4O__F1F2_cond2 (z : ServingCellConfig__ext4O__Type)
 : ServingCellConfig__ext4O__F2 (ServingCellConfig__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfig__ext4O__F2F1_cond (y : seq_type ServingCellConfig__ext4O__list)
  : seq_cond ServingCellConfig__ext4O__list y ->
 (ServingCellConfig__ext4O__cond (ServingCellConfig__ext4O__F2 y)) /\  ServingCellConfig__ext4O__F1 (ServingCellConfig__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfig__ext4O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfig__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfig__ext4O__Format : T_Format ServingCellConfig__ext4O__Type ServingCellConfig__ext4O__cond :=
        proj2_format  ServingCellConfig__ext4O__cond ServingCellConfig__ext4O__list__Format
    ServingCellConfig__ext4O__F1 ServingCellConfig__ext4O__F2 ServingCellConfig__ext4O__F1F2_cond  ServingCellConfig__ext4O__F1F2_cond2 ServingCellConfig__ext4O__F2F1_cond.
Opaque ServingCellConfig__ext4O__cond ServingCellConfig__ext4O__Format.

Definition ServingCellConfig__ext4__check_all_none (b : ServingCellConfig__ext4O__Type) : bool :=
match b with 
  | make__ServingCellConfig__ext4O__Type None  => false 
  | _ => true 
 end.
Definition ServingCellConfig__ext4__Format : T_Format ServingCellConfig__ext4__Type ServingCellConfig__ext4__cond :=
  restrict_add_format ServingCellConfig__ext4__check_all_none ServingCellConfig__ext4O__Format.

Opaque ServingCellConfig__ext4__cond ServingCellConfig__ext4__Format.


Definition ServingCellConfig__root_Format_Type := Eval cbn in seq_format_prod ServingCellConfig__root_list.
Definition ServingCellConfig__root_Format_list : ServingCellConfig__root_Format_Type :=
  (TDD_UL_DL_ConfigDedicated__Format, (BWP_DownlinkDedicated__Format, (ServingCellConfig__downlinkBWP_ToReleaseList__Format, (ServingCellConfig__downlinkBWP_ToAddModList__Format, (BWP_Id__Format, (ServingCellConfig__bwp_InactivityTimer__Format, (BWP_Id__Format, (UplinkConfig__Format, (UplinkConfig__Format, (ServingCellConfig__pdcch_ServingCellConfig__Format, (ServingCellConfig__pdsch_ServingCellConfig__Format, (ServingCellConfig__csi_MeasConfig__Format, (ServingCellConfig__sCellDeactivationTimer__Format, (CrossCarrierSchedulingConfig__Format, (TAG_Id__Format, (ServingCellConfig__dummy1__Format, (ServingCellConfig__pathlossReferenceLinking__Format, (MeasObjectId__Format, unit_format)))))))))))))))))).

Definition ServingCellConfig__ext_Format_Type := Eval cbn in get_formats ServingCellConfig__ext_list.
Definition ServingCellConfig__ext_Format_list : ServingCellConfig__ext_Format_Type :=
  (ServingCellConfig__ext0__Format, (ServingCellConfig__ext1__Format, (ServingCellConfig__ext2__Format, (ServingCellConfig__ext3__Format, (ServingCellConfig__ext4__Format, unit__Format))))).

Definition ServingCellConfig__list_type : Set := (seq_type ServingCellConfig__root_list) * (seq_ext_type ServingCellConfig__ext_list).
Definition ServingCellConfig__list_cond (z : ServingCellConfig__list_type) : Prop :=
        (seq_cond ServingCellConfig__root_list (fst z)) /\ (seq_ext_cond ServingCellConfig__ext_list (snd z)).
Definition ServingCellConfig__list_format : T_Format ServingCellConfig__list_type ServingCellConfig__list_cond :=
 (* Eval compute in *) seq_ext_format ServingCellConfig__root_list ServingCellConfig__root_Format_list ServingCellConfig__ext_list ServingCellConfig__ext_Format_list.

Opaque ServingCellConfig__list_format.
Definition ServingCellConfig__F1 (z : ServingCellConfig__Type) : ServingCellConfig__list_type :=
  (((ServingCellConfig__tdd_UL_DL_ConfigurationDedicated z, (ServingCellConfig__initialDownlinkBWP z, (ServingCellConfig__downlinkBWP_ToReleaseList z, (ServingCellConfig__downlinkBWP_ToAddModList z, (ServingCellConfig__firstActiveDownlinkBWP_Id z, (ServingCellConfig__bwp_InactivityTimer z, (ServingCellConfig__defaultDownlinkBWP_Id z, (ServingCellConfig__uplinkConfig z, (ServingCellConfig__supplementaryUplink z, (ServingCellConfig__pdcch_ServingCellConfig z, (ServingCellConfig__pdsch_ServingCellConfig z, (ServingCellConfig__csi_MeasConfig z, (ServingCellConfig__sCellDeactivationTimer z, (ServingCellConfig__crossCarrierSchedulingConfig z, (ServingCellConfig__tag_Id z, (ServingCellConfig__dummy1 z, (ServingCellConfig__pathlossReferenceLinking z, (ServingCellConfig__servingCellMO z, tt))))))))))))))))))), (
(ServingCellConfig__ext0 z, (ServingCellConfig__ext1 z, (ServingCellConfig__ext2 z, (ServingCellConfig__ext3 z, (ServingCellConfig__ext4 z, tt))))))).
Definition ServingCellConfig__F2 (y : ServingCellConfig__list_type) : ServingCellConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, _)))))))))))))))))), (i0, (i1, (i2, (i3, (i4, _))))))=>
    make__ServingCellConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 i0 i1 i2 i3 i4
  end.
Definition ServingCellConfig__helper1 : (forall a : ServingCellConfig__Type, ServingCellConfig__cond a -> ServingCellConfig__list_cond (ServingCellConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ServingCellConfig__helper2 : (forall a : ServingCellConfig__Type, ServingCellConfig__F2 (ServingCellConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ServingCellConfig__helper3 : (forall b : ServingCellConfig__list_type, ServingCellConfig__list_cond b -> ServingCellConfig__cond (ServingCellConfig__F2 b) /\ ServingCellConfig__F1 (ServingCellConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ServingCellConfig__cond, ServingCellConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ServingCellConfig__Format : T_Format ServingCellConfig__Type ServingCellConfig__cond :=
 proj2_format ServingCellConfig__cond ServingCellConfig__list_format  ServingCellConfig__F1 ServingCellConfig__F2 ServingCellConfig__helper1 ServingCellConfig__helper2 ServingCellConfig__helper3.

Opaque ServingCellConfig__cond ServingCellConfig__Format.

