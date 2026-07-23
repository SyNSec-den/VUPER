Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__helper1 : (0 <= 262)%Z.  lia. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__helper2 : to_bit_sz (Z.to_nat (262 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (262 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__Type := Z.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__cond := (fun z => (0 <= z <= 262)%Z).
Inductive RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Type : Set :=
 | RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__one
 | RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__two
 | RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__four
 | RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__eight
.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__cond := (fun (_ : RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Type) => True).
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__nat__helper.

Definition RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F1 t :=
  match t with
  | RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__one => 0
  | RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__two => 1
  | RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__four => 2
  | RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__eight => 3
  end.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F2 n :=
  match n with
  | 0 => RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__one
  | 1 => RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__two
  | 2 => RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__four
  | 3 => RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__eight
  | _ => RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__one
  end.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F1F2 : forall x : RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Type, (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F1 x <= 3) /\ RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F2 (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F2F1 : forall (y : nat) (H : y <= 3), RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F1 (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F2 y) = y. enum_solve H y. Qed.

Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__Type := Z.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__Type := Z.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__cond := (fun z => (0 <= z <= 15)%Z).
Inductive RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Type : Set :=
 | RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB0
 | RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB2
 | RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB4
 | RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB6
.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__cond := (fun (_ : RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Type) => True).
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__nat__helper.

Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F1 t :=
  match t with
  | RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB0 => 0
  | RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB2 => 1
  | RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB4 => 2
  | RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB6 => 3
  end.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F2 n :=
  match n with
  | 0 => RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB0
  | 1 => RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB2
  | 2 => RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB4
  | 3 => RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB6
  | _ => RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__dB0
  end.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F1F2 : forall x : RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Type, (RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F1 x <= 3) /\ RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F2 (RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F2F1 : forall (y : nat) (H : y <= 3), RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F1 (RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F2 y) = y. enum_solve H y. Qed.

Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__helper1 : (-202 <= -60)%Z.  lia. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__helper2 : to_bit_sz (Z.to_nat (-60 - -202)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-60 - -202))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__Type := Z.
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__cond := (fun z => (-202 <= z <= -60)%Z).
Inductive RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Type : Set :=
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl1
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl2
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl4
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl8
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl10
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl20
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl40
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl80
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl160
 | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl320
.
Definition RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__cond := (fun (_ : RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Type) => True).
Lemma RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__nat__helper.

Definition RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F1 t :=
  match t with
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl1 => 0
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl2 => 1
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl4 => 2
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl8 => 3
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl10 => 4
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl20 => 5
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl40 => 6
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl80 => 7
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl160 => 8
  | RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl320 => 9
  end.
Definition RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F2 n :=
  match n with
  | 0 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl1
  | 1 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl2
  | 2 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl4
  | 3 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl8
  | 4 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl10
  | 5 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl20
  | 6 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl40
  | 7 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl80
  | 8 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl160
  | 9 => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl320
  | _ => RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__sl1
  end.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F1F2 : forall x : RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Type, (RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F1 x <= 9) /\ RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F2 (RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F2F1 : forall (y : nat) (H : y <= 9), RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F1 (RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Type : Set :=
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n3
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n4
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n5
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n6
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n7
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n8
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n10
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n20
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n50
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n100
 | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n200
.
Definition RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__cond := (fun (_ : RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Type) => True).
Lemma RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__nat__helper.

Definition RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F1 t :=
  match t with
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n3 => 0
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n4 => 1
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n5 => 2
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n6 => 3
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n7 => 4
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n8 => 5
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n10 => 6
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n20 => 7
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n50 => 8
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n100 => 9
  | RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n200 => 10
  end.
Definition RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F2 n :=
  match n with
  | 0 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n3
  | 1 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n4
  | 2 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n5
  | 3 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n6
  | 4 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n7
  | 5 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n8
  | 6 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n10
  | 7 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n20
  | 8 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n50
  | 9 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n100
  | 10 => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n200
  | _ => RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__n3
  end.
Lemma RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F1F2 : forall x : RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Type, (RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F1 x <= 10) /\ RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F2 (RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F2F1 : forall (y : nat) (H : y <= 10), RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F1 (RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Type : Set :=
 | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl240
 | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl640
 | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl960
 | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl1280
 | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl1920
 | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl2560
.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__cond := (fun (_ : RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Type) => True).
Lemma RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__nat__helper.

Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F1 t :=
  match t with
  | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl240 => 0
  | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl640 => 1
  | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl960 => 2
  | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl1280 => 3
  | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl1920 => 4
  | RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl2560 => 5
  end.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F2 n :=
  match n with
  | 0 => RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl240
  | 1 => RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl640
  | 2 => RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl960
  | 3 => RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl1280
  | 4 => RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl1920
  | 5 => RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl2560
  | _ => RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__sl240
  end.
Lemma RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F1F2 : forall x : RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Type, (RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F1 x <= 5) /\ RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F2 (RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F2F1 : forall (y : nat) (H : y <= 5), RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F1 (RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F2 y) = y. enum_solve H y. Qed.

Record RACH_ConfigGenericTwoStepRA_r16__ext0O__Type : Set :=
  make__RACH_ConfigGenericTwoStepRA_r16__ext0O__Type {
    RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700 : option RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Type ;
}.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__list := (
 Opt RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Type RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__cond ::
 nil).
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__cond z := 
  opt_cond RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__cond (RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700 z) /\
  True.

Definition RACH_ConfigGenericTwoStepRA_r16__ext0__Type := RACH_ConfigGenericTwoStepRA_r16__ext0O__Type.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0__cond := RACH_ConfigGenericTwoStepRA_r16__ext0O__cond.

Record RACH_ConfigGenericTwoStepRA_r16__Type : Set :=
  make__RACH_ConfigGenericTwoStepRA_r16__Type {
    RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16 : option Z ;
    RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16 : option RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Type ;
    RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16 : option Z ;
    RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16 : option Z ;
    RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16 : option RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Type ;
    RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16 : option Z ;
    RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16 : option RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Type ;
    RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16 : option RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Type ;
    RACH_ConfigGenericTwoStepRA_r16__ext0 : option RACH_ConfigGenericTwoStepRA_r16__ext0__Type ;
}.
Definition RACH_ConfigGenericTwoStepRA_r16__root_list : list seq_elem := (
 Opt Z RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__cond ::
 Opt RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Type RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__cond ::
 Opt Z RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__cond ::
 Opt Z RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__cond ::
 Opt RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Type RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__cond ::
 Opt Z RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__cond ::
 Opt RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Type RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__cond ::
 Opt RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Type RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__cond ::
 nil).
Definition RACH_ConfigGenericTwoStepRA_r16__ext_list : list typ := (
  typ_cons RACH_ConfigGenericTwoStepRA_r16__ext0__Type RACH_ConfigGenericTwoStepRA_r16__ext0__cond ::
  nil).
Definition RACH_ConfigGenericTwoStepRA_r16__cond (z : RACH_ConfigGenericTwoStepRA_r16__Type) := 
(  opt_cond RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__cond (RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16 z) /\
  opt_cond RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__cond (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16 z) /\
  opt_cond RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__cond (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16 z) /\
  opt_cond RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__cond (RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16 z) /\
  opt_cond RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__cond (RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16 z) /\
  opt_cond RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__cond (RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16 z) /\
  opt_cond RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__cond (RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16 z) /\
  opt_cond RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__cond (RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16 z) /\
  True) /\ 
(  opt_cond RACH_ConfigGenericTwoStepRA_r16__ext0__cond (RACH_ConfigGenericTwoStepRA_r16__ext0 z) /\
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
Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__Format : T_Format Z RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__cond :=
 ranged_int_format (0) (262) RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__helper1 RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__helper2.

Opaque RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__cond RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Format : T_Format RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__nat__Format RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F1 RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F2 RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F1F2 RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__F2F1.

Opaque RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__cond RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__Format : T_Format Z RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__helper1 RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__helper2.

Opaque RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__cond RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__Format : T_Format Z RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__cond :=
 ranged_int_format (0) (15) RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__helper1 RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__helper2.

Opaque RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__cond RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Format : T_Format RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__nat__Format RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F1 RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F2 RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F1F2 RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__F2F1.

Opaque RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__cond RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__Format : T_Format Z RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__cond :=
 ranged_int_format (-202) (-60) RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__helper1 RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__helper2.

Opaque RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__cond RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Format : T_Format RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__nat__Format RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F1 RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F2 RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F1F2 RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__F2F1.

Opaque RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__cond RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Format : T_Format RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__nat__Format RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F1 RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F2 RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F1F2 RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__F2F1.

Opaque RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__cond RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Format : T_Format RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__nat__Format RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F1 RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F2 RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F1F2 RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__F2F1.

Opaque RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__cond RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Format.


Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__Format_Type := Eval cbn in seq_format_prod RACH_ConfigGenericTwoStepRA_r16__ext0O__list.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__Format_list : RACH_ConfigGenericTwoStepRA_r16__ext0O__Format_Type :=
  (RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700__Format, unit_format).
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__list__Format := (*Eval compute in *) seq_format RACH_ConfigGenericTwoStepRA_r16__ext0O__list RACH_ConfigGenericTwoStepRA_r16__ext0O__Format_list.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__F1 z :=
  (RACH_ConfigGenericTwoStepRA_r16__ext0O__msgB_ResponseWindow_v1700 z, tt).
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__F2 (y : seq_type RACH_ConfigGenericTwoStepRA_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RACH_ConfigGenericTwoStepRA_r16__ext0O__Type i0
  end.
Lemma RACH_ConfigGenericTwoStepRA_r16__ext0O__F1F2_cond (z : RACH_ConfigGenericTwoStepRA_r16__ext0O__Type)
  : RACH_ConfigGenericTwoStepRA_r16__ext0O__cond z ->
  (seq_cond RACH_ConfigGenericTwoStepRA_r16__ext0O__list (RACH_ConfigGenericTwoStepRA_r16__ext0O__F1 z)).
intro H. unfold RACH_ConfigGenericTwoStepRA_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__ext0O__F1F2_cond2 (z : RACH_ConfigGenericTwoStepRA_r16__ext0O__Type)
 : RACH_ConfigGenericTwoStepRA_r16__ext0O__F2 (RACH_ConfigGenericTwoStepRA_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RACH_ConfigGenericTwoStepRA_r16__ext0O__F2F1_cond (y : seq_type RACH_ConfigGenericTwoStepRA_r16__ext0O__list)
  : seq_cond RACH_ConfigGenericTwoStepRA_r16__ext0O__list y ->
 (RACH_ConfigGenericTwoStepRA_r16__ext0O__cond (RACH_ConfigGenericTwoStepRA_r16__ext0O__F2 y)) /\  RACH_ConfigGenericTwoStepRA_r16__ext0O__F1 (RACH_ConfigGenericTwoStepRA_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RACH_ConfigGenericTwoStepRA_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold RACH_ConfigGenericTwoStepRA_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0O__Format : T_Format RACH_ConfigGenericTwoStepRA_r16__ext0O__Type RACH_ConfigGenericTwoStepRA_r16__ext0O__cond :=
        proj2_format  RACH_ConfigGenericTwoStepRA_r16__ext0O__cond RACH_ConfigGenericTwoStepRA_r16__ext0O__list__Format
    RACH_ConfigGenericTwoStepRA_r16__ext0O__F1 RACH_ConfigGenericTwoStepRA_r16__ext0O__F2 RACH_ConfigGenericTwoStepRA_r16__ext0O__F1F2_cond  RACH_ConfigGenericTwoStepRA_r16__ext0O__F1F2_cond2 RACH_ConfigGenericTwoStepRA_r16__ext0O__F2F1_cond.
Opaque RACH_ConfigGenericTwoStepRA_r16__ext0O__cond RACH_ConfigGenericTwoStepRA_r16__ext0O__Format.

Definition RACH_ConfigGenericTwoStepRA_r16__ext0__check_all_none (b : RACH_ConfigGenericTwoStepRA_r16__ext0O__Type) : bool :=
match b with 
  | make__RACH_ConfigGenericTwoStepRA_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RACH_ConfigGenericTwoStepRA_r16__ext0__Format : T_Format RACH_ConfigGenericTwoStepRA_r16__ext0__Type RACH_ConfigGenericTwoStepRA_r16__ext0__cond :=
  restrict_add_format RACH_ConfigGenericTwoStepRA_r16__ext0__check_all_none RACH_ConfigGenericTwoStepRA_r16__ext0O__Format.

Opaque RACH_ConfigGenericTwoStepRA_r16__ext0__cond RACH_ConfigGenericTwoStepRA_r16__ext0__Format.


Definition RACH_ConfigGenericTwoStepRA_r16__root_Format_Type := Eval cbn in seq_format_prod RACH_ConfigGenericTwoStepRA_r16__root_list.
Definition RACH_ConfigGenericTwoStepRA_r16__root_Format_list : RACH_ConfigGenericTwoStepRA_r16__root_Format_Type :=
  (RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16__Format, (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16__Format, (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16__Format, (RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16__Format, (RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16__Format, (RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16__Format, (RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16__Format, (RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16__Format, unit_format)))))))).

Definition RACH_ConfigGenericTwoStepRA_r16__ext_Format_Type := Eval cbn in get_formats RACH_ConfigGenericTwoStepRA_r16__ext_list.
Definition RACH_ConfigGenericTwoStepRA_r16__ext_Format_list : RACH_ConfigGenericTwoStepRA_r16__ext_Format_Type :=
  (RACH_ConfigGenericTwoStepRA_r16__ext0__Format, unit__Format).

Definition RACH_ConfigGenericTwoStepRA_r16__list_type : Set := (seq_type RACH_ConfigGenericTwoStepRA_r16__root_list) * (seq_ext_type RACH_ConfigGenericTwoStepRA_r16__ext_list).
Definition RACH_ConfigGenericTwoStepRA_r16__list_cond (z : RACH_ConfigGenericTwoStepRA_r16__list_type) : Prop :=
        (seq_cond RACH_ConfigGenericTwoStepRA_r16__root_list (fst z)) /\ (seq_ext_cond RACH_ConfigGenericTwoStepRA_r16__ext_list (snd z)).
Definition RACH_ConfigGenericTwoStepRA_r16__list_format : T_Format RACH_ConfigGenericTwoStepRA_r16__list_type RACH_ConfigGenericTwoStepRA_r16__list_cond :=
 (* Eval compute in *) seq_ext_format RACH_ConfigGenericTwoStepRA_r16__root_list RACH_ConfigGenericTwoStepRA_r16__root_Format_list RACH_ConfigGenericTwoStepRA_r16__ext_list RACH_ConfigGenericTwoStepRA_r16__ext_Format_list.

Opaque RACH_ConfigGenericTwoStepRA_r16__list_format.
Definition RACH_ConfigGenericTwoStepRA_r16__F1 (z : RACH_ConfigGenericTwoStepRA_r16__Type) : RACH_ConfigGenericTwoStepRA_r16__list_type :=
  (((RACH_ConfigGenericTwoStepRA_r16__msgA_PRACH_ConfigurationIndex_r16 z, (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FDM_r16 z, (RACH_ConfigGenericTwoStepRA_r16__msgA_RO_FrequencyStart_r16 z, (RACH_ConfigGenericTwoStepRA_r16__msgA_ZeroCorrelationZoneConfig_r16 z, (RACH_ConfigGenericTwoStepRA_r16__msgA_PreamblePowerRampingStep_r16 z, (RACH_ConfigGenericTwoStepRA_r16__msgA_PreambleReceivedTargetPower_r16 z, (RACH_ConfigGenericTwoStepRA_r16__msgB_ResponseWindow_r16 z, (RACH_ConfigGenericTwoStepRA_r16__preambleTransMax_r16 z, tt))))))))), (
(RACH_ConfigGenericTwoStepRA_r16__ext0 z, tt))).
Definition RACH_ConfigGenericTwoStepRA_r16__F2 (y : RACH_ConfigGenericTwoStepRA_r16__list_type) : RACH_ConfigGenericTwoStepRA_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, _))=>
    make__RACH_ConfigGenericTwoStepRA_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 i0
  end.
Definition RACH_ConfigGenericTwoStepRA_r16__helper1 : (forall a : RACH_ConfigGenericTwoStepRA_r16__Type, RACH_ConfigGenericTwoStepRA_r16__cond a -> RACH_ConfigGenericTwoStepRA_r16__list_cond (RACH_ConfigGenericTwoStepRA_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__helper2 : (forall a : RACH_ConfigGenericTwoStepRA_r16__Type, RACH_ConfigGenericTwoStepRA_r16__F2 (RACH_ConfigGenericTwoStepRA_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__helper3 : (forall b : RACH_ConfigGenericTwoStepRA_r16__list_type, RACH_ConfigGenericTwoStepRA_r16__list_cond b -> RACH_ConfigGenericTwoStepRA_r16__cond (RACH_ConfigGenericTwoStepRA_r16__F2 b) /\ RACH_ConfigGenericTwoStepRA_r16__F1 (RACH_ConfigGenericTwoStepRA_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RACH_ConfigGenericTwoStepRA_r16__cond, RACH_ConfigGenericTwoStepRA_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RACH_ConfigGenericTwoStepRA_r16__Format : T_Format RACH_ConfigGenericTwoStepRA_r16__Type RACH_ConfigGenericTwoStepRA_r16__cond :=
 proj2_format RACH_ConfigGenericTwoStepRA_r16__cond RACH_ConfigGenericTwoStepRA_r16__list_format  RACH_ConfigGenericTwoStepRA_r16__F1 RACH_ConfigGenericTwoStepRA_r16__F2 RACH_ConfigGenericTwoStepRA_r16__helper1 RACH_ConfigGenericTwoStepRA_r16__helper2 RACH_ConfigGenericTwoStepRA_r16__helper3.

Opaque RACH_ConfigGenericTwoStepRA_r16__cond RACH_ConfigGenericTwoStepRA_r16__Format.

