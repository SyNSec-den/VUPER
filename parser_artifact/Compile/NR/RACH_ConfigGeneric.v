Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma RACH_ConfigGeneric__prach_ConfigurationIndex__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma RACH_ConfigGeneric__prach_ConfigurationIndex__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGeneric__prach_ConfigurationIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGeneric__prach_ConfigurationIndex__Type := Z.
Definition RACH_ConfigGeneric__prach_ConfigurationIndex__cond := (fun z => (0 <= z <= 255)%Z).
Inductive RACH_ConfigGeneric__msg1_FDM__Type : Set :=
 | RACH_ConfigGeneric__msg1_FDM__one
 | RACH_ConfigGeneric__msg1_FDM__two
 | RACH_ConfigGeneric__msg1_FDM__four
 | RACH_ConfigGeneric__msg1_FDM__eight
.
Definition RACH_ConfigGeneric__msg1_FDM__cond := (fun (_ : RACH_ConfigGeneric__msg1_FDM__Type) => True).
Lemma RACH_ConfigGeneric__msg1_FDM__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGeneric__msg1_FDM__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RACH_ConfigGeneric__msg1_FDM__nat__helper.

Definition RACH_ConfigGeneric__msg1_FDM__F1 t :=
  match t with
  | RACH_ConfigGeneric__msg1_FDM__one => 0
  | RACH_ConfigGeneric__msg1_FDM__two => 1
  | RACH_ConfigGeneric__msg1_FDM__four => 2
  | RACH_ConfigGeneric__msg1_FDM__eight => 3
  end.
Definition RACH_ConfigGeneric__msg1_FDM__F2 n :=
  match n with
  | 0 => RACH_ConfigGeneric__msg1_FDM__one
  | 1 => RACH_ConfigGeneric__msg1_FDM__two
  | 2 => RACH_ConfigGeneric__msg1_FDM__four
  | 3 => RACH_ConfigGeneric__msg1_FDM__eight
  | _ => RACH_ConfigGeneric__msg1_FDM__one
  end.
Lemma RACH_ConfigGeneric__msg1_FDM__F1F2 : forall x : RACH_ConfigGeneric__msg1_FDM__Type, (RACH_ConfigGeneric__msg1_FDM__F1 x <= 3) /\ RACH_ConfigGeneric__msg1_FDM__F2 (RACH_ConfigGeneric__msg1_FDM__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGeneric__msg1_FDM__F2F1 : forall (y : nat) (H : y <= 3), RACH_ConfigGeneric__msg1_FDM__F1 (RACH_ConfigGeneric__msg1_FDM__F2 y) = y. enum_solve H y. Qed.

Lemma RACH_ConfigGeneric__msg1_FrequencyStart__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma RACH_ConfigGeneric__msg1_FrequencyStart__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGeneric__msg1_FrequencyStart__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGeneric__msg1_FrequencyStart__Type := Z.
Definition RACH_ConfigGeneric__msg1_FrequencyStart__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Lemma RACH_ConfigGeneric__zeroCorrelationZoneConfig__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma RACH_ConfigGeneric__zeroCorrelationZoneConfig__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGeneric__zeroCorrelationZoneConfig__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGeneric__zeroCorrelationZoneConfig__Type := Z.
Definition RACH_ConfigGeneric__zeroCorrelationZoneConfig__cond := (fun z => (0 <= z <= 15)%Z).
Lemma RACH_ConfigGeneric__preambleReceivedTargetPower__helper1 : (-202 <= -60)%Z.  lia. Qed.
Lemma RACH_ConfigGeneric__preambleReceivedTargetPower__helper2 : to_bit_sz (Z.to_nat (-60 - -202)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (-60 - -202))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGeneric__preambleReceivedTargetPower__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGeneric__preambleReceivedTargetPower__Type := Z.
Definition RACH_ConfigGeneric__preambleReceivedTargetPower__cond := (fun z => (-202 <= z <= -60)%Z).
Inductive RACH_ConfigGeneric__preambleTransMax__Type : Set :=
 | RACH_ConfigGeneric__preambleTransMax__n3
 | RACH_ConfigGeneric__preambleTransMax__n4
 | RACH_ConfigGeneric__preambleTransMax__n5
 | RACH_ConfigGeneric__preambleTransMax__n6
 | RACH_ConfigGeneric__preambleTransMax__n7
 | RACH_ConfigGeneric__preambleTransMax__n8
 | RACH_ConfigGeneric__preambleTransMax__n10
 | RACH_ConfigGeneric__preambleTransMax__n20
 | RACH_ConfigGeneric__preambleTransMax__n50
 | RACH_ConfigGeneric__preambleTransMax__n100
 | RACH_ConfigGeneric__preambleTransMax__n200
.
Definition RACH_ConfigGeneric__preambleTransMax__cond := (fun (_ : RACH_ConfigGeneric__preambleTransMax__Type) => True).
Lemma RACH_ConfigGeneric__preambleTransMax__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGeneric__preambleTransMax__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 RACH_ConfigGeneric__preambleTransMax__nat__helper.

Definition RACH_ConfigGeneric__preambleTransMax__F1 t :=
  match t with
  | RACH_ConfigGeneric__preambleTransMax__n3 => 0
  | RACH_ConfigGeneric__preambleTransMax__n4 => 1
  | RACH_ConfigGeneric__preambleTransMax__n5 => 2
  | RACH_ConfigGeneric__preambleTransMax__n6 => 3
  | RACH_ConfigGeneric__preambleTransMax__n7 => 4
  | RACH_ConfigGeneric__preambleTransMax__n8 => 5
  | RACH_ConfigGeneric__preambleTransMax__n10 => 6
  | RACH_ConfigGeneric__preambleTransMax__n20 => 7
  | RACH_ConfigGeneric__preambleTransMax__n50 => 8
  | RACH_ConfigGeneric__preambleTransMax__n100 => 9
  | RACH_ConfigGeneric__preambleTransMax__n200 => 10
  end.
Definition RACH_ConfigGeneric__preambleTransMax__F2 n :=
  match n with
  | 0 => RACH_ConfigGeneric__preambleTransMax__n3
  | 1 => RACH_ConfigGeneric__preambleTransMax__n4
  | 2 => RACH_ConfigGeneric__preambleTransMax__n5
  | 3 => RACH_ConfigGeneric__preambleTransMax__n6
  | 4 => RACH_ConfigGeneric__preambleTransMax__n7
  | 5 => RACH_ConfigGeneric__preambleTransMax__n8
  | 6 => RACH_ConfigGeneric__preambleTransMax__n10
  | 7 => RACH_ConfigGeneric__preambleTransMax__n20
  | 8 => RACH_ConfigGeneric__preambleTransMax__n50
  | 9 => RACH_ConfigGeneric__preambleTransMax__n100
  | 10 => RACH_ConfigGeneric__preambleTransMax__n200
  | _ => RACH_ConfigGeneric__preambleTransMax__n3
  end.
Lemma RACH_ConfigGeneric__preambleTransMax__F1F2 : forall x : RACH_ConfigGeneric__preambleTransMax__Type, (RACH_ConfigGeneric__preambleTransMax__F1 x <= 10) /\ RACH_ConfigGeneric__preambleTransMax__F2 (RACH_ConfigGeneric__preambleTransMax__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGeneric__preambleTransMax__F2F1 : forall (y : nat) (H : y <= 10), RACH_ConfigGeneric__preambleTransMax__F1 (RACH_ConfigGeneric__preambleTransMax__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigGeneric__powerRampingStep__Type : Set :=
 | RACH_ConfigGeneric__powerRampingStep__dB0
 | RACH_ConfigGeneric__powerRampingStep__dB2
 | RACH_ConfigGeneric__powerRampingStep__dB4
 | RACH_ConfigGeneric__powerRampingStep__dB6
.
Definition RACH_ConfigGeneric__powerRampingStep__cond := (fun (_ : RACH_ConfigGeneric__powerRampingStep__Type) => True).
Lemma RACH_ConfigGeneric__powerRampingStep__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGeneric__powerRampingStep__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RACH_ConfigGeneric__powerRampingStep__nat__helper.

Definition RACH_ConfigGeneric__powerRampingStep__F1 t :=
  match t with
  | RACH_ConfigGeneric__powerRampingStep__dB0 => 0
  | RACH_ConfigGeneric__powerRampingStep__dB2 => 1
  | RACH_ConfigGeneric__powerRampingStep__dB4 => 2
  | RACH_ConfigGeneric__powerRampingStep__dB6 => 3
  end.
Definition RACH_ConfigGeneric__powerRampingStep__F2 n :=
  match n with
  | 0 => RACH_ConfigGeneric__powerRampingStep__dB0
  | 1 => RACH_ConfigGeneric__powerRampingStep__dB2
  | 2 => RACH_ConfigGeneric__powerRampingStep__dB4
  | 3 => RACH_ConfigGeneric__powerRampingStep__dB6
  | _ => RACH_ConfigGeneric__powerRampingStep__dB0
  end.
Lemma RACH_ConfigGeneric__powerRampingStep__F1F2 : forall x : RACH_ConfigGeneric__powerRampingStep__Type, (RACH_ConfigGeneric__powerRampingStep__F1 x <= 3) /\ RACH_ConfigGeneric__powerRampingStep__F2 (RACH_ConfigGeneric__powerRampingStep__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGeneric__powerRampingStep__F2F1 : forall (y : nat) (H : y <= 3), RACH_ConfigGeneric__powerRampingStep__F1 (RACH_ConfigGeneric__powerRampingStep__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigGeneric__ra_ResponseWindow__Type : Set :=
 | RACH_ConfigGeneric__ra_ResponseWindow__sl1
 | RACH_ConfigGeneric__ra_ResponseWindow__sl2
 | RACH_ConfigGeneric__ra_ResponseWindow__sl4
 | RACH_ConfigGeneric__ra_ResponseWindow__sl8
 | RACH_ConfigGeneric__ra_ResponseWindow__sl10
 | RACH_ConfigGeneric__ra_ResponseWindow__sl20
 | RACH_ConfigGeneric__ra_ResponseWindow__sl40
 | RACH_ConfigGeneric__ra_ResponseWindow__sl80
.
Definition RACH_ConfigGeneric__ra_ResponseWindow__cond := (fun (_ : RACH_ConfigGeneric__ra_ResponseWindow__Type) => True).
Lemma RACH_ConfigGeneric__ra_ResponseWindow__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGeneric__ra_ResponseWindow__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RACH_ConfigGeneric__ra_ResponseWindow__nat__helper.

Definition RACH_ConfigGeneric__ra_ResponseWindow__F1 t :=
  match t with
  | RACH_ConfigGeneric__ra_ResponseWindow__sl1 => 0
  | RACH_ConfigGeneric__ra_ResponseWindow__sl2 => 1
  | RACH_ConfigGeneric__ra_ResponseWindow__sl4 => 2
  | RACH_ConfigGeneric__ra_ResponseWindow__sl8 => 3
  | RACH_ConfigGeneric__ra_ResponseWindow__sl10 => 4
  | RACH_ConfigGeneric__ra_ResponseWindow__sl20 => 5
  | RACH_ConfigGeneric__ra_ResponseWindow__sl40 => 6
  | RACH_ConfigGeneric__ra_ResponseWindow__sl80 => 7
  end.
Definition RACH_ConfigGeneric__ra_ResponseWindow__F2 n :=
  match n with
  | 0 => RACH_ConfigGeneric__ra_ResponseWindow__sl1
  | 1 => RACH_ConfigGeneric__ra_ResponseWindow__sl2
  | 2 => RACH_ConfigGeneric__ra_ResponseWindow__sl4
  | 3 => RACH_ConfigGeneric__ra_ResponseWindow__sl8
  | 4 => RACH_ConfigGeneric__ra_ResponseWindow__sl10
  | 5 => RACH_ConfigGeneric__ra_ResponseWindow__sl20
  | 6 => RACH_ConfigGeneric__ra_ResponseWindow__sl40
  | 7 => RACH_ConfigGeneric__ra_ResponseWindow__sl80
  | _ => RACH_ConfigGeneric__ra_ResponseWindow__sl1
  end.
Lemma RACH_ConfigGeneric__ra_ResponseWindow__F1F2 : forall x : RACH_ConfigGeneric__ra_ResponseWindow__Type, (RACH_ConfigGeneric__ra_ResponseWindow__F1 x <= 7) /\ RACH_ConfigGeneric__ra_ResponseWindow__F2 (RACH_ConfigGeneric__ra_ResponseWindow__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGeneric__ra_ResponseWindow__F2F1 : forall (y : nat) (H : y <= 7), RACH_ConfigGeneric__ra_ResponseWindow__F1 (RACH_ConfigGeneric__ra_ResponseWindow__F2 y) = y. enum_solve H y. Qed.

Inductive RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Type : Set :=
 | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf1
 | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf2
 | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf4
 | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf8
 | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf16
 | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf32
 | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf64
.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__cond := (fun (_ : RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Type) => True).
Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__nat__helper.

Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F1 t :=
  match t with
  | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf1 => 0
  | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf2 => 1
  | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf4 => 2
  | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf8 => 3
  | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf16 => 4
  | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf32 => 5
  | RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf64 => 6
  end.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F2 n :=
  match n with
  | 0 => RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf1
  | 1 => RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf2
  | 2 => RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf4
  | 3 => RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf8
  | 4 => RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf16
  | 5 => RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf32
  | 6 => RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf64
  | _ => RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__scf1
  end.
Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F1F2 : forall x : RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Type, (RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F1 x <= 6) /\ RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F2 (RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F2F1 : forall (y : nat) (H : y <= 6), RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F1 (RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__Type := Z.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__cond := (fun z => (0 <= z <= 63)%Z).
Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__Type := Z.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__cond := (fun z => (0 <= z <= 39)%Z).
Inductive RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Type : Set :=
 | RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__sl60
 | RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__sl160
.
Definition RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__cond := (fun (_ : RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Type) => True).
Lemma RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__nat__helper.

Definition RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F1 t :=
  match t with
  | RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__sl60 => 0
  | RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__sl160 => 1
  end.
Definition RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F2 n :=
  match n with
  | 0 => RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__sl60
  | 1 => RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__sl160
  | _ => RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__sl60
  end.
Lemma RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F1F2 : forall x : RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Type, (RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F1 x <= 1) /\ RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F2 (RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F2F1 : forall (y : nat) (H : y <= 1), RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F1 (RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F2 y) = y. enum_solve H y. Qed.

Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__helper1 : (256 <= 262)%Z.  lia. Qed.
Lemma RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__helper2 : to_bit_sz (Z.to_nat (262 - 256)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (262 - 256))%Z). { apply Zorder.Zle_minus_le_0. apply RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__Type := Z.
Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__cond := (fun z => (256 <= z <= 262)%Z).
Record RACH_ConfigGeneric__ext0O__Type : Set :=
  make__RACH_ConfigGeneric__ext0O__Type {
    RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16 : option RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Type ;
    RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16 : option Z ;
    RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16 : option Z ;
    RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610 : option RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Type ;
    RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610 : option Z ;
}.
Definition RACH_ConfigGeneric__ext0O__list := (
 Opt RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Type RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__cond ::
 Opt Z RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__cond ::
 Opt Z RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__cond ::
 Opt RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Type RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__cond ::
 Opt Z RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__cond ::
 nil).
Definition RACH_ConfigGeneric__ext0O__cond z := 
  opt_cond RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__cond (RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16 z) /\
  opt_cond RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__cond (RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16 z) /\
  opt_cond RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__cond (RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16 z) /\
  opt_cond RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__cond (RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610 z) /\
  opt_cond RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__cond (RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610 z) /\
  True.

Definition RACH_ConfigGeneric__ext0__Type := RACH_ConfigGeneric__ext0O__Type.
Definition RACH_ConfigGeneric__ext0__cond := RACH_ConfigGeneric__ext0O__cond.

Inductive RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Type : Set :=
 | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl240
 | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl320
 | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl640
 | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl960
 | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl1280
 | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl1920
 | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl2560
.
Definition RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__cond := (fun (_ : RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Type) => True).
Lemma RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__nat__helper.

Definition RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F1 t :=
  match t with
  | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl240 => 0
  | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl320 => 1
  | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl640 => 2
  | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl960 => 3
  | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl1280 => 4
  | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl1920 => 5
  | RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl2560 => 6
  end.
Definition RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F2 n :=
  match n with
  | 0 => RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl240
  | 1 => RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl320
  | 2 => RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl640
  | 3 => RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl960
  | 4 => RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl1280
  | 5 => RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl1920
  | 6 => RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl2560
  | _ => RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__sl240
  end.
Lemma RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F1F2 : forall x : RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Type, (RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F1 x <= 6) /\ RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F2 (RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F1 x) = x. imp_solve. Qed.
Lemma RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F2F1 : forall (y : nat) (H : y <= 6), RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F1 (RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F2 y) = y. enum_solve H y. Qed.

Record RACH_ConfigGeneric__ext1O__Type : Set :=
  make__RACH_ConfigGeneric__ext1O__Type {
    RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700 : option RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Type ;
}.
Definition RACH_ConfigGeneric__ext1O__list := (
 Opt RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Type RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__cond ::
 nil).
Definition RACH_ConfigGeneric__ext1O__cond z := 
  opt_cond RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__cond (RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700 z) /\
  True.

Definition RACH_ConfigGeneric__ext1__Type := RACH_ConfigGeneric__ext1O__Type.
Definition RACH_ConfigGeneric__ext1__cond := RACH_ConfigGeneric__ext1O__cond.

Record RACH_ConfigGeneric__Type : Set :=
  make__RACH_ConfigGeneric__Type {
    RACH_ConfigGeneric__prach_ConfigurationIndex : Z ;
    RACH_ConfigGeneric__msg1_FDM : RACH_ConfigGeneric__msg1_FDM__Type ;
    RACH_ConfigGeneric__msg1_FrequencyStart : Z ;
    RACH_ConfigGeneric__zeroCorrelationZoneConfig : Z ;
    RACH_ConfigGeneric__preambleReceivedTargetPower : Z ;
    RACH_ConfigGeneric__preambleTransMax : RACH_ConfigGeneric__preambleTransMax__Type ;
    RACH_ConfigGeneric__powerRampingStep : RACH_ConfigGeneric__powerRampingStep__Type ;
    RACH_ConfigGeneric__ra_ResponseWindow : RACH_ConfigGeneric__ra_ResponseWindow__Type ;
    RACH_ConfigGeneric__ext0 : option RACH_ConfigGeneric__ext0__Type ;
    RACH_ConfigGeneric__ext1 : option RACH_ConfigGeneric__ext1__Type ;
}.
Definition RACH_ConfigGeneric__root_list : list seq_elem := (
 Nor Z RACH_ConfigGeneric__prach_ConfigurationIndex__cond ::
 Nor RACH_ConfigGeneric__msg1_FDM__Type RACH_ConfigGeneric__msg1_FDM__cond ::
 Nor Z RACH_ConfigGeneric__msg1_FrequencyStart__cond ::
 Nor Z RACH_ConfigGeneric__zeroCorrelationZoneConfig__cond ::
 Nor Z RACH_ConfigGeneric__preambleReceivedTargetPower__cond ::
 Nor RACH_ConfigGeneric__preambleTransMax__Type RACH_ConfigGeneric__preambleTransMax__cond ::
 Nor RACH_ConfigGeneric__powerRampingStep__Type RACH_ConfigGeneric__powerRampingStep__cond ::
 Nor RACH_ConfigGeneric__ra_ResponseWindow__Type RACH_ConfigGeneric__ra_ResponseWindow__cond ::
 nil).
Definition RACH_ConfigGeneric__ext_list : list typ := (
  typ_cons RACH_ConfigGeneric__ext0__Type RACH_ConfigGeneric__ext0__cond ::
  typ_cons RACH_ConfigGeneric__ext1__Type RACH_ConfigGeneric__ext1__cond ::
  nil).
Definition RACH_ConfigGeneric__cond (z : RACH_ConfigGeneric__Type) := 
(  RACH_ConfigGeneric__prach_ConfigurationIndex__cond (RACH_ConfigGeneric__prach_ConfigurationIndex z) /\
  RACH_ConfigGeneric__msg1_FDM__cond (RACH_ConfigGeneric__msg1_FDM z) /\
  RACH_ConfigGeneric__msg1_FrequencyStart__cond (RACH_ConfigGeneric__msg1_FrequencyStart z) /\
  RACH_ConfigGeneric__zeroCorrelationZoneConfig__cond (RACH_ConfigGeneric__zeroCorrelationZoneConfig z) /\
  RACH_ConfigGeneric__preambleReceivedTargetPower__cond (RACH_ConfigGeneric__preambleReceivedTargetPower z) /\
  RACH_ConfigGeneric__preambleTransMax__cond (RACH_ConfigGeneric__preambleTransMax z) /\
  RACH_ConfigGeneric__powerRampingStep__cond (RACH_ConfigGeneric__powerRampingStep z) /\
  RACH_ConfigGeneric__ra_ResponseWindow__cond (RACH_ConfigGeneric__ra_ResponseWindow z) /\
  True) /\ 
(  opt_cond RACH_ConfigGeneric__ext0__cond (RACH_ConfigGeneric__ext0 z) /\
  opt_cond RACH_ConfigGeneric__ext1__cond (RACH_ConfigGeneric__ext1 z) /\
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
Definition RACH_ConfigGeneric__prach_ConfigurationIndex__Format : T_Format Z RACH_ConfigGeneric__prach_ConfigurationIndex__cond :=
 ranged_int_format (0) (255) RACH_ConfigGeneric__prach_ConfigurationIndex__helper1 RACH_ConfigGeneric__prach_ConfigurationIndex__helper2.

Opaque RACH_ConfigGeneric__prach_ConfigurationIndex__cond RACH_ConfigGeneric__prach_ConfigurationIndex__Format.

Definition RACH_ConfigGeneric__msg1_FDM__Format : T_Format RACH_ConfigGeneric__msg1_FDM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGeneric__msg1_FDM__nat__Format RACH_ConfigGeneric__msg1_FDM__F1 RACH_ConfigGeneric__msg1_FDM__F2 RACH_ConfigGeneric__msg1_FDM__F1F2 RACH_ConfigGeneric__msg1_FDM__F2F1.

Opaque RACH_ConfigGeneric__msg1_FDM__cond RACH_ConfigGeneric__msg1_FDM__Format.

Definition RACH_ConfigGeneric__msg1_FrequencyStart__Format : T_Format Z RACH_ConfigGeneric__msg1_FrequencyStart__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) RACH_ConfigGeneric__msg1_FrequencyStart__helper1 RACH_ConfigGeneric__msg1_FrequencyStart__helper2.

Opaque RACH_ConfigGeneric__msg1_FrequencyStart__cond RACH_ConfigGeneric__msg1_FrequencyStart__Format.

Definition RACH_ConfigGeneric__zeroCorrelationZoneConfig__Format : T_Format Z RACH_ConfigGeneric__zeroCorrelationZoneConfig__cond :=
 ranged_int_format (0) (15) RACH_ConfigGeneric__zeroCorrelationZoneConfig__helper1 RACH_ConfigGeneric__zeroCorrelationZoneConfig__helper2.

Opaque RACH_ConfigGeneric__zeroCorrelationZoneConfig__cond RACH_ConfigGeneric__zeroCorrelationZoneConfig__Format.

Definition RACH_ConfigGeneric__preambleReceivedTargetPower__Format : T_Format Z RACH_ConfigGeneric__preambleReceivedTargetPower__cond :=
 ranged_int_format (-202) (-60) RACH_ConfigGeneric__preambleReceivedTargetPower__helper1 RACH_ConfigGeneric__preambleReceivedTargetPower__helper2.

Opaque RACH_ConfigGeneric__preambleReceivedTargetPower__cond RACH_ConfigGeneric__preambleReceivedTargetPower__Format.

Definition RACH_ConfigGeneric__preambleTransMax__Format : T_Format RACH_ConfigGeneric__preambleTransMax__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGeneric__preambleTransMax__nat__Format RACH_ConfigGeneric__preambleTransMax__F1 RACH_ConfigGeneric__preambleTransMax__F2 RACH_ConfigGeneric__preambleTransMax__F1F2 RACH_ConfigGeneric__preambleTransMax__F2F1.

Opaque RACH_ConfigGeneric__preambleTransMax__cond RACH_ConfigGeneric__preambleTransMax__Format.

Definition RACH_ConfigGeneric__powerRampingStep__Format : T_Format RACH_ConfigGeneric__powerRampingStep__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGeneric__powerRampingStep__nat__Format RACH_ConfigGeneric__powerRampingStep__F1 RACH_ConfigGeneric__powerRampingStep__F2 RACH_ConfigGeneric__powerRampingStep__F1F2 RACH_ConfigGeneric__powerRampingStep__F2F1.

Opaque RACH_ConfigGeneric__powerRampingStep__cond RACH_ConfigGeneric__powerRampingStep__Format.

Definition RACH_ConfigGeneric__ra_ResponseWindow__Format : T_Format RACH_ConfigGeneric__ra_ResponseWindow__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGeneric__ra_ResponseWindow__nat__Format RACH_ConfigGeneric__ra_ResponseWindow__F1 RACH_ConfigGeneric__ra_ResponseWindow__F2 RACH_ConfigGeneric__ra_ResponseWindow__F1F2 RACH_ConfigGeneric__ra_ResponseWindow__F2F1.

Opaque RACH_ConfigGeneric__ra_ResponseWindow__cond RACH_ConfigGeneric__ra_ResponseWindow__Format.

Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Format : T_Format RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__nat__Format RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F1 RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F2 RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F1F2 RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__F2F1.

Opaque RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__cond RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Format.

Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__Format : T_Format Z RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__cond :=
 ranged_int_format (0) (63) RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__helper1 RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__helper2.

Opaque RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__cond RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__Format.

Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__Format : T_Format Z RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__cond :=
 ranged_int_format (0) (39) RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__helper1 RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__helper2.

Opaque RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__cond RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__Format.

Definition RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Format : T_Format RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__nat__Format RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F1 RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F2 RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F1F2 RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__F2F1.

Opaque RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__cond RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Format.

Definition RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__Format : T_Format Z RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__cond :=
 ranged_int_format (256) (262) RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__helper1 RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__helper2.

Opaque RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__cond RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__Format.


Definition RACH_ConfigGeneric__ext0O__Format_Type := Eval cbn in seq_format_prod RACH_ConfigGeneric__ext0O__list.
Definition RACH_ConfigGeneric__ext0O__Format_list : RACH_ConfigGeneric__ext0O__Format_Type :=
  (RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16__Format, (RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16__Format, (RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16__Format, (RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610__Format, (RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610__Format, unit_format))))).
Definition RACH_ConfigGeneric__ext0O__list__Format := (*Eval compute in *) seq_format RACH_ConfigGeneric__ext0O__list RACH_ConfigGeneric__ext0O__Format_list.
Definition RACH_ConfigGeneric__ext0O__F1 z :=
  (RACH_ConfigGeneric__ext0O__prach_ConfigurationPeriodScaling_IAB_r16 z, (RACH_ConfigGeneric__ext0O__prach_ConfigurationFrameOffset_IAB_r16 z, (RACH_ConfigGeneric__ext0O__prach_ConfigurationSOffset_IAB_r16 z, (RACH_ConfigGeneric__ext0O__ra_ResponseWindow_v1610 z, (RACH_ConfigGeneric__ext0O__prach_ConfigurationIndex_v1610 z, tt))))).
Definition RACH_ConfigGeneric__ext0O__F2 (y : seq_type RACH_ConfigGeneric__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__RACH_ConfigGeneric__ext0O__Type i0 i1 i2 i3 i4
  end.
Lemma RACH_ConfigGeneric__ext0O__F1F2_cond (z : RACH_ConfigGeneric__ext0O__Type)
  : RACH_ConfigGeneric__ext0O__cond z ->
  (seq_cond RACH_ConfigGeneric__ext0O__list (RACH_ConfigGeneric__ext0O__F1 z)).
intro H. unfold RACH_ConfigGeneric__ext0O__cond in H. simpl. auto. Qed.
Lemma RACH_ConfigGeneric__ext0O__F1F2_cond2 (z : RACH_ConfigGeneric__ext0O__Type)
 : RACH_ConfigGeneric__ext0O__F2 (RACH_ConfigGeneric__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RACH_ConfigGeneric__ext0O__F2F1_cond (y : seq_type RACH_ConfigGeneric__ext0O__list)
  : seq_cond RACH_ConfigGeneric__ext0O__list y ->
 (RACH_ConfigGeneric__ext0O__cond (RACH_ConfigGeneric__ext0O__F2 y)) /\  RACH_ConfigGeneric__ext0O__F1 (RACH_ConfigGeneric__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RACH_ConfigGeneric__ext0O__cond. simpl in *. auto.
 - simpl. unfold RACH_ConfigGeneric__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RACH_ConfigGeneric__ext0O__Format : T_Format RACH_ConfigGeneric__ext0O__Type RACH_ConfigGeneric__ext0O__cond :=
        proj2_format  RACH_ConfigGeneric__ext0O__cond RACH_ConfigGeneric__ext0O__list__Format
    RACH_ConfigGeneric__ext0O__F1 RACH_ConfigGeneric__ext0O__F2 RACH_ConfigGeneric__ext0O__F1F2_cond  RACH_ConfigGeneric__ext0O__F1F2_cond2 RACH_ConfigGeneric__ext0O__F2F1_cond.
Opaque RACH_ConfigGeneric__ext0O__cond RACH_ConfigGeneric__ext0O__Format.

Definition RACH_ConfigGeneric__ext0__check_all_none (b : RACH_ConfigGeneric__ext0O__Type) : bool :=
match b with 
  | make__RACH_ConfigGeneric__ext0O__Type None None None None None  => false 
  | _ => true 
 end.
Definition RACH_ConfigGeneric__ext0__Format : T_Format RACH_ConfigGeneric__ext0__Type RACH_ConfigGeneric__ext0__cond :=
  restrict_add_format RACH_ConfigGeneric__ext0__check_all_none RACH_ConfigGeneric__ext0O__Format.

Opaque RACH_ConfigGeneric__ext0__cond RACH_ConfigGeneric__ext0__Format.

Definition RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Format : T_Format RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__nat__Format RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F1 RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F2 RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F1F2 RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__F2F1.

Opaque RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__cond RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Format.


Definition RACH_ConfigGeneric__ext1O__Format_Type := Eval cbn in seq_format_prod RACH_ConfigGeneric__ext1O__list.
Definition RACH_ConfigGeneric__ext1O__Format_list : RACH_ConfigGeneric__ext1O__Format_Type :=
  (RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700__Format, unit_format).
Definition RACH_ConfigGeneric__ext1O__list__Format := (*Eval compute in *) seq_format RACH_ConfigGeneric__ext1O__list RACH_ConfigGeneric__ext1O__Format_list.
Definition RACH_ConfigGeneric__ext1O__F1 z :=
  (RACH_ConfigGeneric__ext1O__ra_ResponseWindow_v1700 z, tt).
Definition RACH_ConfigGeneric__ext1O__F2 (y : seq_type RACH_ConfigGeneric__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__RACH_ConfigGeneric__ext1O__Type i0
  end.
Lemma RACH_ConfigGeneric__ext1O__F1F2_cond (z : RACH_ConfigGeneric__ext1O__Type)
  : RACH_ConfigGeneric__ext1O__cond z ->
  (seq_cond RACH_ConfigGeneric__ext1O__list (RACH_ConfigGeneric__ext1O__F1 z)).
intro H. unfold RACH_ConfigGeneric__ext1O__cond in H. simpl. auto. Qed.
Lemma RACH_ConfigGeneric__ext1O__F1F2_cond2 (z : RACH_ConfigGeneric__ext1O__Type)
 : RACH_ConfigGeneric__ext1O__F2 (RACH_ConfigGeneric__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RACH_ConfigGeneric__ext1O__F2F1_cond (y : seq_type RACH_ConfigGeneric__ext1O__list)
  : seq_cond RACH_ConfigGeneric__ext1O__list y ->
 (RACH_ConfigGeneric__ext1O__cond (RACH_ConfigGeneric__ext1O__F2 y)) /\  RACH_ConfigGeneric__ext1O__F1 (RACH_ConfigGeneric__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RACH_ConfigGeneric__ext1O__cond. simpl in *. auto.
 - simpl. unfold RACH_ConfigGeneric__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RACH_ConfigGeneric__ext1O__Format : T_Format RACH_ConfigGeneric__ext1O__Type RACH_ConfigGeneric__ext1O__cond :=
        proj2_format  RACH_ConfigGeneric__ext1O__cond RACH_ConfigGeneric__ext1O__list__Format
    RACH_ConfigGeneric__ext1O__F1 RACH_ConfigGeneric__ext1O__F2 RACH_ConfigGeneric__ext1O__F1F2_cond  RACH_ConfigGeneric__ext1O__F1F2_cond2 RACH_ConfigGeneric__ext1O__F2F1_cond.
Opaque RACH_ConfigGeneric__ext1O__cond RACH_ConfigGeneric__ext1O__Format.

Definition RACH_ConfigGeneric__ext1__check_all_none (b : RACH_ConfigGeneric__ext1O__Type) : bool :=
match b with 
  | make__RACH_ConfigGeneric__ext1O__Type None  => false 
  | _ => true 
 end.
Definition RACH_ConfigGeneric__ext1__Format : T_Format RACH_ConfigGeneric__ext1__Type RACH_ConfigGeneric__ext1__cond :=
  restrict_add_format RACH_ConfigGeneric__ext1__check_all_none RACH_ConfigGeneric__ext1O__Format.

Opaque RACH_ConfigGeneric__ext1__cond RACH_ConfigGeneric__ext1__Format.


Definition RACH_ConfigGeneric__root_Format_Type := Eval cbn in seq_format_prod RACH_ConfigGeneric__root_list.
Definition RACH_ConfigGeneric__root_Format_list : RACH_ConfigGeneric__root_Format_Type :=
  (RACH_ConfigGeneric__prach_ConfigurationIndex__Format, (RACH_ConfigGeneric__msg1_FDM__Format, (RACH_ConfigGeneric__msg1_FrequencyStart__Format, (RACH_ConfigGeneric__zeroCorrelationZoneConfig__Format, (RACH_ConfigGeneric__preambleReceivedTargetPower__Format, (RACH_ConfigGeneric__preambleTransMax__Format, (RACH_ConfigGeneric__powerRampingStep__Format, (RACH_ConfigGeneric__ra_ResponseWindow__Format, unit_format)))))))).

Definition RACH_ConfigGeneric__ext_Format_Type := Eval cbn in get_formats RACH_ConfigGeneric__ext_list.
Definition RACH_ConfigGeneric__ext_Format_list : RACH_ConfigGeneric__ext_Format_Type :=
  (RACH_ConfigGeneric__ext0__Format, (RACH_ConfigGeneric__ext1__Format, unit__Format)).

Definition RACH_ConfigGeneric__list_type : Set := (seq_type RACH_ConfigGeneric__root_list) * (seq_ext_type RACH_ConfigGeneric__ext_list).
Definition RACH_ConfigGeneric__list_cond (z : RACH_ConfigGeneric__list_type) : Prop :=
        (seq_cond RACH_ConfigGeneric__root_list (fst z)) /\ (seq_ext_cond RACH_ConfigGeneric__ext_list (snd z)).
Definition RACH_ConfigGeneric__list_format : T_Format RACH_ConfigGeneric__list_type RACH_ConfigGeneric__list_cond :=
 (* Eval compute in *) seq_ext_format RACH_ConfigGeneric__root_list RACH_ConfigGeneric__root_Format_list RACH_ConfigGeneric__ext_list RACH_ConfigGeneric__ext_Format_list.

Opaque RACH_ConfigGeneric__list_format.
Definition RACH_ConfigGeneric__F1 (z : RACH_ConfigGeneric__Type) : RACH_ConfigGeneric__list_type :=
  (((RACH_ConfigGeneric__prach_ConfigurationIndex z, (RACH_ConfigGeneric__msg1_FDM z, (RACH_ConfigGeneric__msg1_FrequencyStart z, (RACH_ConfigGeneric__zeroCorrelationZoneConfig z, (RACH_ConfigGeneric__preambleReceivedTargetPower z, (RACH_ConfigGeneric__preambleTransMax z, (RACH_ConfigGeneric__powerRampingStep z, (RACH_ConfigGeneric__ra_ResponseWindow z, tt))))))))), (
(RACH_ConfigGeneric__ext0 z, (RACH_ConfigGeneric__ext1 z, tt)))).
Definition RACH_ConfigGeneric__F2 (y : RACH_ConfigGeneric__list_type) : RACH_ConfigGeneric__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, (i1, _)))=>
    make__RACH_ConfigGeneric__Type j0 j1 j2 j3 j4 j5 j6 j7 i0 i1
  end.
Definition RACH_ConfigGeneric__helper1 : (forall a : RACH_ConfigGeneric__Type, RACH_ConfigGeneric__cond a -> RACH_ConfigGeneric__list_cond (RACH_ConfigGeneric__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RACH_ConfigGeneric__helper2 : (forall a : RACH_ConfigGeneric__Type, RACH_ConfigGeneric__F2 (RACH_ConfigGeneric__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RACH_ConfigGeneric__helper3 : (forall b : RACH_ConfigGeneric__list_type, RACH_ConfigGeneric__list_cond b -> RACH_ConfigGeneric__cond (RACH_ConfigGeneric__F2 b) /\ RACH_ConfigGeneric__F1 (RACH_ConfigGeneric__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RACH_ConfigGeneric__cond, RACH_ConfigGeneric__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RACH_ConfigGeneric__Format : T_Format RACH_ConfigGeneric__Type RACH_ConfigGeneric__cond :=
 proj2_format RACH_ConfigGeneric__cond RACH_ConfigGeneric__list_format  RACH_ConfigGeneric__F1 RACH_ConfigGeneric__F2 RACH_ConfigGeneric__helper1 RACH_ConfigGeneric__helper2 RACH_ConfigGeneric__helper3.

Opaque RACH_ConfigGeneric__cond RACH_ConfigGeneric__Format.

