Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FeatureCombination_r17.

Opaque FeatureCombination_r17__cond FeatureCombination_r17__Format.

Lemma FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__Type := Z.
Definition FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__cond := (fun z => (0 <= z <= 63)%Z).
Lemma FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__Type := Z.
Definition FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__cond := (fun z => (1 <= z <= 64)%Z).
Lemma FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__Type := Z.
Definition FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__cond := (fun z => (1 <= z <= 15)%Z).
Inductive FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Type : Set :=
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b56
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b144
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b208
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b256
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b282
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b480
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b640
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b800
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b1000
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b72
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare6
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare5
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare4
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare3
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare2
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare1
.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__cond := (fun (_ : FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Type) => True).
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__nat__helper.

Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F1 t :=
  match t with
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b56 => 0
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b144 => 1
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b208 => 2
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b256 => 3
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b282 => 4
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b480 => 5
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b640 => 6
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b800 => 7
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b1000 => 8
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b72 => 9
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare6 => 10
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare5 => 11
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare4 => 12
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare3 => 13
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare2 => 14
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare1 => 15
  end.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F2 n :=
  match n with
  | 0 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b56
  | 1 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b144
  | 2 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b208
  | 3 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b256
  | 4 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b282
  | 5 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b480
  | 6 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b640
  | 7 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b800
  | 8 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b1000
  | 9 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b72
  | 10 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare6
  | 11 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare5
  | 12 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare4
  | 13 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare3
  | 14 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare2
  | 15 => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__spare1
  | _ => FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__b56
  end.
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F1F2 : forall x : FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Type, (FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F1 x <= 15) /\ FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F2 (FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F2F1 : forall (y : nat) (H : y <= 15), FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F1 (FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Type : Set :=
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__minusinfinity
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB0
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB5
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB8
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB10
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB12
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB15
 | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB18
.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__cond := (fun (_ : FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Type) => True).
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__nat__helper.

Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F1 t :=
  match t with
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__minusinfinity => 0
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB0 => 1
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB5 => 2
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB8 => 3
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB10 => 4
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB12 => 5
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB15 => 6
  | FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB18 => 7
  end.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F2 n :=
  match n with
  | 0 => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__minusinfinity
  | 1 => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB0
  | 2 => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB5
  | 3 => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB8
  | 4 => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB10
  | 5 => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB12
  | 6 => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB15
  | 7 => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__dB18
  | _ => FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__minusinfinity
  end.
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F1F2 : forall x : FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Type, (FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F1 x <= 7) /\ FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F2 (FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F1 x) = x. imp_solve. Qed.
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F2F1 : forall (y : nat) (H : y <= 7), FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F1 (FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F2 y) = y. enum_solve H y. Qed.

Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__Type := Z.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__cond := (fun z => (1 <= z <= 64)%Z).
Record FeatureCombinationPreambles_r17__groupBconfigured_r17__Type : Set :=
  make__FeatureCombinationPreambles_r17__groupBconfigured_r17__Type {
    FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17 : FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Type ;
    FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17 : FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Type ;
    FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17 : Z ;
}.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__list := (
 Nor FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Type FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__cond ::
 Nor FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Type FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__cond ::
 Nor Z FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__cond ::
 nil).
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__cond z := 
  FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__cond (FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17 z) /\
  FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__cond (FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17 z) /\
  FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__cond (FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17 z) /\
  True.

Require Import NR.MsgA_PUSCH_Config_r16.

Opaque MsgA_PUSCH_Config_r16__cond MsgA_PUSCH_Config_r16__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Lemma FeatureCombinationPreambles_r17__deltaPreamble_r17__helper1 : (-1 <= 6)%Z.  lia. Qed.
Lemma FeatureCombinationPreambles_r17__deltaPreamble_r17__helper2 : to_bit_sz (Z.to_nat (6 - -1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - -1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureCombinationPreambles_r17__deltaPreamble_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureCombinationPreambles_r17__deltaPreamble_r17__Type := Z.
Definition FeatureCombinationPreambles_r17__deltaPreamble_r17__cond := (fun z => (-1 <= z <= 6)%Z).
Record FeatureCombinationPreambles_r17__Type : Set :=
  make__FeatureCombinationPreambles_r17__Type {
    FeatureCombinationPreambles_r17__featureCombination_r17 : FeatureCombination_r17__Type ;
    FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17 : Z ;
    FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17 : Z ;
    FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17 : option Z ;
    FeatureCombinationPreambles_r17__groupBconfigured_r17 : option FeatureCombinationPreambles_r17__groupBconfigured_r17__Type ;
    FeatureCombinationPreambles_r17__separateMsgA_PUSCH_Config_r17 : option MsgA_PUSCH_Config_r16__Type ;
    FeatureCombinationPreambles_r17__msgA_RSRP_Threshold_r17 : option RSRP_Range__Type ;
    FeatureCombinationPreambles_r17__rsrp_ThresholdSSB_r17 : option RSRP_Range__Type ;
    FeatureCombinationPreambles_r17__deltaPreamble_r17 : option Z ;
}.
Definition FeatureCombinationPreambles_r17__root_list : list seq_elem := (
 Nor FeatureCombination_r17__Type FeatureCombination_r17__cond ::
 Nor Z FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__cond ::
 Nor Z FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__cond ::
 Opt Z FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__cond ::
 Opt FeatureCombinationPreambles_r17__groupBconfigured_r17__Type FeatureCombinationPreambles_r17__groupBconfigured_r17__cond ::
 Opt MsgA_PUSCH_Config_r16__Type MsgA_PUSCH_Config_r16__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt Z FeatureCombinationPreambles_r17__deltaPreamble_r17__cond ::
 nil).
Definition FeatureCombinationPreambles_r17__ext_list : list typ := (
  nil).
Definition FeatureCombinationPreambles_r17__cond (z : FeatureCombinationPreambles_r17__Type) := 
(  FeatureCombination_r17__cond (FeatureCombinationPreambles_r17__featureCombination_r17 z) /\
  FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__cond (FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17 z) /\
  FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__cond (FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17 z) /\
  opt_cond FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__cond (FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17 z) /\
  opt_cond FeatureCombinationPreambles_r17__groupBconfigured_r17__cond (FeatureCombinationPreambles_r17__groupBconfigured_r17 z) /\
  opt_cond MsgA_PUSCH_Config_r16__cond (FeatureCombinationPreambles_r17__separateMsgA_PUSCH_Config_r17 z) /\
  opt_cond RSRP_Range__cond (FeatureCombinationPreambles_r17__msgA_RSRP_Threshold_r17 z) /\
  opt_cond RSRP_Range__cond (FeatureCombinationPreambles_r17__rsrp_ThresholdSSB_r17 z) /\
  opt_cond FeatureCombinationPreambles_r17__deltaPreamble_r17__cond (FeatureCombinationPreambles_r17__deltaPreamble_r17 z) /\
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
Definition FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__Format : T_Format Z FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__cond :=
 ranged_int_format (0) (63) FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__helper1 FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__helper2.

Opaque FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__cond FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__Format.

Definition FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__Format : T_Format Z FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__cond :=
 ranged_int_format (1) (64) FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__helper1 FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__helper2.

Opaque FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__cond FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__Format.

Definition FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__Format : T_Format Z FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__cond :=
 ranged_int_format (1) (15) FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__helper1 FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__helper2.

Opaque FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__cond FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__Format.

Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Format : T_Format FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__nat__Format FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F1 FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F2 FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F1F2 FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__F2F1.

Opaque FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__cond FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Format.

Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Format : T_Format FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__nat__Format FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F1 FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F2 FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F1F2 FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__F2F1.

Opaque FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__cond FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Format.

Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__Format : T_Format Z FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__cond :=
 ranged_int_format (1) (64) FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__helper1 FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__helper2.

Opaque FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__cond FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__Format.


Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__Format_Type := Eval cbn in seq_format_prod FeatureCombinationPreambles_r17__groupBconfigured_r17__list.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__Format_list : FeatureCombinationPreambles_r17__groupBconfigured_r17__Format_Type :=
  (FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17__Format, (FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17__Format, (FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17__Format, unit_format))).
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__list__Format := (*Eval compute in *) seq_format FeatureCombinationPreambles_r17__groupBconfigured_r17__list FeatureCombinationPreambles_r17__groupBconfigured_r17__Format_list.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__F1 z :=
  (FeatureCombinationPreambles_r17__groupBconfigured_r17__ra_SizeGroupA_r17 z, (FeatureCombinationPreambles_r17__groupBconfigured_r17__messagePowerOffsetGroupB_r17 z, (FeatureCombinationPreambles_r17__groupBconfigured_r17__numberOfRA_PreamblesGroupA_r17 z, tt))).
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__F2 (y : seq_type FeatureCombinationPreambles_r17__groupBconfigured_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FeatureCombinationPreambles_r17__groupBconfigured_r17__Type i0 i1 i2
  end.
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__F1F2_cond (z : FeatureCombinationPreambles_r17__groupBconfigured_r17__Type)
  : FeatureCombinationPreambles_r17__groupBconfigured_r17__cond z ->
  (seq_cond FeatureCombinationPreambles_r17__groupBconfigured_r17__list (FeatureCombinationPreambles_r17__groupBconfigured_r17__F1 z)).
intro H. unfold FeatureCombinationPreambles_r17__groupBconfigured_r17__cond in H. simpl. auto. Qed.
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__F1F2_cond2 (z : FeatureCombinationPreambles_r17__groupBconfigured_r17__Type)
 : FeatureCombinationPreambles_r17__groupBconfigured_r17__F2 (FeatureCombinationPreambles_r17__groupBconfigured_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureCombinationPreambles_r17__groupBconfigured_r17__F2F1_cond (y : seq_type FeatureCombinationPreambles_r17__groupBconfigured_r17__list)
  : seq_cond FeatureCombinationPreambles_r17__groupBconfigured_r17__list y ->
 (FeatureCombinationPreambles_r17__groupBconfigured_r17__cond (FeatureCombinationPreambles_r17__groupBconfigured_r17__F2 y)) /\  FeatureCombinationPreambles_r17__groupBconfigured_r17__F1 (FeatureCombinationPreambles_r17__groupBconfigured_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureCombinationPreambles_r17__groupBconfigured_r17__cond. simpl in *. auto.
 - simpl. unfold FeatureCombinationPreambles_r17__groupBconfigured_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureCombinationPreambles_r17__groupBconfigured_r17__Format : T_Format FeatureCombinationPreambles_r17__groupBconfigured_r17__Type FeatureCombinationPreambles_r17__groupBconfigured_r17__cond :=
        proj2_format  FeatureCombinationPreambles_r17__groupBconfigured_r17__cond FeatureCombinationPreambles_r17__groupBconfigured_r17__list__Format
    FeatureCombinationPreambles_r17__groupBconfigured_r17__F1 FeatureCombinationPreambles_r17__groupBconfigured_r17__F2 FeatureCombinationPreambles_r17__groupBconfigured_r17__F1F2_cond  FeatureCombinationPreambles_r17__groupBconfigured_r17__F1F2_cond2 FeatureCombinationPreambles_r17__groupBconfigured_r17__F2F1_cond.
Opaque FeatureCombinationPreambles_r17__groupBconfigured_r17__cond FeatureCombinationPreambles_r17__groupBconfigured_r17__Format.

Definition FeatureCombinationPreambles_r17__deltaPreamble_r17__Format : T_Format Z FeatureCombinationPreambles_r17__deltaPreamble_r17__cond :=
 ranged_int_format (-1) (6) FeatureCombinationPreambles_r17__deltaPreamble_r17__helper1 FeatureCombinationPreambles_r17__deltaPreamble_r17__helper2.

Opaque FeatureCombinationPreambles_r17__deltaPreamble_r17__cond FeatureCombinationPreambles_r17__deltaPreamble_r17__Format.


Definition FeatureCombinationPreambles_r17__root_Format_Type := Eval cbn in seq_format_prod FeatureCombinationPreambles_r17__root_list.
Definition FeatureCombinationPreambles_r17__root_Format_list : FeatureCombinationPreambles_r17__root_Format_Type :=
  (FeatureCombination_r17__Format, (FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17__Format, (FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17__Format, (FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17__Format, (FeatureCombinationPreambles_r17__groupBconfigured_r17__Format, (MsgA_PUSCH_Config_r16__Format, (RSRP_Range__Format, (RSRP_Range__Format, (FeatureCombinationPreambles_r17__deltaPreamble_r17__Format, unit_format))))))))).

Definition FeatureCombinationPreambles_r17__ext_Format_Type := Eval cbn in get_formats FeatureCombinationPreambles_r17__ext_list.
Definition FeatureCombinationPreambles_r17__ext_Format_list : FeatureCombinationPreambles_r17__ext_Format_Type :=
  unit__Format.

Definition FeatureCombinationPreambles_r17__list_type : Set := (seq_type FeatureCombinationPreambles_r17__root_list) * (seq_ext_type FeatureCombinationPreambles_r17__ext_list).
Definition FeatureCombinationPreambles_r17__list_cond (z : FeatureCombinationPreambles_r17__list_type) : Prop :=
        (seq_cond FeatureCombinationPreambles_r17__root_list (fst z)) /\ (seq_ext_cond FeatureCombinationPreambles_r17__ext_list (snd z)).
Definition FeatureCombinationPreambles_r17__list_format : T_Format FeatureCombinationPreambles_r17__list_type FeatureCombinationPreambles_r17__list_cond :=
 (* Eval compute in *) seq_ext_format FeatureCombinationPreambles_r17__root_list FeatureCombinationPreambles_r17__root_Format_list FeatureCombinationPreambles_r17__ext_list FeatureCombinationPreambles_r17__ext_Format_list.

Opaque FeatureCombinationPreambles_r17__list_format.
Definition FeatureCombinationPreambles_r17__F1 (z : FeatureCombinationPreambles_r17__Type) : FeatureCombinationPreambles_r17__list_type :=
  (((FeatureCombinationPreambles_r17__featureCombination_r17 z, (FeatureCombinationPreambles_r17__startPreambleForThisPartition_r17 z, (FeatureCombinationPreambles_r17__numberOfPreamblesPerSSB_ForThisPartition_r17 z, (FeatureCombinationPreambles_r17__ssb_SharedRO_MaskIndex_r17 z, (FeatureCombinationPreambles_r17__groupBconfigured_r17 z, (FeatureCombinationPreambles_r17__separateMsgA_PUSCH_Config_r17 z, (FeatureCombinationPreambles_r17__msgA_RSRP_Threshold_r17 z, (FeatureCombinationPreambles_r17__rsrp_ThresholdSSB_r17 z, (FeatureCombinationPreambles_r17__deltaPreamble_r17 z, tt)))))))))), (
tt)).
Definition FeatureCombinationPreambles_r17__F2 (y : FeatureCombinationPreambles_r17__list_type) : FeatureCombinationPreambles_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), _)=>
    make__FeatureCombinationPreambles_r17__Type j0 j1 j2 j3 j4 j5 j6 j7 j8
  end.
Definition FeatureCombinationPreambles_r17__helper1 : (forall a : FeatureCombinationPreambles_r17__Type, FeatureCombinationPreambles_r17__cond a -> FeatureCombinationPreambles_r17__list_cond (FeatureCombinationPreambles_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition FeatureCombinationPreambles_r17__helper2 : (forall a : FeatureCombinationPreambles_r17__Type, FeatureCombinationPreambles_r17__F2 (FeatureCombinationPreambles_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition FeatureCombinationPreambles_r17__helper3 : (forall b : FeatureCombinationPreambles_r17__list_type, FeatureCombinationPreambles_r17__list_cond b -> FeatureCombinationPreambles_r17__cond (FeatureCombinationPreambles_r17__F2 b) /\ FeatureCombinationPreambles_r17__F1 (FeatureCombinationPreambles_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold FeatureCombinationPreambles_r17__cond, FeatureCombinationPreambles_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition FeatureCombinationPreambles_r17__Format : T_Format FeatureCombinationPreambles_r17__Type FeatureCombinationPreambles_r17__cond :=
 proj2_format FeatureCombinationPreambles_r17__cond FeatureCombinationPreambles_r17__list_format  FeatureCombinationPreambles_r17__F1 FeatureCombinationPreambles_r17__F2 FeatureCombinationPreambles_r17__helper1 FeatureCombinationPreambles_r17__helper2 FeatureCombinationPreambles_r17__helper3.

Opaque FeatureCombinationPreambles_r17__cond FeatureCombinationPreambles_r17__Format.

