Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SL_LogicalChannelConfig_r16__sl_Priority_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_Priority_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_LogicalChannelConfig_r16__sl_Priority_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_LogicalChannelConfig_r16__sl_Priority_r16__Type := Z.
Definition SL_LogicalChannelConfig_r16__sl_Priority_r16__cond := (fun z => (1 <= z <= 8)%Z).
Inductive SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Type : Set :=
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps0
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps8
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps16
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps32
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps64
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps128
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps256
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps512
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps1024
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps2048
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps4096
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps8192
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps16384
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps32768
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps65536
 | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__infinity
.
Definition SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__cond := (fun (_ : SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Type) => True).
Lemma SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__nat__helper.

Definition SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F1 t :=
  match t with
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps0 => 0
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps8 => 1
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps16 => 2
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps32 => 3
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps64 => 4
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps128 => 5
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps256 => 6
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps512 => 7
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps1024 => 8
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps2048 => 9
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps4096 => 10
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps8192 => 11
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps16384 => 12
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps32768 => 13
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps65536 => 14
  | SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__infinity => 15
  end.
Definition SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F2 n :=
  match n with
  | 0 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps0
  | 1 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps8
  | 2 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps16
  | 3 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps32
  | 4 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps64
  | 5 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps128
  | 6 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps256
  | 7 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps512
  | 8 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps1024
  | 9 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps2048
  | 10 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps4096
  | 11 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps8192
  | 12 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps16384
  | 13 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps32768
  | 14 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps65536
  | 15 => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__infinity
  | _ => SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__kBps0
  end.
Lemma SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F1F2 : forall x : SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Type, (SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F1 x <= 15) /\ SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F2 (SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F2F1 : forall (y : nat) (H : y <= 15), SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F1 (SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Type : Set :=
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms5
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms10
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms20
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms50
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms100
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms150
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms300
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms500
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms1000
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare7
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare6
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare5
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare4
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare3
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare2
 | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare1
.
Definition SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__cond := (fun (_ : SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Type) => True).
Lemma SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__nat__helper.

Definition SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F1 t :=
  match t with
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms5 => 0
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms10 => 1
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms20 => 2
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms50 => 3
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms100 => 4
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms150 => 5
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms300 => 6
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms500 => 7
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms1000 => 8
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare7 => 9
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare6 => 10
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare5 => 11
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare4 => 12
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare3 => 13
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare2 => 14
  | SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare1 => 15
  end.
Definition SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F2 n :=
  match n with
  | 0 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms5
  | 1 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms10
  | 2 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms20
  | 3 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms50
  | 4 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms100
  | 5 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms150
  | 6 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms300
  | 7 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms500
  | 8 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms1000
  | 9 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare7
  | 10 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare6
  | 11 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare5
  | 12 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare4
  | 13 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare3
  | 14 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare2
  | 15 => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__spare1
  | _ => SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__ms5
  end.
Lemma SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F1F2 : forall x : SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Type, (SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F1 x <= 15) /\ SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F2 (SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F2F1 : forall (y : nat) (H : y <= 15), SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F1 (SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Type : Set :=
 | SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__true
.
Definition SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__cond := (fun (_ : SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Type) => True).
Lemma SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__nat__helper.

Definition SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F1 t :=
  match t with
  | SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__true => 0
  end.
Definition SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F2 n :=
  match n with
  | 0 => SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__true
  | _ => SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__true
  end.
Lemma SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F1F2 : forall x : SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Type, (SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F1 x <= 0) /\ SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F2 (SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F2F1 : forall (y : nat) (H : y <= 0), SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F1 (SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Type : Set :=
 | SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__enabled
 | SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__disabled
.
Definition SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__cond := (fun (_ : SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Type) => True).
Lemma SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__nat__helper.

Definition SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F1 t :=
  match t with
  | SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__enabled => 0
  | SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__disabled => 1
  end.
Definition SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F2 n :=
  match n with
  | 0 => SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__enabled
  | 1 => SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__disabled
  | _ => SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__enabled
  end.
Lemma SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F1F2 : forall x : SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Type, (SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F1 x <= 1) /\ SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F2 (SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F2F1 : forall (y : nat) (H : y <= 1), SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F1 (SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_ConfigIndexCG_r16.

Opaque SL_ConfigIndexCG_r16__cond SL_ConfigIndexCG_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__Type := list SL_ConfigIndexCG_r16__Type.

Lemma SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__helper1 : (0 <= 0 <= maxNrofCG_SL_1_r16)%Z. unfold maxNrofCG_SL_1_r16.
 lia. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCG_SL_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCG_SL_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__cond (z : SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__Type) :=  (0 <= Z.of_nat (length z) <= maxNrofCG_SL_1_r16)%Z /\ (list_and SL_ConfigIndexCG_r16__cond z) .

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Definition SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__Type := list SubcarrierSpacing__Type.

Lemma SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__cond (z : SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SubcarrierSpacing__cond z) .

Inductive SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Type : Set :=
 | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p02
 | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p04
 | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p0625
 | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p125
 | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p25
 | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p5
 | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__spare2
 | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__spare1
.
Definition SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__cond := (fun (_ : SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Type) => True).
Lemma SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__nat__helper.

Definition SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F1 t :=
  match t with
  | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p02 => 0
  | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p04 => 1
  | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p0625 => 2
  | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p125 => 3
  | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p25 => 4
  | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p5 => 5
  | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__spare2 => 6
  | SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__spare1 => 7
  end.
Definition SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F2 n :=
  match n with
  | 0 => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p02
  | 1 => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p04
  | 2 => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p0625
  | 3 => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p125
  | 4 => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p25
  | 5 => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p5
  | 6 => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__spare2
  | 7 => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__spare1
  | _ => SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__ms0p02
  end.
Lemma SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F1F2 : forall x : SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Type, (SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F1 x <= 7) /\ SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F2 (SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F1 (SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F2 y) = y. enum_solve H y. Qed.

Lemma SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__helper1 : (0 <= maxLCG_ID)%Z. unfold maxLCG_ID.
 lia. Qed.
Lemma SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__helper2 : to_bit_sz (Z.to_nat (maxLCG_ID - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxLCG_ID - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__Type := Z.
Definition SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__cond := (fun z => (0 <= z <= maxLCG_ID)%Z).
Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Record SL_LogicalChannelConfig_r16__Type : Set :=
  make__SL_LogicalChannelConfig_r16__Type {
    SL_LogicalChannelConfig_r16__sl_Priority_r16 : Z ;
    SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16 : SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Type ;
    SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16 : SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Type ;
    SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16 : option SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Type ;
    SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16 : option SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Type ;
    SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16 : option SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__Type ;
    SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16 : option SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__Type ;
    SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16 : option SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Type ;
    SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16 : option Z ;
    SL_LogicalChannelConfig_r16__sl_SchedulingRequestId_r16 : option SchedulingRequestId__Type ;
    SL_LogicalChannelConfig_r16__sl_LogicalChannelSR_DelayTimerApplied_r16 : option bool ;
}.
Definition SL_LogicalChannelConfig_r16__root_list : list seq_elem := (
 Nor Z SL_LogicalChannelConfig_r16__sl_Priority_r16__cond ::
 Nor SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Type SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__cond ::
 Nor SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Type SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__cond ::
 Opt SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Type SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__cond ::
 Opt SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Type SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__cond ::
 Opt SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__Type SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__cond ::
 Opt SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__Type SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__cond ::
 Opt SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Type SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__cond ::
 Opt Z SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__cond ::
 Opt SchedulingRequestId__Type SchedulingRequestId__cond ::
 Opt bool (fun _ => True) ::
 nil).
Definition SL_LogicalChannelConfig_r16__ext_list : list typ := (
  nil).
Definition SL_LogicalChannelConfig_r16__cond (z : SL_LogicalChannelConfig_r16__Type) := 
(  SL_LogicalChannelConfig_r16__sl_Priority_r16__cond (SL_LogicalChannelConfig_r16__sl_Priority_r16 z) /\
  SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__cond (SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16 z) /\
  SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__cond (SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16 z) /\
  opt_cond SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__cond (SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16 z) /\
  opt_cond SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__cond (SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16 z) /\
  opt_cond SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__cond (SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16 z) /\
  opt_cond SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__cond (SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16 z) /\
  opt_cond SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__cond (SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16 z) /\
  opt_cond SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__cond (SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16 z) /\
  opt_cond SchedulingRequestId__cond (SL_LogicalChannelConfig_r16__sl_SchedulingRequestId_r16 z) /\
  opt_cond (fun _ => True) (SL_LogicalChannelConfig_r16__sl_LogicalChannelSR_DelayTimerApplied_r16 z) /\
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
Definition SL_LogicalChannelConfig_r16__sl_Priority_r16__Format : T_Format Z SL_LogicalChannelConfig_r16__sl_Priority_r16__cond :=
 ranged_int_format (1) (8) SL_LogicalChannelConfig_r16__sl_Priority_r16__helper1 SL_LogicalChannelConfig_r16__sl_Priority_r16__helper2.

Opaque SL_LogicalChannelConfig_r16__sl_Priority_r16__cond SL_LogicalChannelConfig_r16__sl_Priority_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Format : T_Format SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__nat__Format SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F1 SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F2 SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F1F2 SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__F2F1.

Opaque SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__cond SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Format : T_Format SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__nat__Format SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F1 SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F2 SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F1F2 SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__F2F1.

Opaque SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__cond SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Format : T_Format SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__nat__Format SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F1 SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F2 SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F1F2 SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__F2F1.

Opaque SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__cond SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Format : T_Format SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__nat__Format SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F1 SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F2 SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F1F2 SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__F2F1.

Opaque SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__cond SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__Format : T_Format SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__Type SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__cond := seq_of_format SL_ConfigIndexCG_r16__Format 0 maxNrofCG_SL_1_r16 SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__helper1 SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__helper2.

Opaque SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__cond SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__Format : T_Format SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__Type SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__cond := seq_of_format SubcarrierSpacing__Format 1 maxSCSs SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__helper1 SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__helper2.

Opaque SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__cond SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Format : T_Format SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__nat__Format SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F1 SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F2 SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F1F2 SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__F2F1.

Opaque SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__cond SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Format.

Definition SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__Format : T_Format Z SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__cond :=
 ranged_int_format (0) (maxLCG_ID) SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__helper1 SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__helper2.

Opaque SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__cond SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__Format.


Definition SL_LogicalChannelConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_LogicalChannelConfig_r16__root_list.
Definition SL_LogicalChannelConfig_r16__root_Format_list : SL_LogicalChannelConfig_r16__root_Format_Type :=
  (SL_LogicalChannelConfig_r16__sl_Priority_r16__Format, (SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16__Format, (SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16__Format, (SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16__Format, (SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16__Format, (SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16__Format, (SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16__Format, (SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16__Format, (SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16__Format, (SchedulingRequestId__Format, (bool__Format, unit_format))))))))))).

Definition SL_LogicalChannelConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_LogicalChannelConfig_r16__ext_list.
Definition SL_LogicalChannelConfig_r16__ext_Format_list : SL_LogicalChannelConfig_r16__ext_Format_Type :=
  unit__Format.

Definition SL_LogicalChannelConfig_r16__list_type : Set := (seq_type SL_LogicalChannelConfig_r16__root_list) * (seq_ext_type SL_LogicalChannelConfig_r16__ext_list).
Definition SL_LogicalChannelConfig_r16__list_cond (z : SL_LogicalChannelConfig_r16__list_type) : Prop :=
        (seq_cond SL_LogicalChannelConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_LogicalChannelConfig_r16__ext_list (snd z)).
Definition SL_LogicalChannelConfig_r16__list_format : T_Format SL_LogicalChannelConfig_r16__list_type SL_LogicalChannelConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_LogicalChannelConfig_r16__root_list SL_LogicalChannelConfig_r16__root_Format_list SL_LogicalChannelConfig_r16__ext_list SL_LogicalChannelConfig_r16__ext_Format_list.

Opaque SL_LogicalChannelConfig_r16__list_format.
Definition SL_LogicalChannelConfig_r16__F1 (z : SL_LogicalChannelConfig_r16__Type) : SL_LogicalChannelConfig_r16__list_type :=
  (((SL_LogicalChannelConfig_r16__sl_Priority_r16 z, (SL_LogicalChannelConfig_r16__sl_PrioritisedBitRate_r16 z, (SL_LogicalChannelConfig_r16__sl_BucketSizeDuration_r16 z, (SL_LogicalChannelConfig_r16__sl_ConfiguredGrantType1Allowed_r16 z, (SL_LogicalChannelConfig_r16__sl_HARQ_FeedbackEnabled_r16 z, (SL_LogicalChannelConfig_r16__sl_AllowedCG_List_r16 z, (SL_LogicalChannelConfig_r16__sl_AllowedSCS_List_r16 z, (SL_LogicalChannelConfig_r16__sl_MaxPUSCH_Duration_r16 z, (SL_LogicalChannelConfig_r16__sl_LogicalChannelGroup_r16 z, (SL_LogicalChannelConfig_r16__sl_SchedulingRequestId_r16 z, (SL_LogicalChannelConfig_r16__sl_LogicalChannelSR_DelayTimerApplied_r16 z, tt)))))))))))), (
tt)).
Definition SL_LogicalChannelConfig_r16__F2 (y : SL_LogicalChannelConfig_r16__list_type) : SL_LogicalChannelConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, _))))))))))), _)=>
    make__SL_LogicalChannelConfig_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10
  end.
Definition SL_LogicalChannelConfig_r16__helper1 : (forall a : SL_LogicalChannelConfig_r16__Type, SL_LogicalChannelConfig_r16__cond a -> SL_LogicalChannelConfig_r16__list_cond (SL_LogicalChannelConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_LogicalChannelConfig_r16__helper2 : (forall a : SL_LogicalChannelConfig_r16__Type, SL_LogicalChannelConfig_r16__F2 (SL_LogicalChannelConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_LogicalChannelConfig_r16__helper3 : (forall b : SL_LogicalChannelConfig_r16__list_type, SL_LogicalChannelConfig_r16__list_cond b -> SL_LogicalChannelConfig_r16__cond (SL_LogicalChannelConfig_r16__F2 b) /\ SL_LogicalChannelConfig_r16__F1 (SL_LogicalChannelConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_LogicalChannelConfig_r16__cond, SL_LogicalChannelConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_LogicalChannelConfig_r16__Format : T_Format SL_LogicalChannelConfig_r16__Type SL_LogicalChannelConfig_r16__cond :=
 proj2_format SL_LogicalChannelConfig_r16__cond SL_LogicalChannelConfig_r16__list_format  SL_LogicalChannelConfig_r16__F1 SL_LogicalChannelConfig_r16__F2 SL_LogicalChannelConfig_r16__helper1 SL_LogicalChannelConfig_r16__helper2 SL_LogicalChannelConfig_r16__helper3.

Opaque SL_LogicalChannelConfig_r16__cond SL_LogicalChannelConfig_r16__Format.

