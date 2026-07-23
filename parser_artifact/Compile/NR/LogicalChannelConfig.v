Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma LogicalChannelConfig__ul_SpecificParameters__priority__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__priority__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply LogicalChannelConfig__ul_SpecificParameters__priority__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__priority__Type := Z.
Definition LogicalChannelConfig__ul_SpecificParameters__priority__cond := (fun z => (1 <= z <= 16)%Z).
Inductive LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Type : Set :=
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps0
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps8
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps16
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps32
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps64
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps128
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps256
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps512
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps1024
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps2048
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps4096
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps8192
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps16384
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps32768
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps65536
 | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__infinity
.
Definition LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__cond := (fun (_ : LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Type) => True).
Lemma LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__nat__helper.

Definition LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F1 t :=
  match t with
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps0 => 0
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps8 => 1
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps16 => 2
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps32 => 3
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps64 => 4
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps128 => 5
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps256 => 6
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps512 => 7
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps1024 => 8
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps2048 => 9
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps4096 => 10
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps8192 => 11
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps16384 => 12
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps32768 => 13
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps65536 => 14
  | LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__infinity => 15
  end.
Definition LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F2 n :=
  match n with
  | 0 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps0
  | 1 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps8
  | 2 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps16
  | 3 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps32
  | 4 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps64
  | 5 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps128
  | 6 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps256
  | 7 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps512
  | 8 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps1024
  | 9 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps2048
  | 10 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps4096
  | 11 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps8192
  | 12 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps16384
  | 13 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps32768
  | 14 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps65536
  | 15 => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__infinity
  | _ => LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__kBps0
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F1F2 : forall x : LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Type, (LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F1 x <= 15) /\ LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F2 (LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F1 x) = x. imp_solve. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F2F1 : forall (y : nat) (H : y <= 15), LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F1 (LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F2 y) = y. enum_solve H y. Qed.

Inductive LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Type : Set :=
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms5
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms10
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms20
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms50
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms100
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms150
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms300
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms500
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms1000
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare7
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare6
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare5
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare4
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare3
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare2
 | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare1
.
Definition LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__cond := (fun (_ : LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Type) => True).
Lemma LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__nat__helper.

Definition LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F1 t :=
  match t with
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms5 => 0
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms10 => 1
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms20 => 2
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms50 => 3
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms100 => 4
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms150 => 5
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms300 => 6
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms500 => 7
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms1000 => 8
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare7 => 9
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare6 => 10
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare5 => 11
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare4 => 12
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare3 => 13
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare2 => 14
  | LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare1 => 15
  end.
Definition LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F2 n :=
  match n with
  | 0 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms5
  | 1 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms10
  | 2 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms20
  | 3 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms50
  | 4 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms100
  | 5 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms150
  | 6 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms300
  | 7 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms500
  | 8 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms1000
  | 9 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare7
  | 10 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare6
  | 11 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare5
  | 12 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare4
  | 13 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare3
  | 14 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare2
  | 15 => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__spare1
  | _ => LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__ms5
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F1F2 : forall x : LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Type, (LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F1 x <= 15) /\ LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F2 (LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F1 x) = x. imp_solve. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F2F1 : forall (y : nat) (H : y <= 15), LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F1 (LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__Type := list ServCellIndex__Type.

Lemma LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__helper1 : (0 <= 1 <= maxNrofServingCells_1)%Z. unfold maxNrofServingCells_1.
 lia. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__cond (z : LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofServingCells_1)%Z /\ (list_and ServCellIndex__cond z) .

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__Type := list SubcarrierSpacing__Type.

Lemma LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__helper1 : (0 <= 1 <= maxSCSs)%Z. unfold maxSCSs.
 lia. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__helper2 : to_bit_sz (Z.to_nat (maxSCSs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSCSs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__cond (z : LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__Type) :=  (1 <= Z.of_nat (length z) <= maxSCSs)%Z /\ (list_and SubcarrierSpacing__cond z) .

Inductive LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Type : Set :=
 | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p02
 | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p04
 | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p0625
 | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p125
 | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p25
 | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p5
 | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p01_v1700
 | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__spare1
.
Definition LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__cond := (fun (_ : LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Type) => True).
Lemma LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__nat__helper.

Definition LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F1 t :=
  match t with
  | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p02 => 0
  | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p04 => 1
  | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p0625 => 2
  | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p125 => 3
  | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p25 => 4
  | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p5 => 5
  | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p01_v1700 => 6
  | LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__spare1 => 7
  end.
Definition LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F2 n :=
  match n with
  | 0 => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p02
  | 1 => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p04
  | 2 => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p0625
  | 3 => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p125
  | 4 => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p25
  | 5 => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p5
  | 6 => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p01_v1700
  | 7 => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__spare1
  | _ => LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__ms0p02
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F1F2 : forall x : LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Type, (LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F1 x <= 7) /\ LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F2 (LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F1 x) = x. imp_solve. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F2F1 : forall (y : nat) (H : y <= 7), LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F1 (LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F2 y) = y. enum_solve H y. Qed.

Inductive LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Type : Set :=
 | LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__true
.
Definition LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__cond := (fun (_ : LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Type) => True).
Lemma LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__nat__helper.

Definition LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F1 t :=
  match t with
  | LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__true => 0
  end.
Definition LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F2 n :=
  match n with
  | 0 => LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__true
  | _ => LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__true
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F1F2 : forall x : LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Type, (LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F1 x <= 0) /\ LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F2 (LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F1 x) = x. imp_solve. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F2F1 : forall (y : nat) (H : y <= 0), LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F1 (LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F2 y) = y. enum_solve H y. Qed.

Lemma LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__helper1 : (0 <= maxLCG_ID)%Z. unfold maxLCG_ID.
 lia. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__helper2 : to_bit_sz (Z.to_nat (maxLCG_ID - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxLCG_ID - 0))%Z). { apply Zorder.Zle_minus_le_0. apply LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__Type := Z.
Definition LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__cond := (fun z => (0 <= z <= maxLCG_ID)%Z).
Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Inductive LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Type : Set :=
 | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0
 | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0dot4
 | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0dot8
 | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s1dot6
 | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s3
 | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s6
 | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s12
 | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s30
.
Definition LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__cond := (fun (_ : LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Type) => True).
Lemma LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__nat__helper.

Definition LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F1 t :=
  match t with
  | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0 => 0
  | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0dot4 => 1
  | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0dot8 => 2
  | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s1dot6 => 3
  | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s3 => 4
  | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s6 => 5
  | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s12 => 6
  | LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s30 => 7
  end.
Definition LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F2 n :=
  match n with
  | 0 => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0
  | 1 => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0dot4
  | 2 => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0dot8
  | 3 => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s1dot6
  | 4 => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s3
  | 5 => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s6
  | 6 => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s12
  | 7 => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s30
  | _ => LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__s0
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F1F2 : forall x : LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Type, (LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F1 x <= 7) /\ LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F2 (LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F1 x) = x. imp_solve. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F2F1 : forall (y : nat) (H : y <= 7), LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F1 (LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ConfiguredGrantConfigIndexMAC_r16.

Opaque ConfiguredGrantConfigIndexMAC_r16__cond ConfiguredGrantConfigIndexMAC_r16__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__Type := list ConfiguredGrantConfigIndexMAC_r16__Type.

Lemma LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__helper1 : (0 <= 0 <= maxNrofConfiguredGrantConfigMAC_1_r16)%Z. unfold maxNrofConfiguredGrantConfigMAC_1_r16.
 lia. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofConfiguredGrantConfigMAC_1_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofConfiguredGrantConfigMAC_1_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__cond (z : LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__Type) :=  (0 <= Z.of_nat (length z) <= maxNrofConfiguredGrantConfigMAC_1_r16)%Z /\ (list_and ConfiguredGrantConfigIndexMAC_r16__cond z) .

Inductive LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Type : Set :=
 | LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__p0
 | LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__p1
.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__cond := (fun (_ : LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Type) => True).
Lemma LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__nat__helper.

Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F1 t :=
  match t with
  | LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__p0 => 0
  | LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__p1 => 1
  end.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F2 n :=
  match n with
  | 0 => LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__p0
  | 1 => LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__p1
  | _ => LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__p0
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F1F2 : forall x : LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Type, (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F1 x <= 1) /\ LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F2 (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F1 x) = x. imp_solve. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F2F1 : forall (y : nat) (H : y <= 1), LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F1 (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F2 y) = y. enum_solve H y. Qed.

Record LogicalChannelConfig__ul_SpecificParameters__ext1O__Type : Set :=
  make__LogicalChannelConfig__ul_SpecificParameters__ext1O__Type {
    LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16 : option LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__Type ;
    LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16 : option LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Type ;
}.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__list := (
 Opt LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__Type LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__cond ::
 Opt LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Type LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__cond ::
 nil).
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__cond z := 
  opt_cond LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__cond (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16 z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__cond (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16 z) /\
  True.

Definition LogicalChannelConfig__ul_SpecificParameters__ext1__Type := LogicalChannelConfig__ul_SpecificParameters__ext1O__Type.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1__cond := LogicalChannelConfig__ul_SpecificParameters__ext1O__cond.

Lemma LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__helper1 : (0 <= maxLCG_ID_IAB_r17)%Z. unfold maxLCG_ID_IAB_r17.
 lia. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__helper2 : to_bit_sz (Z.to_nat (maxLCG_ID_IAB_r17 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxLCG_ID_IAB_r17 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__Type := Z.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__cond := (fun z => (0 <= z <= maxLCG_ID_IAB_r17)%Z).
Inductive LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Type : Set :=
 | LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__harqModeA
 | LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__harqModeB
.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__cond := (fun (_ : LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Type) => True).
Lemma LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__nat__helper.

Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F1 t :=
  match t with
  | LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__harqModeA => 0
  | LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__harqModeB => 1
  end.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F2 n :=
  match n with
  | 0 => LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__harqModeA
  | 1 => LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__harqModeB
  | _ => LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__harqModeA
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F1F2 : forall x : LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Type, (LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F1 x <= 1) /\ LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F2 (LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F1 x) = x. imp_solve. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F2F1 : forall (y : nat) (H : y <= 1), LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F1 (LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F2 y) = y. enum_solve H y. Qed.

Record LogicalChannelConfig__ul_SpecificParameters__ext2O__Type : Set :=
  make__LogicalChannelConfig__ul_SpecificParameters__ext2O__Type {
    LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17 : option Z ;
    LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17 : option LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Type ;
}.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__list := (
 Opt Z LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__cond ::
 Opt LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Type LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__cond ::
 nil).
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__cond z := 
  opt_cond LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__cond (LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17 z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__cond (LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17 z) /\
  True.

Definition LogicalChannelConfig__ul_SpecificParameters__ext2__Type := LogicalChannelConfig__ul_SpecificParameters__ext2O__Type.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2__cond := LogicalChannelConfig__ul_SpecificParameters__ext2O__cond.

Record LogicalChannelConfig__ul_SpecificParameters__Type : Set :=
  make__LogicalChannelConfig__ul_SpecificParameters__Type {
    LogicalChannelConfig__ul_SpecificParameters__priority : Z ;
    LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate : LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Type ;
    LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration : LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Type ;
    LogicalChannelConfig__ul_SpecificParameters__allowedServingCells : option LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__Type ;
    LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List : option LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__Type ;
    LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration : option LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Type ;
    LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed : option LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Type ;
    LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup : option Z ;
    LogicalChannelConfig__ul_SpecificParameters__schedulingRequestID : option SchedulingRequestId__Type ;
    LogicalChannelConfig__ul_SpecificParameters__logicalChannelSR_Mask : bool ;
    LogicalChannelConfig__ul_SpecificParameters__logicalChannelSR_DelayTimerApplied : bool ;
    LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer : option LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Type ;
    LogicalChannelConfig__ul_SpecificParameters__ext1 : option LogicalChannelConfig__ul_SpecificParameters__ext1__Type ;
    LogicalChannelConfig__ul_SpecificParameters__ext2 : option LogicalChannelConfig__ul_SpecificParameters__ext2__Type ;
}.
Definition LogicalChannelConfig__ul_SpecificParameters__root_list : list seq_elem := (
 Nor Z LogicalChannelConfig__ul_SpecificParameters__priority__cond ::
 Nor LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Type LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__cond ::
 Nor LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Type LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__cond ::
 Opt LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__Type LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__cond ::
 Opt LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__Type LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__cond ::
 Opt LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Type LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__cond ::
 Opt LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Type LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__cond ::
 Opt Z LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__cond ::
 Opt SchedulingRequestId__Type SchedulingRequestId__cond ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 nil).
Definition LogicalChannelConfig__ul_SpecificParameters__ext_list : list typ := (
  typ_cons LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Type LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__cond ::
  typ_cons LogicalChannelConfig__ul_SpecificParameters__ext1__Type LogicalChannelConfig__ul_SpecificParameters__ext1__cond ::
  typ_cons LogicalChannelConfig__ul_SpecificParameters__ext2__Type LogicalChannelConfig__ul_SpecificParameters__ext2__cond ::
  nil).
Definition LogicalChannelConfig__ul_SpecificParameters__cond (z : LogicalChannelConfig__ul_SpecificParameters__Type) := 
(  LogicalChannelConfig__ul_SpecificParameters__priority__cond (LogicalChannelConfig__ul_SpecificParameters__priority z) /\
  LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__cond (LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate z) /\
  LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__cond (LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__cond (LogicalChannelConfig__ul_SpecificParameters__allowedServingCells z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__cond (LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__cond (LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__cond (LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__cond (LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup z) /\
  opt_cond SchedulingRequestId__cond (LogicalChannelConfig__ul_SpecificParameters__schedulingRequestID z) /\
  (fun _ => True) (LogicalChannelConfig__ul_SpecificParameters__logicalChannelSR_Mask z) /\
  (fun _ => True) (LogicalChannelConfig__ul_SpecificParameters__logicalChannelSR_DelayTimerApplied z) /\
  True) /\ 
(  opt_cond LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__cond (LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__ext1__cond (LogicalChannelConfig__ul_SpecificParameters__ext1 z) /\
  opt_cond LogicalChannelConfig__ul_SpecificParameters__ext2__cond (LogicalChannelConfig__ul_SpecificParameters__ext2 z) /\
  True).

Lemma LogicalChannelConfig__ext0O__channelAccessPriority_r16__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma LogicalChannelConfig__ext0O__channelAccessPriority_r16__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply LogicalChannelConfig__ext0O__channelAccessPriority_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition LogicalChannelConfig__ext0O__channelAccessPriority_r16__Type := Z.
Definition LogicalChannelConfig__ext0O__channelAccessPriority_r16__cond := (fun z => (1 <= z <= 4)%Z).
Inductive LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Type : Set :=
 | LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x40
 | LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x70
 | LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x100
 | LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x200
.
Definition LogicalChannelConfig__ext0O__bitRateMultiplier_r16__cond := (fun (_ : LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Type) => True).
Lemma LogicalChannelConfig__ext0O__bitRateMultiplier_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition LogicalChannelConfig__ext0O__bitRateMultiplier_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 LogicalChannelConfig__ext0O__bitRateMultiplier_r16__nat__helper.

Definition LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F1 t :=
  match t with
  | LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x40 => 0
  | LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x70 => 1
  | LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x100 => 2
  | LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x200 => 3
  end.
Definition LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F2 n :=
  match n with
  | 0 => LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x40
  | 1 => LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x70
  | 2 => LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x100
  | 3 => LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x200
  | _ => LogicalChannelConfig__ext0O__bitRateMultiplier_r16__x40
  end.
Lemma LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F1F2 : forall x : LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Type, (LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F1 x <= 3) /\ LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F2 (LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F1 x) = x. imp_solve. Qed.
Lemma LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F2F1 : forall (y : nat) (H : y <= 3), LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F1 (LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F2 y) = y. enum_solve H y. Qed.

Record LogicalChannelConfig__ext0O__Type : Set :=
  make__LogicalChannelConfig__ext0O__Type {
    LogicalChannelConfig__ext0O__channelAccessPriority_r16 : option Z ;
    LogicalChannelConfig__ext0O__bitRateMultiplier_r16 : option LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Type ;
}.
Definition LogicalChannelConfig__ext0O__list := (
 Opt Z LogicalChannelConfig__ext0O__channelAccessPriority_r16__cond ::
 Opt LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Type LogicalChannelConfig__ext0O__bitRateMultiplier_r16__cond ::
 nil).
Definition LogicalChannelConfig__ext0O__cond z := 
  opt_cond LogicalChannelConfig__ext0O__channelAccessPriority_r16__cond (LogicalChannelConfig__ext0O__channelAccessPriority_r16 z) /\
  opt_cond LogicalChannelConfig__ext0O__bitRateMultiplier_r16__cond (LogicalChannelConfig__ext0O__bitRateMultiplier_r16 z) /\
  True.

Definition LogicalChannelConfig__ext0__Type := LogicalChannelConfig__ext0O__Type.
Definition LogicalChannelConfig__ext0__cond := LogicalChannelConfig__ext0O__cond.

Record LogicalChannelConfig__Type : Set :=
  make__LogicalChannelConfig__Type {
    LogicalChannelConfig__ul_SpecificParameters : option LogicalChannelConfig__ul_SpecificParameters__Type ;
    LogicalChannelConfig__ext0 : option LogicalChannelConfig__ext0__Type ;
}.
Definition LogicalChannelConfig__root_list : list seq_elem := (
 Opt LogicalChannelConfig__ul_SpecificParameters__Type LogicalChannelConfig__ul_SpecificParameters__cond ::
 nil).
Definition LogicalChannelConfig__ext_list : list typ := (
  typ_cons LogicalChannelConfig__ext0__Type LogicalChannelConfig__ext0__cond ::
  nil).
Definition LogicalChannelConfig__cond (z : LogicalChannelConfig__Type) := 
(  opt_cond LogicalChannelConfig__ul_SpecificParameters__cond (LogicalChannelConfig__ul_SpecificParameters z) /\
  True) /\ 
(  opt_cond LogicalChannelConfig__ext0__cond (LogicalChannelConfig__ext0 z) /\
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
Definition LogicalChannelConfig__ul_SpecificParameters__priority__Format : T_Format Z LogicalChannelConfig__ul_SpecificParameters__priority__cond :=
 ranged_int_format (1) (16) LogicalChannelConfig__ul_SpecificParameters__priority__helper1 LogicalChannelConfig__ul_SpecificParameters__priority__helper2.

Opaque LogicalChannelConfig__ul_SpecificParameters__priority__cond LogicalChannelConfig__ul_SpecificParameters__priority__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__nat__Format LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F1 LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F2 LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F1F2 LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__F2F1.

Opaque LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__cond LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__nat__Format LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F1 LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F2 LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F1F2 LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__F2F1.

Opaque LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__cond LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__Type LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__cond := seq_of_format ServCellIndex__Format 1 maxNrofServingCells_1 LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__helper1 LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__helper2.

Opaque LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__cond LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__Type LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__cond := seq_of_format SubcarrierSpacing__Format 1 maxSCSs LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__helper1 LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__helper2.

Opaque LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__cond LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__nat__Format LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F1 LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F2 LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F1F2 LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__F2F1.

Opaque LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__cond LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__nat__Format LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F1 LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F2 LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F1F2 LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__F2F1.

Opaque LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__cond LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__Format : T_Format Z LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__cond :=
 ranged_int_format (0) (maxLCG_ID) LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__helper1 LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__helper2.

Opaque LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__cond LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__nat__Format LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F1 LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F2 LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F1F2 LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__F2F1.

Opaque LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__cond LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__Type LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__cond := seq_of_format ConfiguredGrantConfigIndexMAC_r16__Format 0 maxNrofConfiguredGrantConfigMAC_1_r16 LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__helper1 LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__helper2.

Opaque LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__cond LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__nat__Format LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F1 LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F2 LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F1F2 LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__F2F1.

Opaque LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__cond LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Format.


Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__Format_Type := Eval cbn in seq_format_prod LogicalChannelConfig__ul_SpecificParameters__ext1O__list.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__Format_list : LogicalChannelConfig__ul_SpecificParameters__ext1O__Format_Type :=
  (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16__Format, (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16__Format, unit_format)).
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__list__Format := (*Eval compute in *) seq_format LogicalChannelConfig__ul_SpecificParameters__ext1O__list LogicalChannelConfig__ul_SpecificParameters__ext1O__Format_list.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__F1 z :=
  (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedCG_List_r16 z, (LogicalChannelConfig__ul_SpecificParameters__ext1O__allowedPHY_PriorityIndex_r16 z, tt)).
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__F2 (y : seq_type LogicalChannelConfig__ul_SpecificParameters__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__LogicalChannelConfig__ul_SpecificParameters__ext1O__Type i0 i1
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext1O__F1F2_cond (z : LogicalChannelConfig__ul_SpecificParameters__ext1O__Type)
  : LogicalChannelConfig__ul_SpecificParameters__ext1O__cond z ->
  (seq_cond LogicalChannelConfig__ul_SpecificParameters__ext1O__list (LogicalChannelConfig__ul_SpecificParameters__ext1O__F1 z)).
intro H. unfold LogicalChannelConfig__ul_SpecificParameters__ext1O__cond in H. simpl. auto. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext1O__F1F2_cond2 (z : LogicalChannelConfig__ul_SpecificParameters__ext1O__Type)
 : LogicalChannelConfig__ul_SpecificParameters__ext1O__F2 (LogicalChannelConfig__ul_SpecificParameters__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext1O__F2F1_cond (y : seq_type LogicalChannelConfig__ul_SpecificParameters__ext1O__list)
  : seq_cond LogicalChannelConfig__ul_SpecificParameters__ext1O__list y ->
 (LogicalChannelConfig__ul_SpecificParameters__ext1O__cond (LogicalChannelConfig__ul_SpecificParameters__ext1O__F2 y)) /\  LogicalChannelConfig__ul_SpecificParameters__ext1O__F1 (LogicalChannelConfig__ul_SpecificParameters__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold LogicalChannelConfig__ul_SpecificParameters__ext1O__cond. simpl in *. auto.
 - simpl. unfold LogicalChannelConfig__ul_SpecificParameters__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1O__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__ext1O__Type LogicalChannelConfig__ul_SpecificParameters__ext1O__cond :=
        proj2_format  LogicalChannelConfig__ul_SpecificParameters__ext1O__cond LogicalChannelConfig__ul_SpecificParameters__ext1O__list__Format
    LogicalChannelConfig__ul_SpecificParameters__ext1O__F1 LogicalChannelConfig__ul_SpecificParameters__ext1O__F2 LogicalChannelConfig__ul_SpecificParameters__ext1O__F1F2_cond  LogicalChannelConfig__ul_SpecificParameters__ext1O__F1F2_cond2 LogicalChannelConfig__ul_SpecificParameters__ext1O__F2F1_cond.
Opaque LogicalChannelConfig__ul_SpecificParameters__ext1O__cond LogicalChannelConfig__ul_SpecificParameters__ext1O__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__ext1__check_all_none (b : LogicalChannelConfig__ul_SpecificParameters__ext1O__Type) : bool :=
match b with 
  | make__LogicalChannelConfig__ul_SpecificParameters__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition LogicalChannelConfig__ul_SpecificParameters__ext1__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__ext1__Type LogicalChannelConfig__ul_SpecificParameters__ext1__cond :=
  restrict_add_format LogicalChannelConfig__ul_SpecificParameters__ext1__check_all_none LogicalChannelConfig__ul_SpecificParameters__ext1O__Format.

Opaque LogicalChannelConfig__ul_SpecificParameters__ext1__cond LogicalChannelConfig__ul_SpecificParameters__ext1__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__Format : T_Format Z LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__cond :=
 ranged_int_format (0) (maxLCG_ID_IAB_r17) LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__helper1 LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__helper2.

Opaque LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__cond LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__nat__Format LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F1 LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F2 LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F1F2 LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__F2F1.

Opaque LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__cond LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Format.


Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__Format_Type := Eval cbn in seq_format_prod LogicalChannelConfig__ul_SpecificParameters__ext2O__list.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__Format_list : LogicalChannelConfig__ul_SpecificParameters__ext2O__Format_Type :=
  (LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17__Format, (LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17__Format, unit_format)).
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__list__Format := (*Eval compute in *) seq_format LogicalChannelConfig__ul_SpecificParameters__ext2O__list LogicalChannelConfig__ul_SpecificParameters__ext2O__Format_list.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__F1 z :=
  (LogicalChannelConfig__ul_SpecificParameters__ext2O__logicalChannelGroupIAB_Ext_r17 z, (LogicalChannelConfig__ul_SpecificParameters__ext2O__allowedHARQ_mode_r17 z, tt)).
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__F2 (y : seq_type LogicalChannelConfig__ul_SpecificParameters__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__LogicalChannelConfig__ul_SpecificParameters__ext2O__Type i0 i1
  end.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext2O__F1F2_cond (z : LogicalChannelConfig__ul_SpecificParameters__ext2O__Type)
  : LogicalChannelConfig__ul_SpecificParameters__ext2O__cond z ->
  (seq_cond LogicalChannelConfig__ul_SpecificParameters__ext2O__list (LogicalChannelConfig__ul_SpecificParameters__ext2O__F1 z)).
intro H. unfold LogicalChannelConfig__ul_SpecificParameters__ext2O__cond in H. simpl. auto. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext2O__F1F2_cond2 (z : LogicalChannelConfig__ul_SpecificParameters__ext2O__Type)
 : LogicalChannelConfig__ul_SpecificParameters__ext2O__F2 (LogicalChannelConfig__ul_SpecificParameters__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma LogicalChannelConfig__ul_SpecificParameters__ext2O__F2F1_cond (y : seq_type LogicalChannelConfig__ul_SpecificParameters__ext2O__list)
  : seq_cond LogicalChannelConfig__ul_SpecificParameters__ext2O__list y ->
 (LogicalChannelConfig__ul_SpecificParameters__ext2O__cond (LogicalChannelConfig__ul_SpecificParameters__ext2O__F2 y)) /\  LogicalChannelConfig__ul_SpecificParameters__ext2O__F1 (LogicalChannelConfig__ul_SpecificParameters__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold LogicalChannelConfig__ul_SpecificParameters__ext2O__cond. simpl in *. auto.
 - simpl. unfold LogicalChannelConfig__ul_SpecificParameters__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2O__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__ext2O__Type LogicalChannelConfig__ul_SpecificParameters__ext2O__cond :=
        proj2_format  LogicalChannelConfig__ul_SpecificParameters__ext2O__cond LogicalChannelConfig__ul_SpecificParameters__ext2O__list__Format
    LogicalChannelConfig__ul_SpecificParameters__ext2O__F1 LogicalChannelConfig__ul_SpecificParameters__ext2O__F2 LogicalChannelConfig__ul_SpecificParameters__ext2O__F1F2_cond  LogicalChannelConfig__ul_SpecificParameters__ext2O__F1F2_cond2 LogicalChannelConfig__ul_SpecificParameters__ext2O__F2F1_cond.
Opaque LogicalChannelConfig__ul_SpecificParameters__ext2O__cond LogicalChannelConfig__ul_SpecificParameters__ext2O__Format.

Definition LogicalChannelConfig__ul_SpecificParameters__ext2__check_all_none (b : LogicalChannelConfig__ul_SpecificParameters__ext2O__Type) : bool :=
match b with 
  | make__LogicalChannelConfig__ul_SpecificParameters__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition LogicalChannelConfig__ul_SpecificParameters__ext2__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__ext2__Type LogicalChannelConfig__ul_SpecificParameters__ext2__cond :=
  restrict_add_format LogicalChannelConfig__ul_SpecificParameters__ext2__check_all_none LogicalChannelConfig__ul_SpecificParameters__ext2O__Format.

Opaque LogicalChannelConfig__ul_SpecificParameters__ext2__cond LogicalChannelConfig__ul_SpecificParameters__ext2__Format.


Definition LogicalChannelConfig__ul_SpecificParameters__root_Format_Type := Eval cbn in seq_format_prod LogicalChannelConfig__ul_SpecificParameters__root_list.
Definition LogicalChannelConfig__ul_SpecificParameters__root_Format_list : LogicalChannelConfig__ul_SpecificParameters__root_Format_Type :=
  (LogicalChannelConfig__ul_SpecificParameters__priority__Format, (LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate__Format, (LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration__Format, (LogicalChannelConfig__ul_SpecificParameters__allowedServingCells__Format, (LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List__Format, (LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration__Format, (LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed__Format, (LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup__Format, (SchedulingRequestId__Format, (bool__Format, (bool__Format, unit_format))))))))))).

Definition LogicalChannelConfig__ul_SpecificParameters__ext_Format_Type := Eval cbn in get_formats LogicalChannelConfig__ul_SpecificParameters__ext_list.
Definition LogicalChannelConfig__ul_SpecificParameters__ext_Format_list : LogicalChannelConfig__ul_SpecificParameters__ext_Format_Type :=
  (LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer__Format, (LogicalChannelConfig__ul_SpecificParameters__ext1__Format, (LogicalChannelConfig__ul_SpecificParameters__ext2__Format, unit__Format))).

Definition LogicalChannelConfig__ul_SpecificParameters__list_type : Set := (seq_type LogicalChannelConfig__ul_SpecificParameters__root_list) * (seq_ext_type LogicalChannelConfig__ul_SpecificParameters__ext_list).
Definition LogicalChannelConfig__ul_SpecificParameters__list_cond (z : LogicalChannelConfig__ul_SpecificParameters__list_type) : Prop :=
        (seq_cond LogicalChannelConfig__ul_SpecificParameters__root_list (fst z)) /\ (seq_ext_cond LogicalChannelConfig__ul_SpecificParameters__ext_list (snd z)).
Definition LogicalChannelConfig__ul_SpecificParameters__list_format : T_Format LogicalChannelConfig__ul_SpecificParameters__list_type LogicalChannelConfig__ul_SpecificParameters__list_cond :=
 (* Eval compute in *) seq_ext_format LogicalChannelConfig__ul_SpecificParameters__root_list LogicalChannelConfig__ul_SpecificParameters__root_Format_list LogicalChannelConfig__ul_SpecificParameters__ext_list LogicalChannelConfig__ul_SpecificParameters__ext_Format_list.

Opaque LogicalChannelConfig__ul_SpecificParameters__list_format.
Definition LogicalChannelConfig__ul_SpecificParameters__F1 (z : LogicalChannelConfig__ul_SpecificParameters__Type) : LogicalChannelConfig__ul_SpecificParameters__list_type :=
  (((LogicalChannelConfig__ul_SpecificParameters__priority z, (LogicalChannelConfig__ul_SpecificParameters__prioritisedBitRate z, (LogicalChannelConfig__ul_SpecificParameters__bucketSizeDuration z, (LogicalChannelConfig__ul_SpecificParameters__allowedServingCells z, (LogicalChannelConfig__ul_SpecificParameters__allowedSCS_List z, (LogicalChannelConfig__ul_SpecificParameters__maxPUSCH_Duration z, (LogicalChannelConfig__ul_SpecificParameters__configuredGrantType1Allowed z, (LogicalChannelConfig__ul_SpecificParameters__logicalChannelGroup z, (LogicalChannelConfig__ul_SpecificParameters__schedulingRequestID z, (LogicalChannelConfig__ul_SpecificParameters__logicalChannelSR_Mask z, (LogicalChannelConfig__ul_SpecificParameters__logicalChannelSR_DelayTimerApplied z, tt)))))))))))), (
(LogicalChannelConfig__ul_SpecificParameters__bitRateQueryProhibitTimer z, (LogicalChannelConfig__ul_SpecificParameters__ext1 z, (LogicalChannelConfig__ul_SpecificParameters__ext2 z, tt))))).
Definition LogicalChannelConfig__ul_SpecificParameters__F2 (y : LogicalChannelConfig__ul_SpecificParameters__list_type) : LogicalChannelConfig__ul_SpecificParameters__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, _))))))))))), (i0, (i1, (i2, _))))=>
    make__LogicalChannelConfig__ul_SpecificParameters__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 i0 i1 i2
  end.
Definition LogicalChannelConfig__ul_SpecificParameters__helper1 : (forall a : LogicalChannelConfig__ul_SpecificParameters__Type, LogicalChannelConfig__ul_SpecificParameters__cond a -> LogicalChannelConfig__ul_SpecificParameters__list_cond (LogicalChannelConfig__ul_SpecificParameters__F1 a)).
                     intros. destruct a. auto. Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__helper2 : (forall a : LogicalChannelConfig__ul_SpecificParameters__Type, LogicalChannelConfig__ul_SpecificParameters__F2 (LogicalChannelConfig__ul_SpecificParameters__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__helper3 : (forall b : LogicalChannelConfig__ul_SpecificParameters__list_type, LogicalChannelConfig__ul_SpecificParameters__list_cond b -> LogicalChannelConfig__ul_SpecificParameters__cond (LogicalChannelConfig__ul_SpecificParameters__F2 b) /\ LogicalChannelConfig__ul_SpecificParameters__F1 (LogicalChannelConfig__ul_SpecificParameters__F2 b) = b).
                     intros. destruct b as [y y1]. unfold LogicalChannelConfig__ul_SpecificParameters__cond, LogicalChannelConfig__ul_SpecificParameters__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition LogicalChannelConfig__ul_SpecificParameters__Format : T_Format LogicalChannelConfig__ul_SpecificParameters__Type LogicalChannelConfig__ul_SpecificParameters__cond :=
 proj2_format LogicalChannelConfig__ul_SpecificParameters__cond LogicalChannelConfig__ul_SpecificParameters__list_format  LogicalChannelConfig__ul_SpecificParameters__F1 LogicalChannelConfig__ul_SpecificParameters__F2 LogicalChannelConfig__ul_SpecificParameters__helper1 LogicalChannelConfig__ul_SpecificParameters__helper2 LogicalChannelConfig__ul_SpecificParameters__helper3.

Opaque LogicalChannelConfig__ul_SpecificParameters__cond LogicalChannelConfig__ul_SpecificParameters__Format.

Definition LogicalChannelConfig__ext0O__channelAccessPriority_r16__Format : T_Format Z LogicalChannelConfig__ext0O__channelAccessPriority_r16__cond :=
 ranged_int_format (1) (4) LogicalChannelConfig__ext0O__channelAccessPriority_r16__helper1 LogicalChannelConfig__ext0O__channelAccessPriority_r16__helper2.

Opaque LogicalChannelConfig__ext0O__channelAccessPriority_r16__cond LogicalChannelConfig__ext0O__channelAccessPriority_r16__Format.

Definition LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Format : T_Format LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format LogicalChannelConfig__ext0O__bitRateMultiplier_r16__nat__Format LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F1 LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F2 LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F1F2 LogicalChannelConfig__ext0O__bitRateMultiplier_r16__F2F1.

Opaque LogicalChannelConfig__ext0O__bitRateMultiplier_r16__cond LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Format.


Definition LogicalChannelConfig__ext0O__Format_Type := Eval cbn in seq_format_prod LogicalChannelConfig__ext0O__list.
Definition LogicalChannelConfig__ext0O__Format_list : LogicalChannelConfig__ext0O__Format_Type :=
  (LogicalChannelConfig__ext0O__channelAccessPriority_r16__Format, (LogicalChannelConfig__ext0O__bitRateMultiplier_r16__Format, unit_format)).
Definition LogicalChannelConfig__ext0O__list__Format := (*Eval compute in *) seq_format LogicalChannelConfig__ext0O__list LogicalChannelConfig__ext0O__Format_list.
Definition LogicalChannelConfig__ext0O__F1 z :=
  (LogicalChannelConfig__ext0O__channelAccessPriority_r16 z, (LogicalChannelConfig__ext0O__bitRateMultiplier_r16 z, tt)).
Definition LogicalChannelConfig__ext0O__F2 (y : seq_type LogicalChannelConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__LogicalChannelConfig__ext0O__Type i0 i1
  end.
Lemma LogicalChannelConfig__ext0O__F1F2_cond (z : LogicalChannelConfig__ext0O__Type)
  : LogicalChannelConfig__ext0O__cond z ->
  (seq_cond LogicalChannelConfig__ext0O__list (LogicalChannelConfig__ext0O__F1 z)).
intro H. unfold LogicalChannelConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma LogicalChannelConfig__ext0O__F1F2_cond2 (z : LogicalChannelConfig__ext0O__Type)
 : LogicalChannelConfig__ext0O__F2 (LogicalChannelConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma LogicalChannelConfig__ext0O__F2F1_cond (y : seq_type LogicalChannelConfig__ext0O__list)
  : seq_cond LogicalChannelConfig__ext0O__list y ->
 (LogicalChannelConfig__ext0O__cond (LogicalChannelConfig__ext0O__F2 y)) /\  LogicalChannelConfig__ext0O__F1 (LogicalChannelConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold LogicalChannelConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold LogicalChannelConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition LogicalChannelConfig__ext0O__Format : T_Format LogicalChannelConfig__ext0O__Type LogicalChannelConfig__ext0O__cond :=
        proj2_format  LogicalChannelConfig__ext0O__cond LogicalChannelConfig__ext0O__list__Format
    LogicalChannelConfig__ext0O__F1 LogicalChannelConfig__ext0O__F2 LogicalChannelConfig__ext0O__F1F2_cond  LogicalChannelConfig__ext0O__F1F2_cond2 LogicalChannelConfig__ext0O__F2F1_cond.
Opaque LogicalChannelConfig__ext0O__cond LogicalChannelConfig__ext0O__Format.

Definition LogicalChannelConfig__ext0__check_all_none (b : LogicalChannelConfig__ext0O__Type) : bool :=
match b with 
  | make__LogicalChannelConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition LogicalChannelConfig__ext0__Format : T_Format LogicalChannelConfig__ext0__Type LogicalChannelConfig__ext0__cond :=
  restrict_add_format LogicalChannelConfig__ext0__check_all_none LogicalChannelConfig__ext0O__Format.

Opaque LogicalChannelConfig__ext0__cond LogicalChannelConfig__ext0__Format.


Definition LogicalChannelConfig__root_Format_Type := Eval cbn in seq_format_prod LogicalChannelConfig__root_list.
Definition LogicalChannelConfig__root_Format_list : LogicalChannelConfig__root_Format_Type :=
  (LogicalChannelConfig__ul_SpecificParameters__Format, unit_format).

Definition LogicalChannelConfig__ext_Format_Type := Eval cbn in get_formats LogicalChannelConfig__ext_list.
Definition LogicalChannelConfig__ext_Format_list : LogicalChannelConfig__ext_Format_Type :=
  (LogicalChannelConfig__ext0__Format, unit__Format).

Definition LogicalChannelConfig__list_type : Set := (seq_type LogicalChannelConfig__root_list) * (seq_ext_type LogicalChannelConfig__ext_list).
Definition LogicalChannelConfig__list_cond (z : LogicalChannelConfig__list_type) : Prop :=
        (seq_cond LogicalChannelConfig__root_list (fst z)) /\ (seq_ext_cond LogicalChannelConfig__ext_list (snd z)).
Definition LogicalChannelConfig__list_format : T_Format LogicalChannelConfig__list_type LogicalChannelConfig__list_cond :=
 (* Eval compute in *) seq_ext_format LogicalChannelConfig__root_list LogicalChannelConfig__root_Format_list LogicalChannelConfig__ext_list LogicalChannelConfig__ext_Format_list.

Opaque LogicalChannelConfig__list_format.
Definition LogicalChannelConfig__F1 (z : LogicalChannelConfig__Type) : LogicalChannelConfig__list_type :=
  (((LogicalChannelConfig__ul_SpecificParameters z, tt)), (
(LogicalChannelConfig__ext0 z, tt))).
Definition LogicalChannelConfig__F2 (y : LogicalChannelConfig__list_type) : LogicalChannelConfig__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__LogicalChannelConfig__Type j0 i0
  end.
Definition LogicalChannelConfig__helper1 : (forall a : LogicalChannelConfig__Type, LogicalChannelConfig__cond a -> LogicalChannelConfig__list_cond (LogicalChannelConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition LogicalChannelConfig__helper2 : (forall a : LogicalChannelConfig__Type, LogicalChannelConfig__F2 (LogicalChannelConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition LogicalChannelConfig__helper3 : (forall b : LogicalChannelConfig__list_type, LogicalChannelConfig__list_cond b -> LogicalChannelConfig__cond (LogicalChannelConfig__F2 b) /\ LogicalChannelConfig__F1 (LogicalChannelConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold LogicalChannelConfig__cond, LogicalChannelConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition LogicalChannelConfig__Format : T_Format LogicalChannelConfig__Type LogicalChannelConfig__cond :=
 proj2_format LogicalChannelConfig__cond LogicalChannelConfig__list_format  LogicalChannelConfig__F1 LogicalChannelConfig__F2 LogicalChannelConfig__helper1 LogicalChannelConfig__helper2 LogicalChannelConfig__helper3.

Opaque LogicalChannelConfig__cond LogicalChannelConfig__Format.

