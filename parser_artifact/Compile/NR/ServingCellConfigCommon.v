Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.DownlinkConfigCommon.

Opaque DownlinkConfigCommon__cond DownlinkConfigCommon__Format.

Require Import NR.UplinkConfigCommon.

Opaque UplinkConfigCommon__cond UplinkConfigCommon__Format.

Require Import NR.UplinkConfigCommon.

Opaque UplinkConfigCommon__cond UplinkConfigCommon__Format.

Inductive ServingCellConfigCommon__n_TimingAdvanceOffset__Type : Set :=
 | ServingCellConfigCommon__n_TimingAdvanceOffset__n0
 | ServingCellConfigCommon__n_TimingAdvanceOffset__n25600
 | ServingCellConfigCommon__n_TimingAdvanceOffset__n39936
.
Definition ServingCellConfigCommon__n_TimingAdvanceOffset__cond := (fun (_ : ServingCellConfigCommon__n_TimingAdvanceOffset__Type) => True).
Lemma ServingCellConfigCommon__n_TimingAdvanceOffset__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommon__n_TimingAdvanceOffset__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ServingCellConfigCommon__n_TimingAdvanceOffset__nat__helper.

Definition ServingCellConfigCommon__n_TimingAdvanceOffset__F1 t :=
  match t with
  | ServingCellConfigCommon__n_TimingAdvanceOffset__n0 => 0
  | ServingCellConfigCommon__n_TimingAdvanceOffset__n25600 => 1
  | ServingCellConfigCommon__n_TimingAdvanceOffset__n39936 => 2
  end.
Definition ServingCellConfigCommon__n_TimingAdvanceOffset__F2 n :=
  match n with
  | 0 => ServingCellConfigCommon__n_TimingAdvanceOffset__n0
  | 1 => ServingCellConfigCommon__n_TimingAdvanceOffset__n25600
  | 2 => ServingCellConfigCommon__n_TimingAdvanceOffset__n39936
  | _ => ServingCellConfigCommon__n_TimingAdvanceOffset__n0
  end.
Lemma ServingCellConfigCommon__n_TimingAdvanceOffset__F1F2 : forall x : ServingCellConfigCommon__n_TimingAdvanceOffset__Type, (ServingCellConfigCommon__n_TimingAdvanceOffset__F1 x <= 2) /\ ServingCellConfigCommon__n_TimingAdvanceOffset__F2 (ServingCellConfigCommon__n_TimingAdvanceOffset__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommon__n_TimingAdvanceOffset__F2F1 : forall (y : nat) (H : y <= 2), ServingCellConfigCommon__n_TimingAdvanceOffset__F1 (ServingCellConfigCommon__n_TimingAdvanceOffset__F2 y) = y. enum_solve H y. Qed.

Definition ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__Type := bit_string_fixed.
Definition ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__Type := bit_string_fixed.
Definition ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__Type := bit_string_fixed.
Definition ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 64 /\ bit_string_len_prop (fst z) (snd z)).

Inductive ServingCellConfigCommon__ssb_PositionsInBurst__Type : Set :=
  | ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap : ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__Type -> ServingCellConfigCommon__ssb_PositionsInBurst__Type
  | ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap : ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__Type -> ServingCellConfigCommon__ssb_PositionsInBurst__Type
  | ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap : ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__Type -> ServingCellConfigCommon__ssb_PositionsInBurst__Type
.
Definition ServingCellConfigCommon__ssb_PositionsInBurst__list : list typ := (
typ_cons ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__Type ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__cond ::
typ_cons ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__Type ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__cond ::
typ_cons ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__Type ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__cond ::
 nil).
Definition ServingCellConfigCommon__ssb_PositionsInBurst__cond (c : ServingCellConfigCommon__ssb_PositionsInBurst__Type) := 
  match c with
  | ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap t => ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__cond t 
  | ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap t => ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__cond t 
  | ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap t => ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__cond t 
  end.

Lemma ServingCellConfigCommon__ssb_PositionsInBurst__len_helper1 : to_bit_sz (length ServingCellConfigCommon__ssb_PositionsInBurst__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ServingCellConfigCommon__ssb_PositionsInBurst__len_helper2 : 2 <= length2 ServingCellConfigCommon__ssb_PositionsInBurst__list.
 simpl. lia. Qed.
Inductive ServingCellConfigCommon__ssb_periodicityServingCell__Type : Set :=
 | ServingCellConfigCommon__ssb_periodicityServingCell__ms5
 | ServingCellConfigCommon__ssb_periodicityServingCell__ms10
 | ServingCellConfigCommon__ssb_periodicityServingCell__ms20
 | ServingCellConfigCommon__ssb_periodicityServingCell__ms40
 | ServingCellConfigCommon__ssb_periodicityServingCell__ms80
 | ServingCellConfigCommon__ssb_periodicityServingCell__ms160
 | ServingCellConfigCommon__ssb_periodicityServingCell__spare2
 | ServingCellConfigCommon__ssb_periodicityServingCell__spare1
.
Definition ServingCellConfigCommon__ssb_periodicityServingCell__cond := (fun (_ : ServingCellConfigCommon__ssb_periodicityServingCell__Type) => True).
Lemma ServingCellConfigCommon__ssb_periodicityServingCell__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommon__ssb_periodicityServingCell__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 ServingCellConfigCommon__ssb_periodicityServingCell__nat__helper.

Definition ServingCellConfigCommon__ssb_periodicityServingCell__F1 t :=
  match t with
  | ServingCellConfigCommon__ssb_periodicityServingCell__ms5 => 0
  | ServingCellConfigCommon__ssb_periodicityServingCell__ms10 => 1
  | ServingCellConfigCommon__ssb_periodicityServingCell__ms20 => 2
  | ServingCellConfigCommon__ssb_periodicityServingCell__ms40 => 3
  | ServingCellConfigCommon__ssb_periodicityServingCell__ms80 => 4
  | ServingCellConfigCommon__ssb_periodicityServingCell__ms160 => 5
  | ServingCellConfigCommon__ssb_periodicityServingCell__spare2 => 6
  | ServingCellConfigCommon__ssb_periodicityServingCell__spare1 => 7
  end.
Definition ServingCellConfigCommon__ssb_periodicityServingCell__F2 n :=
  match n with
  | 0 => ServingCellConfigCommon__ssb_periodicityServingCell__ms5
  | 1 => ServingCellConfigCommon__ssb_periodicityServingCell__ms10
  | 2 => ServingCellConfigCommon__ssb_periodicityServingCell__ms20
  | 3 => ServingCellConfigCommon__ssb_periodicityServingCell__ms40
  | 4 => ServingCellConfigCommon__ssb_periodicityServingCell__ms80
  | 5 => ServingCellConfigCommon__ssb_periodicityServingCell__ms160
  | 6 => ServingCellConfigCommon__ssb_periodicityServingCell__spare2
  | 7 => ServingCellConfigCommon__ssb_periodicityServingCell__spare1
  | _ => ServingCellConfigCommon__ssb_periodicityServingCell__ms5
  end.
Lemma ServingCellConfigCommon__ssb_periodicityServingCell__F1F2 : forall x : ServingCellConfigCommon__ssb_periodicityServingCell__Type, (ServingCellConfigCommon__ssb_periodicityServingCell__F1 x <= 7) /\ ServingCellConfigCommon__ssb_periodicityServingCell__F2 (ServingCellConfigCommon__ssb_periodicityServingCell__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommon__ssb_periodicityServingCell__F2F1 : forall (y : nat) (H : y <= 7), ServingCellConfigCommon__ssb_periodicityServingCell__F1 (ServingCellConfigCommon__ssb_periodicityServingCell__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfigCommon__dmrs_TypeA_Position__Type : Set :=
 | ServingCellConfigCommon__dmrs_TypeA_Position__pos2
 | ServingCellConfigCommon__dmrs_TypeA_Position__pos3
.
Definition ServingCellConfigCommon__dmrs_TypeA_Position__cond := (fun (_ : ServingCellConfigCommon__dmrs_TypeA_Position__Type) => True).
Lemma ServingCellConfigCommon__dmrs_TypeA_Position__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommon__dmrs_TypeA_Position__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ServingCellConfigCommon__dmrs_TypeA_Position__nat__helper.

Definition ServingCellConfigCommon__dmrs_TypeA_Position__F1 t :=
  match t with
  | ServingCellConfigCommon__dmrs_TypeA_Position__pos2 => 0
  | ServingCellConfigCommon__dmrs_TypeA_Position__pos3 => 1
  end.
Definition ServingCellConfigCommon__dmrs_TypeA_Position__F2 n :=
  match n with
  | 0 => ServingCellConfigCommon__dmrs_TypeA_Position__pos2
  | 1 => ServingCellConfigCommon__dmrs_TypeA_Position__pos3
  | _ => ServingCellConfigCommon__dmrs_TypeA_Position__pos2
  end.
Lemma ServingCellConfigCommon__dmrs_TypeA_Position__F1F2 : forall x : ServingCellConfigCommon__dmrs_TypeA_Position__Type, (ServingCellConfigCommon__dmrs_TypeA_Position__F1 x <= 1) /\ ServingCellConfigCommon__dmrs_TypeA_Position__F2 (ServingCellConfigCommon__dmrs_TypeA_Position__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommon__dmrs_TypeA_Position__F2F1 : forall (y : nat) (H : y <= 1), ServingCellConfigCommon__dmrs_TypeA_Position__F1 (ServingCellConfigCommon__dmrs_TypeA_Position__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.RateMatchPatternLTE_CRS.
Definition ServingCellConfigCommon__lte_CRS_ToMatchAround__Type := SetupRelease__Type RateMatchPatternLTE_CRS__Type.
Definition ServingCellConfigCommon__lte_CRS_ToMatchAround__cond := SetupRelease__cond _ RateMatchPatternLTE_CRS__cond.
Definition ServingCellConfigCommon__lte_CRS_ToMatchAround__Format : T_Format ServingCellConfigCommon__lte_CRS_ToMatchAround__Type ServingCellConfigCommon__lte_CRS_ToMatchAround__cond := SetupRelease__Format _ _ RateMatchPatternLTE_CRS__Format.
Opaque ServingCellConfigCommon__lte_CRS_ToMatchAround__cond ServingCellConfigCommon__lte_CRS_ToMatchAround__Format.

Require Import NR.RateMatchPattern.

Opaque RateMatchPattern__cond RateMatchPattern__Format.

Definition ServingCellConfigCommon__rateMatchPatternToAddModList__Type := list RateMatchPattern__Type.

Lemma ServingCellConfigCommon__rateMatchPatternToAddModList__helper1 : (0 <= 1 <= maxNrofRateMatchPatterns)%Z. unfold maxNrofRateMatchPatterns.
 lia. Qed.
Lemma ServingCellConfigCommon__rateMatchPatternToAddModList__helper2 : to_bit_sz (Z.to_nat (maxNrofRateMatchPatterns - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRateMatchPatterns - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfigCommon__rateMatchPatternToAddModList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfigCommon__rateMatchPatternToAddModList__cond (z : ServingCellConfigCommon__rateMatchPatternToAddModList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRateMatchPatterns)%Z /\ (list_and RateMatchPattern__cond z) .

Require Import NR.RateMatchPatternId.

Opaque RateMatchPatternId__cond RateMatchPatternId__Format.

Definition ServingCellConfigCommon__rateMatchPatternToReleaseList__Type := list RateMatchPatternId__Type.

Lemma ServingCellConfigCommon__rateMatchPatternToReleaseList__helper1 : (0 <= 1 <= maxNrofRateMatchPatterns)%Z. unfold maxNrofRateMatchPatterns.
 lia. Qed.
Lemma ServingCellConfigCommon__rateMatchPatternToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofRateMatchPatterns - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRateMatchPatterns - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfigCommon__rateMatchPatternToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfigCommon__rateMatchPatternToReleaseList__cond (z : ServingCellConfigCommon__rateMatchPatternToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRateMatchPatterns)%Z /\ (list_and RateMatchPatternId__cond z) .

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.TDD_UL_DL_ConfigCommon.

Opaque TDD_UL_DL_ConfigCommon__cond TDD_UL_DL_ConfigCommon__Format.

Lemma ServingCellConfigCommon__ss_PBCH_BlockPower__helper1 : (-60 <= 50)%Z.  lia. Qed.
Lemma ServingCellConfigCommon__ss_PBCH_BlockPower__helper2 : to_bit_sz (Z.to_nat (50 - -60)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (50 - -60))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfigCommon__ss_PBCH_BlockPower__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfigCommon__ss_PBCH_BlockPower__Type := Z.
Definition ServingCellConfigCommon__ss_PBCH_BlockPower__cond := (fun z => (-60 <= z <= 50)%Z).
Require Import NR.SemiStaticChannelAccessConfig_r16.

Opaque SemiStaticChannelAccessConfig_r16__cond SemiStaticChannelAccessConfig_r16__Format.


Inductive ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type : Set :=
  | ServingCellConfigCommon__ext0O__channelAccessMode_r16__dynamic : unit -> ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type
  | ServingCellConfigCommon__ext0O__channelAccessMode_r16__semiStatic : SemiStaticChannelAccessConfig_r16__Type -> ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type
.
Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons SemiStaticChannelAccessConfig_r16__Type SemiStaticChannelAccessConfig_r16__cond ::
 nil).
Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__cond (c : ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type) := 
  match c with
  | ServingCellConfigCommon__ext0O__channelAccessMode_r16__dynamic t => (fun _ => True) t 
  | ServingCellConfigCommon__ext0O__channelAccessMode_r16__semiStatic t => SemiStaticChannelAccessConfig_r16__cond t 
  end.

Lemma ServingCellConfigCommon__ext0O__channelAccessMode_r16__len_helper1 : to_bit_sz (length ServingCellConfigCommon__ext0O__channelAccessMode_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ServingCellConfigCommon__ext0O__channelAccessMode_r16__len_helper2 : 2 <= length2 ServingCellConfigCommon__ext0O__channelAccessMode_r16__list.
 simpl. lia. Qed.
Inductive ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Type : Set :=
 | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms0dot5
 | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms1
 | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms2
 | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms3
 | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms4
 | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms5
.
Definition ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__cond := (fun (_ : ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Type) => True).
Lemma ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__nat__helper.

Definition ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F1 t :=
  match t with
  | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms0dot5 => 0
  | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms1 => 1
  | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms2 => 2
  | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms3 => 3
  | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms4 => 4
  | ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms5 => 5
  end.
Definition ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F2 n :=
  match n with
  | 0 => ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms0dot5
  | 1 => ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms1
  | 2 => ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms2
  | 3 => ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms3
  | 4 => ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms4
  | 5 => ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms5
  | _ => ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__ms0dot5
  end.
Lemma ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F1F2 : forall x : ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Type, (ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F1 x <= 5) /\ ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F2 (ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F2F1 : forall (y : nat) (H : y <= 5), ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F1 (ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SSB_PositionQCL_Relation_r16.

Opaque SSB_PositionQCL_Relation_r16__cond SSB_PositionQCL_Relation_r16__Format.

Require Import NR.HighSpeedConfig_r16.

Opaque HighSpeedConfig_r16__cond HighSpeedConfig_r16__Format.

Record ServingCellConfigCommon__ext0O__Type : Set :=
  make__ServingCellConfigCommon__ext0O__Type {
    ServingCellConfigCommon__ext0O__channelAccessMode_r16 : option ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type ;
    ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16 : option ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Type ;
    ServingCellConfigCommon__ext0O__ssb_PositionQCL_r16 : option SSB_PositionQCL_Relation_r16__Type ;
    ServingCellConfigCommon__ext0O__highSpeedConfig_r16 : option HighSpeedConfig_r16__Type ;
}.
Definition ServingCellConfigCommon__ext0O__list := (
 Opt ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type ServingCellConfigCommon__ext0O__channelAccessMode_r16__cond ::
 Opt ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Type ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__cond ::
 Opt SSB_PositionQCL_Relation_r16__Type SSB_PositionQCL_Relation_r16__cond ::
 Opt HighSpeedConfig_r16__Type HighSpeedConfig_r16__cond ::
 nil).
Definition ServingCellConfigCommon__ext0O__cond z := 
  opt_cond ServingCellConfigCommon__ext0O__channelAccessMode_r16__cond (ServingCellConfigCommon__ext0O__channelAccessMode_r16 z) /\
  opt_cond ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__cond (ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16 z) /\
  opt_cond SSB_PositionQCL_Relation_r16__cond (ServingCellConfigCommon__ext0O__ssb_PositionQCL_r16 z) /\
  opt_cond HighSpeedConfig_r16__cond (ServingCellConfigCommon__ext0O__highSpeedConfig_r16 z) /\
  True.

Definition ServingCellConfigCommon__ext0__Type := ServingCellConfigCommon__ext0O__Type.
Definition ServingCellConfigCommon__ext0__cond := ServingCellConfigCommon__ext0O__cond.

Require Import NR.HighSpeedConfig_v1700.

Opaque HighSpeedConfig_v1700__cond HighSpeedConfig_v1700__Format.

Inductive ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Type : Set :=
 | ServingCellConfigCommon__ext1O__channelAccessMode2_r17__enabled
.
Definition ServingCellConfigCommon__ext1O__channelAccessMode2_r17__cond := (fun (_ : ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Type) => True).
Lemma ServingCellConfigCommon__ext1O__channelAccessMode2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommon__ext1O__channelAccessMode2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfigCommon__ext1O__channelAccessMode2_r17__nat__helper.

Definition ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F1 t :=
  match t with
  | ServingCellConfigCommon__ext1O__channelAccessMode2_r17__enabled => 0
  end.
Definition ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F2 n :=
  match n with
  | 0 => ServingCellConfigCommon__ext1O__channelAccessMode2_r17__enabled
  | _ => ServingCellConfigCommon__ext1O__channelAccessMode2_r17__enabled
  end.
Lemma ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F1F2 : forall x : ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Type, (ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F1 x <= 0) /\ ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F2 (ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F1 (ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Type : Set :=
 | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot125
 | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot25
 | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot5
 | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot75
 | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms1
 | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms1dot25
.
Definition ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__cond := (fun (_ : ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Type) => True).
Lemma ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__nat__helper.

Definition ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F1 t :=
  match t with
  | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot125 => 0
  | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot25 => 1
  | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot5 => 2
  | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot75 => 3
  | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms1 => 4
  | ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms1dot25 => 5
  end.
Definition ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F2 n :=
  match n with
  | 0 => ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot125
  | 1 => ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot25
  | 2 => ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot5
  | 3 => ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot75
  | 4 => ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms1
  | 5 => ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms1dot25
  | _ => ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__ms0dot125
  end.
Lemma ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F1F2 : forall x : ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Type, (ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F1 x <= 5) /\ ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F2 (ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F2F1 : forall (y : nat) (H : y <= 5), ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F1 (ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SSB_PositionQCL_Relation_r17.

Opaque SSB_PositionQCL_Relation_r17__cond SSB_PositionQCL_Relation_r17__Format.

Require Import NR.HighSpeedConfigFR2_r17.

Opaque HighSpeedConfigFR2_r17__cond HighSpeedConfigFR2_r17__Format.

Require Import NR.UplinkConfigCommon_v1700.

Opaque UplinkConfigCommon_v1700__cond UplinkConfigCommon_v1700__Format.

Require Import NR.NTN_Config_r17.

Opaque NTN_Config_r17__cond NTN_Config_r17__Format.

Record ServingCellConfigCommon__ext1O__Type : Set :=
  make__ServingCellConfigCommon__ext1O__Type {
    ServingCellConfigCommon__ext1O__highSpeedConfig_v1700 : option HighSpeedConfig_v1700__Type ;
    ServingCellConfigCommon__ext1O__channelAccessMode2_r17 : option ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Type ;
    ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17 : option ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Type ;
    ServingCellConfigCommon__ext1O__ssb_PositionQCL_r17 : option SSB_PositionQCL_Relation_r17__Type ;
    ServingCellConfigCommon__ext1O__highSpeedConfigFR2_r17 : option HighSpeedConfigFR2_r17__Type ;
    ServingCellConfigCommon__ext1O__uplinkConfigCommon_v1700 : option UplinkConfigCommon_v1700__Type ;
    ServingCellConfigCommon__ext1O__ntn_Config_r17 : option NTN_Config_r17__Type ;
}.
Definition ServingCellConfigCommon__ext1O__list := (
 Opt HighSpeedConfig_v1700__Type HighSpeedConfig_v1700__cond ::
 Opt ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Type ServingCellConfigCommon__ext1O__channelAccessMode2_r17__cond ::
 Opt ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Type ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__cond ::
 Opt SSB_PositionQCL_Relation_r17__Type SSB_PositionQCL_Relation_r17__cond ::
 Opt HighSpeedConfigFR2_r17__Type HighSpeedConfigFR2_r17__cond ::
 Opt UplinkConfigCommon_v1700__Type UplinkConfigCommon_v1700__cond ::
 Opt NTN_Config_r17__Type NTN_Config_r17__cond ::
 nil).
Definition ServingCellConfigCommon__ext1O__cond z := 
  opt_cond HighSpeedConfig_v1700__cond (ServingCellConfigCommon__ext1O__highSpeedConfig_v1700 z) /\
  opt_cond ServingCellConfigCommon__ext1O__channelAccessMode2_r17__cond (ServingCellConfigCommon__ext1O__channelAccessMode2_r17 z) /\
  opt_cond ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__cond (ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17 z) /\
  opt_cond SSB_PositionQCL_Relation_r17__cond (ServingCellConfigCommon__ext1O__ssb_PositionQCL_r17 z) /\
  opt_cond HighSpeedConfigFR2_r17__cond (ServingCellConfigCommon__ext1O__highSpeedConfigFR2_r17 z) /\
  opt_cond UplinkConfigCommon_v1700__cond (ServingCellConfigCommon__ext1O__uplinkConfigCommon_v1700 z) /\
  opt_cond NTN_Config_r17__cond (ServingCellConfigCommon__ext1O__ntn_Config_r17 z) /\
  True.

Definition ServingCellConfigCommon__ext1__Type := ServingCellConfigCommon__ext1O__Type.
Definition ServingCellConfigCommon__ext1__cond := ServingCellConfigCommon__ext1O__cond.

Require Import NR.FeaturePriority_r17.

Opaque FeaturePriority_r17__cond FeaturePriority_r17__Format.

Require Import NR.FeaturePriority_r17.

Opaque FeaturePriority_r17__cond FeaturePriority_r17__Format.

Require Import NR.FeaturePriority_r17.

Opaque FeaturePriority_r17__cond FeaturePriority_r17__Format.

Require Import NR.FeaturePriority_r17.

Opaque FeaturePriority_r17__cond FeaturePriority_r17__Format.

Record ServingCellConfigCommon__ext2O__featurePriorities_r17__Type : Set :=
  make__ServingCellConfigCommon__ext2O__featurePriorities_r17__Type {
    ServingCellConfigCommon__ext2O__featurePriorities_r17__redCapPriority_r17 : option FeaturePriority_r17__Type ;
    ServingCellConfigCommon__ext2O__featurePriorities_r17__slicingPriority_r17 : option FeaturePriority_r17__Type ;
    ServingCellConfigCommon__ext2O__featurePriorities_r17__msg3_Repetitions_Priority_r17 : option FeaturePriority_r17__Type ;
    ServingCellConfigCommon__ext2O__featurePriorities_r17__sdt_Priority_r17 : option FeaturePriority_r17__Type ;
}.
Definition ServingCellConfigCommon__ext2O__featurePriorities_r17__list := (
 Opt FeaturePriority_r17__Type FeaturePriority_r17__cond ::
 Opt FeaturePriority_r17__Type FeaturePriority_r17__cond ::
 Opt FeaturePriority_r17__Type FeaturePriority_r17__cond ::
 Opt FeaturePriority_r17__Type FeaturePriority_r17__cond ::
 nil).
Definition ServingCellConfigCommon__ext2O__featurePriorities_r17__cond z := 
  opt_cond FeaturePriority_r17__cond (ServingCellConfigCommon__ext2O__featurePriorities_r17__redCapPriority_r17 z) /\
  opt_cond FeaturePriority_r17__cond (ServingCellConfigCommon__ext2O__featurePriorities_r17__slicingPriority_r17 z) /\
  opt_cond FeaturePriority_r17__cond (ServingCellConfigCommon__ext2O__featurePriorities_r17__msg3_Repetitions_Priority_r17 z) /\
  opt_cond FeaturePriority_r17__cond (ServingCellConfigCommon__ext2O__featurePriorities_r17__sdt_Priority_r17 z) /\
  True.

Record ServingCellConfigCommon__ext2O__Type : Set :=
  make__ServingCellConfigCommon__ext2O__Type {
    ServingCellConfigCommon__ext2O__featurePriorities_r17 : option ServingCellConfigCommon__ext2O__featurePriorities_r17__Type ;
}.
Definition ServingCellConfigCommon__ext2O__list := (
 Opt ServingCellConfigCommon__ext2O__featurePriorities_r17__Type ServingCellConfigCommon__ext2O__featurePriorities_r17__cond ::
 nil).
Definition ServingCellConfigCommon__ext2O__cond z := 
  opt_cond ServingCellConfigCommon__ext2O__featurePriorities_r17__cond (ServingCellConfigCommon__ext2O__featurePriorities_r17 z) /\
  True.

Definition ServingCellConfigCommon__ext2__Type := ServingCellConfigCommon__ext2O__Type.
Definition ServingCellConfigCommon__ext2__cond := ServingCellConfigCommon__ext2O__cond.

Record ServingCellConfigCommon__Type : Set :=
  make__ServingCellConfigCommon__Type {
    ServingCellConfigCommon__physCellId : option PhysCellId__Type ;
    ServingCellConfigCommon__downlinkConfigCommon : option DownlinkConfigCommon__Type ;
    ServingCellConfigCommon__uplinkConfigCommon : option UplinkConfigCommon__Type ;
    ServingCellConfigCommon__supplementaryUplinkConfig : option UplinkConfigCommon__Type ;
    ServingCellConfigCommon__n_TimingAdvanceOffset : option ServingCellConfigCommon__n_TimingAdvanceOffset__Type ;
    ServingCellConfigCommon__ssb_PositionsInBurst : option ServingCellConfigCommon__ssb_PositionsInBurst__Type ;
    ServingCellConfigCommon__ssb_periodicityServingCell : option ServingCellConfigCommon__ssb_periodicityServingCell__Type ;
    ServingCellConfigCommon__dmrs_TypeA_Position : ServingCellConfigCommon__dmrs_TypeA_Position__Type ;
    ServingCellConfigCommon__lte_CRS_ToMatchAround : option ServingCellConfigCommon__lte_CRS_ToMatchAround__Type ;
    ServingCellConfigCommon__rateMatchPatternToAddModList : option ServingCellConfigCommon__rateMatchPatternToAddModList__Type ;
    ServingCellConfigCommon__rateMatchPatternToReleaseList : option ServingCellConfigCommon__rateMatchPatternToReleaseList__Type ;
    ServingCellConfigCommon__ssbSubcarrierSpacing : option SubcarrierSpacing__Type ;
    ServingCellConfigCommon__tdd_UL_DL_ConfigurationCommon : option TDD_UL_DL_ConfigCommon__Type ;
    ServingCellConfigCommon__ss_PBCH_BlockPower : Z ;
    ServingCellConfigCommon__ext0 : option ServingCellConfigCommon__ext0__Type ;
    ServingCellConfigCommon__ext1 : option ServingCellConfigCommon__ext1__Type ;
    ServingCellConfigCommon__ext2 : option ServingCellConfigCommon__ext2__Type ;
}.
Definition ServingCellConfigCommon__root_list : list seq_elem := (
 Opt PhysCellId__Type PhysCellId__cond ::
 Opt DownlinkConfigCommon__Type DownlinkConfigCommon__cond ::
 Opt UplinkConfigCommon__Type UplinkConfigCommon__cond ::
 Opt UplinkConfigCommon__Type UplinkConfigCommon__cond ::
 Opt ServingCellConfigCommon__n_TimingAdvanceOffset__Type ServingCellConfigCommon__n_TimingAdvanceOffset__cond ::
 Opt ServingCellConfigCommon__ssb_PositionsInBurst__Type ServingCellConfigCommon__ssb_PositionsInBurst__cond ::
 Opt ServingCellConfigCommon__ssb_periodicityServingCell__Type ServingCellConfigCommon__ssb_periodicityServingCell__cond ::
 Nor ServingCellConfigCommon__dmrs_TypeA_Position__Type ServingCellConfigCommon__dmrs_TypeA_Position__cond ::
 Opt ServingCellConfigCommon__lte_CRS_ToMatchAround__Type ServingCellConfigCommon__lte_CRS_ToMatchAround__cond ::
 Opt ServingCellConfigCommon__rateMatchPatternToAddModList__Type ServingCellConfigCommon__rateMatchPatternToAddModList__cond ::
 Opt ServingCellConfigCommon__rateMatchPatternToReleaseList__Type ServingCellConfigCommon__rateMatchPatternToReleaseList__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt TDD_UL_DL_ConfigCommon__Type TDD_UL_DL_ConfigCommon__cond ::
 Nor Z ServingCellConfigCommon__ss_PBCH_BlockPower__cond ::
 nil).
Definition ServingCellConfigCommon__ext_list : list typ := (
  typ_cons ServingCellConfigCommon__ext0__Type ServingCellConfigCommon__ext0__cond ::
  typ_cons ServingCellConfigCommon__ext1__Type ServingCellConfigCommon__ext1__cond ::
  typ_cons ServingCellConfigCommon__ext2__Type ServingCellConfigCommon__ext2__cond ::
  nil).
Definition ServingCellConfigCommon__cond (z : ServingCellConfigCommon__Type) := 
(  opt_cond PhysCellId__cond (ServingCellConfigCommon__physCellId z) /\
  opt_cond DownlinkConfigCommon__cond (ServingCellConfigCommon__downlinkConfigCommon z) /\
  opt_cond UplinkConfigCommon__cond (ServingCellConfigCommon__uplinkConfigCommon z) /\
  opt_cond UplinkConfigCommon__cond (ServingCellConfigCommon__supplementaryUplinkConfig z) /\
  opt_cond ServingCellConfigCommon__n_TimingAdvanceOffset__cond (ServingCellConfigCommon__n_TimingAdvanceOffset z) /\
  opt_cond ServingCellConfigCommon__ssb_PositionsInBurst__cond (ServingCellConfigCommon__ssb_PositionsInBurst z) /\
  opt_cond ServingCellConfigCommon__ssb_periodicityServingCell__cond (ServingCellConfigCommon__ssb_periodicityServingCell z) /\
  ServingCellConfigCommon__dmrs_TypeA_Position__cond (ServingCellConfigCommon__dmrs_TypeA_Position z) /\
  opt_cond ServingCellConfigCommon__lte_CRS_ToMatchAround__cond (ServingCellConfigCommon__lte_CRS_ToMatchAround z) /\
  opt_cond ServingCellConfigCommon__rateMatchPatternToAddModList__cond (ServingCellConfigCommon__rateMatchPatternToAddModList z) /\
  opt_cond ServingCellConfigCommon__rateMatchPatternToReleaseList__cond (ServingCellConfigCommon__rateMatchPatternToReleaseList z) /\
  opt_cond SubcarrierSpacing__cond (ServingCellConfigCommon__ssbSubcarrierSpacing z) /\
  opt_cond TDD_UL_DL_ConfigCommon__cond (ServingCellConfigCommon__tdd_UL_DL_ConfigurationCommon z) /\
  ServingCellConfigCommon__ss_PBCH_BlockPower__cond (ServingCellConfigCommon__ss_PBCH_BlockPower z) /\
  True) /\ 
(  opt_cond ServingCellConfigCommon__ext0__cond (ServingCellConfigCommon__ext0 z) /\
  opt_cond ServingCellConfigCommon__ext1__cond (ServingCellConfigCommon__ext1 z) /\
  opt_cond ServingCellConfigCommon__ext2__cond (ServingCellConfigCommon__ext2 z) /\
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
Definition ServingCellConfigCommon__n_TimingAdvanceOffset__Format : T_Format ServingCellConfigCommon__n_TimingAdvanceOffset__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommon__n_TimingAdvanceOffset__nat__Format ServingCellConfigCommon__n_TimingAdvanceOffset__F1 ServingCellConfigCommon__n_TimingAdvanceOffset__F2 ServingCellConfigCommon__n_TimingAdvanceOffset__F1F2 ServingCellConfigCommon__n_TimingAdvanceOffset__F2F1.

Opaque ServingCellConfigCommon__n_TimingAdvanceOffset__cond ServingCellConfigCommon__n_TimingAdvanceOffset__Format.

Definition ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__Format : T_Format ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__Type ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__cond ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__Format.

Definition ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__Format : T_Format ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__Type ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__cond ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__Format.

Definition ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__Format : T_Format ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__Type ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__cond := (* Eval compute in *) bit_string_fixed_format 64.
Opaque ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__cond ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__Format.


Definition ServingCellConfigCommon__ssb_PositionsInBurst__Format_Type := Eval cbn in get_formats ServingCellConfigCommon__ssb_PositionsInBurst__list.
Definition ServingCellConfigCommon__ssb_PositionsInBurst__Format_list : ServingCellConfigCommon__ssb_PositionsInBurst__Format_Type :=
  (ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__Format, (ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__Format, (ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__Format, unit__Format))).
Definition ServingCellConfigCommon__ssb_PositionsInBurst__list__Format := Eval compute in choice_format ServingCellConfigCommon__ssb_PositionsInBurst__list ServingCellConfigCommon__ssb_PositionsInBurst__len_helper1 ServingCellConfigCommon__ssb_PositionsInBurst__len_helper2  ServingCellConfigCommon__ssb_PositionsInBurst__Format_list.
Definition ServingCellConfigCommon__ssb_PositionsInBurst__F1 (z : ServingCellConfigCommon__ssb_PositionsInBurst__Type) : (choice ServingCellConfigCommon__ssb_PositionsInBurst__list) :=
  match z with
   | ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap t => existT _ 0 t
  | ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap t => existT _ 1 t
  | ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap t => existT _ 2 t
  end.
Definition ServingCellConfigCommon__ssb_PositionsInBurst__g := (fun n => typ_set (get_nth_typ ServingCellConfigCommon__ssb_PositionsInBurst__list n)).
Definition ServingCellConfigCommon__ssb_PositionsInBurst__F2 (y : choice ServingCellConfigCommon__ssb_PositionsInBurst__list) : ServingCellConfigCommon__ssb_PositionsInBurst__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ServingCellConfigCommon__ssb_PositionsInBurst__g n -> ServingCellConfigCommon__ssb_PositionsInBurst__Type) with
    | 0 => fun (t : ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap__Type) => ServingCellConfigCommon__ssb_PositionsInBurst__shortBitmap t 
    | 1 => fun (t : ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap__Type) => ServingCellConfigCommon__ssb_PositionsInBurst__mediumBitmap t 
    | 2 => fun (t : ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap__Type) => ServingCellConfigCommon__ssb_PositionsInBurst__longBitmap t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : ServingCellConfigCommon__ssb_PositionsInBurst__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ ServingCellConfigCommon__ssb_PositionsInBurst__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ServingCellConfigCommon__ssb_PositionsInBurst__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return ServingCellConfigCommon__ssb_PositionsInBurst__Type with end) n0
           end t0).

Lemma ServingCellConfigCommon__ssb_PositionsInBurst__helper2 :  forall (y : ServingCellConfigCommon__ssb_PositionsInBurst__Type), ServingCellConfigCommon__ssb_PositionsInBurst__cond y -> choice_cond ServingCellConfigCommon__ssb_PositionsInBurst__list (ServingCellConfigCommon__ssb_PositionsInBurst__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ServingCellConfigCommon__ssb_PositionsInBurst__helper3 :  forall (y : ServingCellConfigCommon__ssb_PositionsInBurst__Type), ServingCellConfigCommon__ssb_PositionsInBurst__F2 (ServingCellConfigCommon__ssb_PositionsInBurst__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ServingCellConfigCommon__ssb_PositionsInBurst__helper4 : (forall b : choice ServingCellConfigCommon__ssb_PositionsInBurst__list, choice_cond ServingCellConfigCommon__ssb_PositionsInBurst__list b -> ServingCellConfigCommon__ssb_PositionsInBurst__cond (ServingCellConfigCommon__ssb_PositionsInBurst__F2 b) /\ ServingCellConfigCommon__ssb_PositionsInBurst__F1 (ServingCellConfigCommon__ssb_PositionsInBurst__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ServingCellConfigCommon__ssb_PositionsInBurst__F1 ServingCellConfigCommon__ssb_PositionsInBurst__F2.
Definition ServingCellConfigCommon__ssb_PositionsInBurst__Format : T_Format ServingCellConfigCommon__ssb_PositionsInBurst__Type ServingCellConfigCommon__ssb_PositionsInBurst__cond :=
  (* Eval compute in *) proj2_format ServingCellConfigCommon__ssb_PositionsInBurst__cond ServingCellConfigCommon__ssb_PositionsInBurst__list__Format ServingCellConfigCommon__ssb_PositionsInBurst__F1 ServingCellConfigCommon__ssb_PositionsInBurst__F2 ServingCellConfigCommon__ssb_PositionsInBurst__helper2 ServingCellConfigCommon__ssb_PositionsInBurst__helper3 ServingCellConfigCommon__ssb_PositionsInBurst__helper4.
Opaque ServingCellConfigCommon__ssb_PositionsInBurst__cond ServingCellConfigCommon__ssb_PositionsInBurst__Format.

Definition ServingCellConfigCommon__ssb_periodicityServingCell__Format : T_Format ServingCellConfigCommon__ssb_periodicityServingCell__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommon__ssb_periodicityServingCell__nat__Format ServingCellConfigCommon__ssb_periodicityServingCell__F1 ServingCellConfigCommon__ssb_periodicityServingCell__F2 ServingCellConfigCommon__ssb_periodicityServingCell__F1F2 ServingCellConfigCommon__ssb_periodicityServingCell__F2F1.

Opaque ServingCellConfigCommon__ssb_periodicityServingCell__cond ServingCellConfigCommon__ssb_periodicityServingCell__Format.

Definition ServingCellConfigCommon__dmrs_TypeA_Position__Format : T_Format ServingCellConfigCommon__dmrs_TypeA_Position__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommon__dmrs_TypeA_Position__nat__Format ServingCellConfigCommon__dmrs_TypeA_Position__F1 ServingCellConfigCommon__dmrs_TypeA_Position__F2 ServingCellConfigCommon__dmrs_TypeA_Position__F1F2 ServingCellConfigCommon__dmrs_TypeA_Position__F2F1.

Opaque ServingCellConfigCommon__dmrs_TypeA_Position__cond ServingCellConfigCommon__dmrs_TypeA_Position__Format.

Opaque ServingCellConfigCommon__lte_CRS_ToMatchAround__cond ServingCellConfigCommon__lte_CRS_ToMatchAround__Format.

Definition ServingCellConfigCommon__rateMatchPatternToAddModList__Format : T_Format ServingCellConfigCommon__rateMatchPatternToAddModList__Type ServingCellConfigCommon__rateMatchPatternToAddModList__cond := seq_of_format RateMatchPattern__Format 1 maxNrofRateMatchPatterns ServingCellConfigCommon__rateMatchPatternToAddModList__helper1 ServingCellConfigCommon__rateMatchPatternToAddModList__helper2.

Opaque ServingCellConfigCommon__rateMatchPatternToAddModList__cond ServingCellConfigCommon__rateMatchPatternToAddModList__Format.

Definition ServingCellConfigCommon__rateMatchPatternToReleaseList__Format : T_Format ServingCellConfigCommon__rateMatchPatternToReleaseList__Type ServingCellConfigCommon__rateMatchPatternToReleaseList__cond := seq_of_format RateMatchPatternId__Format 1 maxNrofRateMatchPatterns ServingCellConfigCommon__rateMatchPatternToReleaseList__helper1 ServingCellConfigCommon__rateMatchPatternToReleaseList__helper2.

Opaque ServingCellConfigCommon__rateMatchPatternToReleaseList__cond ServingCellConfigCommon__rateMatchPatternToReleaseList__Format.

Definition ServingCellConfigCommon__ss_PBCH_BlockPower__Format : T_Format Z ServingCellConfigCommon__ss_PBCH_BlockPower__cond :=
 ranged_int_format (-60) (50) ServingCellConfigCommon__ss_PBCH_BlockPower__helper1 ServingCellConfigCommon__ss_PBCH_BlockPower__helper2.

Opaque ServingCellConfigCommon__ss_PBCH_BlockPower__cond ServingCellConfigCommon__ss_PBCH_BlockPower__Format.


Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__Format_Type := Eval cbn in get_formats ServingCellConfigCommon__ext0O__channelAccessMode_r16__list.
Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__Format_list : ServingCellConfigCommon__ext0O__channelAccessMode_r16__Format_Type :=
  (unit__Format, (SemiStaticChannelAccessConfig_r16__Format, unit__Format)).
Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__list__Format := Eval compute in choice_format ServingCellConfigCommon__ext0O__channelAccessMode_r16__list ServingCellConfigCommon__ext0O__channelAccessMode_r16__len_helper1 ServingCellConfigCommon__ext0O__channelAccessMode_r16__len_helper2  ServingCellConfigCommon__ext0O__channelAccessMode_r16__Format_list.
Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__F1 (z : ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type) : (choice ServingCellConfigCommon__ext0O__channelAccessMode_r16__list) :=
  match z with
   | ServingCellConfigCommon__ext0O__channelAccessMode_r16__dynamic t => existT _ 0 t
  | ServingCellConfigCommon__ext0O__channelAccessMode_r16__semiStatic t => existT _ 1 t
  end.
Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__g := (fun n => typ_set (get_nth_typ ServingCellConfigCommon__ext0O__channelAccessMode_r16__list n)).
Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__F2 (y : choice ServingCellConfigCommon__ext0O__channelAccessMode_r16__list) : ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ServingCellConfigCommon__ext0O__channelAccessMode_r16__g n -> ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type) with
    | 0 => fun (t : unit) => ServingCellConfigCommon__ext0O__channelAccessMode_r16__dynamic t 
    | 1 => fun (t : SemiStaticChannelAccessConfig_r16__Type) => ServingCellConfigCommon__ext0O__channelAccessMode_r16__semiStatic t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ServingCellConfigCommon__ext0O__channelAccessMode_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ServingCellConfigCommon__ext0O__channelAccessMode_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ServingCellConfigCommon__ext0O__channelAccessMode_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type with end) n0
           end t0).

Lemma ServingCellConfigCommon__ext0O__channelAccessMode_r16__helper2 :  forall (y : ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type), ServingCellConfigCommon__ext0O__channelAccessMode_r16__cond y -> choice_cond ServingCellConfigCommon__ext0O__channelAccessMode_r16__list (ServingCellConfigCommon__ext0O__channelAccessMode_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ServingCellConfigCommon__ext0O__channelAccessMode_r16__helper3 :  forall (y : ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type), ServingCellConfigCommon__ext0O__channelAccessMode_r16__F2 (ServingCellConfigCommon__ext0O__channelAccessMode_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ServingCellConfigCommon__ext0O__channelAccessMode_r16__helper4 : (forall b : choice ServingCellConfigCommon__ext0O__channelAccessMode_r16__list, choice_cond ServingCellConfigCommon__ext0O__channelAccessMode_r16__list b -> ServingCellConfigCommon__ext0O__channelAccessMode_r16__cond (ServingCellConfigCommon__ext0O__channelAccessMode_r16__F2 b) /\ ServingCellConfigCommon__ext0O__channelAccessMode_r16__F1 (ServingCellConfigCommon__ext0O__channelAccessMode_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ServingCellConfigCommon__ext0O__channelAccessMode_r16__F1 ServingCellConfigCommon__ext0O__channelAccessMode_r16__F2.
Definition ServingCellConfigCommon__ext0O__channelAccessMode_r16__Format : T_Format ServingCellConfigCommon__ext0O__channelAccessMode_r16__Type ServingCellConfigCommon__ext0O__channelAccessMode_r16__cond :=
  (* Eval compute in *) proj2_format ServingCellConfigCommon__ext0O__channelAccessMode_r16__cond ServingCellConfigCommon__ext0O__channelAccessMode_r16__list__Format ServingCellConfigCommon__ext0O__channelAccessMode_r16__F1 ServingCellConfigCommon__ext0O__channelAccessMode_r16__F2 ServingCellConfigCommon__ext0O__channelAccessMode_r16__helper2 ServingCellConfigCommon__ext0O__channelAccessMode_r16__helper3 ServingCellConfigCommon__ext0O__channelAccessMode_r16__helper4.
Opaque ServingCellConfigCommon__ext0O__channelAccessMode_r16__cond ServingCellConfigCommon__ext0O__channelAccessMode_r16__Format.

Definition ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Format : T_Format ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__nat__Format ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F1 ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F2 ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F1F2 ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__F2F1.

Opaque ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__cond ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Format.


Definition ServingCellConfigCommon__ext0O__Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommon__ext0O__list.
Definition ServingCellConfigCommon__ext0O__Format_list : ServingCellConfigCommon__ext0O__Format_Type :=
  (ServingCellConfigCommon__ext0O__channelAccessMode_r16__Format, (ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16__Format, (SSB_PositionQCL_Relation_r16__Format, (HighSpeedConfig_r16__Format, unit_format)))).
Definition ServingCellConfigCommon__ext0O__list__Format := (*Eval compute in *) seq_format ServingCellConfigCommon__ext0O__list ServingCellConfigCommon__ext0O__Format_list.
Definition ServingCellConfigCommon__ext0O__F1 z :=
  (ServingCellConfigCommon__ext0O__channelAccessMode_r16 z, (ServingCellConfigCommon__ext0O__discoveryBurstWindowLength_r16 z, (ServingCellConfigCommon__ext0O__ssb_PositionQCL_r16 z, (ServingCellConfigCommon__ext0O__highSpeedConfig_r16 z, tt)))).
Definition ServingCellConfigCommon__ext0O__F2 (y : seq_type ServingCellConfigCommon__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ServingCellConfigCommon__ext0O__Type i0 i1 i2 i3
  end.
Lemma ServingCellConfigCommon__ext0O__F1F2_cond (z : ServingCellConfigCommon__ext0O__Type)
  : ServingCellConfigCommon__ext0O__cond z ->
  (seq_cond ServingCellConfigCommon__ext0O__list (ServingCellConfigCommon__ext0O__F1 z)).
intro H. unfold ServingCellConfigCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfigCommon__ext0O__F1F2_cond2 (z : ServingCellConfigCommon__ext0O__Type)
 : ServingCellConfigCommon__ext0O__F2 (ServingCellConfigCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfigCommon__ext0O__F2F1_cond (y : seq_type ServingCellConfigCommon__ext0O__list)
  : seq_cond ServingCellConfigCommon__ext0O__list y ->
 (ServingCellConfigCommon__ext0O__cond (ServingCellConfigCommon__ext0O__F2 y)) /\  ServingCellConfigCommon__ext0O__F1 (ServingCellConfigCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfigCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfigCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfigCommon__ext0O__Format : T_Format ServingCellConfigCommon__ext0O__Type ServingCellConfigCommon__ext0O__cond :=
        proj2_format  ServingCellConfigCommon__ext0O__cond ServingCellConfigCommon__ext0O__list__Format
    ServingCellConfigCommon__ext0O__F1 ServingCellConfigCommon__ext0O__F2 ServingCellConfigCommon__ext0O__F1F2_cond  ServingCellConfigCommon__ext0O__F1F2_cond2 ServingCellConfigCommon__ext0O__F2F1_cond.
Opaque ServingCellConfigCommon__ext0O__cond ServingCellConfigCommon__ext0O__Format.

Definition ServingCellConfigCommon__ext0__check_all_none (b : ServingCellConfigCommon__ext0O__Type) : bool :=
match b with 
  | make__ServingCellConfigCommon__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition ServingCellConfigCommon__ext0__Format : T_Format ServingCellConfigCommon__ext0__Type ServingCellConfigCommon__ext0__cond :=
  restrict_add_format ServingCellConfigCommon__ext0__check_all_none ServingCellConfigCommon__ext0O__Format.

Opaque ServingCellConfigCommon__ext0__cond ServingCellConfigCommon__ext0__Format.

Definition ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Format : T_Format ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommon__ext1O__channelAccessMode2_r17__nat__Format ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F1 ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F2 ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F1F2 ServingCellConfigCommon__ext1O__channelAccessMode2_r17__F2F1.

Opaque ServingCellConfigCommon__ext1O__channelAccessMode2_r17__cond ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Format.

Definition ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Format : T_Format ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__nat__Format ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F1 ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F2 ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F1F2 ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__F2F1.

Opaque ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__cond ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Format.


Definition ServingCellConfigCommon__ext1O__Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommon__ext1O__list.
Definition ServingCellConfigCommon__ext1O__Format_list : ServingCellConfigCommon__ext1O__Format_Type :=
  (HighSpeedConfig_v1700__Format, (ServingCellConfigCommon__ext1O__channelAccessMode2_r17__Format, (ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17__Format, (SSB_PositionQCL_Relation_r17__Format, (HighSpeedConfigFR2_r17__Format, (UplinkConfigCommon_v1700__Format, (NTN_Config_r17__Format, unit_format))))))).
Definition ServingCellConfigCommon__ext1O__list__Format := (*Eval compute in *) seq_format ServingCellConfigCommon__ext1O__list ServingCellConfigCommon__ext1O__Format_list.
Definition ServingCellConfigCommon__ext1O__F1 z :=
  (ServingCellConfigCommon__ext1O__highSpeedConfig_v1700 z, (ServingCellConfigCommon__ext1O__channelAccessMode2_r17 z, (ServingCellConfigCommon__ext1O__discoveryBurstWindowLength_r17 z, (ServingCellConfigCommon__ext1O__ssb_PositionQCL_r17 z, (ServingCellConfigCommon__ext1O__highSpeedConfigFR2_r17 z, (ServingCellConfigCommon__ext1O__uplinkConfigCommon_v1700 z, (ServingCellConfigCommon__ext1O__ntn_Config_r17 z, tt))))))).
Definition ServingCellConfigCommon__ext1O__F2 (y : seq_type ServingCellConfigCommon__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__ServingCellConfigCommon__ext1O__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma ServingCellConfigCommon__ext1O__F1F2_cond (z : ServingCellConfigCommon__ext1O__Type)
  : ServingCellConfigCommon__ext1O__cond z ->
  (seq_cond ServingCellConfigCommon__ext1O__list (ServingCellConfigCommon__ext1O__F1 z)).
intro H. unfold ServingCellConfigCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfigCommon__ext1O__F1F2_cond2 (z : ServingCellConfigCommon__ext1O__Type)
 : ServingCellConfigCommon__ext1O__F2 (ServingCellConfigCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfigCommon__ext1O__F2F1_cond (y : seq_type ServingCellConfigCommon__ext1O__list)
  : seq_cond ServingCellConfigCommon__ext1O__list y ->
 (ServingCellConfigCommon__ext1O__cond (ServingCellConfigCommon__ext1O__F2 y)) /\  ServingCellConfigCommon__ext1O__F1 (ServingCellConfigCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfigCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfigCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfigCommon__ext1O__Format : T_Format ServingCellConfigCommon__ext1O__Type ServingCellConfigCommon__ext1O__cond :=
        proj2_format  ServingCellConfigCommon__ext1O__cond ServingCellConfigCommon__ext1O__list__Format
    ServingCellConfigCommon__ext1O__F1 ServingCellConfigCommon__ext1O__F2 ServingCellConfigCommon__ext1O__F1F2_cond  ServingCellConfigCommon__ext1O__F1F2_cond2 ServingCellConfigCommon__ext1O__F2F1_cond.
Opaque ServingCellConfigCommon__ext1O__cond ServingCellConfigCommon__ext1O__Format.

Definition ServingCellConfigCommon__ext1__check_all_none (b : ServingCellConfigCommon__ext1O__Type) : bool :=
match b with 
  | make__ServingCellConfigCommon__ext1O__Type None None None None None None None  => false 
  | _ => true 
 end.
Definition ServingCellConfigCommon__ext1__Format : T_Format ServingCellConfigCommon__ext1__Type ServingCellConfigCommon__ext1__cond :=
  restrict_add_format ServingCellConfigCommon__ext1__check_all_none ServingCellConfigCommon__ext1O__Format.

Opaque ServingCellConfigCommon__ext1__cond ServingCellConfigCommon__ext1__Format.


Definition ServingCellConfigCommon__ext2O__featurePriorities_r17__Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommon__ext2O__featurePriorities_r17__list.
Definition ServingCellConfigCommon__ext2O__featurePriorities_r17__Format_list : ServingCellConfigCommon__ext2O__featurePriorities_r17__Format_Type :=
  (FeaturePriority_r17__Format, (FeaturePriority_r17__Format, (FeaturePriority_r17__Format, (FeaturePriority_r17__Format, unit_format)))).
Definition ServingCellConfigCommon__ext2O__featurePriorities_r17__list__Format := (*Eval compute in *) seq_format ServingCellConfigCommon__ext2O__featurePriorities_r17__list ServingCellConfigCommon__ext2O__featurePriorities_r17__Format_list.
Definition ServingCellConfigCommon__ext2O__featurePriorities_r17__F1 z :=
  (ServingCellConfigCommon__ext2O__featurePriorities_r17__redCapPriority_r17 z, (ServingCellConfigCommon__ext2O__featurePriorities_r17__slicingPriority_r17 z, (ServingCellConfigCommon__ext2O__featurePriorities_r17__msg3_Repetitions_Priority_r17 z, (ServingCellConfigCommon__ext2O__featurePriorities_r17__sdt_Priority_r17 z, tt)))).
Definition ServingCellConfigCommon__ext2O__featurePriorities_r17__F2 (y : seq_type ServingCellConfigCommon__ext2O__featurePriorities_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ServingCellConfigCommon__ext2O__featurePriorities_r17__Type i0 i1 i2 i3
  end.
Lemma ServingCellConfigCommon__ext2O__featurePriorities_r17__F1F2_cond (z : ServingCellConfigCommon__ext2O__featurePriorities_r17__Type)
  : ServingCellConfigCommon__ext2O__featurePriorities_r17__cond z ->
  (seq_cond ServingCellConfigCommon__ext2O__featurePriorities_r17__list (ServingCellConfigCommon__ext2O__featurePriorities_r17__F1 z)).
intro H. unfold ServingCellConfigCommon__ext2O__featurePriorities_r17__cond in H. simpl. auto. Qed.
Lemma ServingCellConfigCommon__ext2O__featurePriorities_r17__F1F2_cond2 (z : ServingCellConfigCommon__ext2O__featurePriorities_r17__Type)
 : ServingCellConfigCommon__ext2O__featurePriorities_r17__F2 (ServingCellConfigCommon__ext2O__featurePriorities_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfigCommon__ext2O__featurePriorities_r17__F2F1_cond (y : seq_type ServingCellConfigCommon__ext2O__featurePriorities_r17__list)
  : seq_cond ServingCellConfigCommon__ext2O__featurePriorities_r17__list y ->
 (ServingCellConfigCommon__ext2O__featurePriorities_r17__cond (ServingCellConfigCommon__ext2O__featurePriorities_r17__F2 y)) /\  ServingCellConfigCommon__ext2O__featurePriorities_r17__F1 (ServingCellConfigCommon__ext2O__featurePriorities_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfigCommon__ext2O__featurePriorities_r17__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfigCommon__ext2O__featurePriorities_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfigCommon__ext2O__featurePriorities_r17__Format : T_Format ServingCellConfigCommon__ext2O__featurePriorities_r17__Type ServingCellConfigCommon__ext2O__featurePriorities_r17__cond :=
        proj2_format  ServingCellConfigCommon__ext2O__featurePriorities_r17__cond ServingCellConfigCommon__ext2O__featurePriorities_r17__list__Format
    ServingCellConfigCommon__ext2O__featurePriorities_r17__F1 ServingCellConfigCommon__ext2O__featurePriorities_r17__F2 ServingCellConfigCommon__ext2O__featurePriorities_r17__F1F2_cond  ServingCellConfigCommon__ext2O__featurePriorities_r17__F1F2_cond2 ServingCellConfigCommon__ext2O__featurePriorities_r17__F2F1_cond.
Opaque ServingCellConfigCommon__ext2O__featurePriorities_r17__cond ServingCellConfigCommon__ext2O__featurePriorities_r17__Format.


Definition ServingCellConfigCommon__ext2O__Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommon__ext2O__list.
Definition ServingCellConfigCommon__ext2O__Format_list : ServingCellConfigCommon__ext2O__Format_Type :=
  (ServingCellConfigCommon__ext2O__featurePriorities_r17__Format, unit_format).
Definition ServingCellConfigCommon__ext2O__list__Format := (*Eval compute in *) seq_format ServingCellConfigCommon__ext2O__list ServingCellConfigCommon__ext2O__Format_list.
Definition ServingCellConfigCommon__ext2O__F1 z :=
  (ServingCellConfigCommon__ext2O__featurePriorities_r17 z, tt).
Definition ServingCellConfigCommon__ext2O__F2 (y : seq_type ServingCellConfigCommon__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__ServingCellConfigCommon__ext2O__Type i0
  end.
Lemma ServingCellConfigCommon__ext2O__F1F2_cond (z : ServingCellConfigCommon__ext2O__Type)
  : ServingCellConfigCommon__ext2O__cond z ->
  (seq_cond ServingCellConfigCommon__ext2O__list (ServingCellConfigCommon__ext2O__F1 z)).
intro H. unfold ServingCellConfigCommon__ext2O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfigCommon__ext2O__F1F2_cond2 (z : ServingCellConfigCommon__ext2O__Type)
 : ServingCellConfigCommon__ext2O__F2 (ServingCellConfigCommon__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfigCommon__ext2O__F2F1_cond (y : seq_type ServingCellConfigCommon__ext2O__list)
  : seq_cond ServingCellConfigCommon__ext2O__list y ->
 (ServingCellConfigCommon__ext2O__cond (ServingCellConfigCommon__ext2O__F2 y)) /\  ServingCellConfigCommon__ext2O__F1 (ServingCellConfigCommon__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfigCommon__ext2O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfigCommon__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfigCommon__ext2O__Format : T_Format ServingCellConfigCommon__ext2O__Type ServingCellConfigCommon__ext2O__cond :=
        proj2_format  ServingCellConfigCommon__ext2O__cond ServingCellConfigCommon__ext2O__list__Format
    ServingCellConfigCommon__ext2O__F1 ServingCellConfigCommon__ext2O__F2 ServingCellConfigCommon__ext2O__F1F2_cond  ServingCellConfigCommon__ext2O__F1F2_cond2 ServingCellConfigCommon__ext2O__F2F1_cond.
Opaque ServingCellConfigCommon__ext2O__cond ServingCellConfigCommon__ext2O__Format.

Definition ServingCellConfigCommon__ext2__check_all_none (b : ServingCellConfigCommon__ext2O__Type) : bool :=
match b with 
  | make__ServingCellConfigCommon__ext2O__Type None  => false 
  | _ => true 
 end.
Definition ServingCellConfigCommon__ext2__Format : T_Format ServingCellConfigCommon__ext2__Type ServingCellConfigCommon__ext2__cond :=
  restrict_add_format ServingCellConfigCommon__ext2__check_all_none ServingCellConfigCommon__ext2O__Format.

Opaque ServingCellConfigCommon__ext2__cond ServingCellConfigCommon__ext2__Format.


Definition ServingCellConfigCommon__root_Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommon__root_list.
Definition ServingCellConfigCommon__root_Format_list : ServingCellConfigCommon__root_Format_Type :=
  (PhysCellId__Format, (DownlinkConfigCommon__Format, (UplinkConfigCommon__Format, (UplinkConfigCommon__Format, (ServingCellConfigCommon__n_TimingAdvanceOffset__Format, (ServingCellConfigCommon__ssb_PositionsInBurst__Format, (ServingCellConfigCommon__ssb_periodicityServingCell__Format, (ServingCellConfigCommon__dmrs_TypeA_Position__Format, (ServingCellConfigCommon__lte_CRS_ToMatchAround__Format, (ServingCellConfigCommon__rateMatchPatternToAddModList__Format, (ServingCellConfigCommon__rateMatchPatternToReleaseList__Format, (SubcarrierSpacing__Format, (TDD_UL_DL_ConfigCommon__Format, (ServingCellConfigCommon__ss_PBCH_BlockPower__Format, unit_format)))))))))))))).

Definition ServingCellConfigCommon__ext_Format_Type := Eval cbn in get_formats ServingCellConfigCommon__ext_list.
Definition ServingCellConfigCommon__ext_Format_list : ServingCellConfigCommon__ext_Format_Type :=
  (ServingCellConfigCommon__ext0__Format, (ServingCellConfigCommon__ext1__Format, (ServingCellConfigCommon__ext2__Format, unit__Format))).

Definition ServingCellConfigCommon__list_type : Set := (seq_type ServingCellConfigCommon__root_list) * (seq_ext_type ServingCellConfigCommon__ext_list).
Definition ServingCellConfigCommon__list_cond (z : ServingCellConfigCommon__list_type) : Prop :=
        (seq_cond ServingCellConfigCommon__root_list (fst z)) /\ (seq_ext_cond ServingCellConfigCommon__ext_list (snd z)).
Definition ServingCellConfigCommon__list_format : T_Format ServingCellConfigCommon__list_type ServingCellConfigCommon__list_cond :=
 (* Eval compute in *) seq_ext_format ServingCellConfigCommon__root_list ServingCellConfigCommon__root_Format_list ServingCellConfigCommon__ext_list ServingCellConfigCommon__ext_Format_list.

Opaque ServingCellConfigCommon__list_format.
Definition ServingCellConfigCommon__F1 (z : ServingCellConfigCommon__Type) : ServingCellConfigCommon__list_type :=
  (((ServingCellConfigCommon__physCellId z, (ServingCellConfigCommon__downlinkConfigCommon z, (ServingCellConfigCommon__uplinkConfigCommon z, (ServingCellConfigCommon__supplementaryUplinkConfig z, (ServingCellConfigCommon__n_TimingAdvanceOffset z, (ServingCellConfigCommon__ssb_PositionsInBurst z, (ServingCellConfigCommon__ssb_periodicityServingCell z, (ServingCellConfigCommon__dmrs_TypeA_Position z, (ServingCellConfigCommon__lte_CRS_ToMatchAround z, (ServingCellConfigCommon__rateMatchPatternToAddModList z, (ServingCellConfigCommon__rateMatchPatternToReleaseList z, (ServingCellConfigCommon__ssbSubcarrierSpacing z, (ServingCellConfigCommon__tdd_UL_DL_ConfigurationCommon z, (ServingCellConfigCommon__ss_PBCH_BlockPower z, tt))))))))))))))), (
(ServingCellConfigCommon__ext0 z, (ServingCellConfigCommon__ext1 z, (ServingCellConfigCommon__ext2 z, tt))))).
Definition ServingCellConfigCommon__F2 (y : ServingCellConfigCommon__list_type) : ServingCellConfigCommon__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, _)))))))))))))), (i0, (i1, (i2, _))))=>
    make__ServingCellConfigCommon__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 i0 i1 i2
  end.
Definition ServingCellConfigCommon__helper1 : (forall a : ServingCellConfigCommon__Type, ServingCellConfigCommon__cond a -> ServingCellConfigCommon__list_cond (ServingCellConfigCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ServingCellConfigCommon__helper2 : (forall a : ServingCellConfigCommon__Type, ServingCellConfigCommon__F2 (ServingCellConfigCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ServingCellConfigCommon__helper3 : (forall b : ServingCellConfigCommon__list_type, ServingCellConfigCommon__list_cond b -> ServingCellConfigCommon__cond (ServingCellConfigCommon__F2 b) /\ ServingCellConfigCommon__F1 (ServingCellConfigCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ServingCellConfigCommon__cond, ServingCellConfigCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ServingCellConfigCommon__Format : T_Format ServingCellConfigCommon__Type ServingCellConfigCommon__cond :=
 proj2_format ServingCellConfigCommon__cond ServingCellConfigCommon__list_format  ServingCellConfigCommon__F1 ServingCellConfigCommon__F2 ServingCellConfigCommon__helper1 ServingCellConfigCommon__helper2 ServingCellConfigCommon__helper3.

Opaque ServingCellConfigCommon__cond ServingCellConfigCommon__Format.

