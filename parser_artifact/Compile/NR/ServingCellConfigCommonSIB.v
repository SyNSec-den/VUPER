Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DownlinkConfigCommonSIB.

Opaque DownlinkConfigCommonSIB__cond DownlinkConfigCommonSIB__Format.

Require Import NR.UplinkConfigCommonSIB.

Opaque UplinkConfigCommonSIB__cond UplinkConfigCommonSIB__Format.

Require Import NR.UplinkConfigCommonSIB.

Opaque UplinkConfigCommonSIB__cond UplinkConfigCommonSIB__Format.

Inductive ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Type : Set :=
 | ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n0
 | ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n25600
 | ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n39936
.
Definition ServingCellConfigCommonSIB__n_TimingAdvanceOffset__cond := (fun (_ : ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Type) => True).
Lemma ServingCellConfigCommonSIB__n_TimingAdvanceOffset__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommonSIB__n_TimingAdvanceOffset__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ServingCellConfigCommonSIB__n_TimingAdvanceOffset__nat__helper.

Definition ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F1 t :=
  match t with
  | ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n0 => 0
  | ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n25600 => 1
  | ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n39936 => 2
  end.
Definition ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F2 n :=
  match n with
  | 0 => ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n0
  | 1 => ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n25600
  | 2 => ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n39936
  | _ => ServingCellConfigCommonSIB__n_TimingAdvanceOffset__n0
  end.
Lemma ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F1F2 : forall x : ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Type, (ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F1 x <= 2) /\ ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F2 (ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F2F1 : forall (y : nat) (H : y <= 2), ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F1 (ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F2 y) = y. enum_solve H y. Qed.

Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__Type := bit_string_fixed.
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__Type := bit_string_fixed.
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Record ServingCellConfigCommonSIB__ssb_PositionsInBurst__Type : Set :=
  make__ServingCellConfigCommonSIB__ssb_PositionsInBurst__Type {
    ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup : ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__Type ;
    ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence : option ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__Type ;
}.
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__list := (
 Nor ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__Type ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__cond ::
 Opt ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__Type ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__cond ::
 nil).
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond z := 
  ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__cond (ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup z) /\
  opt_cond ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__cond (ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence z) /\
  True.

Inductive ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Type : Set :=
 | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms5
 | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms10
 | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms20
 | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms40
 | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms80
 | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms160
.
Definition ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__cond := (fun (_ : ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Type) => True).
Lemma ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__nat__helper.

Definition ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F1 t :=
  match t with
  | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms5 => 0
  | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms10 => 1
  | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms20 => 2
  | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms40 => 3
  | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms80 => 4
  | ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms160 => 5
  end.
Definition ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F2 n :=
  match n with
  | 0 => ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms5
  | 1 => ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms10
  | 2 => ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms20
  | 3 => ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms40
  | 4 => ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms80
  | 5 => ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms160
  | _ => ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__ms5
  end.
Lemma ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F1F2 : forall x : ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Type, (ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F1 x <= 5) /\ ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F2 (ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F2F1 : forall (y : nat) (H : y <= 5), ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F1 (ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F2 y) = y. enum_solve H y. Qed.

Require Import NR.TDD_UL_DL_ConfigCommon.

Opaque TDD_UL_DL_ConfigCommon__cond TDD_UL_DL_ConfigCommon__Format.

Lemma ServingCellConfigCommonSIB__ss_PBCH_BlockPower__helper1 : (-60 <= 50)%Z.  lia. Qed.
Lemma ServingCellConfigCommonSIB__ss_PBCH_BlockPower__helper2 : to_bit_sz (Z.to_nat (50 - -60)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (50 - -60))%Z). { apply Zorder.Zle_minus_le_0. apply ServingCellConfigCommonSIB__ss_PBCH_BlockPower__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ServingCellConfigCommonSIB__ss_PBCH_BlockPower__Type := Z.
Definition ServingCellConfigCommonSIB__ss_PBCH_BlockPower__cond := (fun z => (-60 <= z <= 50)%Z).
Require Import NR.SemiStaticChannelAccessConfig_r16.

Opaque SemiStaticChannelAccessConfig_r16__cond SemiStaticChannelAccessConfig_r16__Format.


Inductive ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type : Set :=
  | ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__dynamic : unit -> ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type
  | ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__semiStatic : SemiStaticChannelAccessConfig_r16__Type -> ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type
.
Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons SemiStaticChannelAccessConfig_r16__Type SemiStaticChannelAccessConfig_r16__cond ::
 nil).
Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__cond (c : ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type) := 
  match c with
  | ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__dynamic t => (fun _ => True) t 
  | ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__semiStatic t => SemiStaticChannelAccessConfig_r16__cond t 
  end.

Lemma ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__len_helper1 : to_bit_sz (length ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__len_helper2 : 2 <= length2 ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list.
 simpl. lia. Qed.
Inductive ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Type : Set :=
 | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms0dot5
 | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms1
 | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms2
 | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms3
 | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms4
 | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms5
.
Definition ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__cond := (fun (_ : ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Type) => True).
Lemma ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__nat__helper.

Definition ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F1 t :=
  match t with
  | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms0dot5 => 0
  | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms1 => 1
  | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms2 => 2
  | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms3 => 3
  | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms4 => 4
  | ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms5 => 5
  end.
Definition ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F2 n :=
  match n with
  | 0 => ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms0dot5
  | 1 => ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms1
  | 2 => ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms2
  | 3 => ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms3
  | 4 => ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms4
  | 5 => ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms5
  | _ => ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__ms0dot5
  end.
Lemma ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F1F2 : forall x : ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Type, (ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F1 x <= 5) /\ ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F2 (ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F2F1 : forall (y : nat) (H : y <= 5), ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F1 (ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.HighSpeedConfig_r16.

Opaque HighSpeedConfig_r16__cond HighSpeedConfig_r16__Format.

Record ServingCellConfigCommonSIB__ext0O__Type : Set :=
  make__ServingCellConfigCommonSIB__ext0O__Type {
    ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16 : option ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type ;
    ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16 : option ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Type ;
    ServingCellConfigCommonSIB__ext0O__highSpeedConfig_r16 : option HighSpeedConfig_r16__Type ;
}.
Definition ServingCellConfigCommonSIB__ext0O__list := (
 Opt ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__cond ::
 Opt ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Type ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__cond ::
 Opt HighSpeedConfig_r16__Type HighSpeedConfig_r16__cond ::
 nil).
Definition ServingCellConfigCommonSIB__ext0O__cond z := 
  opt_cond ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__cond (ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16 z) /\
  opt_cond ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__cond (ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16 z) /\
  opt_cond HighSpeedConfig_r16__cond (ServingCellConfigCommonSIB__ext0O__highSpeedConfig_r16 z) /\
  True.

Definition ServingCellConfigCommonSIB__ext0__Type := ServingCellConfigCommonSIB__ext0O__Type.
Definition ServingCellConfigCommonSIB__ext0__cond := ServingCellConfigCommonSIB__ext0O__cond.

Inductive ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Type : Set :=
 | ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__enabled
.
Definition ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__cond := (fun (_ : ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Type) => True).
Lemma ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__nat__helper.

Definition ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F1 t :=
  match t with
  | ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__enabled => 0
  end.
Definition ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F2 n :=
  match n with
  | 0 => ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__enabled
  | _ => ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__enabled
  end.
Lemma ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F1F2 : forall x : ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Type, (ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F1 x <= 0) /\ ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F2 (ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F1 (ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Type : Set :=
 | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot125
 | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot25
 | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot5
 | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot75
 | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms1
 | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms1dot25
.
Definition ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__cond := (fun (_ : ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Type) => True).
Lemma ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__nat__helper.

Definition ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F1 t :=
  match t with
  | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot125 => 0
  | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot25 => 1
  | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot5 => 2
  | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot75 => 3
  | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms1 => 4
  | ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms1dot25 => 5
  end.
Definition ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F2 n :=
  match n with
  | 0 => ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot125
  | 1 => ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot25
  | 2 => ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot5
  | 3 => ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot75
  | 4 => ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms1
  | 5 => ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms1dot25
  | _ => ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__ms0dot125
  end.
Lemma ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F1F2 : forall x : ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Type, (ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F1 x <= 5) /\ ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F2 (ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F2F1 : forall (y : nat) (H : y <= 5), ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F1 (ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F2 y) = y. enum_solve H y. Qed.

Require Import NR.HighSpeedConfigFR2_r17.

Opaque HighSpeedConfigFR2_r17__cond HighSpeedConfigFR2_r17__Format.

Require Import NR.UplinkConfigCommonSIB_v1700.

Opaque UplinkConfigCommonSIB_v1700__cond UplinkConfigCommonSIB_v1700__Format.

Record ServingCellConfigCommonSIB__ext1O__Type : Set :=
  make__ServingCellConfigCommonSIB__ext1O__Type {
    ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17 : option ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Type ;
    ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700 : option ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Type ;
    ServingCellConfigCommonSIB__ext1O__highSpeedConfigFR2_r17 : option HighSpeedConfigFR2_r17__Type ;
    ServingCellConfigCommonSIB__ext1O__uplinkConfigCommon_v1700 : option UplinkConfigCommonSIB_v1700__Type ;
}.
Definition ServingCellConfigCommonSIB__ext1O__list := (
 Opt ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Type ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__cond ::
 Opt ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Type ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__cond ::
 Opt HighSpeedConfigFR2_r17__Type HighSpeedConfigFR2_r17__cond ::
 Opt UplinkConfigCommonSIB_v1700__Type UplinkConfigCommonSIB_v1700__cond ::
 nil).
Definition ServingCellConfigCommonSIB__ext1O__cond z := 
  opt_cond ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__cond (ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17 z) /\
  opt_cond ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__cond (ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700 z) /\
  opt_cond HighSpeedConfigFR2_r17__cond (ServingCellConfigCommonSIB__ext1O__highSpeedConfigFR2_r17 z) /\
  opt_cond UplinkConfigCommonSIB_v1700__cond (ServingCellConfigCommonSIB__ext1O__uplinkConfigCommon_v1700 z) /\
  True.

Definition ServingCellConfigCommonSIB__ext1__Type := ServingCellConfigCommonSIB__ext1O__Type.
Definition ServingCellConfigCommonSIB__ext1__cond := ServingCellConfigCommonSIB__ext1O__cond.

Inductive ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Type : Set :=
 | ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__true
.
Definition ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__cond := (fun (_ : ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Type) => True).
Lemma ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__nat__helper.

Definition ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F1 t :=
  match t with
  | ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__true => 0
  end.
Definition ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F2 n :=
  match n with
  | 0 => ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__true
  | _ => ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__true
  end.
Lemma ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F1F2 : forall x : ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Type, (ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F1 x <= 0) /\ ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F2 (ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F1 x) = x. imp_solve. Qed.
Lemma ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F2F1 : forall (y : nat) (H : y <= 0), ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F1 (ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F2 y) = y. enum_solve H y. Qed.

Record ServingCellConfigCommonSIB__ext2O__Type : Set :=
  make__ServingCellConfigCommonSIB__ext2O__Type {
    ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17 : option ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Type ;
}.
Definition ServingCellConfigCommonSIB__ext2O__list := (
 Opt ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Type ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__cond ::
 nil).
Definition ServingCellConfigCommonSIB__ext2O__cond z := 
  opt_cond ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__cond (ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17 z) /\
  True.

Definition ServingCellConfigCommonSIB__ext2__Type := ServingCellConfigCommonSIB__ext2O__Type.
Definition ServingCellConfigCommonSIB__ext2__cond := ServingCellConfigCommonSIB__ext2O__cond.

Record ServingCellConfigCommonSIB__Type : Set :=
  make__ServingCellConfigCommonSIB__Type {
    ServingCellConfigCommonSIB__downlinkConfigCommon : DownlinkConfigCommonSIB__Type ;
    ServingCellConfigCommonSIB__uplinkConfigCommon : option UplinkConfigCommonSIB__Type ;
    ServingCellConfigCommonSIB__supplementaryUplink : option UplinkConfigCommonSIB__Type ;
    ServingCellConfigCommonSIB__n_TimingAdvanceOffset : option ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Type ;
    ServingCellConfigCommonSIB__ssb_PositionsInBurst : ServingCellConfigCommonSIB__ssb_PositionsInBurst__Type ;
    ServingCellConfigCommonSIB__ssb_PeriodicityServingCell : ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Type ;
    ServingCellConfigCommonSIB__tdd_UL_DL_ConfigurationCommon : option TDD_UL_DL_ConfigCommon__Type ;
    ServingCellConfigCommonSIB__ss_PBCH_BlockPower : Z ;
    ServingCellConfigCommonSIB__ext0 : option ServingCellConfigCommonSIB__ext0__Type ;
    ServingCellConfigCommonSIB__ext1 : option ServingCellConfigCommonSIB__ext1__Type ;
    ServingCellConfigCommonSIB__ext2 : option ServingCellConfigCommonSIB__ext2__Type ;
}.
Definition ServingCellConfigCommonSIB__root_list : list seq_elem := (
 Nor DownlinkConfigCommonSIB__Type DownlinkConfigCommonSIB__cond ::
 Opt UplinkConfigCommonSIB__Type UplinkConfigCommonSIB__cond ::
 Opt UplinkConfigCommonSIB__Type UplinkConfigCommonSIB__cond ::
 Opt ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Type ServingCellConfigCommonSIB__n_TimingAdvanceOffset__cond ::
 Nor ServingCellConfigCommonSIB__ssb_PositionsInBurst__Type ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond ::
 Nor ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Type ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__cond ::
 Opt TDD_UL_DL_ConfigCommon__Type TDD_UL_DL_ConfigCommon__cond ::
 Nor Z ServingCellConfigCommonSIB__ss_PBCH_BlockPower__cond ::
 nil).
Definition ServingCellConfigCommonSIB__ext_list : list typ := (
  typ_cons ServingCellConfigCommonSIB__ext0__Type ServingCellConfigCommonSIB__ext0__cond ::
  typ_cons ServingCellConfigCommonSIB__ext1__Type ServingCellConfigCommonSIB__ext1__cond ::
  typ_cons ServingCellConfigCommonSIB__ext2__Type ServingCellConfigCommonSIB__ext2__cond ::
  nil).
Definition ServingCellConfigCommonSIB__cond (z : ServingCellConfigCommonSIB__Type) := 
(  DownlinkConfigCommonSIB__cond (ServingCellConfigCommonSIB__downlinkConfigCommon z) /\
  opt_cond UplinkConfigCommonSIB__cond (ServingCellConfigCommonSIB__uplinkConfigCommon z) /\
  opt_cond UplinkConfigCommonSIB__cond (ServingCellConfigCommonSIB__supplementaryUplink z) /\
  opt_cond ServingCellConfigCommonSIB__n_TimingAdvanceOffset__cond (ServingCellConfigCommonSIB__n_TimingAdvanceOffset z) /\
  ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond (ServingCellConfigCommonSIB__ssb_PositionsInBurst z) /\
  ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__cond (ServingCellConfigCommonSIB__ssb_PeriodicityServingCell z) /\
  opt_cond TDD_UL_DL_ConfigCommon__cond (ServingCellConfigCommonSIB__tdd_UL_DL_ConfigurationCommon z) /\
  ServingCellConfigCommonSIB__ss_PBCH_BlockPower__cond (ServingCellConfigCommonSIB__ss_PBCH_BlockPower z) /\
  True) /\ 
(  opt_cond ServingCellConfigCommonSIB__ext0__cond (ServingCellConfigCommonSIB__ext0 z) /\
  opt_cond ServingCellConfigCommonSIB__ext1__cond (ServingCellConfigCommonSIB__ext1 z) /\
  opt_cond ServingCellConfigCommonSIB__ext2__cond (ServingCellConfigCommonSIB__ext2 z) /\
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
Definition ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Format : T_Format ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommonSIB__n_TimingAdvanceOffset__nat__Format ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F1 ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F2 ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F1F2 ServingCellConfigCommonSIB__n_TimingAdvanceOffset__F2F1.

Opaque ServingCellConfigCommonSIB__n_TimingAdvanceOffset__cond ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Format.

Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__Format : T_Format ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__Type ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__cond ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__Format.

Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__Format : T_Format ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__Type ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__cond ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__Format.


Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommonSIB__ssb_PositionsInBurst__list.
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__Format_list : ServingCellConfigCommonSIB__ssb_PositionsInBurst__Format_Type :=
  (ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup__Format, (ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence__Format, unit_format)).
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__list__Format := (*Eval compute in *) seq_format ServingCellConfigCommonSIB__ssb_PositionsInBurst__list ServingCellConfigCommonSIB__ssb_PositionsInBurst__Format_list.
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1 z :=
  (ServingCellConfigCommonSIB__ssb_PositionsInBurst__inOneGroup z, (ServingCellConfigCommonSIB__ssb_PositionsInBurst__groupPresence z, tt)).
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__F2 (y : seq_type ServingCellConfigCommonSIB__ssb_PositionsInBurst__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ServingCellConfigCommonSIB__ssb_PositionsInBurst__Type i0 i1
  end.
Lemma ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1F2_cond (z : ServingCellConfigCommonSIB__ssb_PositionsInBurst__Type)
  : ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond z ->
  (seq_cond ServingCellConfigCommonSIB__ssb_PositionsInBurst__list (ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1 z)).
intro H. unfold ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond in H. simpl. auto. Qed.
Lemma ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1F2_cond2 (z : ServingCellConfigCommonSIB__ssb_PositionsInBurst__Type)
 : ServingCellConfigCommonSIB__ssb_PositionsInBurst__F2 (ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfigCommonSIB__ssb_PositionsInBurst__F2F1_cond (y : seq_type ServingCellConfigCommonSIB__ssb_PositionsInBurst__list)
  : seq_cond ServingCellConfigCommonSIB__ssb_PositionsInBurst__list y ->
 (ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond (ServingCellConfigCommonSIB__ssb_PositionsInBurst__F2 y)) /\  ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1 (ServingCellConfigCommonSIB__ssb_PositionsInBurst__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfigCommonSIB__ssb_PositionsInBurst__Format : T_Format ServingCellConfigCommonSIB__ssb_PositionsInBurst__Type ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond :=
        proj2_format  ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond ServingCellConfigCommonSIB__ssb_PositionsInBurst__list__Format
    ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1 ServingCellConfigCommonSIB__ssb_PositionsInBurst__F2 ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1F2_cond  ServingCellConfigCommonSIB__ssb_PositionsInBurst__F1F2_cond2 ServingCellConfigCommonSIB__ssb_PositionsInBurst__F2F1_cond.
Opaque ServingCellConfigCommonSIB__ssb_PositionsInBurst__cond ServingCellConfigCommonSIB__ssb_PositionsInBurst__Format.

Definition ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Format : T_Format ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__nat__Format ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F1 ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F2 ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F1F2 ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__F2F1.

Opaque ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__cond ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Format.

Definition ServingCellConfigCommonSIB__ss_PBCH_BlockPower__Format : T_Format Z ServingCellConfigCommonSIB__ss_PBCH_BlockPower__cond :=
 ranged_int_format (-60) (50) ServingCellConfigCommonSIB__ss_PBCH_BlockPower__helper1 ServingCellConfigCommonSIB__ss_PBCH_BlockPower__helper2.

Opaque ServingCellConfigCommonSIB__ss_PBCH_BlockPower__cond ServingCellConfigCommonSIB__ss_PBCH_BlockPower__Format.


Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Format_Type := Eval cbn in get_formats ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list.
Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Format_list : ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Format_Type :=
  (unit__Format, (SemiStaticChannelAccessConfig_r16__Format, unit__Format)).
Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list__Format := Eval compute in choice_format ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__len_helper1 ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__len_helper2  ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Format_list.
Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F1 (z : ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type) : (choice ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list) :=
  match z with
   | ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__dynamic t => existT _ 0 t
  | ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__semiStatic t => existT _ 1 t
  end.
Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__g := (fun n => typ_set (get_nth_typ ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list n)).
Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F2 (y : choice ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list) : ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__g n -> ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type) with
    | 0 => fun (t : unit) => ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__dynamic t 
    | 1 => fun (t : SemiStaticChannelAccessConfig_r16__Type) => ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__semiStatic t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type with end) n0
           end t0).

Lemma ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__helper2 :  forall (y : ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type), ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__cond y -> choice_cond ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list (ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__helper3 :  forall (y : ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type), ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F2 (ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__helper4 : (forall b : choice ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list, choice_cond ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list b -> ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__cond (ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F2 b) /\ ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F1 (ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F1 ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F2.
Definition ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Format : T_Format ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Type ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__cond :=
  (* Eval compute in *) proj2_format ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__cond ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__list__Format ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F1 ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__F2 ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__helper2 ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__helper3 ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__helper4.
Opaque ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__cond ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Format.

Definition ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Format : T_Format ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__nat__Format ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F1 ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F2 ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F1F2 ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__F2F1.

Opaque ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__cond ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Format.


Definition ServingCellConfigCommonSIB__ext0O__Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommonSIB__ext0O__list.
Definition ServingCellConfigCommonSIB__ext0O__Format_list : ServingCellConfigCommonSIB__ext0O__Format_Type :=
  (ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16__Format, (ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16__Format, (HighSpeedConfig_r16__Format, unit_format))).
Definition ServingCellConfigCommonSIB__ext0O__list__Format := (*Eval compute in *) seq_format ServingCellConfigCommonSIB__ext0O__list ServingCellConfigCommonSIB__ext0O__Format_list.
Definition ServingCellConfigCommonSIB__ext0O__F1 z :=
  (ServingCellConfigCommonSIB__ext0O__channelAccessMode_r16 z, (ServingCellConfigCommonSIB__ext0O__discoveryBurstWindowLength_r16 z, (ServingCellConfigCommonSIB__ext0O__highSpeedConfig_r16 z, tt))).
Definition ServingCellConfigCommonSIB__ext0O__F2 (y : seq_type ServingCellConfigCommonSIB__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ServingCellConfigCommonSIB__ext0O__Type i0 i1 i2
  end.
Lemma ServingCellConfigCommonSIB__ext0O__F1F2_cond (z : ServingCellConfigCommonSIB__ext0O__Type)
  : ServingCellConfigCommonSIB__ext0O__cond z ->
  (seq_cond ServingCellConfigCommonSIB__ext0O__list (ServingCellConfigCommonSIB__ext0O__F1 z)).
intro H. unfold ServingCellConfigCommonSIB__ext0O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfigCommonSIB__ext0O__F1F2_cond2 (z : ServingCellConfigCommonSIB__ext0O__Type)
 : ServingCellConfigCommonSIB__ext0O__F2 (ServingCellConfigCommonSIB__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfigCommonSIB__ext0O__F2F1_cond (y : seq_type ServingCellConfigCommonSIB__ext0O__list)
  : seq_cond ServingCellConfigCommonSIB__ext0O__list y ->
 (ServingCellConfigCommonSIB__ext0O__cond (ServingCellConfigCommonSIB__ext0O__F2 y)) /\  ServingCellConfigCommonSIB__ext0O__F1 (ServingCellConfigCommonSIB__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfigCommonSIB__ext0O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfigCommonSIB__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfigCommonSIB__ext0O__Format : T_Format ServingCellConfigCommonSIB__ext0O__Type ServingCellConfigCommonSIB__ext0O__cond :=
        proj2_format  ServingCellConfigCommonSIB__ext0O__cond ServingCellConfigCommonSIB__ext0O__list__Format
    ServingCellConfigCommonSIB__ext0O__F1 ServingCellConfigCommonSIB__ext0O__F2 ServingCellConfigCommonSIB__ext0O__F1F2_cond  ServingCellConfigCommonSIB__ext0O__F1F2_cond2 ServingCellConfigCommonSIB__ext0O__F2F1_cond.
Opaque ServingCellConfigCommonSIB__ext0O__cond ServingCellConfigCommonSIB__ext0O__Format.

Definition ServingCellConfigCommonSIB__ext0__check_all_none (b : ServingCellConfigCommonSIB__ext0O__Type) : bool :=
match b with 
  | make__ServingCellConfigCommonSIB__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition ServingCellConfigCommonSIB__ext0__Format : T_Format ServingCellConfigCommonSIB__ext0__Type ServingCellConfigCommonSIB__ext0__cond :=
  restrict_add_format ServingCellConfigCommonSIB__ext0__check_all_none ServingCellConfigCommonSIB__ext0O__Format.

Opaque ServingCellConfigCommonSIB__ext0__cond ServingCellConfigCommonSIB__ext0__Format.

Definition ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Format : T_Format ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__nat__Format ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F1 ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F2 ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F1F2 ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__F2F1.

Opaque ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__cond ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Format.

Definition ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Format : T_Format ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__nat__Format ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F1 ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F2 ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F1F2 ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__F2F1.

Opaque ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__cond ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Format.


Definition ServingCellConfigCommonSIB__ext1O__Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommonSIB__ext1O__list.
Definition ServingCellConfigCommonSIB__ext1O__Format_list : ServingCellConfigCommonSIB__ext1O__Format_Type :=
  (ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17__Format, (ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700__Format, (HighSpeedConfigFR2_r17__Format, (UplinkConfigCommonSIB_v1700__Format, unit_format)))).
Definition ServingCellConfigCommonSIB__ext1O__list__Format := (*Eval compute in *) seq_format ServingCellConfigCommonSIB__ext1O__list ServingCellConfigCommonSIB__ext1O__Format_list.
Definition ServingCellConfigCommonSIB__ext1O__F1 z :=
  (ServingCellConfigCommonSIB__ext1O__channelAccessMode2_r17 z, (ServingCellConfigCommonSIB__ext1O__discoveryBurstWindowLength_v1700 z, (ServingCellConfigCommonSIB__ext1O__highSpeedConfigFR2_r17 z, (ServingCellConfigCommonSIB__ext1O__uplinkConfigCommon_v1700 z, tt)))).
Definition ServingCellConfigCommonSIB__ext1O__F2 (y : seq_type ServingCellConfigCommonSIB__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ServingCellConfigCommonSIB__ext1O__Type i0 i1 i2 i3
  end.
Lemma ServingCellConfigCommonSIB__ext1O__F1F2_cond (z : ServingCellConfigCommonSIB__ext1O__Type)
  : ServingCellConfigCommonSIB__ext1O__cond z ->
  (seq_cond ServingCellConfigCommonSIB__ext1O__list (ServingCellConfigCommonSIB__ext1O__F1 z)).
intro H. unfold ServingCellConfigCommonSIB__ext1O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfigCommonSIB__ext1O__F1F2_cond2 (z : ServingCellConfigCommonSIB__ext1O__Type)
 : ServingCellConfigCommonSIB__ext1O__F2 (ServingCellConfigCommonSIB__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfigCommonSIB__ext1O__F2F1_cond (y : seq_type ServingCellConfigCommonSIB__ext1O__list)
  : seq_cond ServingCellConfigCommonSIB__ext1O__list y ->
 (ServingCellConfigCommonSIB__ext1O__cond (ServingCellConfigCommonSIB__ext1O__F2 y)) /\  ServingCellConfigCommonSIB__ext1O__F1 (ServingCellConfigCommonSIB__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfigCommonSIB__ext1O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfigCommonSIB__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfigCommonSIB__ext1O__Format : T_Format ServingCellConfigCommonSIB__ext1O__Type ServingCellConfigCommonSIB__ext1O__cond :=
        proj2_format  ServingCellConfigCommonSIB__ext1O__cond ServingCellConfigCommonSIB__ext1O__list__Format
    ServingCellConfigCommonSIB__ext1O__F1 ServingCellConfigCommonSIB__ext1O__F2 ServingCellConfigCommonSIB__ext1O__F1F2_cond  ServingCellConfigCommonSIB__ext1O__F1F2_cond2 ServingCellConfigCommonSIB__ext1O__F2F1_cond.
Opaque ServingCellConfigCommonSIB__ext1O__cond ServingCellConfigCommonSIB__ext1O__Format.

Definition ServingCellConfigCommonSIB__ext1__check_all_none (b : ServingCellConfigCommonSIB__ext1O__Type) : bool :=
match b with 
  | make__ServingCellConfigCommonSIB__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition ServingCellConfigCommonSIB__ext1__Format : T_Format ServingCellConfigCommonSIB__ext1__Type ServingCellConfigCommonSIB__ext1__cond :=
  restrict_add_format ServingCellConfigCommonSIB__ext1__check_all_none ServingCellConfigCommonSIB__ext1O__Format.

Opaque ServingCellConfigCommonSIB__ext1__cond ServingCellConfigCommonSIB__ext1__Format.

Definition ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Format : T_Format ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__nat__Format ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F1 ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F2 ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F1F2 ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__F2F1.

Opaque ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__cond ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Format.


Definition ServingCellConfigCommonSIB__ext2O__Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommonSIB__ext2O__list.
Definition ServingCellConfigCommonSIB__ext2O__Format_list : ServingCellConfigCommonSIB__ext2O__Format_Type :=
  (ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17__Format, unit_format).
Definition ServingCellConfigCommonSIB__ext2O__list__Format := (*Eval compute in *) seq_format ServingCellConfigCommonSIB__ext2O__list ServingCellConfigCommonSIB__ext2O__Format_list.
Definition ServingCellConfigCommonSIB__ext2O__F1 z :=
  (ServingCellConfigCommonSIB__ext2O__enhancedMeasurementLEO_r17 z, tt).
Definition ServingCellConfigCommonSIB__ext2O__F2 (y : seq_type ServingCellConfigCommonSIB__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__ServingCellConfigCommonSIB__ext2O__Type i0
  end.
Lemma ServingCellConfigCommonSIB__ext2O__F1F2_cond (z : ServingCellConfigCommonSIB__ext2O__Type)
  : ServingCellConfigCommonSIB__ext2O__cond z ->
  (seq_cond ServingCellConfigCommonSIB__ext2O__list (ServingCellConfigCommonSIB__ext2O__F1 z)).
intro H. unfold ServingCellConfigCommonSIB__ext2O__cond in H. simpl. auto. Qed.
Lemma ServingCellConfigCommonSIB__ext2O__F1F2_cond2 (z : ServingCellConfigCommonSIB__ext2O__Type)
 : ServingCellConfigCommonSIB__ext2O__F2 (ServingCellConfigCommonSIB__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ServingCellConfigCommonSIB__ext2O__F2F1_cond (y : seq_type ServingCellConfigCommonSIB__ext2O__list)
  : seq_cond ServingCellConfigCommonSIB__ext2O__list y ->
 (ServingCellConfigCommonSIB__ext2O__cond (ServingCellConfigCommonSIB__ext2O__F2 y)) /\  ServingCellConfigCommonSIB__ext2O__F1 (ServingCellConfigCommonSIB__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ServingCellConfigCommonSIB__ext2O__cond. simpl in *. auto.
 - simpl. unfold ServingCellConfigCommonSIB__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ServingCellConfigCommonSIB__ext2O__Format : T_Format ServingCellConfigCommonSIB__ext2O__Type ServingCellConfigCommonSIB__ext2O__cond :=
        proj2_format  ServingCellConfigCommonSIB__ext2O__cond ServingCellConfigCommonSIB__ext2O__list__Format
    ServingCellConfigCommonSIB__ext2O__F1 ServingCellConfigCommonSIB__ext2O__F2 ServingCellConfigCommonSIB__ext2O__F1F2_cond  ServingCellConfigCommonSIB__ext2O__F1F2_cond2 ServingCellConfigCommonSIB__ext2O__F2F1_cond.
Opaque ServingCellConfigCommonSIB__ext2O__cond ServingCellConfigCommonSIB__ext2O__Format.

Definition ServingCellConfigCommonSIB__ext2__check_all_none (b : ServingCellConfigCommonSIB__ext2O__Type) : bool :=
match b with 
  | make__ServingCellConfigCommonSIB__ext2O__Type None  => false 
  | _ => true 
 end.
Definition ServingCellConfigCommonSIB__ext2__Format : T_Format ServingCellConfigCommonSIB__ext2__Type ServingCellConfigCommonSIB__ext2__cond :=
  restrict_add_format ServingCellConfigCommonSIB__ext2__check_all_none ServingCellConfigCommonSIB__ext2O__Format.

Opaque ServingCellConfigCommonSIB__ext2__cond ServingCellConfigCommonSIB__ext2__Format.


Definition ServingCellConfigCommonSIB__root_Format_Type := Eval cbn in seq_format_prod ServingCellConfigCommonSIB__root_list.
Definition ServingCellConfigCommonSIB__root_Format_list : ServingCellConfigCommonSIB__root_Format_Type :=
  (DownlinkConfigCommonSIB__Format, (UplinkConfigCommonSIB__Format, (UplinkConfigCommonSIB__Format, (ServingCellConfigCommonSIB__n_TimingAdvanceOffset__Format, (ServingCellConfigCommonSIB__ssb_PositionsInBurst__Format, (ServingCellConfigCommonSIB__ssb_PeriodicityServingCell__Format, (TDD_UL_DL_ConfigCommon__Format, (ServingCellConfigCommonSIB__ss_PBCH_BlockPower__Format, unit_format)))))))).

Definition ServingCellConfigCommonSIB__ext_Format_Type := Eval cbn in get_formats ServingCellConfigCommonSIB__ext_list.
Definition ServingCellConfigCommonSIB__ext_Format_list : ServingCellConfigCommonSIB__ext_Format_Type :=
  (ServingCellConfigCommonSIB__ext0__Format, (ServingCellConfigCommonSIB__ext1__Format, (ServingCellConfigCommonSIB__ext2__Format, unit__Format))).

Definition ServingCellConfigCommonSIB__list_type : Set := (seq_type ServingCellConfigCommonSIB__root_list) * (seq_ext_type ServingCellConfigCommonSIB__ext_list).
Definition ServingCellConfigCommonSIB__list_cond (z : ServingCellConfigCommonSIB__list_type) : Prop :=
        (seq_cond ServingCellConfigCommonSIB__root_list (fst z)) /\ (seq_ext_cond ServingCellConfigCommonSIB__ext_list (snd z)).
Definition ServingCellConfigCommonSIB__list_format : T_Format ServingCellConfigCommonSIB__list_type ServingCellConfigCommonSIB__list_cond :=
 (* Eval compute in *) seq_ext_format ServingCellConfigCommonSIB__root_list ServingCellConfigCommonSIB__root_Format_list ServingCellConfigCommonSIB__ext_list ServingCellConfigCommonSIB__ext_Format_list.

Opaque ServingCellConfigCommonSIB__list_format.
Definition ServingCellConfigCommonSIB__F1 (z : ServingCellConfigCommonSIB__Type) : ServingCellConfigCommonSIB__list_type :=
  (((ServingCellConfigCommonSIB__downlinkConfigCommon z, (ServingCellConfigCommonSIB__uplinkConfigCommon z, (ServingCellConfigCommonSIB__supplementaryUplink z, (ServingCellConfigCommonSIB__n_TimingAdvanceOffset z, (ServingCellConfigCommonSIB__ssb_PositionsInBurst z, (ServingCellConfigCommonSIB__ssb_PeriodicityServingCell z, (ServingCellConfigCommonSIB__tdd_UL_DL_ConfigurationCommon z, (ServingCellConfigCommonSIB__ss_PBCH_BlockPower z, tt))))))))), (
(ServingCellConfigCommonSIB__ext0 z, (ServingCellConfigCommonSIB__ext1 z, (ServingCellConfigCommonSIB__ext2 z, tt))))).
Definition ServingCellConfigCommonSIB__F2 (y : ServingCellConfigCommonSIB__list_type) : ServingCellConfigCommonSIB__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, (i1, (i2, _))))=>
    make__ServingCellConfigCommonSIB__Type j0 j1 j2 j3 j4 j5 j6 j7 i0 i1 i2
  end.
Definition ServingCellConfigCommonSIB__helper1 : (forall a : ServingCellConfigCommonSIB__Type, ServingCellConfigCommonSIB__cond a -> ServingCellConfigCommonSIB__list_cond (ServingCellConfigCommonSIB__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ServingCellConfigCommonSIB__helper2 : (forall a : ServingCellConfigCommonSIB__Type, ServingCellConfigCommonSIB__F2 (ServingCellConfigCommonSIB__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ServingCellConfigCommonSIB__helper3 : (forall b : ServingCellConfigCommonSIB__list_type, ServingCellConfigCommonSIB__list_cond b -> ServingCellConfigCommonSIB__cond (ServingCellConfigCommonSIB__F2 b) /\ ServingCellConfigCommonSIB__F1 (ServingCellConfigCommonSIB__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ServingCellConfigCommonSIB__cond, ServingCellConfigCommonSIB__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ServingCellConfigCommonSIB__Format : T_Format ServingCellConfigCommonSIB__Type ServingCellConfigCommonSIB__cond :=
 proj2_format ServingCellConfigCommonSIB__cond ServingCellConfigCommonSIB__list_format  ServingCellConfigCommonSIB__F1 ServingCellConfigCommonSIB__F2 ServingCellConfigCommonSIB__helper1 ServingCellConfigCommonSIB__helper2 ServingCellConfigCommonSIB__helper3.

Opaque ServingCellConfigCommonSIB__cond ServingCellConfigCommonSIB__Format.

