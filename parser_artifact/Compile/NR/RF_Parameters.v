Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandNR.

Opaque BandNR__cond BandNR__Format.

Definition RF_Parameters__supportedBandListNR__Type := list BandNR__Type.

Lemma RF_Parameters__supportedBandListNR__helper1 : (0 <= 1 <= maxBands)%Z. unfold maxBands.
 lia. Qed.
Lemma RF_Parameters__supportedBandListNR__helper2 : to_bit_sz (Z.to_nat (maxBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RF_Parameters__supportedBandListNR__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RF_Parameters__supportedBandListNR__cond (z : RF_Parameters__supportedBandListNR__Type) :=  (1 <= Z.of_nat (length z) <= maxBands)%Z /\ (list_and BandNR__cond z) .

Require Import NR.BandCombinationList.

Opaque BandCombinationList__cond BandCombinationList__Format.

Require Import NR.FreqBandList.

Opaque FreqBandList__cond FreqBandList__Format.

Require Import NR.BandCombinationList_v1540.

Opaque BandCombinationList_v1540__cond BandCombinationList_v1540__Format.

Inductive RF_Parameters__ext0O__srs_SwitchingTimeRequested__Type : Set :=
 | RF_Parameters__ext0O__srs_SwitchingTimeRequested__true
.
Definition RF_Parameters__ext0O__srs_SwitchingTimeRequested__cond := (fun (_ : RF_Parameters__ext0O__srs_SwitchingTimeRequested__Type) => True).
Lemma RF_Parameters__ext0O__srs_SwitchingTimeRequested__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RF_Parameters__ext0O__srs_SwitchingTimeRequested__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RF_Parameters__ext0O__srs_SwitchingTimeRequested__nat__helper.

Definition RF_Parameters__ext0O__srs_SwitchingTimeRequested__F1 t :=
  match t with
  | RF_Parameters__ext0O__srs_SwitchingTimeRequested__true => 0
  end.
Definition RF_Parameters__ext0O__srs_SwitchingTimeRequested__F2 n :=
  match n with
  | 0 => RF_Parameters__ext0O__srs_SwitchingTimeRequested__true
  | _ => RF_Parameters__ext0O__srs_SwitchingTimeRequested__true
  end.
Lemma RF_Parameters__ext0O__srs_SwitchingTimeRequested__F1F2 : forall x : RF_Parameters__ext0O__srs_SwitchingTimeRequested__Type, (RF_Parameters__ext0O__srs_SwitchingTimeRequested__F1 x <= 0) /\ RF_Parameters__ext0O__srs_SwitchingTimeRequested__F2 (RF_Parameters__ext0O__srs_SwitchingTimeRequested__F1 x) = x. imp_solve. Qed.
Lemma RF_Parameters__ext0O__srs_SwitchingTimeRequested__F2F1 : forall (y : nat) (H : y <= 0), RF_Parameters__ext0O__srs_SwitchingTimeRequested__F1 (RF_Parameters__ext0O__srs_SwitchingTimeRequested__F2 y) = y. enum_solve H y. Qed.

Record RF_Parameters__ext0O__Type : Set :=
  make__RF_Parameters__ext0O__Type {
    RF_Parameters__ext0O__supportedBandCombinationList_v1540 : option BandCombinationList_v1540__Type ;
    RF_Parameters__ext0O__srs_SwitchingTimeRequested : option RF_Parameters__ext0O__srs_SwitchingTimeRequested__Type ;
}.
Definition RF_Parameters__ext0O__list := (
 Opt BandCombinationList_v1540__Type BandCombinationList_v1540__cond ::
 Opt RF_Parameters__ext0O__srs_SwitchingTimeRequested__Type RF_Parameters__ext0O__srs_SwitchingTimeRequested__cond ::
 nil).
Definition RF_Parameters__ext0O__cond z := 
  opt_cond BandCombinationList_v1540__cond (RF_Parameters__ext0O__supportedBandCombinationList_v1540 z) /\
  opt_cond RF_Parameters__ext0O__srs_SwitchingTimeRequested__cond (RF_Parameters__ext0O__srs_SwitchingTimeRequested z) /\
  True.

Definition RF_Parameters__ext0__Type := RF_Parameters__ext0O__Type.
Definition RF_Parameters__ext0__cond := RF_Parameters__ext0O__cond.

Require Import NR.BandCombinationList_v1550.

Opaque BandCombinationList_v1550__cond BandCombinationList_v1550__Format.

Record RF_Parameters__ext1O__Type : Set :=
  make__RF_Parameters__ext1O__Type {
    RF_Parameters__ext1O__supportedBandCombinationList_v1550 : option BandCombinationList_v1550__Type ;
}.
Definition RF_Parameters__ext1O__list := (
 Opt BandCombinationList_v1550__Type BandCombinationList_v1550__cond ::
 nil).
Definition RF_Parameters__ext1O__cond z := 
  opt_cond BandCombinationList_v1550__cond (RF_Parameters__ext1O__supportedBandCombinationList_v1550 z) /\
  True.

Definition RF_Parameters__ext1__Type := RF_Parameters__ext1O__Type.
Definition RF_Parameters__ext1__cond := RF_Parameters__ext1O__cond.

Require Import NR.BandCombinationList_v1560.

Opaque BandCombinationList_v1560__cond BandCombinationList_v1560__Format.

Record RF_Parameters__ext2O__Type : Set :=
  make__RF_Parameters__ext2O__Type {
    RF_Parameters__ext2O__supportedBandCombinationList_v1560 : option BandCombinationList_v1560__Type ;
}.
Definition RF_Parameters__ext2O__list := (
 Opt BandCombinationList_v1560__Type BandCombinationList_v1560__cond ::
 nil).
Definition RF_Parameters__ext2O__cond z := 
  opt_cond BandCombinationList_v1560__cond (RF_Parameters__ext2O__supportedBandCombinationList_v1560 z) /\
  True.

Definition RF_Parameters__ext2__Type := RF_Parameters__ext2O__Type.
Definition RF_Parameters__ext2__cond := RF_Parameters__ext2O__cond.

Require Import NR.BandCombinationList_v1610.

Opaque BandCombinationList_v1610__cond BandCombinationList_v1610__Format.

Require Import NR.BandCombinationListSidelinkEUTRA_NR_r16.

Opaque BandCombinationListSidelinkEUTRA_NR_r16__cond BandCombinationListSidelinkEUTRA_NR_r16__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_r16.

Opaque BandCombinationList_UplinkTxSwitch_r16__cond BandCombinationList_UplinkTxSwitch_r16__Format.

Record RF_Parameters__ext3O__Type : Set :=
  make__RF_Parameters__ext3O__Type {
    RF_Parameters__ext3O__supportedBandCombinationList_v1610 : option BandCombinationList_v1610__Type ;
    RF_Parameters__ext3O__supportedBandCombinationListSidelinkEUTRA_NR_r16 : option BandCombinationListSidelinkEUTRA_NR_r16__Type ;
    RF_Parameters__ext3O__supportedBandCombinationList_UplinkTxSwitch_r16 : option BandCombinationList_UplinkTxSwitch_r16__Type ;
}.
Definition RF_Parameters__ext3O__list := (
 Opt BandCombinationList_v1610__Type BandCombinationList_v1610__cond ::
 Opt BandCombinationListSidelinkEUTRA_NR_r16__Type BandCombinationListSidelinkEUTRA_NR_r16__cond ::
 Opt BandCombinationList_UplinkTxSwitch_r16__Type BandCombinationList_UplinkTxSwitch_r16__cond ::
 nil).
Definition RF_Parameters__ext3O__cond z := 
  opt_cond BandCombinationList_v1610__cond (RF_Parameters__ext3O__supportedBandCombinationList_v1610 z) /\
  opt_cond BandCombinationListSidelinkEUTRA_NR_r16__cond (RF_Parameters__ext3O__supportedBandCombinationListSidelinkEUTRA_NR_r16 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_r16__cond (RF_Parameters__ext3O__supportedBandCombinationList_UplinkTxSwitch_r16 z) /\
  True.

Definition RF_Parameters__ext3__Type := RF_Parameters__ext3O__Type.
Definition RF_Parameters__ext3__cond := RF_Parameters__ext3O__cond.

Require Import NR.BandCombinationList_v1630.

Opaque BandCombinationList_v1630__cond BandCombinationList_v1630__Format.

Require Import NR.BandCombinationListSidelinkEUTRA_NR_v1630.

Opaque BandCombinationListSidelinkEUTRA_NR_v1630__cond BandCombinationListSidelinkEUTRA_NR_v1630__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1630.

Opaque BandCombinationList_UplinkTxSwitch_v1630__cond BandCombinationList_UplinkTxSwitch_v1630__Format.

Record RF_Parameters__ext4O__Type : Set :=
  make__RF_Parameters__ext4O__Type {
    RF_Parameters__ext4O__supportedBandCombinationList_v1630 : option BandCombinationList_v1630__Type ;
    RF_Parameters__ext4O__supportedBandCombinationListSidelinkEUTRA_NR_v1630 : option BandCombinationListSidelinkEUTRA_NR_v1630__Type ;
    RF_Parameters__ext4O__supportedBandCombinationList_UplinkTxSwitch_v1630 : option BandCombinationList_UplinkTxSwitch_v1630__Type ;
}.
Definition RF_Parameters__ext4O__list := (
 Opt BandCombinationList_v1630__Type BandCombinationList_v1630__cond ::
 Opt BandCombinationListSidelinkEUTRA_NR_v1630__Type BandCombinationListSidelinkEUTRA_NR_v1630__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1630__Type BandCombinationList_UplinkTxSwitch_v1630__cond ::
 nil).
Definition RF_Parameters__ext4O__cond z := 
  opt_cond BandCombinationList_v1630__cond (RF_Parameters__ext4O__supportedBandCombinationList_v1630 z) /\
  opt_cond BandCombinationListSidelinkEUTRA_NR_v1630__cond (RF_Parameters__ext4O__supportedBandCombinationListSidelinkEUTRA_NR_v1630 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1630__cond (RF_Parameters__ext4O__supportedBandCombinationList_UplinkTxSwitch_v1630 z) /\
  True.

Definition RF_Parameters__ext4__Type := RF_Parameters__ext4O__Type.
Definition RF_Parameters__ext4__cond := RF_Parameters__ext4O__cond.

Require Import NR.BandCombinationList_v1640.

Opaque BandCombinationList_v1640__cond BandCombinationList_v1640__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1640.

Opaque BandCombinationList_UplinkTxSwitch_v1640__cond BandCombinationList_UplinkTxSwitch_v1640__Format.

Record RF_Parameters__ext5O__Type : Set :=
  make__RF_Parameters__ext5O__Type {
    RF_Parameters__ext5O__supportedBandCombinationList_v1640 : option BandCombinationList_v1640__Type ;
    RF_Parameters__ext5O__supportedBandCombinationList_UplinkTxSwitch_v1640 : option BandCombinationList_UplinkTxSwitch_v1640__Type ;
}.
Definition RF_Parameters__ext5O__list := (
 Opt BandCombinationList_v1640__Type BandCombinationList_v1640__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1640__Type BandCombinationList_UplinkTxSwitch_v1640__cond ::
 nil).
Definition RF_Parameters__ext5O__cond z := 
  opt_cond BandCombinationList_v1640__cond (RF_Parameters__ext5O__supportedBandCombinationList_v1640 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1640__cond (RF_Parameters__ext5O__supportedBandCombinationList_UplinkTxSwitch_v1640 z) /\
  True.

Definition RF_Parameters__ext5__Type := RF_Parameters__ext5O__Type.
Definition RF_Parameters__ext5__cond := RF_Parameters__ext5O__cond.

Require Import NR.BandCombinationList_v1650.

Opaque BandCombinationList_v1650__cond BandCombinationList_v1650__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1650.

Opaque BandCombinationList_UplinkTxSwitch_v1650__cond BandCombinationList_UplinkTxSwitch_v1650__Format.

Record RF_Parameters__ext6O__Type : Set :=
  make__RF_Parameters__ext6O__Type {
    RF_Parameters__ext6O__supportedBandCombinationList_v1650 : option BandCombinationList_v1650__Type ;
    RF_Parameters__ext6O__supportedBandCombinationList_UplinkTxSwitch_v1650 : option BandCombinationList_UplinkTxSwitch_v1650__Type ;
}.
Definition RF_Parameters__ext6O__list := (
 Opt BandCombinationList_v1650__Type BandCombinationList_v1650__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1650__Type BandCombinationList_UplinkTxSwitch_v1650__cond ::
 nil).
Definition RF_Parameters__ext6O__cond z := 
  opt_cond BandCombinationList_v1650__cond (RF_Parameters__ext6O__supportedBandCombinationList_v1650 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1650__cond (RF_Parameters__ext6O__supportedBandCombinationList_UplinkTxSwitch_v1650 z) /\
  True.

Definition RF_Parameters__ext6__Type := RF_Parameters__ext6O__Type.
Definition RF_Parameters__ext6__cond := RF_Parameters__ext6O__cond.

Inductive RF_Parameters__ext7O__extendedBand_n77_r16__Type : Set :=
 | RF_Parameters__ext7O__extendedBand_n77_r16__supported
.
Definition RF_Parameters__ext7O__extendedBand_n77_r16__cond := (fun (_ : RF_Parameters__ext7O__extendedBand_n77_r16__Type) => True).
Lemma RF_Parameters__ext7O__extendedBand_n77_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RF_Parameters__ext7O__extendedBand_n77_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RF_Parameters__ext7O__extendedBand_n77_r16__nat__helper.

Definition RF_Parameters__ext7O__extendedBand_n77_r16__F1 t :=
  match t with
  | RF_Parameters__ext7O__extendedBand_n77_r16__supported => 0
  end.
Definition RF_Parameters__ext7O__extendedBand_n77_r16__F2 n :=
  match n with
  | 0 => RF_Parameters__ext7O__extendedBand_n77_r16__supported
  | _ => RF_Parameters__ext7O__extendedBand_n77_r16__supported
  end.
Lemma RF_Parameters__ext7O__extendedBand_n77_r16__F1F2 : forall x : RF_Parameters__ext7O__extendedBand_n77_r16__Type, (RF_Parameters__ext7O__extendedBand_n77_r16__F1 x <= 0) /\ RF_Parameters__ext7O__extendedBand_n77_r16__F2 (RF_Parameters__ext7O__extendedBand_n77_r16__F1 x) = x. imp_solve. Qed.
Lemma RF_Parameters__ext7O__extendedBand_n77_r16__F2F1 : forall (y : nat) (H : y <= 0), RF_Parameters__ext7O__extendedBand_n77_r16__F1 (RF_Parameters__ext7O__extendedBand_n77_r16__F2 y) = y. enum_solve H y. Qed.

Record RF_Parameters__ext7O__Type : Set :=
  make__RF_Parameters__ext7O__Type {
    RF_Parameters__ext7O__extendedBand_n77_r16 : option RF_Parameters__ext7O__extendedBand_n77_r16__Type ;
}.
Definition RF_Parameters__ext7O__list := (
 Opt RF_Parameters__ext7O__extendedBand_n77_r16__Type RF_Parameters__ext7O__extendedBand_n77_r16__cond ::
 nil).
Definition RF_Parameters__ext7O__cond z := 
  opt_cond RF_Parameters__ext7O__extendedBand_n77_r16__cond (RF_Parameters__ext7O__extendedBand_n77_r16 z) /\
  True.

Definition RF_Parameters__ext7__Type := RF_Parameters__ext7O__Type.
Definition RF_Parameters__ext7__cond := RF_Parameters__ext7O__cond.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1670.

Opaque BandCombinationList_UplinkTxSwitch_v1670__cond BandCombinationList_UplinkTxSwitch_v1670__Format.

Record RF_Parameters__ext8O__Type : Set :=
  make__RF_Parameters__ext8O__Type {
    RF_Parameters__ext8O__supportedBandCombinationList_UplinkTxSwitch_v1670 : option BandCombinationList_UplinkTxSwitch_v1670__Type ;
}.
Definition RF_Parameters__ext8O__list := (
 Opt BandCombinationList_UplinkTxSwitch_v1670__Type BandCombinationList_UplinkTxSwitch_v1670__cond ::
 nil).
Definition RF_Parameters__ext8O__cond z := 
  opt_cond BandCombinationList_UplinkTxSwitch_v1670__cond (RF_Parameters__ext8O__supportedBandCombinationList_UplinkTxSwitch_v1670 z) /\
  True.

Definition RF_Parameters__ext8__Type := RF_Parameters__ext8O__Type.
Definition RF_Parameters__ext8__cond := RF_Parameters__ext8O__cond.

Require Import NR.BandCombinationList_v1680.

Opaque BandCombinationList_v1680__cond BandCombinationList_v1680__Format.

Record RF_Parameters__ext9O__Type : Set :=
  make__RF_Parameters__ext9O__Type {
    RF_Parameters__ext9O__supportedBandCombinationList_v1680 : option BandCombinationList_v1680__Type ;
}.
Definition RF_Parameters__ext9O__list := (
 Opt BandCombinationList_v1680__Type BandCombinationList_v1680__cond ::
 nil).
Definition RF_Parameters__ext9O__cond z := 
  opt_cond BandCombinationList_v1680__cond (RF_Parameters__ext9O__supportedBandCombinationList_v1680 z) /\
  True.

Definition RF_Parameters__ext9__Type := RF_Parameters__ext9O__Type.
Definition RF_Parameters__ext9__cond := RF_Parameters__ext9O__cond.

Require Import NR.BandCombinationList_v1690.

Opaque BandCombinationList_v1690__cond BandCombinationList_v1690__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1690.

Opaque BandCombinationList_UplinkTxSwitch_v1690__cond BandCombinationList_UplinkTxSwitch_v1690__Format.

Record RF_Parameters__ext10O__Type : Set :=
  make__RF_Parameters__ext10O__Type {
    RF_Parameters__ext10O__supportedBandCombinationList_v1690 : option BandCombinationList_v1690__Type ;
    RF_Parameters__ext10O__supportedBandCombinationList_UplinkTxSwitch_v1690 : option BandCombinationList_UplinkTxSwitch_v1690__Type ;
}.
Definition RF_Parameters__ext10O__list := (
 Opt BandCombinationList_v1690__Type BandCombinationList_v1690__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1690__Type BandCombinationList_UplinkTxSwitch_v1690__cond ::
 nil).
Definition RF_Parameters__ext10O__cond z := 
  opt_cond BandCombinationList_v1690__cond (RF_Parameters__ext10O__supportedBandCombinationList_v1690 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1690__cond (RF_Parameters__ext10O__supportedBandCombinationList_UplinkTxSwitch_v1690 z) /\
  True.

Definition RF_Parameters__ext10__Type := RF_Parameters__ext10O__Type.
Definition RF_Parameters__ext10__cond := RF_Parameters__ext10O__cond.

Require Import NR.BandCombinationList_v1700.

Opaque BandCombinationList_v1700__cond BandCombinationList_v1700__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1700.

Opaque BandCombinationList_UplinkTxSwitch_v1700__cond BandCombinationList_UplinkTxSwitch_v1700__Format.

Require Import NR.BandCombinationListSidelinkEUTRA_NR_v1710.

Opaque BandCombinationListSidelinkEUTRA_NR_v1710__cond BandCombinationListSidelinkEUTRA_NR_v1710__Format.

Inductive RF_Parameters__ext11O__sidelinkRequested_r17__Type : Set :=
 | RF_Parameters__ext11O__sidelinkRequested_r17__true
.
Definition RF_Parameters__ext11O__sidelinkRequested_r17__cond := (fun (_ : RF_Parameters__ext11O__sidelinkRequested_r17__Type) => True).
Lemma RF_Parameters__ext11O__sidelinkRequested_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RF_Parameters__ext11O__sidelinkRequested_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RF_Parameters__ext11O__sidelinkRequested_r17__nat__helper.

Definition RF_Parameters__ext11O__sidelinkRequested_r17__F1 t :=
  match t with
  | RF_Parameters__ext11O__sidelinkRequested_r17__true => 0
  end.
Definition RF_Parameters__ext11O__sidelinkRequested_r17__F2 n :=
  match n with
  | 0 => RF_Parameters__ext11O__sidelinkRequested_r17__true
  | _ => RF_Parameters__ext11O__sidelinkRequested_r17__true
  end.
Lemma RF_Parameters__ext11O__sidelinkRequested_r17__F1F2 : forall x : RF_Parameters__ext11O__sidelinkRequested_r17__Type, (RF_Parameters__ext11O__sidelinkRequested_r17__F1 x <= 0) /\ RF_Parameters__ext11O__sidelinkRequested_r17__F2 (RF_Parameters__ext11O__sidelinkRequested_r17__F1 x) = x. imp_solve. Qed.
Lemma RF_Parameters__ext11O__sidelinkRequested_r17__F2F1 : forall (y : nat) (H : y <= 0), RF_Parameters__ext11O__sidelinkRequested_r17__F1 (RF_Parameters__ext11O__sidelinkRequested_r17__F2 y) = y. enum_solve H y. Qed.

Inductive RF_Parameters__ext11O__extendedBand_n77_2_r17__Type : Set :=
 | RF_Parameters__ext11O__extendedBand_n77_2_r17__supported
.
Definition RF_Parameters__ext11O__extendedBand_n77_2_r17__cond := (fun (_ : RF_Parameters__ext11O__extendedBand_n77_2_r17__Type) => True).
Lemma RF_Parameters__ext11O__extendedBand_n77_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RF_Parameters__ext11O__extendedBand_n77_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RF_Parameters__ext11O__extendedBand_n77_2_r17__nat__helper.

Definition RF_Parameters__ext11O__extendedBand_n77_2_r17__F1 t :=
  match t with
  | RF_Parameters__ext11O__extendedBand_n77_2_r17__supported => 0
  end.
Definition RF_Parameters__ext11O__extendedBand_n77_2_r17__F2 n :=
  match n with
  | 0 => RF_Parameters__ext11O__extendedBand_n77_2_r17__supported
  | _ => RF_Parameters__ext11O__extendedBand_n77_2_r17__supported
  end.
Lemma RF_Parameters__ext11O__extendedBand_n77_2_r17__F1F2 : forall x : RF_Parameters__ext11O__extendedBand_n77_2_r17__Type, (RF_Parameters__ext11O__extendedBand_n77_2_r17__F1 x <= 0) /\ RF_Parameters__ext11O__extendedBand_n77_2_r17__F2 (RF_Parameters__ext11O__extendedBand_n77_2_r17__F1 x) = x. imp_solve. Qed.
Lemma RF_Parameters__ext11O__extendedBand_n77_2_r17__F2F1 : forall (y : nat) (H : y <= 0), RF_Parameters__ext11O__extendedBand_n77_2_r17__F1 (RF_Parameters__ext11O__extendedBand_n77_2_r17__F2 y) = y. enum_solve H y. Qed.

Record RF_Parameters__ext11O__Type : Set :=
  make__RF_Parameters__ext11O__Type {
    RF_Parameters__ext11O__supportedBandCombinationList_v1700 : option BandCombinationList_v1700__Type ;
    RF_Parameters__ext11O__supportedBandCombinationList_UplinkTxSwitch_v1700 : option BandCombinationList_UplinkTxSwitch_v1700__Type ;
    RF_Parameters__ext11O__supportedBandCombinationListSL_RelayDiscovery_r17 : option octet_string ;
    RF_Parameters__ext11O__supportedBandCombinationListSL_NonRelayDiscovery_r17 : option octet_string ;
    RF_Parameters__ext11O__supportedBandCombinationListSidelinkEUTRA_NR_v1710 : option BandCombinationListSidelinkEUTRA_NR_v1710__Type ;
    RF_Parameters__ext11O__sidelinkRequested_r17 : option RF_Parameters__ext11O__sidelinkRequested_r17__Type ;
    RF_Parameters__ext11O__extendedBand_n77_2_r17 : option RF_Parameters__ext11O__extendedBand_n77_2_r17__Type ;
}.
Definition RF_Parameters__ext11O__list := (
 Opt BandCombinationList_v1700__Type BandCombinationList_v1700__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1700__Type BandCombinationList_UplinkTxSwitch_v1700__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt BandCombinationListSidelinkEUTRA_NR_v1710__Type BandCombinationListSidelinkEUTRA_NR_v1710__cond ::
 Opt RF_Parameters__ext11O__sidelinkRequested_r17__Type RF_Parameters__ext11O__sidelinkRequested_r17__cond ::
 Opt RF_Parameters__ext11O__extendedBand_n77_2_r17__Type RF_Parameters__ext11O__extendedBand_n77_2_r17__cond ::
 nil).
Definition RF_Parameters__ext11O__cond z := 
  opt_cond BandCombinationList_v1700__cond (RF_Parameters__ext11O__supportedBandCombinationList_v1700 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1700__cond (RF_Parameters__ext11O__supportedBandCombinationList_UplinkTxSwitch_v1700 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RF_Parameters__ext11O__supportedBandCombinationListSL_RelayDiscovery_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RF_Parameters__ext11O__supportedBandCombinationListSL_NonRelayDiscovery_r17 z) /\
  opt_cond BandCombinationListSidelinkEUTRA_NR_v1710__cond (RF_Parameters__ext11O__supportedBandCombinationListSidelinkEUTRA_NR_v1710 z) /\
  opt_cond RF_Parameters__ext11O__sidelinkRequested_r17__cond (RF_Parameters__ext11O__sidelinkRequested_r17 z) /\
  opt_cond RF_Parameters__ext11O__extendedBand_n77_2_r17__cond (RF_Parameters__ext11O__extendedBand_n77_2_r17 z) /\
  True.

Definition RF_Parameters__ext11__Type := RF_Parameters__ext11O__Type.
Definition RF_Parameters__ext11__cond := RF_Parameters__ext11O__cond.

Require Import NR.BandCombinationList_v1720.

Opaque BandCombinationList_v1720__cond BandCombinationList_v1720__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1720.

Opaque BandCombinationList_UplinkTxSwitch_v1720__cond BandCombinationList_UplinkTxSwitch_v1720__Format.

Record RF_Parameters__ext12O__Type : Set :=
  make__RF_Parameters__ext12O__Type {
    RF_Parameters__ext12O__supportedBandCombinationList_v1720 : option BandCombinationList_v1720__Type ;
    RF_Parameters__ext12O__supportedBandCombinationList_UplinkTxSwitch_v1720 : option BandCombinationList_UplinkTxSwitch_v1720__Type ;
}.
Definition RF_Parameters__ext12O__list := (
 Opt BandCombinationList_v1720__Type BandCombinationList_v1720__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1720__Type BandCombinationList_UplinkTxSwitch_v1720__cond ::
 nil).
Definition RF_Parameters__ext12O__cond z := 
  opt_cond BandCombinationList_v1720__cond (RF_Parameters__ext12O__supportedBandCombinationList_v1720 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1720__cond (RF_Parameters__ext12O__supportedBandCombinationList_UplinkTxSwitch_v1720 z) /\
  True.

Definition RF_Parameters__ext12__Type := RF_Parameters__ext12O__Type.
Definition RF_Parameters__ext12__cond := RF_Parameters__ext12O__cond.

Require Import NR.BandCombinationList_v1730.

Opaque BandCombinationList_v1730__cond BandCombinationList_v1730__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1730.

Opaque BandCombinationList_UplinkTxSwitch_v1730__cond BandCombinationList_UplinkTxSwitch_v1730__Format.

Require Import NR.BandCombinationListSL_Discovery_r17.

Opaque BandCombinationListSL_Discovery_r17__cond BandCombinationListSL_Discovery_r17__Format.

Require Import NR.BandCombinationListSL_Discovery_r17.

Opaque BandCombinationListSL_Discovery_r17__cond BandCombinationListSL_Discovery_r17__Format.

Record RF_Parameters__ext13O__Type : Set :=
  make__RF_Parameters__ext13O__Type {
    RF_Parameters__ext13O__supportedBandCombinationList_v1730 : option BandCombinationList_v1730__Type ;
    RF_Parameters__ext13O__supportedBandCombinationList_UplinkTxSwitch_v1730 : option BandCombinationList_UplinkTxSwitch_v1730__Type ;
    RF_Parameters__ext13O__supportedBandCombinationListSL_RelayDiscovery_v1730 : option BandCombinationListSL_Discovery_r17__Type ;
    RF_Parameters__ext13O__supportedBandCombinationListSL_NonRelayDiscovery_v1730 : option BandCombinationListSL_Discovery_r17__Type ;
}.
Definition RF_Parameters__ext13O__list := (
 Opt BandCombinationList_v1730__Type BandCombinationList_v1730__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1730__Type BandCombinationList_UplinkTxSwitch_v1730__cond ::
 Opt BandCombinationListSL_Discovery_r17__Type BandCombinationListSL_Discovery_r17__cond ::
 Opt BandCombinationListSL_Discovery_r17__Type BandCombinationListSL_Discovery_r17__cond ::
 nil).
Definition RF_Parameters__ext13O__cond z := 
  opt_cond BandCombinationList_v1730__cond (RF_Parameters__ext13O__supportedBandCombinationList_v1730 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1730__cond (RF_Parameters__ext13O__supportedBandCombinationList_UplinkTxSwitch_v1730 z) /\
  opt_cond BandCombinationListSL_Discovery_r17__cond (RF_Parameters__ext13O__supportedBandCombinationListSL_RelayDiscovery_v1730 z) /\
  opt_cond BandCombinationListSL_Discovery_r17__cond (RF_Parameters__ext13O__supportedBandCombinationListSL_NonRelayDiscovery_v1730 z) /\
  True.

Definition RF_Parameters__ext13__Type := RF_Parameters__ext13O__Type.
Definition RF_Parameters__ext13__cond := RF_Parameters__ext13O__cond.

Record RF_Parameters__Type : Set :=
  make__RF_Parameters__Type {
    RF_Parameters__supportedBandListNR : RF_Parameters__supportedBandListNR__Type ;
    RF_Parameters__supportedBandCombinationList : option BandCombinationList__Type ;
    RF_Parameters__appliedFreqBandListFilter : option FreqBandList__Type ;
    RF_Parameters__ext0 : option RF_Parameters__ext0__Type ;
    RF_Parameters__ext1 : option RF_Parameters__ext1__Type ;
    RF_Parameters__ext2 : option RF_Parameters__ext2__Type ;
    RF_Parameters__ext3 : option RF_Parameters__ext3__Type ;
    RF_Parameters__ext4 : option RF_Parameters__ext4__Type ;
    RF_Parameters__ext5 : option RF_Parameters__ext5__Type ;
    RF_Parameters__ext6 : option RF_Parameters__ext6__Type ;
    RF_Parameters__ext7 : option RF_Parameters__ext7__Type ;
    RF_Parameters__ext8 : option RF_Parameters__ext8__Type ;
    RF_Parameters__ext9 : option RF_Parameters__ext9__Type ;
    RF_Parameters__ext10 : option RF_Parameters__ext10__Type ;
    RF_Parameters__ext11 : option RF_Parameters__ext11__Type ;
    RF_Parameters__ext12 : option RF_Parameters__ext12__Type ;
    RF_Parameters__ext13 : option RF_Parameters__ext13__Type ;
}.
Definition RF_Parameters__root_list : list seq_elem := (
 Nor RF_Parameters__supportedBandListNR__Type RF_Parameters__supportedBandListNR__cond ::
 Opt BandCombinationList__Type BandCombinationList__cond ::
 Opt FreqBandList__Type FreqBandList__cond ::
 nil).
Definition RF_Parameters__ext_list : list typ := (
  typ_cons RF_Parameters__ext0__Type RF_Parameters__ext0__cond ::
  typ_cons RF_Parameters__ext1__Type RF_Parameters__ext1__cond ::
  typ_cons RF_Parameters__ext2__Type RF_Parameters__ext2__cond ::
  typ_cons RF_Parameters__ext3__Type RF_Parameters__ext3__cond ::
  typ_cons RF_Parameters__ext4__Type RF_Parameters__ext4__cond ::
  typ_cons RF_Parameters__ext5__Type RF_Parameters__ext5__cond ::
  typ_cons RF_Parameters__ext6__Type RF_Parameters__ext6__cond ::
  typ_cons RF_Parameters__ext7__Type RF_Parameters__ext7__cond ::
  typ_cons RF_Parameters__ext8__Type RF_Parameters__ext8__cond ::
  typ_cons RF_Parameters__ext9__Type RF_Parameters__ext9__cond ::
  typ_cons RF_Parameters__ext10__Type RF_Parameters__ext10__cond ::
  typ_cons RF_Parameters__ext11__Type RF_Parameters__ext11__cond ::
  typ_cons RF_Parameters__ext12__Type RF_Parameters__ext12__cond ::
  typ_cons RF_Parameters__ext13__Type RF_Parameters__ext13__cond ::
  nil).
Definition RF_Parameters__cond (z : RF_Parameters__Type) := 
(  RF_Parameters__supportedBandListNR__cond (RF_Parameters__supportedBandListNR z) /\
  opt_cond BandCombinationList__cond (RF_Parameters__supportedBandCombinationList z) /\
  opt_cond FreqBandList__cond (RF_Parameters__appliedFreqBandListFilter z) /\
  True) /\ 
(  opt_cond RF_Parameters__ext0__cond (RF_Parameters__ext0 z) /\
  opt_cond RF_Parameters__ext1__cond (RF_Parameters__ext1 z) /\
  opt_cond RF_Parameters__ext2__cond (RF_Parameters__ext2 z) /\
  opt_cond RF_Parameters__ext3__cond (RF_Parameters__ext3 z) /\
  opt_cond RF_Parameters__ext4__cond (RF_Parameters__ext4 z) /\
  opt_cond RF_Parameters__ext5__cond (RF_Parameters__ext5 z) /\
  opt_cond RF_Parameters__ext6__cond (RF_Parameters__ext6 z) /\
  opt_cond RF_Parameters__ext7__cond (RF_Parameters__ext7 z) /\
  opt_cond RF_Parameters__ext8__cond (RF_Parameters__ext8 z) /\
  opt_cond RF_Parameters__ext9__cond (RF_Parameters__ext9 z) /\
  opt_cond RF_Parameters__ext10__cond (RF_Parameters__ext10 z) /\
  opt_cond RF_Parameters__ext11__cond (RF_Parameters__ext11 z) /\
  opt_cond RF_Parameters__ext12__cond (RF_Parameters__ext12 z) /\
  opt_cond RF_Parameters__ext13__cond (RF_Parameters__ext13 z) /\
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
Definition RF_Parameters__supportedBandListNR__Format : T_Format RF_Parameters__supportedBandListNR__Type RF_Parameters__supportedBandListNR__cond := seq_of_format BandNR__Format 1 maxBands RF_Parameters__supportedBandListNR__helper1 RF_Parameters__supportedBandListNR__helper2.

Opaque RF_Parameters__supportedBandListNR__cond RF_Parameters__supportedBandListNR__Format.

Definition RF_Parameters__ext0O__srs_SwitchingTimeRequested__Format : T_Format RF_Parameters__ext0O__srs_SwitchingTimeRequested__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RF_Parameters__ext0O__srs_SwitchingTimeRequested__nat__Format RF_Parameters__ext0O__srs_SwitchingTimeRequested__F1 RF_Parameters__ext0O__srs_SwitchingTimeRequested__F2 RF_Parameters__ext0O__srs_SwitchingTimeRequested__F1F2 RF_Parameters__ext0O__srs_SwitchingTimeRequested__F2F1.

Opaque RF_Parameters__ext0O__srs_SwitchingTimeRequested__cond RF_Parameters__ext0O__srs_SwitchingTimeRequested__Format.


Definition RF_Parameters__ext0O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext0O__list.
Definition RF_Parameters__ext0O__Format_list : RF_Parameters__ext0O__Format_Type :=
  (BandCombinationList_v1540__Format, (RF_Parameters__ext0O__srs_SwitchingTimeRequested__Format, unit_format)).
Definition RF_Parameters__ext0O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext0O__list RF_Parameters__ext0O__Format_list.
Definition RF_Parameters__ext0O__F1 z :=
  (RF_Parameters__ext0O__supportedBandCombinationList_v1540 z, (RF_Parameters__ext0O__srs_SwitchingTimeRequested z, tt)).
Definition RF_Parameters__ext0O__F2 (y : seq_type RF_Parameters__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_Parameters__ext0O__Type i0 i1
  end.
Lemma RF_Parameters__ext0O__F1F2_cond (z : RF_Parameters__ext0O__Type)
  : RF_Parameters__ext0O__cond z ->
  (seq_cond RF_Parameters__ext0O__list (RF_Parameters__ext0O__F1 z)).
intro H. unfold RF_Parameters__ext0O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext0O__F1F2_cond2 (z : RF_Parameters__ext0O__Type)
 : RF_Parameters__ext0O__F2 (RF_Parameters__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext0O__F2F1_cond (y : seq_type RF_Parameters__ext0O__list)
  : seq_cond RF_Parameters__ext0O__list y ->
 (RF_Parameters__ext0O__cond (RF_Parameters__ext0O__F2 y)) /\  RF_Parameters__ext0O__F1 (RF_Parameters__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext0O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext0O__Format : T_Format RF_Parameters__ext0O__Type RF_Parameters__ext0O__cond :=
        proj2_format  RF_Parameters__ext0O__cond RF_Parameters__ext0O__list__Format
    RF_Parameters__ext0O__F1 RF_Parameters__ext0O__F2 RF_Parameters__ext0O__F1F2_cond  RF_Parameters__ext0O__F1F2_cond2 RF_Parameters__ext0O__F2F1_cond.
Opaque RF_Parameters__ext0O__cond RF_Parameters__ext0O__Format.

Definition RF_Parameters__ext0__check_all_none (b : RF_Parameters__ext0O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext0__Format : T_Format RF_Parameters__ext0__Type RF_Parameters__ext0__cond :=
  restrict_add_format RF_Parameters__ext0__check_all_none RF_Parameters__ext0O__Format.

Opaque RF_Parameters__ext0__cond RF_Parameters__ext0__Format.


Definition RF_Parameters__ext1O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext1O__list.
Definition RF_Parameters__ext1O__Format_list : RF_Parameters__ext1O__Format_Type :=
  (BandCombinationList_v1550__Format, unit_format).
Definition RF_Parameters__ext1O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext1O__list RF_Parameters__ext1O__Format_list.
Definition RF_Parameters__ext1O__F1 z :=
  (RF_Parameters__ext1O__supportedBandCombinationList_v1550 z, tt).
Definition RF_Parameters__ext1O__F2 (y : seq_type RF_Parameters__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__RF_Parameters__ext1O__Type i0
  end.
Lemma RF_Parameters__ext1O__F1F2_cond (z : RF_Parameters__ext1O__Type)
  : RF_Parameters__ext1O__cond z ->
  (seq_cond RF_Parameters__ext1O__list (RF_Parameters__ext1O__F1 z)).
intro H. unfold RF_Parameters__ext1O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext1O__F1F2_cond2 (z : RF_Parameters__ext1O__Type)
 : RF_Parameters__ext1O__F2 (RF_Parameters__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext1O__F2F1_cond (y : seq_type RF_Parameters__ext1O__list)
  : seq_cond RF_Parameters__ext1O__list y ->
 (RF_Parameters__ext1O__cond (RF_Parameters__ext1O__F2 y)) /\  RF_Parameters__ext1O__F1 (RF_Parameters__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext1O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext1O__Format : T_Format RF_Parameters__ext1O__Type RF_Parameters__ext1O__cond :=
        proj2_format  RF_Parameters__ext1O__cond RF_Parameters__ext1O__list__Format
    RF_Parameters__ext1O__F1 RF_Parameters__ext1O__F2 RF_Parameters__ext1O__F1F2_cond  RF_Parameters__ext1O__F1F2_cond2 RF_Parameters__ext1O__F2F1_cond.
Opaque RF_Parameters__ext1O__cond RF_Parameters__ext1O__Format.

Definition RF_Parameters__ext1__check_all_none (b : RF_Parameters__ext1O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext1O__Type None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext1__Format : T_Format RF_Parameters__ext1__Type RF_Parameters__ext1__cond :=
  restrict_add_format RF_Parameters__ext1__check_all_none RF_Parameters__ext1O__Format.

Opaque RF_Parameters__ext1__cond RF_Parameters__ext1__Format.


Definition RF_Parameters__ext2O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext2O__list.
Definition RF_Parameters__ext2O__Format_list : RF_Parameters__ext2O__Format_Type :=
  (BandCombinationList_v1560__Format, unit_format).
Definition RF_Parameters__ext2O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext2O__list RF_Parameters__ext2O__Format_list.
Definition RF_Parameters__ext2O__F1 z :=
  (RF_Parameters__ext2O__supportedBandCombinationList_v1560 z, tt).
Definition RF_Parameters__ext2O__F2 (y : seq_type RF_Parameters__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__RF_Parameters__ext2O__Type i0
  end.
Lemma RF_Parameters__ext2O__F1F2_cond (z : RF_Parameters__ext2O__Type)
  : RF_Parameters__ext2O__cond z ->
  (seq_cond RF_Parameters__ext2O__list (RF_Parameters__ext2O__F1 z)).
intro H. unfold RF_Parameters__ext2O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext2O__F1F2_cond2 (z : RF_Parameters__ext2O__Type)
 : RF_Parameters__ext2O__F2 (RF_Parameters__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext2O__F2F1_cond (y : seq_type RF_Parameters__ext2O__list)
  : seq_cond RF_Parameters__ext2O__list y ->
 (RF_Parameters__ext2O__cond (RF_Parameters__ext2O__F2 y)) /\  RF_Parameters__ext2O__F1 (RF_Parameters__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext2O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext2O__Format : T_Format RF_Parameters__ext2O__Type RF_Parameters__ext2O__cond :=
        proj2_format  RF_Parameters__ext2O__cond RF_Parameters__ext2O__list__Format
    RF_Parameters__ext2O__F1 RF_Parameters__ext2O__F2 RF_Parameters__ext2O__F1F2_cond  RF_Parameters__ext2O__F1F2_cond2 RF_Parameters__ext2O__F2F1_cond.
Opaque RF_Parameters__ext2O__cond RF_Parameters__ext2O__Format.

Definition RF_Parameters__ext2__check_all_none (b : RF_Parameters__ext2O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext2O__Type None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext2__Format : T_Format RF_Parameters__ext2__Type RF_Parameters__ext2__cond :=
  restrict_add_format RF_Parameters__ext2__check_all_none RF_Parameters__ext2O__Format.

Opaque RF_Parameters__ext2__cond RF_Parameters__ext2__Format.


Definition RF_Parameters__ext3O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext3O__list.
Definition RF_Parameters__ext3O__Format_list : RF_Parameters__ext3O__Format_Type :=
  (BandCombinationList_v1610__Format, (BandCombinationListSidelinkEUTRA_NR_r16__Format, (BandCombinationList_UplinkTxSwitch_r16__Format, unit_format))).
Definition RF_Parameters__ext3O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext3O__list RF_Parameters__ext3O__Format_list.
Definition RF_Parameters__ext3O__F1 z :=
  (RF_Parameters__ext3O__supportedBandCombinationList_v1610 z, (RF_Parameters__ext3O__supportedBandCombinationListSidelinkEUTRA_NR_r16 z, (RF_Parameters__ext3O__supportedBandCombinationList_UplinkTxSwitch_r16 z, tt))).
Definition RF_Parameters__ext3O__F2 (y : seq_type RF_Parameters__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RF_Parameters__ext3O__Type i0 i1 i2
  end.
Lemma RF_Parameters__ext3O__F1F2_cond (z : RF_Parameters__ext3O__Type)
  : RF_Parameters__ext3O__cond z ->
  (seq_cond RF_Parameters__ext3O__list (RF_Parameters__ext3O__F1 z)).
intro H. unfold RF_Parameters__ext3O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext3O__F1F2_cond2 (z : RF_Parameters__ext3O__Type)
 : RF_Parameters__ext3O__F2 (RF_Parameters__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext3O__F2F1_cond (y : seq_type RF_Parameters__ext3O__list)
  : seq_cond RF_Parameters__ext3O__list y ->
 (RF_Parameters__ext3O__cond (RF_Parameters__ext3O__F2 y)) /\  RF_Parameters__ext3O__F1 (RF_Parameters__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext3O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext3O__Format : T_Format RF_Parameters__ext3O__Type RF_Parameters__ext3O__cond :=
        proj2_format  RF_Parameters__ext3O__cond RF_Parameters__ext3O__list__Format
    RF_Parameters__ext3O__F1 RF_Parameters__ext3O__F2 RF_Parameters__ext3O__F1F2_cond  RF_Parameters__ext3O__F1F2_cond2 RF_Parameters__ext3O__F2F1_cond.
Opaque RF_Parameters__ext3O__cond RF_Parameters__ext3O__Format.

Definition RF_Parameters__ext3__check_all_none (b : RF_Parameters__ext3O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext3O__Type None None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext3__Format : T_Format RF_Parameters__ext3__Type RF_Parameters__ext3__cond :=
  restrict_add_format RF_Parameters__ext3__check_all_none RF_Parameters__ext3O__Format.

Opaque RF_Parameters__ext3__cond RF_Parameters__ext3__Format.


Definition RF_Parameters__ext4O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext4O__list.
Definition RF_Parameters__ext4O__Format_list : RF_Parameters__ext4O__Format_Type :=
  (BandCombinationList_v1630__Format, (BandCombinationListSidelinkEUTRA_NR_v1630__Format, (BandCombinationList_UplinkTxSwitch_v1630__Format, unit_format))).
Definition RF_Parameters__ext4O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext4O__list RF_Parameters__ext4O__Format_list.
Definition RF_Parameters__ext4O__F1 z :=
  (RF_Parameters__ext4O__supportedBandCombinationList_v1630 z, (RF_Parameters__ext4O__supportedBandCombinationListSidelinkEUTRA_NR_v1630 z, (RF_Parameters__ext4O__supportedBandCombinationList_UplinkTxSwitch_v1630 z, tt))).
Definition RF_Parameters__ext4O__F2 (y : seq_type RF_Parameters__ext4O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RF_Parameters__ext4O__Type i0 i1 i2
  end.
Lemma RF_Parameters__ext4O__F1F2_cond (z : RF_Parameters__ext4O__Type)
  : RF_Parameters__ext4O__cond z ->
  (seq_cond RF_Parameters__ext4O__list (RF_Parameters__ext4O__F1 z)).
intro H. unfold RF_Parameters__ext4O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext4O__F1F2_cond2 (z : RF_Parameters__ext4O__Type)
 : RF_Parameters__ext4O__F2 (RF_Parameters__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext4O__F2F1_cond (y : seq_type RF_Parameters__ext4O__list)
  : seq_cond RF_Parameters__ext4O__list y ->
 (RF_Parameters__ext4O__cond (RF_Parameters__ext4O__F2 y)) /\  RF_Parameters__ext4O__F1 (RF_Parameters__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext4O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext4O__Format : T_Format RF_Parameters__ext4O__Type RF_Parameters__ext4O__cond :=
        proj2_format  RF_Parameters__ext4O__cond RF_Parameters__ext4O__list__Format
    RF_Parameters__ext4O__F1 RF_Parameters__ext4O__F2 RF_Parameters__ext4O__F1F2_cond  RF_Parameters__ext4O__F1F2_cond2 RF_Parameters__ext4O__F2F1_cond.
Opaque RF_Parameters__ext4O__cond RF_Parameters__ext4O__Format.

Definition RF_Parameters__ext4__check_all_none (b : RF_Parameters__ext4O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext4O__Type None None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext4__Format : T_Format RF_Parameters__ext4__Type RF_Parameters__ext4__cond :=
  restrict_add_format RF_Parameters__ext4__check_all_none RF_Parameters__ext4O__Format.

Opaque RF_Parameters__ext4__cond RF_Parameters__ext4__Format.


Definition RF_Parameters__ext5O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext5O__list.
Definition RF_Parameters__ext5O__Format_list : RF_Parameters__ext5O__Format_Type :=
  (BandCombinationList_v1640__Format, (BandCombinationList_UplinkTxSwitch_v1640__Format, unit_format)).
Definition RF_Parameters__ext5O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext5O__list RF_Parameters__ext5O__Format_list.
Definition RF_Parameters__ext5O__F1 z :=
  (RF_Parameters__ext5O__supportedBandCombinationList_v1640 z, (RF_Parameters__ext5O__supportedBandCombinationList_UplinkTxSwitch_v1640 z, tt)).
Definition RF_Parameters__ext5O__F2 (y : seq_type RF_Parameters__ext5O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_Parameters__ext5O__Type i0 i1
  end.
Lemma RF_Parameters__ext5O__F1F2_cond (z : RF_Parameters__ext5O__Type)
  : RF_Parameters__ext5O__cond z ->
  (seq_cond RF_Parameters__ext5O__list (RF_Parameters__ext5O__F1 z)).
intro H. unfold RF_Parameters__ext5O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext5O__F1F2_cond2 (z : RF_Parameters__ext5O__Type)
 : RF_Parameters__ext5O__F2 (RF_Parameters__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext5O__F2F1_cond (y : seq_type RF_Parameters__ext5O__list)
  : seq_cond RF_Parameters__ext5O__list y ->
 (RF_Parameters__ext5O__cond (RF_Parameters__ext5O__F2 y)) /\  RF_Parameters__ext5O__F1 (RF_Parameters__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext5O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext5O__Format : T_Format RF_Parameters__ext5O__Type RF_Parameters__ext5O__cond :=
        proj2_format  RF_Parameters__ext5O__cond RF_Parameters__ext5O__list__Format
    RF_Parameters__ext5O__F1 RF_Parameters__ext5O__F2 RF_Parameters__ext5O__F1F2_cond  RF_Parameters__ext5O__F1F2_cond2 RF_Parameters__ext5O__F2F1_cond.
Opaque RF_Parameters__ext5O__cond RF_Parameters__ext5O__Format.

Definition RF_Parameters__ext5__check_all_none (b : RF_Parameters__ext5O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext5O__Type None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext5__Format : T_Format RF_Parameters__ext5__Type RF_Parameters__ext5__cond :=
  restrict_add_format RF_Parameters__ext5__check_all_none RF_Parameters__ext5O__Format.

Opaque RF_Parameters__ext5__cond RF_Parameters__ext5__Format.


Definition RF_Parameters__ext6O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext6O__list.
Definition RF_Parameters__ext6O__Format_list : RF_Parameters__ext6O__Format_Type :=
  (BandCombinationList_v1650__Format, (BandCombinationList_UplinkTxSwitch_v1650__Format, unit_format)).
Definition RF_Parameters__ext6O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext6O__list RF_Parameters__ext6O__Format_list.
Definition RF_Parameters__ext6O__F1 z :=
  (RF_Parameters__ext6O__supportedBandCombinationList_v1650 z, (RF_Parameters__ext6O__supportedBandCombinationList_UplinkTxSwitch_v1650 z, tt)).
Definition RF_Parameters__ext6O__F2 (y : seq_type RF_Parameters__ext6O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_Parameters__ext6O__Type i0 i1
  end.
Lemma RF_Parameters__ext6O__F1F2_cond (z : RF_Parameters__ext6O__Type)
  : RF_Parameters__ext6O__cond z ->
  (seq_cond RF_Parameters__ext6O__list (RF_Parameters__ext6O__F1 z)).
intro H. unfold RF_Parameters__ext6O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext6O__F1F2_cond2 (z : RF_Parameters__ext6O__Type)
 : RF_Parameters__ext6O__F2 (RF_Parameters__ext6O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext6O__F2F1_cond (y : seq_type RF_Parameters__ext6O__list)
  : seq_cond RF_Parameters__ext6O__list y ->
 (RF_Parameters__ext6O__cond (RF_Parameters__ext6O__F2 y)) /\  RF_Parameters__ext6O__F1 (RF_Parameters__ext6O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext6O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext6O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext6O__Format : T_Format RF_Parameters__ext6O__Type RF_Parameters__ext6O__cond :=
        proj2_format  RF_Parameters__ext6O__cond RF_Parameters__ext6O__list__Format
    RF_Parameters__ext6O__F1 RF_Parameters__ext6O__F2 RF_Parameters__ext6O__F1F2_cond  RF_Parameters__ext6O__F1F2_cond2 RF_Parameters__ext6O__F2F1_cond.
Opaque RF_Parameters__ext6O__cond RF_Parameters__ext6O__Format.

Definition RF_Parameters__ext6__check_all_none (b : RF_Parameters__ext6O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext6O__Type None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext6__Format : T_Format RF_Parameters__ext6__Type RF_Parameters__ext6__cond :=
  restrict_add_format RF_Parameters__ext6__check_all_none RF_Parameters__ext6O__Format.

Opaque RF_Parameters__ext6__cond RF_Parameters__ext6__Format.

Definition RF_Parameters__ext7O__extendedBand_n77_r16__Format : T_Format RF_Parameters__ext7O__extendedBand_n77_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RF_Parameters__ext7O__extendedBand_n77_r16__nat__Format RF_Parameters__ext7O__extendedBand_n77_r16__F1 RF_Parameters__ext7O__extendedBand_n77_r16__F2 RF_Parameters__ext7O__extendedBand_n77_r16__F1F2 RF_Parameters__ext7O__extendedBand_n77_r16__F2F1.

Opaque RF_Parameters__ext7O__extendedBand_n77_r16__cond RF_Parameters__ext7O__extendedBand_n77_r16__Format.


Definition RF_Parameters__ext7O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext7O__list.
Definition RF_Parameters__ext7O__Format_list : RF_Parameters__ext7O__Format_Type :=
  (RF_Parameters__ext7O__extendedBand_n77_r16__Format, unit_format).
Definition RF_Parameters__ext7O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext7O__list RF_Parameters__ext7O__Format_list.
Definition RF_Parameters__ext7O__F1 z :=
  (RF_Parameters__ext7O__extendedBand_n77_r16 z, tt).
Definition RF_Parameters__ext7O__F2 (y : seq_type RF_Parameters__ext7O__list) :=
  match y with
  | (i0, _)=>
    make__RF_Parameters__ext7O__Type i0
  end.
Lemma RF_Parameters__ext7O__F1F2_cond (z : RF_Parameters__ext7O__Type)
  : RF_Parameters__ext7O__cond z ->
  (seq_cond RF_Parameters__ext7O__list (RF_Parameters__ext7O__F1 z)).
intro H. unfold RF_Parameters__ext7O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext7O__F1F2_cond2 (z : RF_Parameters__ext7O__Type)
 : RF_Parameters__ext7O__F2 (RF_Parameters__ext7O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext7O__F2F1_cond (y : seq_type RF_Parameters__ext7O__list)
  : seq_cond RF_Parameters__ext7O__list y ->
 (RF_Parameters__ext7O__cond (RF_Parameters__ext7O__F2 y)) /\  RF_Parameters__ext7O__F1 (RF_Parameters__ext7O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext7O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext7O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext7O__Format : T_Format RF_Parameters__ext7O__Type RF_Parameters__ext7O__cond :=
        proj2_format  RF_Parameters__ext7O__cond RF_Parameters__ext7O__list__Format
    RF_Parameters__ext7O__F1 RF_Parameters__ext7O__F2 RF_Parameters__ext7O__F1F2_cond  RF_Parameters__ext7O__F1F2_cond2 RF_Parameters__ext7O__F2F1_cond.
Opaque RF_Parameters__ext7O__cond RF_Parameters__ext7O__Format.

Definition RF_Parameters__ext7__check_all_none (b : RF_Parameters__ext7O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext7O__Type None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext7__Format : T_Format RF_Parameters__ext7__Type RF_Parameters__ext7__cond :=
  restrict_add_format RF_Parameters__ext7__check_all_none RF_Parameters__ext7O__Format.

Opaque RF_Parameters__ext7__cond RF_Parameters__ext7__Format.


Definition RF_Parameters__ext8O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext8O__list.
Definition RF_Parameters__ext8O__Format_list : RF_Parameters__ext8O__Format_Type :=
  (BandCombinationList_UplinkTxSwitch_v1670__Format, unit_format).
Definition RF_Parameters__ext8O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext8O__list RF_Parameters__ext8O__Format_list.
Definition RF_Parameters__ext8O__F1 z :=
  (RF_Parameters__ext8O__supportedBandCombinationList_UplinkTxSwitch_v1670 z, tt).
Definition RF_Parameters__ext8O__F2 (y : seq_type RF_Parameters__ext8O__list) :=
  match y with
  | (i0, _)=>
    make__RF_Parameters__ext8O__Type i0
  end.
Lemma RF_Parameters__ext8O__F1F2_cond (z : RF_Parameters__ext8O__Type)
  : RF_Parameters__ext8O__cond z ->
  (seq_cond RF_Parameters__ext8O__list (RF_Parameters__ext8O__F1 z)).
intro H. unfold RF_Parameters__ext8O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext8O__F1F2_cond2 (z : RF_Parameters__ext8O__Type)
 : RF_Parameters__ext8O__F2 (RF_Parameters__ext8O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext8O__F2F1_cond (y : seq_type RF_Parameters__ext8O__list)
  : seq_cond RF_Parameters__ext8O__list y ->
 (RF_Parameters__ext8O__cond (RF_Parameters__ext8O__F2 y)) /\  RF_Parameters__ext8O__F1 (RF_Parameters__ext8O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext8O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext8O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext8O__Format : T_Format RF_Parameters__ext8O__Type RF_Parameters__ext8O__cond :=
        proj2_format  RF_Parameters__ext8O__cond RF_Parameters__ext8O__list__Format
    RF_Parameters__ext8O__F1 RF_Parameters__ext8O__F2 RF_Parameters__ext8O__F1F2_cond  RF_Parameters__ext8O__F1F2_cond2 RF_Parameters__ext8O__F2F1_cond.
Opaque RF_Parameters__ext8O__cond RF_Parameters__ext8O__Format.

Definition RF_Parameters__ext8__check_all_none (b : RF_Parameters__ext8O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext8O__Type None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext8__Format : T_Format RF_Parameters__ext8__Type RF_Parameters__ext8__cond :=
  restrict_add_format RF_Parameters__ext8__check_all_none RF_Parameters__ext8O__Format.

Opaque RF_Parameters__ext8__cond RF_Parameters__ext8__Format.


Definition RF_Parameters__ext9O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext9O__list.
Definition RF_Parameters__ext9O__Format_list : RF_Parameters__ext9O__Format_Type :=
  (BandCombinationList_v1680__Format, unit_format).
Definition RF_Parameters__ext9O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext9O__list RF_Parameters__ext9O__Format_list.
Definition RF_Parameters__ext9O__F1 z :=
  (RF_Parameters__ext9O__supportedBandCombinationList_v1680 z, tt).
Definition RF_Parameters__ext9O__F2 (y : seq_type RF_Parameters__ext9O__list) :=
  match y with
  | (i0, _)=>
    make__RF_Parameters__ext9O__Type i0
  end.
Lemma RF_Parameters__ext9O__F1F2_cond (z : RF_Parameters__ext9O__Type)
  : RF_Parameters__ext9O__cond z ->
  (seq_cond RF_Parameters__ext9O__list (RF_Parameters__ext9O__F1 z)).
intro H. unfold RF_Parameters__ext9O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext9O__F1F2_cond2 (z : RF_Parameters__ext9O__Type)
 : RF_Parameters__ext9O__F2 (RF_Parameters__ext9O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext9O__F2F1_cond (y : seq_type RF_Parameters__ext9O__list)
  : seq_cond RF_Parameters__ext9O__list y ->
 (RF_Parameters__ext9O__cond (RF_Parameters__ext9O__F2 y)) /\  RF_Parameters__ext9O__F1 (RF_Parameters__ext9O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext9O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext9O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext9O__Format : T_Format RF_Parameters__ext9O__Type RF_Parameters__ext9O__cond :=
        proj2_format  RF_Parameters__ext9O__cond RF_Parameters__ext9O__list__Format
    RF_Parameters__ext9O__F1 RF_Parameters__ext9O__F2 RF_Parameters__ext9O__F1F2_cond  RF_Parameters__ext9O__F1F2_cond2 RF_Parameters__ext9O__F2F1_cond.
Opaque RF_Parameters__ext9O__cond RF_Parameters__ext9O__Format.

Definition RF_Parameters__ext9__check_all_none (b : RF_Parameters__ext9O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext9O__Type None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext9__Format : T_Format RF_Parameters__ext9__Type RF_Parameters__ext9__cond :=
  restrict_add_format RF_Parameters__ext9__check_all_none RF_Parameters__ext9O__Format.

Opaque RF_Parameters__ext9__cond RF_Parameters__ext9__Format.


Definition RF_Parameters__ext10O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext10O__list.
Definition RF_Parameters__ext10O__Format_list : RF_Parameters__ext10O__Format_Type :=
  (BandCombinationList_v1690__Format, (BandCombinationList_UplinkTxSwitch_v1690__Format, unit_format)).
Definition RF_Parameters__ext10O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext10O__list RF_Parameters__ext10O__Format_list.
Definition RF_Parameters__ext10O__F1 z :=
  (RF_Parameters__ext10O__supportedBandCombinationList_v1690 z, (RF_Parameters__ext10O__supportedBandCombinationList_UplinkTxSwitch_v1690 z, tt)).
Definition RF_Parameters__ext10O__F2 (y : seq_type RF_Parameters__ext10O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_Parameters__ext10O__Type i0 i1
  end.
Lemma RF_Parameters__ext10O__F1F2_cond (z : RF_Parameters__ext10O__Type)
  : RF_Parameters__ext10O__cond z ->
  (seq_cond RF_Parameters__ext10O__list (RF_Parameters__ext10O__F1 z)).
intro H. unfold RF_Parameters__ext10O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext10O__F1F2_cond2 (z : RF_Parameters__ext10O__Type)
 : RF_Parameters__ext10O__F2 (RF_Parameters__ext10O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext10O__F2F1_cond (y : seq_type RF_Parameters__ext10O__list)
  : seq_cond RF_Parameters__ext10O__list y ->
 (RF_Parameters__ext10O__cond (RF_Parameters__ext10O__F2 y)) /\  RF_Parameters__ext10O__F1 (RF_Parameters__ext10O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext10O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext10O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext10O__Format : T_Format RF_Parameters__ext10O__Type RF_Parameters__ext10O__cond :=
        proj2_format  RF_Parameters__ext10O__cond RF_Parameters__ext10O__list__Format
    RF_Parameters__ext10O__F1 RF_Parameters__ext10O__F2 RF_Parameters__ext10O__F1F2_cond  RF_Parameters__ext10O__F1F2_cond2 RF_Parameters__ext10O__F2F1_cond.
Opaque RF_Parameters__ext10O__cond RF_Parameters__ext10O__Format.

Definition RF_Parameters__ext10__check_all_none (b : RF_Parameters__ext10O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext10O__Type None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext10__Format : T_Format RF_Parameters__ext10__Type RF_Parameters__ext10__cond :=
  restrict_add_format RF_Parameters__ext10__check_all_none RF_Parameters__ext10O__Format.

Opaque RF_Parameters__ext10__cond RF_Parameters__ext10__Format.

Definition RF_Parameters__ext11O__sidelinkRequested_r17__Format : T_Format RF_Parameters__ext11O__sidelinkRequested_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RF_Parameters__ext11O__sidelinkRequested_r17__nat__Format RF_Parameters__ext11O__sidelinkRequested_r17__F1 RF_Parameters__ext11O__sidelinkRequested_r17__F2 RF_Parameters__ext11O__sidelinkRequested_r17__F1F2 RF_Parameters__ext11O__sidelinkRequested_r17__F2F1.

Opaque RF_Parameters__ext11O__sidelinkRequested_r17__cond RF_Parameters__ext11O__sidelinkRequested_r17__Format.

Definition RF_Parameters__ext11O__extendedBand_n77_2_r17__Format : T_Format RF_Parameters__ext11O__extendedBand_n77_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RF_Parameters__ext11O__extendedBand_n77_2_r17__nat__Format RF_Parameters__ext11O__extendedBand_n77_2_r17__F1 RF_Parameters__ext11O__extendedBand_n77_2_r17__F2 RF_Parameters__ext11O__extendedBand_n77_2_r17__F1F2 RF_Parameters__ext11O__extendedBand_n77_2_r17__F2F1.

Opaque RF_Parameters__ext11O__extendedBand_n77_2_r17__cond RF_Parameters__ext11O__extendedBand_n77_2_r17__Format.


Definition RF_Parameters__ext11O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext11O__list.
Definition RF_Parameters__ext11O__Format_list : RF_Parameters__ext11O__Format_Type :=
  (BandCombinationList_v1700__Format, (BandCombinationList_UplinkTxSwitch_v1700__Format, (octet_string_nc__Format, (octet_string_nc__Format, (BandCombinationListSidelinkEUTRA_NR_v1710__Format, (RF_Parameters__ext11O__sidelinkRequested_r17__Format, (RF_Parameters__ext11O__extendedBand_n77_2_r17__Format, unit_format))))))).
Definition RF_Parameters__ext11O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext11O__list RF_Parameters__ext11O__Format_list.
Definition RF_Parameters__ext11O__F1 z :=
  (RF_Parameters__ext11O__supportedBandCombinationList_v1700 z, (RF_Parameters__ext11O__supportedBandCombinationList_UplinkTxSwitch_v1700 z, (RF_Parameters__ext11O__supportedBandCombinationListSL_RelayDiscovery_r17 z, (RF_Parameters__ext11O__supportedBandCombinationListSL_NonRelayDiscovery_r17 z, (RF_Parameters__ext11O__supportedBandCombinationListSidelinkEUTRA_NR_v1710 z, (RF_Parameters__ext11O__sidelinkRequested_r17 z, (RF_Parameters__ext11O__extendedBand_n77_2_r17 z, tt))))))).
Definition RF_Parameters__ext11O__F2 (y : seq_type RF_Parameters__ext11O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__RF_Parameters__ext11O__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma RF_Parameters__ext11O__F1F2_cond (z : RF_Parameters__ext11O__Type)
  : RF_Parameters__ext11O__cond z ->
  (seq_cond RF_Parameters__ext11O__list (RF_Parameters__ext11O__F1 z)).
intro H. unfold RF_Parameters__ext11O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext11O__F1F2_cond2 (z : RF_Parameters__ext11O__Type)
 : RF_Parameters__ext11O__F2 (RF_Parameters__ext11O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext11O__F2F1_cond (y : seq_type RF_Parameters__ext11O__list)
  : seq_cond RF_Parameters__ext11O__list y ->
 (RF_Parameters__ext11O__cond (RF_Parameters__ext11O__F2 y)) /\  RF_Parameters__ext11O__F1 (RF_Parameters__ext11O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext11O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext11O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext11O__Format : T_Format RF_Parameters__ext11O__Type RF_Parameters__ext11O__cond :=
        proj2_format  RF_Parameters__ext11O__cond RF_Parameters__ext11O__list__Format
    RF_Parameters__ext11O__F1 RF_Parameters__ext11O__F2 RF_Parameters__ext11O__F1F2_cond  RF_Parameters__ext11O__F1F2_cond2 RF_Parameters__ext11O__F2F1_cond.
Opaque RF_Parameters__ext11O__cond RF_Parameters__ext11O__Format.

Definition RF_Parameters__ext11__check_all_none (b : RF_Parameters__ext11O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext11O__Type None None None None None None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext11__Format : T_Format RF_Parameters__ext11__Type RF_Parameters__ext11__cond :=
  restrict_add_format RF_Parameters__ext11__check_all_none RF_Parameters__ext11O__Format.

Opaque RF_Parameters__ext11__cond RF_Parameters__ext11__Format.


Definition RF_Parameters__ext12O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext12O__list.
Definition RF_Parameters__ext12O__Format_list : RF_Parameters__ext12O__Format_Type :=
  (BandCombinationList_v1720__Format, (BandCombinationList_UplinkTxSwitch_v1720__Format, unit_format)).
Definition RF_Parameters__ext12O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext12O__list RF_Parameters__ext12O__Format_list.
Definition RF_Parameters__ext12O__F1 z :=
  (RF_Parameters__ext12O__supportedBandCombinationList_v1720 z, (RF_Parameters__ext12O__supportedBandCombinationList_UplinkTxSwitch_v1720 z, tt)).
Definition RF_Parameters__ext12O__F2 (y : seq_type RF_Parameters__ext12O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_Parameters__ext12O__Type i0 i1
  end.
Lemma RF_Parameters__ext12O__F1F2_cond (z : RF_Parameters__ext12O__Type)
  : RF_Parameters__ext12O__cond z ->
  (seq_cond RF_Parameters__ext12O__list (RF_Parameters__ext12O__F1 z)).
intro H. unfold RF_Parameters__ext12O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext12O__F1F2_cond2 (z : RF_Parameters__ext12O__Type)
 : RF_Parameters__ext12O__F2 (RF_Parameters__ext12O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext12O__F2F1_cond (y : seq_type RF_Parameters__ext12O__list)
  : seq_cond RF_Parameters__ext12O__list y ->
 (RF_Parameters__ext12O__cond (RF_Parameters__ext12O__F2 y)) /\  RF_Parameters__ext12O__F1 (RF_Parameters__ext12O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext12O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext12O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext12O__Format : T_Format RF_Parameters__ext12O__Type RF_Parameters__ext12O__cond :=
        proj2_format  RF_Parameters__ext12O__cond RF_Parameters__ext12O__list__Format
    RF_Parameters__ext12O__F1 RF_Parameters__ext12O__F2 RF_Parameters__ext12O__F1F2_cond  RF_Parameters__ext12O__F1F2_cond2 RF_Parameters__ext12O__F2F1_cond.
Opaque RF_Parameters__ext12O__cond RF_Parameters__ext12O__Format.

Definition RF_Parameters__ext12__check_all_none (b : RF_Parameters__ext12O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext12O__Type None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext12__Format : T_Format RF_Parameters__ext12__Type RF_Parameters__ext12__cond :=
  restrict_add_format RF_Parameters__ext12__check_all_none RF_Parameters__ext12O__Format.

Opaque RF_Parameters__ext12__cond RF_Parameters__ext12__Format.


Definition RF_Parameters__ext13O__Format_Type := Eval cbn in seq_format_prod RF_Parameters__ext13O__list.
Definition RF_Parameters__ext13O__Format_list : RF_Parameters__ext13O__Format_Type :=
  (BandCombinationList_v1730__Format, (BandCombinationList_UplinkTxSwitch_v1730__Format, (BandCombinationListSL_Discovery_r17__Format, (BandCombinationListSL_Discovery_r17__Format, unit_format)))).
Definition RF_Parameters__ext13O__list__Format := (*Eval compute in *) seq_format RF_Parameters__ext13O__list RF_Parameters__ext13O__Format_list.
Definition RF_Parameters__ext13O__F1 z :=
  (RF_Parameters__ext13O__supportedBandCombinationList_v1730 z, (RF_Parameters__ext13O__supportedBandCombinationList_UplinkTxSwitch_v1730 z, (RF_Parameters__ext13O__supportedBandCombinationListSL_RelayDiscovery_v1730 z, (RF_Parameters__ext13O__supportedBandCombinationListSL_NonRelayDiscovery_v1730 z, tt)))).
Definition RF_Parameters__ext13O__F2 (y : seq_type RF_Parameters__ext13O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__RF_Parameters__ext13O__Type i0 i1 i2 i3
  end.
Lemma RF_Parameters__ext13O__F1F2_cond (z : RF_Parameters__ext13O__Type)
  : RF_Parameters__ext13O__cond z ->
  (seq_cond RF_Parameters__ext13O__list (RF_Parameters__ext13O__F1 z)).
intro H. unfold RF_Parameters__ext13O__cond in H. simpl. auto. Qed.
Lemma RF_Parameters__ext13O__F1F2_cond2 (z : RF_Parameters__ext13O__Type)
 : RF_Parameters__ext13O__F2 (RF_Parameters__ext13O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_Parameters__ext13O__F2F1_cond (y : seq_type RF_Parameters__ext13O__list)
  : seq_cond RF_Parameters__ext13O__list y ->
 (RF_Parameters__ext13O__cond (RF_Parameters__ext13O__F2 y)) /\  RF_Parameters__ext13O__F1 (RF_Parameters__ext13O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_Parameters__ext13O__cond. simpl in *. auto.
 - simpl. unfold RF_Parameters__ext13O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_Parameters__ext13O__Format : T_Format RF_Parameters__ext13O__Type RF_Parameters__ext13O__cond :=
        proj2_format  RF_Parameters__ext13O__cond RF_Parameters__ext13O__list__Format
    RF_Parameters__ext13O__F1 RF_Parameters__ext13O__F2 RF_Parameters__ext13O__F1F2_cond  RF_Parameters__ext13O__F1F2_cond2 RF_Parameters__ext13O__F2F1_cond.
Opaque RF_Parameters__ext13O__cond RF_Parameters__ext13O__Format.

Definition RF_Parameters__ext13__check_all_none (b : RF_Parameters__ext13O__Type) : bool :=
match b with 
  | make__RF_Parameters__ext13O__Type None None None None  => false 
  | _ => true 
 end.
Definition RF_Parameters__ext13__Format : T_Format RF_Parameters__ext13__Type RF_Parameters__ext13__cond :=
  restrict_add_format RF_Parameters__ext13__check_all_none RF_Parameters__ext13O__Format.

Opaque RF_Parameters__ext13__cond RF_Parameters__ext13__Format.


Definition RF_Parameters__root_Format_Type := Eval cbn in seq_format_prod RF_Parameters__root_list.
Definition RF_Parameters__root_Format_list : RF_Parameters__root_Format_Type :=
  (RF_Parameters__supportedBandListNR__Format, (BandCombinationList__Format, (FreqBandList__Format, unit_format))).

Definition RF_Parameters__ext_Format_Type := Eval cbn in get_formats RF_Parameters__ext_list.
Definition RF_Parameters__ext_Format_list : RF_Parameters__ext_Format_Type :=
  (RF_Parameters__ext0__Format, (RF_Parameters__ext1__Format, (RF_Parameters__ext2__Format, (RF_Parameters__ext3__Format, (RF_Parameters__ext4__Format, (RF_Parameters__ext5__Format, (RF_Parameters__ext6__Format, (RF_Parameters__ext7__Format, (RF_Parameters__ext8__Format, (RF_Parameters__ext9__Format, (RF_Parameters__ext10__Format, (RF_Parameters__ext11__Format, (RF_Parameters__ext12__Format, (RF_Parameters__ext13__Format, unit__Format)))))))))))))).

Definition RF_Parameters__list_type : Set := (seq_type RF_Parameters__root_list) * (seq_ext_type RF_Parameters__ext_list).
Definition RF_Parameters__list_cond (z : RF_Parameters__list_type) : Prop :=
        (seq_cond RF_Parameters__root_list (fst z)) /\ (seq_ext_cond RF_Parameters__ext_list (snd z)).
Definition RF_Parameters__list_format : T_Format RF_Parameters__list_type RF_Parameters__list_cond :=
 (* Eval compute in *) seq_ext_format RF_Parameters__root_list RF_Parameters__root_Format_list RF_Parameters__ext_list RF_Parameters__ext_Format_list.

Opaque RF_Parameters__list_format.
Definition RF_Parameters__F1 (z : RF_Parameters__Type) : RF_Parameters__list_type :=
  (((RF_Parameters__supportedBandListNR z, (RF_Parameters__supportedBandCombinationList z, (RF_Parameters__appliedFreqBandListFilter z, tt)))), (
(RF_Parameters__ext0 z, (RF_Parameters__ext1 z, (RF_Parameters__ext2 z, (RF_Parameters__ext3 z, (RF_Parameters__ext4 z, (RF_Parameters__ext5 z, (RF_Parameters__ext6 z, (RF_Parameters__ext7 z, (RF_Parameters__ext8 z, (RF_Parameters__ext9 z, (RF_Parameters__ext10 z, (RF_Parameters__ext11 z, (RF_Parameters__ext12 z, (RF_Parameters__ext13 z, tt)))))))))))))))).
Definition RF_Parameters__F2 (y : RF_Parameters__list_type) : RF_Parameters__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, _)))))))))))))))=>
    make__RF_Parameters__Type j0 j1 j2 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  end.
Definition RF_Parameters__helper1 : (forall a : RF_Parameters__Type, RF_Parameters__cond a -> RF_Parameters__list_cond (RF_Parameters__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RF_Parameters__helper2 : (forall a : RF_Parameters__Type, RF_Parameters__F2 (RF_Parameters__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RF_Parameters__helper3 : (forall b : RF_Parameters__list_type, RF_Parameters__list_cond b -> RF_Parameters__cond (RF_Parameters__F2 b) /\ RF_Parameters__F1 (RF_Parameters__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RF_Parameters__cond, RF_Parameters__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RF_Parameters__Format : T_Format RF_Parameters__Type RF_Parameters__cond :=
 proj2_format RF_Parameters__cond RF_Parameters__list_format  RF_Parameters__F1 RF_Parameters__F2 RF_Parameters__helper1 RF_Parameters__helper2 RF_Parameters__helper3.

Opaque RF_Parameters__cond RF_Parameters__Format.

