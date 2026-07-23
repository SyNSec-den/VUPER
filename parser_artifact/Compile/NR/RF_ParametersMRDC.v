Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandCombinationList.

Opaque BandCombinationList__cond BandCombinationList__Format.

Require Import NR.FreqBandList.

Opaque FreqBandList__cond FreqBandList__Format.

Inductive RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Type : Set :=
 | RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__true
.
Definition RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__cond := (fun (_ : RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Type) => True).
Lemma RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__nat__helper.

Definition RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F1 t :=
  match t with
  | RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__true => 0
  end.
Definition RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F2 n :=
  match n with
  | 0 => RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__true
  | _ => RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__true
  end.
Lemma RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F1F2 : forall x : RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Type, (RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F1 x <= 0) /\ RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F2 (RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F1 x) = x. imp_solve. Qed.
Lemma RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F2F1 : forall (y : nat) (H : y <= 0), RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F1 (RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F2 y) = y. enum_solve H y. Qed.

Require Import NR.BandCombinationList_v1540.

Opaque BandCombinationList_v1540__cond BandCombinationList_v1540__Format.

Record RF_ParametersMRDC__ext0O__Type : Set :=
  make__RF_ParametersMRDC__ext0O__Type {
    RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested : option RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Type ;
    RF_ParametersMRDC__ext0O__supportedBandCombinationList_v1540 : option BandCombinationList_v1540__Type ;
}.
Definition RF_ParametersMRDC__ext0O__list := (
 Opt RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Type RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__cond ::
 Opt BandCombinationList_v1540__Type BandCombinationList_v1540__cond ::
 nil).
Definition RF_ParametersMRDC__ext0O__cond z := 
  opt_cond RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__cond (RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested z) /\
  opt_cond BandCombinationList_v1540__cond (RF_ParametersMRDC__ext0O__supportedBandCombinationList_v1540 z) /\
  True.

Definition RF_ParametersMRDC__ext0__Type := RF_ParametersMRDC__ext0O__Type.
Definition RF_ParametersMRDC__ext0__cond := RF_ParametersMRDC__ext0O__cond.

Require Import NR.BandCombinationList_v1550.

Opaque BandCombinationList_v1550__cond BandCombinationList_v1550__Format.

Record RF_ParametersMRDC__ext1O__Type : Set :=
  make__RF_ParametersMRDC__ext1O__Type {
    RF_ParametersMRDC__ext1O__supportedBandCombinationList_v1550 : option BandCombinationList_v1550__Type ;
}.
Definition RF_ParametersMRDC__ext1O__list := (
 Opt BandCombinationList_v1550__Type BandCombinationList_v1550__cond ::
 nil).
Definition RF_ParametersMRDC__ext1O__cond z := 
  opt_cond BandCombinationList_v1550__cond (RF_ParametersMRDC__ext1O__supportedBandCombinationList_v1550 z) /\
  True.

Definition RF_ParametersMRDC__ext1__Type := RF_ParametersMRDC__ext1O__Type.
Definition RF_ParametersMRDC__ext1__cond := RF_ParametersMRDC__ext1O__cond.

Require Import NR.BandCombinationList_v1560.

Opaque BandCombinationList_v1560__cond BandCombinationList_v1560__Format.

Require Import NR.BandCombinationList.

Opaque BandCombinationList__cond BandCombinationList__Format.

Record RF_ParametersMRDC__ext2O__Type : Set :=
  make__RF_ParametersMRDC__ext2O__Type {
    RF_ParametersMRDC__ext2O__supportedBandCombinationList_v1560 : option BandCombinationList_v1560__Type ;
    RF_ParametersMRDC__ext2O__supportedBandCombinationListNEDC_Only : option BandCombinationList__Type ;
}.
Definition RF_ParametersMRDC__ext2O__list := (
 Opt BandCombinationList_v1560__Type BandCombinationList_v1560__cond ::
 Opt BandCombinationList__Type BandCombinationList__cond ::
 nil).
Definition RF_ParametersMRDC__ext2O__cond z := 
  opt_cond BandCombinationList_v1560__cond (RF_ParametersMRDC__ext2O__supportedBandCombinationList_v1560 z) /\
  opt_cond BandCombinationList__cond (RF_ParametersMRDC__ext2O__supportedBandCombinationListNEDC_Only z) /\
  True.

Definition RF_ParametersMRDC__ext2__Type := RF_ParametersMRDC__ext2O__Type.
Definition RF_ParametersMRDC__ext2__cond := RF_ParametersMRDC__ext2O__cond.

Require Import NR.BandCombinationList_v1570.

Opaque BandCombinationList_v1570__cond BandCombinationList_v1570__Format.

Record RF_ParametersMRDC__ext3O__Type : Set :=
  make__RF_ParametersMRDC__ext3O__Type {
    RF_ParametersMRDC__ext3O__supportedBandCombinationList_v1570 : option BandCombinationList_v1570__Type ;
}.
Definition RF_ParametersMRDC__ext3O__list := (
 Opt BandCombinationList_v1570__Type BandCombinationList_v1570__cond ::
 nil).
Definition RF_ParametersMRDC__ext3O__cond z := 
  opt_cond BandCombinationList_v1570__cond (RF_ParametersMRDC__ext3O__supportedBandCombinationList_v1570 z) /\
  True.

Definition RF_ParametersMRDC__ext3__Type := RF_ParametersMRDC__ext3O__Type.
Definition RF_ParametersMRDC__ext3__cond := RF_ParametersMRDC__ext3O__cond.

Require Import NR.BandCombinationList_v1580.

Opaque BandCombinationList_v1580__cond BandCombinationList_v1580__Format.

Record RF_ParametersMRDC__ext4O__Type : Set :=
  make__RF_ParametersMRDC__ext4O__Type {
    RF_ParametersMRDC__ext4O__supportedBandCombinationList_v1580 : option BandCombinationList_v1580__Type ;
}.
Definition RF_ParametersMRDC__ext4O__list := (
 Opt BandCombinationList_v1580__Type BandCombinationList_v1580__cond ::
 nil).
Definition RF_ParametersMRDC__ext4O__cond z := 
  opt_cond BandCombinationList_v1580__cond (RF_ParametersMRDC__ext4O__supportedBandCombinationList_v1580 z) /\
  True.

Definition RF_ParametersMRDC__ext4__Type := RF_ParametersMRDC__ext4O__Type.
Definition RF_ParametersMRDC__ext4__cond := RF_ParametersMRDC__ext4O__cond.

Require Import NR.BandCombinationList_v1590.

Opaque BandCombinationList_v1590__cond BandCombinationList_v1590__Format.

Record RF_ParametersMRDC__ext5O__Type : Set :=
  make__RF_ParametersMRDC__ext5O__Type {
    RF_ParametersMRDC__ext5O__supportedBandCombinationList_v1590 : option BandCombinationList_v1590__Type ;
}.
Definition RF_ParametersMRDC__ext5O__list := (
 Opt BandCombinationList_v1590__Type BandCombinationList_v1590__cond ::
 nil).
Definition RF_ParametersMRDC__ext5O__cond z := 
  opt_cond BandCombinationList_v1590__cond (RF_ParametersMRDC__ext5O__supportedBandCombinationList_v1590 z) /\
  True.

Definition RF_ParametersMRDC__ext5__Type := RF_ParametersMRDC__ext5O__Type.
Definition RF_ParametersMRDC__ext5__cond := RF_ParametersMRDC__ext5O__cond.

Require Import NR.BandCombinationList_v1540.

Opaque BandCombinationList_v1540__cond BandCombinationList_v1540__Format.

Require Import NR.BandCombinationList_v1560.

Opaque BandCombinationList_v1560__cond BandCombinationList_v1560__Format.

Require Import NR.BandCombinationList_v1570.

Opaque BandCombinationList_v1570__cond BandCombinationList_v1570__Format.

Require Import NR.BandCombinationList_v1580.

Opaque BandCombinationList_v1580__cond BandCombinationList_v1580__Format.

Require Import NR.BandCombinationList_v1590.

Opaque BandCombinationList_v1590__cond BandCombinationList_v1590__Format.

Record RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Type : Set :=
  make__RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Type {
    RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1540 : option BandCombinationList_v1540__Type ;
    RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1560 : option BandCombinationList_v1560__Type ;
    RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1570 : option BandCombinationList_v1570__Type ;
    RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1580 : option BandCombinationList_v1580__Type ;
    RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1590 : option BandCombinationList_v1590__Type ;
}.
Definition RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list := (
 Opt BandCombinationList_v1540__Type BandCombinationList_v1540__cond ::
 Opt BandCombinationList_v1560__Type BandCombinationList_v1560__cond ::
 Opt BandCombinationList_v1570__Type BandCombinationList_v1570__cond ::
 Opt BandCombinationList_v1580__Type BandCombinationList_v1580__cond ::
 Opt BandCombinationList_v1590__Type BandCombinationList_v1590__cond ::
 nil).
Definition RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond z := 
  opt_cond BandCombinationList_v1540__cond (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1540 z) /\
  opt_cond BandCombinationList_v1560__cond (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1560 z) /\
  opt_cond BandCombinationList_v1570__cond (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1570 z) /\
  opt_cond BandCombinationList_v1580__cond (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1580 z) /\
  opt_cond BandCombinationList_v1590__cond (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1590 z) /\
  True.

Record RF_ParametersMRDC__ext6O__Type : Set :=
  make__RF_ParametersMRDC__ext6O__Type {
    RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0 : option RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Type ;
}.
Definition RF_ParametersMRDC__ext6O__list := (
 Opt RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Type RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond ::
 nil).
Definition RF_ParametersMRDC__ext6O__cond z := 
  opt_cond RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0 z) /\
  True.

Definition RF_ParametersMRDC__ext6__Type := RF_ParametersMRDC__ext6O__Type.
Definition RF_ParametersMRDC__ext6__cond := RF_ParametersMRDC__ext6O__cond.

Require Import NR.BandCombinationList_v1610.

Opaque BandCombinationList_v1610__cond BandCombinationList_v1610__Format.

Require Import NR.BandCombinationList_v1610.

Opaque BandCombinationList_v1610__cond BandCombinationList_v1610__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_r16.

Opaque BandCombinationList_UplinkTxSwitch_r16__cond BandCombinationList_UplinkTxSwitch_r16__Format.

Record RF_ParametersMRDC__ext7O__Type : Set :=
  make__RF_ParametersMRDC__ext7O__Type {
    RF_ParametersMRDC__ext7O__supportedBandCombinationList_v1610 : option BandCombinationList_v1610__Type ;
    RF_ParametersMRDC__ext7O__supportedBandCombinationListNEDC_Only_v1610 : option BandCombinationList_v1610__Type ;
    RF_ParametersMRDC__ext7O__supportedBandCombinationList_UplinkTxSwitch_r16 : option BandCombinationList_UplinkTxSwitch_r16__Type ;
}.
Definition RF_ParametersMRDC__ext7O__list := (
 Opt BandCombinationList_v1610__Type BandCombinationList_v1610__cond ::
 Opt BandCombinationList_v1610__Type BandCombinationList_v1610__cond ::
 Opt BandCombinationList_UplinkTxSwitch_r16__Type BandCombinationList_UplinkTxSwitch_r16__cond ::
 nil).
Definition RF_ParametersMRDC__ext7O__cond z := 
  opt_cond BandCombinationList_v1610__cond (RF_ParametersMRDC__ext7O__supportedBandCombinationList_v1610 z) /\
  opt_cond BandCombinationList_v1610__cond (RF_ParametersMRDC__ext7O__supportedBandCombinationListNEDC_Only_v1610 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_r16__cond (RF_ParametersMRDC__ext7O__supportedBandCombinationList_UplinkTxSwitch_r16 z) /\
  True.

Definition RF_ParametersMRDC__ext7__Type := RF_ParametersMRDC__ext7O__Type.
Definition RF_ParametersMRDC__ext7__cond := RF_ParametersMRDC__ext7O__cond.

Require Import NR.BandCombinationList_v1630.

Opaque BandCombinationList_v1630__cond BandCombinationList_v1630__Format.

Require Import NR.BandCombinationList_v1630.

Opaque BandCombinationList_v1630__cond BandCombinationList_v1630__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1630.

Opaque BandCombinationList_UplinkTxSwitch_v1630__cond BandCombinationList_UplinkTxSwitch_v1630__Format.

Record RF_ParametersMRDC__ext8O__Type : Set :=
  make__RF_ParametersMRDC__ext8O__Type {
    RF_ParametersMRDC__ext8O__supportedBandCombinationList_v1630 : option BandCombinationList_v1630__Type ;
    RF_ParametersMRDC__ext8O__supportedBandCombinationListNEDC_Only_v1630 : option BandCombinationList_v1630__Type ;
    RF_ParametersMRDC__ext8O__supportedBandCombinationList_UplinkTxSwitch_v1630 : option BandCombinationList_UplinkTxSwitch_v1630__Type ;
}.
Definition RF_ParametersMRDC__ext8O__list := (
 Opt BandCombinationList_v1630__Type BandCombinationList_v1630__cond ::
 Opt BandCombinationList_v1630__Type BandCombinationList_v1630__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1630__Type BandCombinationList_UplinkTxSwitch_v1630__cond ::
 nil).
Definition RF_ParametersMRDC__ext8O__cond z := 
  opt_cond BandCombinationList_v1630__cond (RF_ParametersMRDC__ext8O__supportedBandCombinationList_v1630 z) /\
  opt_cond BandCombinationList_v1630__cond (RF_ParametersMRDC__ext8O__supportedBandCombinationListNEDC_Only_v1630 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1630__cond (RF_ParametersMRDC__ext8O__supportedBandCombinationList_UplinkTxSwitch_v1630 z) /\
  True.

Definition RF_ParametersMRDC__ext8__Type := RF_ParametersMRDC__ext8O__Type.
Definition RF_ParametersMRDC__ext8__cond := RF_ParametersMRDC__ext8O__cond.

Require Import NR.BandCombinationList_v1640.

Opaque BandCombinationList_v1640__cond BandCombinationList_v1640__Format.

Require Import NR.BandCombinationList_v1640.

Opaque BandCombinationList_v1640__cond BandCombinationList_v1640__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1640.

Opaque BandCombinationList_UplinkTxSwitch_v1640__cond BandCombinationList_UplinkTxSwitch_v1640__Format.

Record RF_ParametersMRDC__ext9O__Type : Set :=
  make__RF_ParametersMRDC__ext9O__Type {
    RF_ParametersMRDC__ext9O__supportedBandCombinationList_v1640 : option BandCombinationList_v1640__Type ;
    RF_ParametersMRDC__ext9O__supportedBandCombinationListNEDC_Only_v1640 : option BandCombinationList_v1640__Type ;
    RF_ParametersMRDC__ext9O__supportedBandCombinationList_UplinkTxSwitch_v1640 : option BandCombinationList_UplinkTxSwitch_v1640__Type ;
}.
Definition RF_ParametersMRDC__ext9O__list := (
 Opt BandCombinationList_v1640__Type BandCombinationList_v1640__cond ::
 Opt BandCombinationList_v1640__Type BandCombinationList_v1640__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1640__Type BandCombinationList_UplinkTxSwitch_v1640__cond ::
 nil).
Definition RF_ParametersMRDC__ext9O__cond z := 
  opt_cond BandCombinationList_v1640__cond (RF_ParametersMRDC__ext9O__supportedBandCombinationList_v1640 z) /\
  opt_cond BandCombinationList_v1640__cond (RF_ParametersMRDC__ext9O__supportedBandCombinationListNEDC_Only_v1640 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1640__cond (RF_ParametersMRDC__ext9O__supportedBandCombinationList_UplinkTxSwitch_v1640 z) /\
  True.

Definition RF_ParametersMRDC__ext9__Type := RF_ParametersMRDC__ext9O__Type.
Definition RF_ParametersMRDC__ext9__cond := RF_ParametersMRDC__ext9O__cond.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1670.

Opaque BandCombinationList_UplinkTxSwitch_v1670__cond BandCombinationList_UplinkTxSwitch_v1670__Format.

Record RF_ParametersMRDC__ext10O__Type : Set :=
  make__RF_ParametersMRDC__ext10O__Type {
    RF_ParametersMRDC__ext10O__supportedBandCombinationList_UplinkTxSwitch_v1670 : option BandCombinationList_UplinkTxSwitch_v1670__Type ;
}.
Definition RF_ParametersMRDC__ext10O__list := (
 Opt BandCombinationList_UplinkTxSwitch_v1670__Type BandCombinationList_UplinkTxSwitch_v1670__cond ::
 nil).
Definition RF_ParametersMRDC__ext10O__cond z := 
  opt_cond BandCombinationList_UplinkTxSwitch_v1670__cond (RF_ParametersMRDC__ext10O__supportedBandCombinationList_UplinkTxSwitch_v1670 z) /\
  True.

Definition RF_ParametersMRDC__ext10__Type := RF_ParametersMRDC__ext10O__Type.
Definition RF_ParametersMRDC__ext10__cond := RF_ParametersMRDC__ext10O__cond.

Require Import NR.BandCombinationList_v1700.

Opaque BandCombinationList_v1700__cond BandCombinationList_v1700__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1700.

Opaque BandCombinationList_UplinkTxSwitch_v1700__cond BandCombinationList_UplinkTxSwitch_v1700__Format.

Record RF_ParametersMRDC__ext11O__Type : Set :=
  make__RF_ParametersMRDC__ext11O__Type {
    RF_ParametersMRDC__ext11O__supportedBandCombinationList_v1700 : option BandCombinationList_v1700__Type ;
    RF_ParametersMRDC__ext11O__supportedBandCombinationList_UplinkTxSwitch_v1700 : option BandCombinationList_UplinkTxSwitch_v1700__Type ;
}.
Definition RF_ParametersMRDC__ext11O__list := (
 Opt BandCombinationList_v1700__Type BandCombinationList_v1700__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1700__Type BandCombinationList_UplinkTxSwitch_v1700__cond ::
 nil).
Definition RF_ParametersMRDC__ext11O__cond z := 
  opt_cond BandCombinationList_v1700__cond (RF_ParametersMRDC__ext11O__supportedBandCombinationList_v1700 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1700__cond (RF_ParametersMRDC__ext11O__supportedBandCombinationList_UplinkTxSwitch_v1700 z) /\
  True.

Definition RF_ParametersMRDC__ext11__Type := RF_ParametersMRDC__ext11O__Type.
Definition RF_ParametersMRDC__ext11__cond := RF_ParametersMRDC__ext11O__cond.

Require Import NR.BandCombinationList_v1720.

Opaque BandCombinationList_v1720__cond BandCombinationList_v1720__Format.

Require Import NR.BandCombinationList_v1700.

Opaque BandCombinationList_v1700__cond BandCombinationList_v1700__Format.

Require Import NR.BandCombinationList_v1720.

Opaque BandCombinationList_v1720__cond BandCombinationList_v1720__Format.

Record RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Type : Set :=
  make__RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Type {
    RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__supportedBandCombinationList_v1700 : option BandCombinationList_v1700__Type ;
    RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__supportedBandCombinationList_v1720 : option BandCombinationList_v1720__Type ;
}.
Definition RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list := (
 Opt BandCombinationList_v1700__Type BandCombinationList_v1700__cond ::
 Opt BandCombinationList_v1720__Type BandCombinationList_v1720__cond ::
 nil).
Definition RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond z := 
  opt_cond BandCombinationList_v1700__cond (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__supportedBandCombinationList_v1700 z) /\
  opt_cond BandCombinationList_v1720__cond (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__supportedBandCombinationList_v1720 z) /\
  True.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1720.

Opaque BandCombinationList_UplinkTxSwitch_v1720__cond BandCombinationList_UplinkTxSwitch_v1720__Format.

Record RF_ParametersMRDC__ext12O__Type : Set :=
  make__RF_ParametersMRDC__ext12O__Type {
    RF_ParametersMRDC__ext12O__supportedBandCombinationList_v1720 : option BandCombinationList_v1720__Type ;
    RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720 : option RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Type ;
    RF_ParametersMRDC__ext12O__supportedBandCombinationList_UplinkTxSwitch_v1720 : option BandCombinationList_UplinkTxSwitch_v1720__Type ;
}.
Definition RF_ParametersMRDC__ext12O__list := (
 Opt BandCombinationList_v1720__Type BandCombinationList_v1720__cond ::
 Opt RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Type RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1720__Type BandCombinationList_UplinkTxSwitch_v1720__cond ::
 nil).
Definition RF_ParametersMRDC__ext12O__cond z := 
  opt_cond BandCombinationList_v1720__cond (RF_ParametersMRDC__ext12O__supportedBandCombinationList_v1720 z) /\
  opt_cond RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1720__cond (RF_ParametersMRDC__ext12O__supportedBandCombinationList_UplinkTxSwitch_v1720 z) /\
  True.

Definition RF_ParametersMRDC__ext12__Type := RF_ParametersMRDC__ext12O__Type.
Definition RF_ParametersMRDC__ext12__cond := RF_ParametersMRDC__ext12O__cond.

Require Import NR.BandCombinationList_v1730.

Opaque BandCombinationList_v1730__cond BandCombinationList_v1730__Format.

Require Import NR.BandCombinationList_v1730.

Opaque BandCombinationList_v1730__cond BandCombinationList_v1730__Format.

Require Import NR.BandCombinationList_UplinkTxSwitch_v1730.

Opaque BandCombinationList_UplinkTxSwitch_v1730__cond BandCombinationList_UplinkTxSwitch_v1730__Format.

Record RF_ParametersMRDC__ext13O__Type : Set :=
  make__RF_ParametersMRDC__ext13O__Type {
    RF_ParametersMRDC__ext13O__supportedBandCombinationList_v1730 : option BandCombinationList_v1730__Type ;
    RF_ParametersMRDC__ext13O__supportedBandCombinationListNEDC_Only_v1730 : option BandCombinationList_v1730__Type ;
    RF_ParametersMRDC__ext13O__supportedBandCombinationList_UplinkTxSwitch_v1730 : option BandCombinationList_UplinkTxSwitch_v1730__Type ;
}.
Definition RF_ParametersMRDC__ext13O__list := (
 Opt BandCombinationList_v1730__Type BandCombinationList_v1730__cond ::
 Opt BandCombinationList_v1730__Type BandCombinationList_v1730__cond ::
 Opt BandCombinationList_UplinkTxSwitch_v1730__Type BandCombinationList_UplinkTxSwitch_v1730__cond ::
 nil).
Definition RF_ParametersMRDC__ext13O__cond z := 
  opt_cond BandCombinationList_v1730__cond (RF_ParametersMRDC__ext13O__supportedBandCombinationList_v1730 z) /\
  opt_cond BandCombinationList_v1730__cond (RF_ParametersMRDC__ext13O__supportedBandCombinationListNEDC_Only_v1730 z) /\
  opt_cond BandCombinationList_UplinkTxSwitch_v1730__cond (RF_ParametersMRDC__ext13O__supportedBandCombinationList_UplinkTxSwitch_v1730 z) /\
  True.

Definition RF_ParametersMRDC__ext13__Type := RF_ParametersMRDC__ext13O__Type.
Definition RF_ParametersMRDC__ext13__cond := RF_ParametersMRDC__ext13O__cond.

Record RF_ParametersMRDC__Type : Set :=
  make__RF_ParametersMRDC__Type {
    RF_ParametersMRDC__supportedBandCombinationList : option BandCombinationList__Type ;
    RF_ParametersMRDC__appliedFreqBandListFilter : option FreqBandList__Type ;
    RF_ParametersMRDC__ext0 : option RF_ParametersMRDC__ext0__Type ;
    RF_ParametersMRDC__ext1 : option RF_ParametersMRDC__ext1__Type ;
    RF_ParametersMRDC__ext2 : option RF_ParametersMRDC__ext2__Type ;
    RF_ParametersMRDC__ext3 : option RF_ParametersMRDC__ext3__Type ;
    RF_ParametersMRDC__ext4 : option RF_ParametersMRDC__ext4__Type ;
    RF_ParametersMRDC__ext5 : option RF_ParametersMRDC__ext5__Type ;
    RF_ParametersMRDC__ext6 : option RF_ParametersMRDC__ext6__Type ;
    RF_ParametersMRDC__ext7 : option RF_ParametersMRDC__ext7__Type ;
    RF_ParametersMRDC__ext8 : option RF_ParametersMRDC__ext8__Type ;
    RF_ParametersMRDC__ext9 : option RF_ParametersMRDC__ext9__Type ;
    RF_ParametersMRDC__ext10 : option RF_ParametersMRDC__ext10__Type ;
    RF_ParametersMRDC__ext11 : option RF_ParametersMRDC__ext11__Type ;
    RF_ParametersMRDC__ext12 : option RF_ParametersMRDC__ext12__Type ;
    RF_ParametersMRDC__ext13 : option RF_ParametersMRDC__ext13__Type ;
}.
Definition RF_ParametersMRDC__root_list : list seq_elem := (
 Opt BandCombinationList__Type BandCombinationList__cond ::
 Opt FreqBandList__Type FreqBandList__cond ::
 nil).
Definition RF_ParametersMRDC__ext_list : list typ := (
  typ_cons RF_ParametersMRDC__ext0__Type RF_ParametersMRDC__ext0__cond ::
  typ_cons RF_ParametersMRDC__ext1__Type RF_ParametersMRDC__ext1__cond ::
  typ_cons RF_ParametersMRDC__ext2__Type RF_ParametersMRDC__ext2__cond ::
  typ_cons RF_ParametersMRDC__ext3__Type RF_ParametersMRDC__ext3__cond ::
  typ_cons RF_ParametersMRDC__ext4__Type RF_ParametersMRDC__ext4__cond ::
  typ_cons RF_ParametersMRDC__ext5__Type RF_ParametersMRDC__ext5__cond ::
  typ_cons RF_ParametersMRDC__ext6__Type RF_ParametersMRDC__ext6__cond ::
  typ_cons RF_ParametersMRDC__ext7__Type RF_ParametersMRDC__ext7__cond ::
  typ_cons RF_ParametersMRDC__ext8__Type RF_ParametersMRDC__ext8__cond ::
  typ_cons RF_ParametersMRDC__ext9__Type RF_ParametersMRDC__ext9__cond ::
  typ_cons RF_ParametersMRDC__ext10__Type RF_ParametersMRDC__ext10__cond ::
  typ_cons RF_ParametersMRDC__ext11__Type RF_ParametersMRDC__ext11__cond ::
  typ_cons RF_ParametersMRDC__ext12__Type RF_ParametersMRDC__ext12__cond ::
  typ_cons RF_ParametersMRDC__ext13__Type RF_ParametersMRDC__ext13__cond ::
  nil).
Definition RF_ParametersMRDC__cond (z : RF_ParametersMRDC__Type) := 
(  opt_cond BandCombinationList__cond (RF_ParametersMRDC__supportedBandCombinationList z) /\
  opt_cond FreqBandList__cond (RF_ParametersMRDC__appliedFreqBandListFilter z) /\
  True) /\ 
(  opt_cond RF_ParametersMRDC__ext0__cond (RF_ParametersMRDC__ext0 z) /\
  opt_cond RF_ParametersMRDC__ext1__cond (RF_ParametersMRDC__ext1 z) /\
  opt_cond RF_ParametersMRDC__ext2__cond (RF_ParametersMRDC__ext2 z) /\
  opt_cond RF_ParametersMRDC__ext3__cond (RF_ParametersMRDC__ext3 z) /\
  opt_cond RF_ParametersMRDC__ext4__cond (RF_ParametersMRDC__ext4 z) /\
  opt_cond RF_ParametersMRDC__ext5__cond (RF_ParametersMRDC__ext5 z) /\
  opt_cond RF_ParametersMRDC__ext6__cond (RF_ParametersMRDC__ext6 z) /\
  opt_cond RF_ParametersMRDC__ext7__cond (RF_ParametersMRDC__ext7 z) /\
  opt_cond RF_ParametersMRDC__ext8__cond (RF_ParametersMRDC__ext8 z) /\
  opt_cond RF_ParametersMRDC__ext9__cond (RF_ParametersMRDC__ext9 z) /\
  opt_cond RF_ParametersMRDC__ext10__cond (RF_ParametersMRDC__ext10 z) /\
  opt_cond RF_ParametersMRDC__ext11__cond (RF_ParametersMRDC__ext11 z) /\
  opt_cond RF_ParametersMRDC__ext12__cond (RF_ParametersMRDC__ext12 z) /\
  opt_cond RF_ParametersMRDC__ext13__cond (RF_ParametersMRDC__ext13 z) /\
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
Definition RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Format : T_Format RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__nat__Format RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F1 RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F2 RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F1F2 RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__F2F1.

Opaque RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__cond RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Format.


Definition RF_ParametersMRDC__ext0O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext0O__list.
Definition RF_ParametersMRDC__ext0O__Format_list : RF_ParametersMRDC__ext0O__Format_Type :=
  (RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested__Format, (BandCombinationList_v1540__Format, unit_format)).
Definition RF_ParametersMRDC__ext0O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext0O__list RF_ParametersMRDC__ext0O__Format_list.
Definition RF_ParametersMRDC__ext0O__F1 z :=
  (RF_ParametersMRDC__ext0O__srs_SwitchingTimeRequested z, (RF_ParametersMRDC__ext0O__supportedBandCombinationList_v1540 z, tt)).
Definition RF_ParametersMRDC__ext0O__F2 (y : seq_type RF_ParametersMRDC__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_ParametersMRDC__ext0O__Type i0 i1
  end.
Lemma RF_ParametersMRDC__ext0O__F1F2_cond (z : RF_ParametersMRDC__ext0O__Type)
  : RF_ParametersMRDC__ext0O__cond z ->
  (seq_cond RF_ParametersMRDC__ext0O__list (RF_ParametersMRDC__ext0O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext0O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext0O__F1F2_cond2 (z : RF_ParametersMRDC__ext0O__Type)
 : RF_ParametersMRDC__ext0O__F2 (RF_ParametersMRDC__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext0O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext0O__list)
  : seq_cond RF_ParametersMRDC__ext0O__list y ->
 (RF_ParametersMRDC__ext0O__cond (RF_ParametersMRDC__ext0O__F2 y)) /\  RF_ParametersMRDC__ext0O__F1 (RF_ParametersMRDC__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext0O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext0O__Format : T_Format RF_ParametersMRDC__ext0O__Type RF_ParametersMRDC__ext0O__cond :=
        proj2_format  RF_ParametersMRDC__ext0O__cond RF_ParametersMRDC__ext0O__list__Format
    RF_ParametersMRDC__ext0O__F1 RF_ParametersMRDC__ext0O__F2 RF_ParametersMRDC__ext0O__F1F2_cond  RF_ParametersMRDC__ext0O__F1F2_cond2 RF_ParametersMRDC__ext0O__F2F1_cond.
Opaque RF_ParametersMRDC__ext0O__cond RF_ParametersMRDC__ext0O__Format.

Definition RF_ParametersMRDC__ext0__check_all_none (b : RF_ParametersMRDC__ext0O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext0__Format : T_Format RF_ParametersMRDC__ext0__Type RF_ParametersMRDC__ext0__cond :=
  restrict_add_format RF_ParametersMRDC__ext0__check_all_none RF_ParametersMRDC__ext0O__Format.

Opaque RF_ParametersMRDC__ext0__cond RF_ParametersMRDC__ext0__Format.


Definition RF_ParametersMRDC__ext1O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext1O__list.
Definition RF_ParametersMRDC__ext1O__Format_list : RF_ParametersMRDC__ext1O__Format_Type :=
  (BandCombinationList_v1550__Format, unit_format).
Definition RF_ParametersMRDC__ext1O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext1O__list RF_ParametersMRDC__ext1O__Format_list.
Definition RF_ParametersMRDC__ext1O__F1 z :=
  (RF_ParametersMRDC__ext1O__supportedBandCombinationList_v1550 z, tt).
Definition RF_ParametersMRDC__ext1O__F2 (y : seq_type RF_ParametersMRDC__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__RF_ParametersMRDC__ext1O__Type i0
  end.
Lemma RF_ParametersMRDC__ext1O__F1F2_cond (z : RF_ParametersMRDC__ext1O__Type)
  : RF_ParametersMRDC__ext1O__cond z ->
  (seq_cond RF_ParametersMRDC__ext1O__list (RF_ParametersMRDC__ext1O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext1O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext1O__F1F2_cond2 (z : RF_ParametersMRDC__ext1O__Type)
 : RF_ParametersMRDC__ext1O__F2 (RF_ParametersMRDC__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext1O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext1O__list)
  : seq_cond RF_ParametersMRDC__ext1O__list y ->
 (RF_ParametersMRDC__ext1O__cond (RF_ParametersMRDC__ext1O__F2 y)) /\  RF_ParametersMRDC__ext1O__F1 (RF_ParametersMRDC__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext1O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext1O__Format : T_Format RF_ParametersMRDC__ext1O__Type RF_ParametersMRDC__ext1O__cond :=
        proj2_format  RF_ParametersMRDC__ext1O__cond RF_ParametersMRDC__ext1O__list__Format
    RF_ParametersMRDC__ext1O__F1 RF_ParametersMRDC__ext1O__F2 RF_ParametersMRDC__ext1O__F1F2_cond  RF_ParametersMRDC__ext1O__F1F2_cond2 RF_ParametersMRDC__ext1O__F2F1_cond.
Opaque RF_ParametersMRDC__ext1O__cond RF_ParametersMRDC__ext1O__Format.

Definition RF_ParametersMRDC__ext1__check_all_none (b : RF_ParametersMRDC__ext1O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext1O__Type None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext1__Format : T_Format RF_ParametersMRDC__ext1__Type RF_ParametersMRDC__ext1__cond :=
  restrict_add_format RF_ParametersMRDC__ext1__check_all_none RF_ParametersMRDC__ext1O__Format.

Opaque RF_ParametersMRDC__ext1__cond RF_ParametersMRDC__ext1__Format.


Definition RF_ParametersMRDC__ext2O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext2O__list.
Definition RF_ParametersMRDC__ext2O__Format_list : RF_ParametersMRDC__ext2O__Format_Type :=
  (BandCombinationList_v1560__Format, (BandCombinationList__Format, unit_format)).
Definition RF_ParametersMRDC__ext2O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext2O__list RF_ParametersMRDC__ext2O__Format_list.
Definition RF_ParametersMRDC__ext2O__F1 z :=
  (RF_ParametersMRDC__ext2O__supportedBandCombinationList_v1560 z, (RF_ParametersMRDC__ext2O__supportedBandCombinationListNEDC_Only z, tt)).
Definition RF_ParametersMRDC__ext2O__F2 (y : seq_type RF_ParametersMRDC__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_ParametersMRDC__ext2O__Type i0 i1
  end.
Lemma RF_ParametersMRDC__ext2O__F1F2_cond (z : RF_ParametersMRDC__ext2O__Type)
  : RF_ParametersMRDC__ext2O__cond z ->
  (seq_cond RF_ParametersMRDC__ext2O__list (RF_ParametersMRDC__ext2O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext2O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext2O__F1F2_cond2 (z : RF_ParametersMRDC__ext2O__Type)
 : RF_ParametersMRDC__ext2O__F2 (RF_ParametersMRDC__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext2O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext2O__list)
  : seq_cond RF_ParametersMRDC__ext2O__list y ->
 (RF_ParametersMRDC__ext2O__cond (RF_ParametersMRDC__ext2O__F2 y)) /\  RF_ParametersMRDC__ext2O__F1 (RF_ParametersMRDC__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext2O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext2O__Format : T_Format RF_ParametersMRDC__ext2O__Type RF_ParametersMRDC__ext2O__cond :=
        proj2_format  RF_ParametersMRDC__ext2O__cond RF_ParametersMRDC__ext2O__list__Format
    RF_ParametersMRDC__ext2O__F1 RF_ParametersMRDC__ext2O__F2 RF_ParametersMRDC__ext2O__F1F2_cond  RF_ParametersMRDC__ext2O__F1F2_cond2 RF_ParametersMRDC__ext2O__F2F1_cond.
Opaque RF_ParametersMRDC__ext2O__cond RF_ParametersMRDC__ext2O__Format.

Definition RF_ParametersMRDC__ext2__check_all_none (b : RF_ParametersMRDC__ext2O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext2__Format : T_Format RF_ParametersMRDC__ext2__Type RF_ParametersMRDC__ext2__cond :=
  restrict_add_format RF_ParametersMRDC__ext2__check_all_none RF_ParametersMRDC__ext2O__Format.

Opaque RF_ParametersMRDC__ext2__cond RF_ParametersMRDC__ext2__Format.


Definition RF_ParametersMRDC__ext3O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext3O__list.
Definition RF_ParametersMRDC__ext3O__Format_list : RF_ParametersMRDC__ext3O__Format_Type :=
  (BandCombinationList_v1570__Format, unit_format).
Definition RF_ParametersMRDC__ext3O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext3O__list RF_ParametersMRDC__ext3O__Format_list.
Definition RF_ParametersMRDC__ext3O__F1 z :=
  (RF_ParametersMRDC__ext3O__supportedBandCombinationList_v1570 z, tt).
Definition RF_ParametersMRDC__ext3O__F2 (y : seq_type RF_ParametersMRDC__ext3O__list) :=
  match y with
  | (i0, _)=>
    make__RF_ParametersMRDC__ext3O__Type i0
  end.
Lemma RF_ParametersMRDC__ext3O__F1F2_cond (z : RF_ParametersMRDC__ext3O__Type)
  : RF_ParametersMRDC__ext3O__cond z ->
  (seq_cond RF_ParametersMRDC__ext3O__list (RF_ParametersMRDC__ext3O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext3O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext3O__F1F2_cond2 (z : RF_ParametersMRDC__ext3O__Type)
 : RF_ParametersMRDC__ext3O__F2 (RF_ParametersMRDC__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext3O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext3O__list)
  : seq_cond RF_ParametersMRDC__ext3O__list y ->
 (RF_ParametersMRDC__ext3O__cond (RF_ParametersMRDC__ext3O__F2 y)) /\  RF_ParametersMRDC__ext3O__F1 (RF_ParametersMRDC__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext3O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext3O__Format : T_Format RF_ParametersMRDC__ext3O__Type RF_ParametersMRDC__ext3O__cond :=
        proj2_format  RF_ParametersMRDC__ext3O__cond RF_ParametersMRDC__ext3O__list__Format
    RF_ParametersMRDC__ext3O__F1 RF_ParametersMRDC__ext3O__F2 RF_ParametersMRDC__ext3O__F1F2_cond  RF_ParametersMRDC__ext3O__F1F2_cond2 RF_ParametersMRDC__ext3O__F2F1_cond.
Opaque RF_ParametersMRDC__ext3O__cond RF_ParametersMRDC__ext3O__Format.

Definition RF_ParametersMRDC__ext3__check_all_none (b : RF_ParametersMRDC__ext3O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext3O__Type None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext3__Format : T_Format RF_ParametersMRDC__ext3__Type RF_ParametersMRDC__ext3__cond :=
  restrict_add_format RF_ParametersMRDC__ext3__check_all_none RF_ParametersMRDC__ext3O__Format.

Opaque RF_ParametersMRDC__ext3__cond RF_ParametersMRDC__ext3__Format.


Definition RF_ParametersMRDC__ext4O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext4O__list.
Definition RF_ParametersMRDC__ext4O__Format_list : RF_ParametersMRDC__ext4O__Format_Type :=
  (BandCombinationList_v1580__Format, unit_format).
Definition RF_ParametersMRDC__ext4O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext4O__list RF_ParametersMRDC__ext4O__Format_list.
Definition RF_ParametersMRDC__ext4O__F1 z :=
  (RF_ParametersMRDC__ext4O__supportedBandCombinationList_v1580 z, tt).
Definition RF_ParametersMRDC__ext4O__F2 (y : seq_type RF_ParametersMRDC__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__RF_ParametersMRDC__ext4O__Type i0
  end.
Lemma RF_ParametersMRDC__ext4O__F1F2_cond (z : RF_ParametersMRDC__ext4O__Type)
  : RF_ParametersMRDC__ext4O__cond z ->
  (seq_cond RF_ParametersMRDC__ext4O__list (RF_ParametersMRDC__ext4O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext4O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext4O__F1F2_cond2 (z : RF_ParametersMRDC__ext4O__Type)
 : RF_ParametersMRDC__ext4O__F2 (RF_ParametersMRDC__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext4O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext4O__list)
  : seq_cond RF_ParametersMRDC__ext4O__list y ->
 (RF_ParametersMRDC__ext4O__cond (RF_ParametersMRDC__ext4O__F2 y)) /\  RF_ParametersMRDC__ext4O__F1 (RF_ParametersMRDC__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext4O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext4O__Format : T_Format RF_ParametersMRDC__ext4O__Type RF_ParametersMRDC__ext4O__cond :=
        proj2_format  RF_ParametersMRDC__ext4O__cond RF_ParametersMRDC__ext4O__list__Format
    RF_ParametersMRDC__ext4O__F1 RF_ParametersMRDC__ext4O__F2 RF_ParametersMRDC__ext4O__F1F2_cond  RF_ParametersMRDC__ext4O__F1F2_cond2 RF_ParametersMRDC__ext4O__F2F1_cond.
Opaque RF_ParametersMRDC__ext4O__cond RF_ParametersMRDC__ext4O__Format.

Definition RF_ParametersMRDC__ext4__check_all_none (b : RF_ParametersMRDC__ext4O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext4O__Type None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext4__Format : T_Format RF_ParametersMRDC__ext4__Type RF_ParametersMRDC__ext4__cond :=
  restrict_add_format RF_ParametersMRDC__ext4__check_all_none RF_ParametersMRDC__ext4O__Format.

Opaque RF_ParametersMRDC__ext4__cond RF_ParametersMRDC__ext4__Format.


Definition RF_ParametersMRDC__ext5O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext5O__list.
Definition RF_ParametersMRDC__ext5O__Format_list : RF_ParametersMRDC__ext5O__Format_Type :=
  (BandCombinationList_v1590__Format, unit_format).
Definition RF_ParametersMRDC__ext5O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext5O__list RF_ParametersMRDC__ext5O__Format_list.
Definition RF_ParametersMRDC__ext5O__F1 z :=
  (RF_ParametersMRDC__ext5O__supportedBandCombinationList_v1590 z, tt).
Definition RF_ParametersMRDC__ext5O__F2 (y : seq_type RF_ParametersMRDC__ext5O__list) :=
  match y with
  | (i0, _)=>
    make__RF_ParametersMRDC__ext5O__Type i0
  end.
Lemma RF_ParametersMRDC__ext5O__F1F2_cond (z : RF_ParametersMRDC__ext5O__Type)
  : RF_ParametersMRDC__ext5O__cond z ->
  (seq_cond RF_ParametersMRDC__ext5O__list (RF_ParametersMRDC__ext5O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext5O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext5O__F1F2_cond2 (z : RF_ParametersMRDC__ext5O__Type)
 : RF_ParametersMRDC__ext5O__F2 (RF_ParametersMRDC__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext5O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext5O__list)
  : seq_cond RF_ParametersMRDC__ext5O__list y ->
 (RF_ParametersMRDC__ext5O__cond (RF_ParametersMRDC__ext5O__F2 y)) /\  RF_ParametersMRDC__ext5O__F1 (RF_ParametersMRDC__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext5O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext5O__Format : T_Format RF_ParametersMRDC__ext5O__Type RF_ParametersMRDC__ext5O__cond :=
        proj2_format  RF_ParametersMRDC__ext5O__cond RF_ParametersMRDC__ext5O__list__Format
    RF_ParametersMRDC__ext5O__F1 RF_ParametersMRDC__ext5O__F2 RF_ParametersMRDC__ext5O__F1F2_cond  RF_ParametersMRDC__ext5O__F1F2_cond2 RF_ParametersMRDC__ext5O__F2F1_cond.
Opaque RF_ParametersMRDC__ext5O__cond RF_ParametersMRDC__ext5O__Format.

Definition RF_ParametersMRDC__ext5__check_all_none (b : RF_ParametersMRDC__ext5O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext5O__Type None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext5__Format : T_Format RF_ParametersMRDC__ext5__Type RF_ParametersMRDC__ext5__cond :=
  restrict_add_format RF_ParametersMRDC__ext5__check_all_none RF_ParametersMRDC__ext5O__Format.

Opaque RF_ParametersMRDC__ext5__cond RF_ParametersMRDC__ext5__Format.


Definition RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list.
Definition RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Format_list : RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Format_Type :=
  (BandCombinationList_v1540__Format, (BandCombinationList_v1560__Format, (BandCombinationList_v1570__Format, (BandCombinationList_v1580__Format, (BandCombinationList_v1590__Format, unit_format))))).
Definition RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Format_list.
Definition RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1 z :=
  (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1540 z, (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1560 z, (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1570 z, (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1580 z, (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__supportedBandCombinationList_v1590 z, tt))))).
Definition RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F2 (y : seq_type RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Type i0 i1 i2 i3 i4
  end.
Lemma RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1F2_cond (z : RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Type)
  : RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond z ->
  (seq_cond RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1 z)).
intro H. unfold RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1F2_cond2 (z : RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Type)
 : RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F2 (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F2F1_cond (y : seq_type RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list)
  : seq_cond RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list y ->
 (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F2 y)) /\  RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1 (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Format : T_Format RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Type RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond :=
        proj2_format  RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__list__Format
    RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1 RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F2 RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1F2_cond  RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F1F2_cond2 RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__F2F1_cond.
Opaque RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__cond RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Format.


Definition RF_ParametersMRDC__ext6O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext6O__list.
Definition RF_ParametersMRDC__ext6O__Format_list : RF_ParametersMRDC__ext6O__Format_Type :=
  (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0__Format, unit_format).
Definition RF_ParametersMRDC__ext6O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext6O__list RF_ParametersMRDC__ext6O__Format_list.
Definition RF_ParametersMRDC__ext6O__F1 z :=
  (RF_ParametersMRDC__ext6O__supportedBandCombinationListNEDC_Only_v15a0 z, tt).
Definition RF_ParametersMRDC__ext6O__F2 (y : seq_type RF_ParametersMRDC__ext6O__list) :=
  match y with
  | (i0, _)=>
    make__RF_ParametersMRDC__ext6O__Type i0
  end.
Lemma RF_ParametersMRDC__ext6O__F1F2_cond (z : RF_ParametersMRDC__ext6O__Type)
  : RF_ParametersMRDC__ext6O__cond z ->
  (seq_cond RF_ParametersMRDC__ext6O__list (RF_ParametersMRDC__ext6O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext6O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext6O__F1F2_cond2 (z : RF_ParametersMRDC__ext6O__Type)
 : RF_ParametersMRDC__ext6O__F2 (RF_ParametersMRDC__ext6O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext6O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext6O__list)
  : seq_cond RF_ParametersMRDC__ext6O__list y ->
 (RF_ParametersMRDC__ext6O__cond (RF_ParametersMRDC__ext6O__F2 y)) /\  RF_ParametersMRDC__ext6O__F1 (RF_ParametersMRDC__ext6O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext6O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext6O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext6O__Format : T_Format RF_ParametersMRDC__ext6O__Type RF_ParametersMRDC__ext6O__cond :=
        proj2_format  RF_ParametersMRDC__ext6O__cond RF_ParametersMRDC__ext6O__list__Format
    RF_ParametersMRDC__ext6O__F1 RF_ParametersMRDC__ext6O__F2 RF_ParametersMRDC__ext6O__F1F2_cond  RF_ParametersMRDC__ext6O__F1F2_cond2 RF_ParametersMRDC__ext6O__F2F1_cond.
Opaque RF_ParametersMRDC__ext6O__cond RF_ParametersMRDC__ext6O__Format.

Definition RF_ParametersMRDC__ext6__check_all_none (b : RF_ParametersMRDC__ext6O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext6O__Type None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext6__Format : T_Format RF_ParametersMRDC__ext6__Type RF_ParametersMRDC__ext6__cond :=
  restrict_add_format RF_ParametersMRDC__ext6__check_all_none RF_ParametersMRDC__ext6O__Format.

Opaque RF_ParametersMRDC__ext6__cond RF_ParametersMRDC__ext6__Format.


Definition RF_ParametersMRDC__ext7O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext7O__list.
Definition RF_ParametersMRDC__ext7O__Format_list : RF_ParametersMRDC__ext7O__Format_Type :=
  (BandCombinationList_v1610__Format, (BandCombinationList_v1610__Format, (BandCombinationList_UplinkTxSwitch_r16__Format, unit_format))).
Definition RF_ParametersMRDC__ext7O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext7O__list RF_ParametersMRDC__ext7O__Format_list.
Definition RF_ParametersMRDC__ext7O__F1 z :=
  (RF_ParametersMRDC__ext7O__supportedBandCombinationList_v1610 z, (RF_ParametersMRDC__ext7O__supportedBandCombinationListNEDC_Only_v1610 z, (RF_ParametersMRDC__ext7O__supportedBandCombinationList_UplinkTxSwitch_r16 z, tt))).
Definition RF_ParametersMRDC__ext7O__F2 (y : seq_type RF_ParametersMRDC__ext7O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RF_ParametersMRDC__ext7O__Type i0 i1 i2
  end.
Lemma RF_ParametersMRDC__ext7O__F1F2_cond (z : RF_ParametersMRDC__ext7O__Type)
  : RF_ParametersMRDC__ext7O__cond z ->
  (seq_cond RF_ParametersMRDC__ext7O__list (RF_ParametersMRDC__ext7O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext7O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext7O__F1F2_cond2 (z : RF_ParametersMRDC__ext7O__Type)
 : RF_ParametersMRDC__ext7O__F2 (RF_ParametersMRDC__ext7O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext7O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext7O__list)
  : seq_cond RF_ParametersMRDC__ext7O__list y ->
 (RF_ParametersMRDC__ext7O__cond (RF_ParametersMRDC__ext7O__F2 y)) /\  RF_ParametersMRDC__ext7O__F1 (RF_ParametersMRDC__ext7O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext7O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext7O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext7O__Format : T_Format RF_ParametersMRDC__ext7O__Type RF_ParametersMRDC__ext7O__cond :=
        proj2_format  RF_ParametersMRDC__ext7O__cond RF_ParametersMRDC__ext7O__list__Format
    RF_ParametersMRDC__ext7O__F1 RF_ParametersMRDC__ext7O__F2 RF_ParametersMRDC__ext7O__F1F2_cond  RF_ParametersMRDC__ext7O__F1F2_cond2 RF_ParametersMRDC__ext7O__F2F1_cond.
Opaque RF_ParametersMRDC__ext7O__cond RF_ParametersMRDC__ext7O__Format.

Definition RF_ParametersMRDC__ext7__check_all_none (b : RF_ParametersMRDC__ext7O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext7O__Type None None None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext7__Format : T_Format RF_ParametersMRDC__ext7__Type RF_ParametersMRDC__ext7__cond :=
  restrict_add_format RF_ParametersMRDC__ext7__check_all_none RF_ParametersMRDC__ext7O__Format.

Opaque RF_ParametersMRDC__ext7__cond RF_ParametersMRDC__ext7__Format.


Definition RF_ParametersMRDC__ext8O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext8O__list.
Definition RF_ParametersMRDC__ext8O__Format_list : RF_ParametersMRDC__ext8O__Format_Type :=
  (BandCombinationList_v1630__Format, (BandCombinationList_v1630__Format, (BandCombinationList_UplinkTxSwitch_v1630__Format, unit_format))).
Definition RF_ParametersMRDC__ext8O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext8O__list RF_ParametersMRDC__ext8O__Format_list.
Definition RF_ParametersMRDC__ext8O__F1 z :=
  (RF_ParametersMRDC__ext8O__supportedBandCombinationList_v1630 z, (RF_ParametersMRDC__ext8O__supportedBandCombinationListNEDC_Only_v1630 z, (RF_ParametersMRDC__ext8O__supportedBandCombinationList_UplinkTxSwitch_v1630 z, tt))).
Definition RF_ParametersMRDC__ext8O__F2 (y : seq_type RF_ParametersMRDC__ext8O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RF_ParametersMRDC__ext8O__Type i0 i1 i2
  end.
Lemma RF_ParametersMRDC__ext8O__F1F2_cond (z : RF_ParametersMRDC__ext8O__Type)
  : RF_ParametersMRDC__ext8O__cond z ->
  (seq_cond RF_ParametersMRDC__ext8O__list (RF_ParametersMRDC__ext8O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext8O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext8O__F1F2_cond2 (z : RF_ParametersMRDC__ext8O__Type)
 : RF_ParametersMRDC__ext8O__F2 (RF_ParametersMRDC__ext8O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext8O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext8O__list)
  : seq_cond RF_ParametersMRDC__ext8O__list y ->
 (RF_ParametersMRDC__ext8O__cond (RF_ParametersMRDC__ext8O__F2 y)) /\  RF_ParametersMRDC__ext8O__F1 (RF_ParametersMRDC__ext8O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext8O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext8O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext8O__Format : T_Format RF_ParametersMRDC__ext8O__Type RF_ParametersMRDC__ext8O__cond :=
        proj2_format  RF_ParametersMRDC__ext8O__cond RF_ParametersMRDC__ext8O__list__Format
    RF_ParametersMRDC__ext8O__F1 RF_ParametersMRDC__ext8O__F2 RF_ParametersMRDC__ext8O__F1F2_cond  RF_ParametersMRDC__ext8O__F1F2_cond2 RF_ParametersMRDC__ext8O__F2F1_cond.
Opaque RF_ParametersMRDC__ext8O__cond RF_ParametersMRDC__ext8O__Format.

Definition RF_ParametersMRDC__ext8__check_all_none (b : RF_ParametersMRDC__ext8O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext8O__Type None None None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext8__Format : T_Format RF_ParametersMRDC__ext8__Type RF_ParametersMRDC__ext8__cond :=
  restrict_add_format RF_ParametersMRDC__ext8__check_all_none RF_ParametersMRDC__ext8O__Format.

Opaque RF_ParametersMRDC__ext8__cond RF_ParametersMRDC__ext8__Format.


Definition RF_ParametersMRDC__ext9O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext9O__list.
Definition RF_ParametersMRDC__ext9O__Format_list : RF_ParametersMRDC__ext9O__Format_Type :=
  (BandCombinationList_v1640__Format, (BandCombinationList_v1640__Format, (BandCombinationList_UplinkTxSwitch_v1640__Format, unit_format))).
Definition RF_ParametersMRDC__ext9O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext9O__list RF_ParametersMRDC__ext9O__Format_list.
Definition RF_ParametersMRDC__ext9O__F1 z :=
  (RF_ParametersMRDC__ext9O__supportedBandCombinationList_v1640 z, (RF_ParametersMRDC__ext9O__supportedBandCombinationListNEDC_Only_v1640 z, (RF_ParametersMRDC__ext9O__supportedBandCombinationList_UplinkTxSwitch_v1640 z, tt))).
Definition RF_ParametersMRDC__ext9O__F2 (y : seq_type RF_ParametersMRDC__ext9O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RF_ParametersMRDC__ext9O__Type i0 i1 i2
  end.
Lemma RF_ParametersMRDC__ext9O__F1F2_cond (z : RF_ParametersMRDC__ext9O__Type)
  : RF_ParametersMRDC__ext9O__cond z ->
  (seq_cond RF_ParametersMRDC__ext9O__list (RF_ParametersMRDC__ext9O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext9O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext9O__F1F2_cond2 (z : RF_ParametersMRDC__ext9O__Type)
 : RF_ParametersMRDC__ext9O__F2 (RF_ParametersMRDC__ext9O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext9O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext9O__list)
  : seq_cond RF_ParametersMRDC__ext9O__list y ->
 (RF_ParametersMRDC__ext9O__cond (RF_ParametersMRDC__ext9O__F2 y)) /\  RF_ParametersMRDC__ext9O__F1 (RF_ParametersMRDC__ext9O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext9O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext9O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext9O__Format : T_Format RF_ParametersMRDC__ext9O__Type RF_ParametersMRDC__ext9O__cond :=
        proj2_format  RF_ParametersMRDC__ext9O__cond RF_ParametersMRDC__ext9O__list__Format
    RF_ParametersMRDC__ext9O__F1 RF_ParametersMRDC__ext9O__F2 RF_ParametersMRDC__ext9O__F1F2_cond  RF_ParametersMRDC__ext9O__F1F2_cond2 RF_ParametersMRDC__ext9O__F2F1_cond.
Opaque RF_ParametersMRDC__ext9O__cond RF_ParametersMRDC__ext9O__Format.

Definition RF_ParametersMRDC__ext9__check_all_none (b : RF_ParametersMRDC__ext9O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext9O__Type None None None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext9__Format : T_Format RF_ParametersMRDC__ext9__Type RF_ParametersMRDC__ext9__cond :=
  restrict_add_format RF_ParametersMRDC__ext9__check_all_none RF_ParametersMRDC__ext9O__Format.

Opaque RF_ParametersMRDC__ext9__cond RF_ParametersMRDC__ext9__Format.


Definition RF_ParametersMRDC__ext10O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext10O__list.
Definition RF_ParametersMRDC__ext10O__Format_list : RF_ParametersMRDC__ext10O__Format_Type :=
  (BandCombinationList_UplinkTxSwitch_v1670__Format, unit_format).
Definition RF_ParametersMRDC__ext10O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext10O__list RF_ParametersMRDC__ext10O__Format_list.
Definition RF_ParametersMRDC__ext10O__F1 z :=
  (RF_ParametersMRDC__ext10O__supportedBandCombinationList_UplinkTxSwitch_v1670 z, tt).
Definition RF_ParametersMRDC__ext10O__F2 (y : seq_type RF_ParametersMRDC__ext10O__list) :=
  match y with
  | (i0, _)=>
    make__RF_ParametersMRDC__ext10O__Type i0
  end.
Lemma RF_ParametersMRDC__ext10O__F1F2_cond (z : RF_ParametersMRDC__ext10O__Type)
  : RF_ParametersMRDC__ext10O__cond z ->
  (seq_cond RF_ParametersMRDC__ext10O__list (RF_ParametersMRDC__ext10O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext10O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext10O__F1F2_cond2 (z : RF_ParametersMRDC__ext10O__Type)
 : RF_ParametersMRDC__ext10O__F2 (RF_ParametersMRDC__ext10O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext10O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext10O__list)
  : seq_cond RF_ParametersMRDC__ext10O__list y ->
 (RF_ParametersMRDC__ext10O__cond (RF_ParametersMRDC__ext10O__F2 y)) /\  RF_ParametersMRDC__ext10O__F1 (RF_ParametersMRDC__ext10O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext10O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext10O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext10O__Format : T_Format RF_ParametersMRDC__ext10O__Type RF_ParametersMRDC__ext10O__cond :=
        proj2_format  RF_ParametersMRDC__ext10O__cond RF_ParametersMRDC__ext10O__list__Format
    RF_ParametersMRDC__ext10O__F1 RF_ParametersMRDC__ext10O__F2 RF_ParametersMRDC__ext10O__F1F2_cond  RF_ParametersMRDC__ext10O__F1F2_cond2 RF_ParametersMRDC__ext10O__F2F1_cond.
Opaque RF_ParametersMRDC__ext10O__cond RF_ParametersMRDC__ext10O__Format.

Definition RF_ParametersMRDC__ext10__check_all_none (b : RF_ParametersMRDC__ext10O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext10O__Type None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext10__Format : T_Format RF_ParametersMRDC__ext10__Type RF_ParametersMRDC__ext10__cond :=
  restrict_add_format RF_ParametersMRDC__ext10__check_all_none RF_ParametersMRDC__ext10O__Format.

Opaque RF_ParametersMRDC__ext10__cond RF_ParametersMRDC__ext10__Format.


Definition RF_ParametersMRDC__ext11O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext11O__list.
Definition RF_ParametersMRDC__ext11O__Format_list : RF_ParametersMRDC__ext11O__Format_Type :=
  (BandCombinationList_v1700__Format, (BandCombinationList_UplinkTxSwitch_v1700__Format, unit_format)).
Definition RF_ParametersMRDC__ext11O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext11O__list RF_ParametersMRDC__ext11O__Format_list.
Definition RF_ParametersMRDC__ext11O__F1 z :=
  (RF_ParametersMRDC__ext11O__supportedBandCombinationList_v1700 z, (RF_ParametersMRDC__ext11O__supportedBandCombinationList_UplinkTxSwitch_v1700 z, tt)).
Definition RF_ParametersMRDC__ext11O__F2 (y : seq_type RF_ParametersMRDC__ext11O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_ParametersMRDC__ext11O__Type i0 i1
  end.
Lemma RF_ParametersMRDC__ext11O__F1F2_cond (z : RF_ParametersMRDC__ext11O__Type)
  : RF_ParametersMRDC__ext11O__cond z ->
  (seq_cond RF_ParametersMRDC__ext11O__list (RF_ParametersMRDC__ext11O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext11O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext11O__F1F2_cond2 (z : RF_ParametersMRDC__ext11O__Type)
 : RF_ParametersMRDC__ext11O__F2 (RF_ParametersMRDC__ext11O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext11O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext11O__list)
  : seq_cond RF_ParametersMRDC__ext11O__list y ->
 (RF_ParametersMRDC__ext11O__cond (RF_ParametersMRDC__ext11O__F2 y)) /\  RF_ParametersMRDC__ext11O__F1 (RF_ParametersMRDC__ext11O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext11O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext11O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext11O__Format : T_Format RF_ParametersMRDC__ext11O__Type RF_ParametersMRDC__ext11O__cond :=
        proj2_format  RF_ParametersMRDC__ext11O__cond RF_ParametersMRDC__ext11O__list__Format
    RF_ParametersMRDC__ext11O__F1 RF_ParametersMRDC__ext11O__F2 RF_ParametersMRDC__ext11O__F1F2_cond  RF_ParametersMRDC__ext11O__F1F2_cond2 RF_ParametersMRDC__ext11O__F2F1_cond.
Opaque RF_ParametersMRDC__ext11O__cond RF_ParametersMRDC__ext11O__Format.

Definition RF_ParametersMRDC__ext11__check_all_none (b : RF_ParametersMRDC__ext11O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext11O__Type None None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext11__Format : T_Format RF_ParametersMRDC__ext11__Type RF_ParametersMRDC__ext11__cond :=
  restrict_add_format RF_ParametersMRDC__ext11__check_all_none RF_ParametersMRDC__ext11O__Format.

Opaque RF_ParametersMRDC__ext11__cond RF_ParametersMRDC__ext11__Format.


Definition RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list.
Definition RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Format_list : RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Format_Type :=
  (BandCombinationList_v1700__Format, (BandCombinationList_v1720__Format, unit_format)).
Definition RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Format_list.
Definition RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1 z :=
  (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__supportedBandCombinationList_v1700 z, (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__supportedBandCombinationList_v1720 z, tt)).
Definition RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F2 (y : seq_type RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Type i0 i1
  end.
Lemma RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1F2_cond (z : RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Type)
  : RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond z ->
  (seq_cond RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1 z)).
intro H. unfold RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1F2_cond2 (z : RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Type)
 : RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F2 (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F2F1_cond (y : seq_type RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list)
  : seq_cond RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list y ->
 (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F2 y)) /\  RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1 (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Format : T_Format RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Type RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond :=
        proj2_format  RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__list__Format
    RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1 RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F2 RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1F2_cond  RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F1F2_cond2 RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__F2F1_cond.
Opaque RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__cond RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Format.


Definition RF_ParametersMRDC__ext12O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext12O__list.
Definition RF_ParametersMRDC__ext12O__Format_list : RF_ParametersMRDC__ext12O__Format_Type :=
  (BandCombinationList_v1720__Format, (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720__Format, (BandCombinationList_UplinkTxSwitch_v1720__Format, unit_format))).
Definition RF_ParametersMRDC__ext12O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext12O__list RF_ParametersMRDC__ext12O__Format_list.
Definition RF_ParametersMRDC__ext12O__F1 z :=
  (RF_ParametersMRDC__ext12O__supportedBandCombinationList_v1720 z, (RF_ParametersMRDC__ext12O__supportedBandCombinationListNEDC_Only_v1720 z, (RF_ParametersMRDC__ext12O__supportedBandCombinationList_UplinkTxSwitch_v1720 z, tt))).
Definition RF_ParametersMRDC__ext12O__F2 (y : seq_type RF_ParametersMRDC__ext12O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RF_ParametersMRDC__ext12O__Type i0 i1 i2
  end.
Lemma RF_ParametersMRDC__ext12O__F1F2_cond (z : RF_ParametersMRDC__ext12O__Type)
  : RF_ParametersMRDC__ext12O__cond z ->
  (seq_cond RF_ParametersMRDC__ext12O__list (RF_ParametersMRDC__ext12O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext12O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext12O__F1F2_cond2 (z : RF_ParametersMRDC__ext12O__Type)
 : RF_ParametersMRDC__ext12O__F2 (RF_ParametersMRDC__ext12O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext12O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext12O__list)
  : seq_cond RF_ParametersMRDC__ext12O__list y ->
 (RF_ParametersMRDC__ext12O__cond (RF_ParametersMRDC__ext12O__F2 y)) /\  RF_ParametersMRDC__ext12O__F1 (RF_ParametersMRDC__ext12O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext12O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext12O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext12O__Format : T_Format RF_ParametersMRDC__ext12O__Type RF_ParametersMRDC__ext12O__cond :=
        proj2_format  RF_ParametersMRDC__ext12O__cond RF_ParametersMRDC__ext12O__list__Format
    RF_ParametersMRDC__ext12O__F1 RF_ParametersMRDC__ext12O__F2 RF_ParametersMRDC__ext12O__F1F2_cond  RF_ParametersMRDC__ext12O__F1F2_cond2 RF_ParametersMRDC__ext12O__F2F1_cond.
Opaque RF_ParametersMRDC__ext12O__cond RF_ParametersMRDC__ext12O__Format.

Definition RF_ParametersMRDC__ext12__check_all_none (b : RF_ParametersMRDC__ext12O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext12O__Type None None None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext12__Format : T_Format RF_ParametersMRDC__ext12__Type RF_ParametersMRDC__ext12__cond :=
  restrict_add_format RF_ParametersMRDC__ext12__check_all_none RF_ParametersMRDC__ext12O__Format.

Opaque RF_ParametersMRDC__ext12__cond RF_ParametersMRDC__ext12__Format.


Definition RF_ParametersMRDC__ext13O__Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__ext13O__list.
Definition RF_ParametersMRDC__ext13O__Format_list : RF_ParametersMRDC__ext13O__Format_Type :=
  (BandCombinationList_v1730__Format, (BandCombinationList_v1730__Format, (BandCombinationList_UplinkTxSwitch_v1730__Format, unit_format))).
Definition RF_ParametersMRDC__ext13O__list__Format := (*Eval compute in *) seq_format RF_ParametersMRDC__ext13O__list RF_ParametersMRDC__ext13O__Format_list.
Definition RF_ParametersMRDC__ext13O__F1 z :=
  (RF_ParametersMRDC__ext13O__supportedBandCombinationList_v1730 z, (RF_ParametersMRDC__ext13O__supportedBandCombinationListNEDC_Only_v1730 z, (RF_ParametersMRDC__ext13O__supportedBandCombinationList_UplinkTxSwitch_v1730 z, tt))).
Definition RF_ParametersMRDC__ext13O__F2 (y : seq_type RF_ParametersMRDC__ext13O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__RF_ParametersMRDC__ext13O__Type i0 i1 i2
  end.
Lemma RF_ParametersMRDC__ext13O__F1F2_cond (z : RF_ParametersMRDC__ext13O__Type)
  : RF_ParametersMRDC__ext13O__cond z ->
  (seq_cond RF_ParametersMRDC__ext13O__list (RF_ParametersMRDC__ext13O__F1 z)).
intro H. unfold RF_ParametersMRDC__ext13O__cond in H. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext13O__F1F2_cond2 (z : RF_ParametersMRDC__ext13O__Type)
 : RF_ParametersMRDC__ext13O__F2 (RF_ParametersMRDC__ext13O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RF_ParametersMRDC__ext13O__F2F1_cond (y : seq_type RF_ParametersMRDC__ext13O__list)
  : seq_cond RF_ParametersMRDC__ext13O__list y ->
 (RF_ParametersMRDC__ext13O__cond (RF_ParametersMRDC__ext13O__F2 y)) /\  RF_ParametersMRDC__ext13O__F1 (RF_ParametersMRDC__ext13O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RF_ParametersMRDC__ext13O__cond. simpl in *. auto.
 - simpl. unfold RF_ParametersMRDC__ext13O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RF_ParametersMRDC__ext13O__Format : T_Format RF_ParametersMRDC__ext13O__Type RF_ParametersMRDC__ext13O__cond :=
        proj2_format  RF_ParametersMRDC__ext13O__cond RF_ParametersMRDC__ext13O__list__Format
    RF_ParametersMRDC__ext13O__F1 RF_ParametersMRDC__ext13O__F2 RF_ParametersMRDC__ext13O__F1F2_cond  RF_ParametersMRDC__ext13O__F1F2_cond2 RF_ParametersMRDC__ext13O__F2F1_cond.
Opaque RF_ParametersMRDC__ext13O__cond RF_ParametersMRDC__ext13O__Format.

Definition RF_ParametersMRDC__ext13__check_all_none (b : RF_ParametersMRDC__ext13O__Type) : bool :=
match b with 
  | make__RF_ParametersMRDC__ext13O__Type None None None  => false 
  | _ => true 
 end.
Definition RF_ParametersMRDC__ext13__Format : T_Format RF_ParametersMRDC__ext13__Type RF_ParametersMRDC__ext13__cond :=
  restrict_add_format RF_ParametersMRDC__ext13__check_all_none RF_ParametersMRDC__ext13O__Format.

Opaque RF_ParametersMRDC__ext13__cond RF_ParametersMRDC__ext13__Format.


Definition RF_ParametersMRDC__root_Format_Type := Eval cbn in seq_format_prod RF_ParametersMRDC__root_list.
Definition RF_ParametersMRDC__root_Format_list : RF_ParametersMRDC__root_Format_Type :=
  (BandCombinationList__Format, (FreqBandList__Format, unit_format)).

Definition RF_ParametersMRDC__ext_Format_Type := Eval cbn in get_formats RF_ParametersMRDC__ext_list.
Definition RF_ParametersMRDC__ext_Format_list : RF_ParametersMRDC__ext_Format_Type :=
  (RF_ParametersMRDC__ext0__Format, (RF_ParametersMRDC__ext1__Format, (RF_ParametersMRDC__ext2__Format, (RF_ParametersMRDC__ext3__Format, (RF_ParametersMRDC__ext4__Format, (RF_ParametersMRDC__ext5__Format, (RF_ParametersMRDC__ext6__Format, (RF_ParametersMRDC__ext7__Format, (RF_ParametersMRDC__ext8__Format, (RF_ParametersMRDC__ext9__Format, (RF_ParametersMRDC__ext10__Format, (RF_ParametersMRDC__ext11__Format, (RF_ParametersMRDC__ext12__Format, (RF_ParametersMRDC__ext13__Format, unit__Format)))))))))))))).

Definition RF_ParametersMRDC__list_type : Set := (seq_type RF_ParametersMRDC__root_list) * (seq_ext_type RF_ParametersMRDC__ext_list).
Definition RF_ParametersMRDC__list_cond (z : RF_ParametersMRDC__list_type) : Prop :=
        (seq_cond RF_ParametersMRDC__root_list (fst z)) /\ (seq_ext_cond RF_ParametersMRDC__ext_list (snd z)).
Definition RF_ParametersMRDC__list_format : T_Format RF_ParametersMRDC__list_type RF_ParametersMRDC__list_cond :=
 (* Eval compute in *) seq_ext_format RF_ParametersMRDC__root_list RF_ParametersMRDC__root_Format_list RF_ParametersMRDC__ext_list RF_ParametersMRDC__ext_Format_list.

Opaque RF_ParametersMRDC__list_format.
Definition RF_ParametersMRDC__F1 (z : RF_ParametersMRDC__Type) : RF_ParametersMRDC__list_type :=
  (((RF_ParametersMRDC__supportedBandCombinationList z, (RF_ParametersMRDC__appliedFreqBandListFilter z, tt))), (
(RF_ParametersMRDC__ext0 z, (RF_ParametersMRDC__ext1 z, (RF_ParametersMRDC__ext2 z, (RF_ParametersMRDC__ext3 z, (RF_ParametersMRDC__ext4 z, (RF_ParametersMRDC__ext5 z, (RF_ParametersMRDC__ext6 z, (RF_ParametersMRDC__ext7 z, (RF_ParametersMRDC__ext8 z, (RF_ParametersMRDC__ext9 z, (RF_ParametersMRDC__ext10 z, (RF_ParametersMRDC__ext11 z, (RF_ParametersMRDC__ext12 z, (RF_ParametersMRDC__ext13 z, tt)))))))))))))))).
Definition RF_ParametersMRDC__F2 (y : RF_ParametersMRDC__list_type) : RF_ParametersMRDC__Type :=
  match y with
  | ((j0, (j1, _)), (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, _)))))))))))))))=>
    make__RF_ParametersMRDC__Type j0 j1 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  end.
Definition RF_ParametersMRDC__helper1 : (forall a : RF_ParametersMRDC__Type, RF_ParametersMRDC__cond a -> RF_ParametersMRDC__list_cond (RF_ParametersMRDC__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RF_ParametersMRDC__helper2 : (forall a : RF_ParametersMRDC__Type, RF_ParametersMRDC__F2 (RF_ParametersMRDC__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RF_ParametersMRDC__helper3 : (forall b : RF_ParametersMRDC__list_type, RF_ParametersMRDC__list_cond b -> RF_ParametersMRDC__cond (RF_ParametersMRDC__F2 b) /\ RF_ParametersMRDC__F1 (RF_ParametersMRDC__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RF_ParametersMRDC__cond, RF_ParametersMRDC__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RF_ParametersMRDC__Format : T_Format RF_ParametersMRDC__Type RF_ParametersMRDC__cond :=
 proj2_format RF_ParametersMRDC__cond RF_ParametersMRDC__list_format  RF_ParametersMRDC__F1 RF_ParametersMRDC__F2 RF_ParametersMRDC__helper1 RF_ParametersMRDC__helper2 RF_ParametersMRDC__helper3.

Opaque RF_ParametersMRDC__cond RF_ParametersMRDC__Format.

