Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__root__eventA1__Type : Set :=
  make__EventTriggerConfig__eventId__root__eventA1__Type {
    EventTriggerConfig__eventId__root__eventA1__a1_Threshold : MeasTriggerQuantity__Type ;
    EventTriggerConfig__eventId__root__eventA1__reportOnLeave : bool ;
    EventTriggerConfig__eventId__root__eventA1__hysteresis : Hysteresis__Type ;
    EventTriggerConfig__eventId__root__eventA1__timeToTrigger : TimeToTrigger__Type ;
}.
Definition EventTriggerConfig__eventId__root__eventA1__list := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfig__eventId__root__eventA1__cond z := 
  MeasTriggerQuantity__cond (EventTriggerConfig__eventId__root__eventA1__a1_Threshold z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA1__reportOnLeave z) /\
  Hysteresis__cond (EventTriggerConfig__eventId__root__eventA1__hysteresis z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__root__eventA1__timeToTrigger z) /\
  True.

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__root__eventA2__Type : Set :=
  make__EventTriggerConfig__eventId__root__eventA2__Type {
    EventTriggerConfig__eventId__root__eventA2__a2_Threshold : MeasTriggerQuantity__Type ;
    EventTriggerConfig__eventId__root__eventA2__reportOnLeave : bool ;
    EventTriggerConfig__eventId__root__eventA2__hysteresis : Hysteresis__Type ;
    EventTriggerConfig__eventId__root__eventA2__timeToTrigger : TimeToTrigger__Type ;
}.
Definition EventTriggerConfig__eventId__root__eventA2__list := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfig__eventId__root__eventA2__cond z := 
  MeasTriggerQuantity__cond (EventTriggerConfig__eventId__root__eventA2__a2_Threshold z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA2__reportOnLeave z) /\
  Hysteresis__cond (EventTriggerConfig__eventId__root__eventA2__hysteresis z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__root__eventA2__timeToTrigger z) /\
  True.

Require Import NR.MeasTriggerQuantityOffset.

Opaque MeasTriggerQuantityOffset__cond MeasTriggerQuantityOffset__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__root__eventA3__Type : Set :=
  make__EventTriggerConfig__eventId__root__eventA3__Type {
    EventTriggerConfig__eventId__root__eventA3__a3_Offset : MeasTriggerQuantityOffset__Type ;
    EventTriggerConfig__eventId__root__eventA3__reportOnLeave : bool ;
    EventTriggerConfig__eventId__root__eventA3__hysteresis : Hysteresis__Type ;
    EventTriggerConfig__eventId__root__eventA3__timeToTrigger : TimeToTrigger__Type ;
    EventTriggerConfig__eventId__root__eventA3__useAllowedCellList : bool ;
}.
Definition EventTriggerConfig__eventId__root__eventA3__list := (
 Nor MeasTriggerQuantityOffset__Type MeasTriggerQuantityOffset__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition EventTriggerConfig__eventId__root__eventA3__cond z := 
  MeasTriggerQuantityOffset__cond (EventTriggerConfig__eventId__root__eventA3__a3_Offset z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA3__reportOnLeave z) /\
  Hysteresis__cond (EventTriggerConfig__eventId__root__eventA3__hysteresis z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__root__eventA3__timeToTrigger z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA3__useAllowedCellList z) /\
  True.

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__root__eventA4__Type : Set :=
  make__EventTriggerConfig__eventId__root__eventA4__Type {
    EventTriggerConfig__eventId__root__eventA4__a4_Threshold : MeasTriggerQuantity__Type ;
    EventTriggerConfig__eventId__root__eventA4__reportOnLeave : bool ;
    EventTriggerConfig__eventId__root__eventA4__hysteresis : Hysteresis__Type ;
    EventTriggerConfig__eventId__root__eventA4__timeToTrigger : TimeToTrigger__Type ;
    EventTriggerConfig__eventId__root__eventA4__useAllowedCellList : bool ;
}.
Definition EventTriggerConfig__eventId__root__eventA4__list := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition EventTriggerConfig__eventId__root__eventA4__cond z := 
  MeasTriggerQuantity__cond (EventTriggerConfig__eventId__root__eventA4__a4_Threshold z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA4__reportOnLeave z) /\
  Hysteresis__cond (EventTriggerConfig__eventId__root__eventA4__hysteresis z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__root__eventA4__timeToTrigger z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA4__useAllowedCellList z) /\
  True.

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__root__eventA5__Type : Set :=
  make__EventTriggerConfig__eventId__root__eventA5__Type {
    EventTriggerConfig__eventId__root__eventA5__a5_Threshold1 : MeasTriggerQuantity__Type ;
    EventTriggerConfig__eventId__root__eventA5__a5_Threshold2 : MeasTriggerQuantity__Type ;
    EventTriggerConfig__eventId__root__eventA5__reportOnLeave : bool ;
    EventTriggerConfig__eventId__root__eventA5__hysteresis : Hysteresis__Type ;
    EventTriggerConfig__eventId__root__eventA5__timeToTrigger : TimeToTrigger__Type ;
    EventTriggerConfig__eventId__root__eventA5__useAllowedCellList : bool ;
}.
Definition EventTriggerConfig__eventId__root__eventA5__list := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition EventTriggerConfig__eventId__root__eventA5__cond z := 
  MeasTriggerQuantity__cond (EventTriggerConfig__eventId__root__eventA5__a5_Threshold1 z) /\
  MeasTriggerQuantity__cond (EventTriggerConfig__eventId__root__eventA5__a5_Threshold2 z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA5__reportOnLeave z) /\
  Hysteresis__cond (EventTriggerConfig__eventId__root__eventA5__hysteresis z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__root__eventA5__timeToTrigger z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA5__useAllowedCellList z) /\
  True.

Require Import NR.MeasTriggerQuantityOffset.

Opaque MeasTriggerQuantityOffset__cond MeasTriggerQuantityOffset__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__root__eventA6__Type : Set :=
  make__EventTriggerConfig__eventId__root__eventA6__Type {
    EventTriggerConfig__eventId__root__eventA6__a6_Offset : MeasTriggerQuantityOffset__Type ;
    EventTriggerConfig__eventId__root__eventA6__reportOnLeave : bool ;
    EventTriggerConfig__eventId__root__eventA6__hysteresis : Hysteresis__Type ;
    EventTriggerConfig__eventId__root__eventA6__timeToTrigger : TimeToTrigger__Type ;
    EventTriggerConfig__eventId__root__eventA6__useAllowedCellList : bool ;
}.
Definition EventTriggerConfig__eventId__root__eventA6__list := (
 Nor MeasTriggerQuantityOffset__Type MeasTriggerQuantityOffset__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition EventTriggerConfig__eventId__root__eventA6__cond z := 
  MeasTriggerQuantityOffset__cond (EventTriggerConfig__eventId__root__eventA6__a6_Offset z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA6__reportOnLeave z) /\
  Hysteresis__cond (EventTriggerConfig__eventId__root__eventA6__hysteresis z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__root__eventA6__timeToTrigger z) /\
  (fun _ => True) (EventTriggerConfig__eventId__root__eventA6__useAllowedCellList z) /\
  True.


Inductive EventTriggerConfig__eventId__root__Type : Set :=
  | EventTriggerConfig__eventId__root__eventA1 : EventTriggerConfig__eventId__root__eventA1__Type -> EventTriggerConfig__eventId__root__Type
  | EventTriggerConfig__eventId__root__eventA2 : EventTriggerConfig__eventId__root__eventA2__Type -> EventTriggerConfig__eventId__root__Type
  | EventTriggerConfig__eventId__root__eventA3 : EventTriggerConfig__eventId__root__eventA3__Type -> EventTriggerConfig__eventId__root__Type
  | EventTriggerConfig__eventId__root__eventA4 : EventTriggerConfig__eventId__root__eventA4__Type -> EventTriggerConfig__eventId__root__Type
  | EventTriggerConfig__eventId__root__eventA5 : EventTriggerConfig__eventId__root__eventA5__Type -> EventTriggerConfig__eventId__root__Type
  | EventTriggerConfig__eventId__root__eventA6 : EventTriggerConfig__eventId__root__eventA6__Type -> EventTriggerConfig__eventId__root__Type
.
Definition EventTriggerConfig__eventId__root__list : list typ := (
typ_cons EventTriggerConfig__eventId__root__eventA1__Type EventTriggerConfig__eventId__root__eventA1__cond ::
typ_cons EventTriggerConfig__eventId__root__eventA2__Type EventTriggerConfig__eventId__root__eventA2__cond ::
typ_cons EventTriggerConfig__eventId__root__eventA3__Type EventTriggerConfig__eventId__root__eventA3__cond ::
typ_cons EventTriggerConfig__eventId__root__eventA4__Type EventTriggerConfig__eventId__root__eventA4__cond ::
typ_cons EventTriggerConfig__eventId__root__eventA5__Type EventTriggerConfig__eventId__root__eventA5__cond ::
typ_cons EventTriggerConfig__eventId__root__eventA6__Type EventTriggerConfig__eventId__root__eventA6__cond ::
 nil).
Definition EventTriggerConfig__eventId__root__cond (c : EventTriggerConfig__eventId__root__Type) := 
  match c with
  | EventTriggerConfig__eventId__root__eventA1 t => EventTriggerConfig__eventId__root__eventA1__cond t 
  | EventTriggerConfig__eventId__root__eventA2 t => EventTriggerConfig__eventId__root__eventA2__cond t 
  | EventTriggerConfig__eventId__root__eventA3 t => EventTriggerConfig__eventId__root__eventA3__cond t 
  | EventTriggerConfig__eventId__root__eventA4 t => EventTriggerConfig__eventId__root__eventA4__cond t 
  | EventTriggerConfig__eventId__root__eventA5 t => EventTriggerConfig__eventId__root__eventA5__cond t 
  | EventTriggerConfig__eventId__root__eventA6 t => EventTriggerConfig__eventId__root__eventA6__cond t 
  end.

Lemma EventTriggerConfig__eventId__root__len_helper1 : to_bit_sz (length EventTriggerConfig__eventId__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma EventTriggerConfig__eventId__root__len_helper2 : 2 <= length2 EventTriggerConfig__eventId__root__list.
 simpl. lia. Qed.
Require Import NR.SL_MeasTriggerQuantity_r16.

Opaque SL_MeasTriggerQuantity_r16__cond SL_MeasTriggerQuantity_r16__Format.

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__ext__eventX1_r17__Type : Set :=
  make__EventTriggerConfig__eventId__ext__eventX1_r17__Type {
    EventTriggerConfig__eventId__ext__eventX1_r17__x1_Threshold1_Relay_r17 : SL_MeasTriggerQuantity_r16__Type ;
    EventTriggerConfig__eventId__ext__eventX1_r17__x1_Threshold2_r17 : MeasTriggerQuantity__Type ;
    EventTriggerConfig__eventId__ext__eventX1_r17__reportOnLeave_r17 : bool ;
    EventTriggerConfig__eventId__ext__eventX1_r17__hysteresis_r17 : Hysteresis__Type ;
    EventTriggerConfig__eventId__ext__eventX1_r17__timeToTrigger_r17 : TimeToTrigger__Type ;
    EventTriggerConfig__eventId__ext__eventX1_r17__useAllowedCellList_r17 : bool ;
}.
Definition EventTriggerConfig__eventId__ext__eventX1_r17__list := (
 Nor SL_MeasTriggerQuantity_r16__Type SL_MeasTriggerQuantity_r16__cond ::
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 Nor bool (fun _ => True) ::
 nil).
Definition EventTriggerConfig__eventId__ext__eventX1_r17__cond z := 
  SL_MeasTriggerQuantity_r16__cond (EventTriggerConfig__eventId__ext__eventX1_r17__x1_Threshold1_Relay_r17 z) /\
  MeasTriggerQuantity__cond (EventTriggerConfig__eventId__ext__eventX1_r17__x1_Threshold2_r17 z) /\
  (fun _ => True) (EventTriggerConfig__eventId__ext__eventX1_r17__reportOnLeave_r17 z) /\
  Hysteresis__cond (EventTriggerConfig__eventId__ext__eventX1_r17__hysteresis_r17 z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__ext__eventX1_r17__timeToTrigger_r17 z) /\
  (fun _ => True) (EventTriggerConfig__eventId__ext__eventX1_r17__useAllowedCellList_r17 z) /\
  True.

Require Import NR.SL_MeasTriggerQuantity_r16.

Opaque SL_MeasTriggerQuantity_r16__cond SL_MeasTriggerQuantity_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__ext__eventX2_r17__Type : Set :=
  make__EventTriggerConfig__eventId__ext__eventX2_r17__Type {
    EventTriggerConfig__eventId__ext__eventX2_r17__x2_Threshold_Relay_r17 : SL_MeasTriggerQuantity_r16__Type ;
    EventTriggerConfig__eventId__ext__eventX2_r17__reportOnLeave_r17 : bool ;
    EventTriggerConfig__eventId__ext__eventX2_r17__hysteresis_r17 : Hysteresis__Type ;
    EventTriggerConfig__eventId__ext__eventX2_r17__timeToTrigger_r17 : TimeToTrigger__Type ;
}.
Definition EventTriggerConfig__eventId__ext__eventX2_r17__list := (
 Nor SL_MeasTriggerQuantity_r16__Type SL_MeasTriggerQuantity_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfig__eventId__ext__eventX2_r17__cond z := 
  SL_MeasTriggerQuantity_r16__cond (EventTriggerConfig__eventId__ext__eventX2_r17__x2_Threshold_Relay_r17 z) /\
  (fun _ => True) (EventTriggerConfig__eventId__ext__eventX2_r17__reportOnLeave_r17 z) /\
  Hysteresis__cond (EventTriggerConfig__eventId__ext__eventX2_r17__hysteresis_r17 z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__ext__eventX2_r17__timeToTrigger_r17 z) /\
  True.

Lemma EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__helper1 : (1 <= 65525)%Z.  lia. Qed.
Lemma EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__helper2 : to_bit_sz (Z.to_nat (65525 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65525 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__Type := Z.
Definition EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__cond := (fun z => (1 <= z <= 65525)%Z).
Lemma EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__helper1 : (1 <= 65525)%Z.  lia. Qed.
Lemma EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__helper2 : to_bit_sz (Z.to_nat (65525 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65525 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__Type := Z.
Definition EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__cond := (fun z => (1 <= z <= 65525)%Z).
Require Import NR.ReferenceLocation_r17.

Opaque ReferenceLocation_r17__cond ReferenceLocation_r17__Format.

Require Import NR.ReferenceLocation_r17.

Opaque ReferenceLocation_r17__cond ReferenceLocation_r17__Format.

Require Import NR.HysteresisLocation_r17.

Opaque HysteresisLocation_r17__cond HysteresisLocation_r17__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfig__eventId__ext__eventD1_r17__Type : Set :=
  make__EventTriggerConfig__eventId__ext__eventD1_r17__Type {
    EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17 : Z ;
    EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17 : Z ;
    EventTriggerConfig__eventId__ext__eventD1_r17__referenceLocation1_r17 : ReferenceLocation_r17__Type ;
    EventTriggerConfig__eventId__ext__eventD1_r17__referenceLocation2_r17 : ReferenceLocation_r17__Type ;
    EventTriggerConfig__eventId__ext__eventD1_r17__reportOnLeave_r17 : bool ;
    EventTriggerConfig__eventId__ext__eventD1_r17__hysteresisLocation_r17 : HysteresisLocation_r17__Type ;
    EventTriggerConfig__eventId__ext__eventD1_r17__timeToTrigger_r17 : TimeToTrigger__Type ;
}.
Definition EventTriggerConfig__eventId__ext__eventD1_r17__list := (
 Nor Z EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__cond ::
 Nor Z EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__cond ::
 Nor ReferenceLocation_r17__Type ReferenceLocation_r17__cond ::
 Nor ReferenceLocation_r17__Type ReferenceLocation_r17__cond ::
 Nor bool (fun _ => True) ::
 Nor HysteresisLocation_r17__Type HysteresisLocation_r17__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfig__eventId__ext__eventD1_r17__cond z := 
  EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__cond (EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17 z) /\
  EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__cond (EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17 z) /\
  ReferenceLocation_r17__cond (EventTriggerConfig__eventId__ext__eventD1_r17__referenceLocation1_r17 z) /\
  ReferenceLocation_r17__cond (EventTriggerConfig__eventId__ext__eventD1_r17__referenceLocation2_r17 z) /\
  (fun _ => True) (EventTriggerConfig__eventId__ext__eventD1_r17__reportOnLeave_r17 z) /\
  HysteresisLocation_r17__cond (EventTriggerConfig__eventId__ext__eventD1_r17__hysteresisLocation_r17 z) /\
  TimeToTrigger__cond (EventTriggerConfig__eventId__ext__eventD1_r17__timeToTrigger_r17 z) /\
  True.


Inductive EventTriggerConfig__eventId__ext__Type : Set :=
  | EventTriggerConfig__eventId__ext__eventX1_r17 : EventTriggerConfig__eventId__ext__eventX1_r17__Type -> EventTriggerConfig__eventId__ext__Type
  | EventTriggerConfig__eventId__ext__eventX2_r17 : EventTriggerConfig__eventId__ext__eventX2_r17__Type -> EventTriggerConfig__eventId__ext__Type
  | EventTriggerConfig__eventId__ext__eventD1_r17 : EventTriggerConfig__eventId__ext__eventD1_r17__Type -> EventTriggerConfig__eventId__ext__Type
.
Definition EventTriggerConfig__eventId__ext__list : list typ := (
typ_cons EventTriggerConfig__eventId__ext__eventX1_r17__Type EventTriggerConfig__eventId__ext__eventX1_r17__cond ::
typ_cons EventTriggerConfig__eventId__ext__eventX2_r17__Type EventTriggerConfig__eventId__ext__eventX2_r17__cond ::
typ_cons EventTriggerConfig__eventId__ext__eventD1_r17__Type EventTriggerConfig__eventId__ext__eventD1_r17__cond ::
 nil).
Definition EventTriggerConfig__eventId__ext__cond (c : EventTriggerConfig__eventId__ext__Type) := 
  match c with
  | EventTriggerConfig__eventId__ext__eventX1_r17 t => EventTriggerConfig__eventId__ext__eventX1_r17__cond t 
  | EventTriggerConfig__eventId__ext__eventX2_r17 t => EventTriggerConfig__eventId__ext__eventX2_r17__cond t 
  | EventTriggerConfig__eventId__ext__eventD1_r17 t => EventTriggerConfig__eventId__ext__eventD1_r17__cond t 
  end.

Lemma EventTriggerConfig__eventId__ext__len_helper1 : to_bit_sz (length EventTriggerConfig__eventId__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition EventTriggerConfig__eventId__Type : Set := EventTriggerConfig__eventId__root__Type + EventTriggerConfig__eventId__ext__Type.
Definition EventTriggerConfig__eventId__cond :=
  sum_cond EventTriggerConfig__eventId__root__cond EventTriggerConfig__eventId__ext__cond.
Require Import NR.NR_RS_Type.

Opaque NR_RS_Type__cond NR_RS_Type__Format.

Require Import NR.ReportInterval.

Opaque ReportInterval__cond ReportInterval__Format.

Inductive EventTriggerConfig__reportAmount__Type : Set :=
 | EventTriggerConfig__reportAmount__r1
 | EventTriggerConfig__reportAmount__r2
 | EventTriggerConfig__reportAmount__r4
 | EventTriggerConfig__reportAmount__r8
 | EventTriggerConfig__reportAmount__r16
 | EventTriggerConfig__reportAmount__r32
 | EventTriggerConfig__reportAmount__r64
 | EventTriggerConfig__reportAmount__infinity
.
Definition EventTriggerConfig__reportAmount__cond := (fun (_ : EventTriggerConfig__reportAmount__Type) => True).
Lemma EventTriggerConfig__reportAmount__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EventTriggerConfig__reportAmount__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 EventTriggerConfig__reportAmount__nat__helper.

Definition EventTriggerConfig__reportAmount__F1 t :=
  match t with
  | EventTriggerConfig__reportAmount__r1 => 0
  | EventTriggerConfig__reportAmount__r2 => 1
  | EventTriggerConfig__reportAmount__r4 => 2
  | EventTriggerConfig__reportAmount__r8 => 3
  | EventTriggerConfig__reportAmount__r16 => 4
  | EventTriggerConfig__reportAmount__r32 => 5
  | EventTriggerConfig__reportAmount__r64 => 6
  | EventTriggerConfig__reportAmount__infinity => 7
  end.
Definition EventTriggerConfig__reportAmount__F2 n :=
  match n with
  | 0 => EventTriggerConfig__reportAmount__r1
  | 1 => EventTriggerConfig__reportAmount__r2
  | 2 => EventTriggerConfig__reportAmount__r4
  | 3 => EventTriggerConfig__reportAmount__r8
  | 4 => EventTriggerConfig__reportAmount__r16
  | 5 => EventTriggerConfig__reportAmount__r32
  | 6 => EventTriggerConfig__reportAmount__r64
  | 7 => EventTriggerConfig__reportAmount__infinity
  | _ => EventTriggerConfig__reportAmount__r1
  end.
Lemma EventTriggerConfig__reportAmount__F1F2 : forall x : EventTriggerConfig__reportAmount__Type, (EventTriggerConfig__reportAmount__F1 x <= 7) /\ EventTriggerConfig__reportAmount__F2 (EventTriggerConfig__reportAmount__F1 x) = x. imp_solve. Qed.
Lemma EventTriggerConfig__reportAmount__F2F1 : forall (y : nat) (H : y <= 7), EventTriggerConfig__reportAmount__F1 (EventTriggerConfig__reportAmount__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasReportQuantity.

Opaque MeasReportQuantity__cond MeasReportQuantity__Format.

Lemma EventTriggerConfig__maxReportCells__helper1 : (1 <= maxCellReport)%Z. unfold maxCellReport.
 lia. Qed.
Lemma EventTriggerConfig__maxReportCells__helper2 : to_bit_sz (Z.to_nat (maxCellReport - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellReport - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EventTriggerConfig__maxReportCells__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EventTriggerConfig__maxReportCells__Type := Z.
Definition EventTriggerConfig__maxReportCells__cond := (fun z => (1 <= z <= maxCellReport)%Z).
Require Import NR.MeasReportQuantity.

Opaque MeasReportQuantity__cond MeasReportQuantity__Format.

Lemma EventTriggerConfig__maxNrofRS_IndexesToReport__helper1 : (1 <= maxNrofIndexesToReport)%Z. unfold maxNrofIndexesToReport.
 lia. Qed.
Lemma EventTriggerConfig__maxNrofRS_IndexesToReport__helper2 : to_bit_sz (Z.to_nat (maxNrofIndexesToReport - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofIndexesToReport - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EventTriggerConfig__maxNrofRS_IndexesToReport__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EventTriggerConfig__maxNrofRS_IndexesToReport__Type := Z.
Definition EventTriggerConfig__maxNrofRS_IndexesToReport__cond := (fun z => (1 <= z <= maxNrofIndexesToReport)%Z).
Inductive EventTriggerConfig__reportAddNeighMeas__Type : Set :=
 | EventTriggerConfig__reportAddNeighMeas__setup
.
Definition EventTriggerConfig__reportAddNeighMeas__cond := (fun (_ : EventTriggerConfig__reportAddNeighMeas__Type) => True).
Lemma EventTriggerConfig__reportAddNeighMeas__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EventTriggerConfig__reportAddNeighMeas__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EventTriggerConfig__reportAddNeighMeas__nat__helper.

Definition EventTriggerConfig__reportAddNeighMeas__F1 t :=
  match t with
  | EventTriggerConfig__reportAddNeighMeas__setup => 0
  end.
Definition EventTriggerConfig__reportAddNeighMeas__F2 n :=
  match n with
  | 0 => EventTriggerConfig__reportAddNeighMeas__setup
  | _ => EventTriggerConfig__reportAddNeighMeas__setup
  end.
Lemma EventTriggerConfig__reportAddNeighMeas__F1F2 : forall x : EventTriggerConfig__reportAddNeighMeas__Type, (EventTriggerConfig__reportAddNeighMeas__F1 x <= 0) /\ EventTriggerConfig__reportAddNeighMeas__F2 (EventTriggerConfig__reportAddNeighMeas__F1 x) = x. imp_solve. Qed.
Lemma EventTriggerConfig__reportAddNeighMeas__F2F1 : forall (y : nat) (H : y <= 0), EventTriggerConfig__reportAddNeighMeas__F1 (EventTriggerConfig__reportAddNeighMeas__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasRSSI_ReportConfig_r16.

Opaque MeasRSSI_ReportConfig_r16__cond MeasRSSI_ReportConfig_r16__Format.

Inductive EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Type : Set :=
 | EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__true
.
Definition EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__cond := (fun (_ : EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Type) => True).
Lemma EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__nat__helper.

Definition EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F1 t :=
  match t with
  | EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__true => 0
  end.
Definition EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F2 n :=
  match n with
  | 0 => EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__true
  | _ => EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__true
  end.
Lemma EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F1F2 : forall x : EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Type, (EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F1 x <= 0) /\ EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F2 (EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F1 x) = x. imp_solve. Qed.
Lemma EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F2F1 : forall (y : nat) (H : y <= 0), EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F1 (EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.BT_NameList_r16.
Definition EventTriggerConfig__ext0O__includeBT_Meas_r16__Type := SetupRelease__Type BT_NameList_r16__Type.
Definition EventTriggerConfig__ext0O__includeBT_Meas_r16__cond := SetupRelease__cond _ BT_NameList_r16__cond.
Definition EventTriggerConfig__ext0O__includeBT_Meas_r16__Format : T_Format EventTriggerConfig__ext0O__includeBT_Meas_r16__Type EventTriggerConfig__ext0O__includeBT_Meas_r16__cond := SetupRelease__Format _ _ BT_NameList_r16__Format.
Opaque EventTriggerConfig__ext0O__includeBT_Meas_r16__cond EventTriggerConfig__ext0O__includeBT_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.WLAN_NameList_r16.
Definition EventTriggerConfig__ext0O__includeWLAN_Meas_r16__Type := SetupRelease__Type WLAN_NameList_r16__Type.
Definition EventTriggerConfig__ext0O__includeWLAN_Meas_r16__cond := SetupRelease__cond _ WLAN_NameList_r16__cond.
Definition EventTriggerConfig__ext0O__includeWLAN_Meas_r16__Format : T_Format EventTriggerConfig__ext0O__includeWLAN_Meas_r16__Type EventTriggerConfig__ext0O__includeWLAN_Meas_r16__cond := SetupRelease__Format _ _ WLAN_NameList_r16__Format.
Opaque EventTriggerConfig__ext0O__includeWLAN_Meas_r16__cond EventTriggerConfig__ext0O__includeWLAN_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.Sensor_NameList_r16.
Definition EventTriggerConfig__ext0O__includeSensor_Meas_r16__Type := SetupRelease__Type Sensor_NameList_r16__Type.
Definition EventTriggerConfig__ext0O__includeSensor_Meas_r16__cond := SetupRelease__cond _ Sensor_NameList_r16__cond.
Definition EventTriggerConfig__ext0O__includeSensor_Meas_r16__Format : T_Format EventTriggerConfig__ext0O__includeSensor_Meas_r16__Type EventTriggerConfig__ext0O__includeSensor_Meas_r16__cond := SetupRelease__Format _ _ Sensor_NameList_r16__Format.
Opaque EventTriggerConfig__ext0O__includeSensor_Meas_r16__cond EventTriggerConfig__ext0O__includeSensor_Meas_r16__Format.

Record EventTriggerConfig__ext0O__Type : Set :=
  make__EventTriggerConfig__ext0O__Type {
    EventTriggerConfig__ext0O__measRSSI_ReportConfig_r16 : option MeasRSSI_ReportConfig_r16__Type ;
    EventTriggerConfig__ext0O__useT312_r16 : option bool ;
    EventTriggerConfig__ext0O__includeCommonLocationInfo_r16 : option EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Type ;
    EventTriggerConfig__ext0O__includeBT_Meas_r16 : option EventTriggerConfig__ext0O__includeBT_Meas_r16__Type ;
    EventTriggerConfig__ext0O__includeWLAN_Meas_r16 : option EventTriggerConfig__ext0O__includeWLAN_Meas_r16__Type ;
    EventTriggerConfig__ext0O__includeSensor_Meas_r16 : option EventTriggerConfig__ext0O__includeSensor_Meas_r16__Type ;
}.
Definition EventTriggerConfig__ext0O__list := (
 Opt MeasRSSI_ReportConfig_r16__Type MeasRSSI_ReportConfig_r16__cond ::
 Opt bool (fun _ => True) ::
 Opt EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Type EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__cond ::
 Opt EventTriggerConfig__ext0O__includeBT_Meas_r16__Type EventTriggerConfig__ext0O__includeBT_Meas_r16__cond ::
 Opt EventTriggerConfig__ext0O__includeWLAN_Meas_r16__Type EventTriggerConfig__ext0O__includeWLAN_Meas_r16__cond ::
 Opt EventTriggerConfig__ext0O__includeSensor_Meas_r16__Type EventTriggerConfig__ext0O__includeSensor_Meas_r16__cond ::
 nil).
Definition EventTriggerConfig__ext0O__cond z := 
  opt_cond MeasRSSI_ReportConfig_r16__cond (EventTriggerConfig__ext0O__measRSSI_ReportConfig_r16 z) /\
  opt_cond (fun _ => True) (EventTriggerConfig__ext0O__useT312_r16 z) /\
  opt_cond EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__cond (EventTriggerConfig__ext0O__includeCommonLocationInfo_r16 z) /\
  opt_cond EventTriggerConfig__ext0O__includeBT_Meas_r16__cond (EventTriggerConfig__ext0O__includeBT_Meas_r16 z) /\
  opt_cond EventTriggerConfig__ext0O__includeWLAN_Meas_r16__cond (EventTriggerConfig__ext0O__includeWLAN_Meas_r16 z) /\
  opt_cond EventTriggerConfig__ext0O__includeSensor_Meas_r16__cond (EventTriggerConfig__ext0O__includeSensor_Meas_r16 z) /\
  True.

Definition EventTriggerConfig__ext0__Type := EventTriggerConfig__ext0O__Type.
Definition EventTriggerConfig__ext0__cond := EventTriggerConfig__ext0O__cond.

Inductive EventTriggerConfig__ext1O__coarseLocationRequest_r17__Type : Set :=
 | EventTriggerConfig__ext1O__coarseLocationRequest_r17__true
.
Definition EventTriggerConfig__ext1O__coarseLocationRequest_r17__cond := (fun (_ : EventTriggerConfig__ext1O__coarseLocationRequest_r17__Type) => True).
Lemma EventTriggerConfig__ext1O__coarseLocationRequest_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EventTriggerConfig__ext1O__coarseLocationRequest_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EventTriggerConfig__ext1O__coarseLocationRequest_r17__nat__helper.

Definition EventTriggerConfig__ext1O__coarseLocationRequest_r17__F1 t :=
  match t with
  | EventTriggerConfig__ext1O__coarseLocationRequest_r17__true => 0
  end.
Definition EventTriggerConfig__ext1O__coarseLocationRequest_r17__F2 n :=
  match n with
  | 0 => EventTriggerConfig__ext1O__coarseLocationRequest_r17__true
  | _ => EventTriggerConfig__ext1O__coarseLocationRequest_r17__true
  end.
Lemma EventTriggerConfig__ext1O__coarseLocationRequest_r17__F1F2 : forall x : EventTriggerConfig__ext1O__coarseLocationRequest_r17__Type, (EventTriggerConfig__ext1O__coarseLocationRequest_r17__F1 x <= 0) /\ EventTriggerConfig__ext1O__coarseLocationRequest_r17__F2 (EventTriggerConfig__ext1O__coarseLocationRequest_r17__F1 x) = x. imp_solve. Qed.
Lemma EventTriggerConfig__ext1O__coarseLocationRequest_r17__F2F1 : forall (y : nat) (H : y <= 0), EventTriggerConfig__ext1O__coarseLocationRequest_r17__F1 (EventTriggerConfig__ext1O__coarseLocationRequest_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_MeasReportQuantity_r16.

Opaque SL_MeasReportQuantity_r16__cond SL_MeasReportQuantity_r16__Format.

Record EventTriggerConfig__ext1O__Type : Set :=
  make__EventTriggerConfig__ext1O__Type {
    EventTriggerConfig__ext1O__coarseLocationRequest_r17 : option EventTriggerConfig__ext1O__coarseLocationRequest_r17__Type ;
    EventTriggerConfig__ext1O__reportQuantityRelay_r17 : option SL_MeasReportQuantity_r16__Type ;
}.
Definition EventTriggerConfig__ext1O__list := (
 Opt EventTriggerConfig__ext1O__coarseLocationRequest_r17__Type EventTriggerConfig__ext1O__coarseLocationRequest_r17__cond ::
 Opt SL_MeasReportQuantity_r16__Type SL_MeasReportQuantity_r16__cond ::
 nil).
Definition EventTriggerConfig__ext1O__cond z := 
  opt_cond EventTriggerConfig__ext1O__coarseLocationRequest_r17__cond (EventTriggerConfig__ext1O__coarseLocationRequest_r17 z) /\
  opt_cond SL_MeasReportQuantity_r16__cond (EventTriggerConfig__ext1O__reportQuantityRelay_r17 z) /\
  True.

Definition EventTriggerConfig__ext1__Type := EventTriggerConfig__ext1O__Type.
Definition EventTriggerConfig__ext1__cond := EventTriggerConfig__ext1O__cond.

Record EventTriggerConfig__Type : Set :=
  make__EventTriggerConfig__Type {
    EventTriggerConfig__eventId : EventTriggerConfig__eventId__Type ;
    EventTriggerConfig__rsType : NR_RS_Type__Type ;
    EventTriggerConfig__reportInterval : ReportInterval__Type ;
    EventTriggerConfig__reportAmount : EventTriggerConfig__reportAmount__Type ;
    EventTriggerConfig__reportQuantityCell : MeasReportQuantity__Type ;
    EventTriggerConfig__maxReportCells : Z ;
    EventTriggerConfig__reportQuantityRS_Indexes : option MeasReportQuantity__Type ;
    EventTriggerConfig__maxNrofRS_IndexesToReport : option Z ;
    EventTriggerConfig__includeBeamMeasurements : bool ;
    EventTriggerConfig__reportAddNeighMeas : option EventTriggerConfig__reportAddNeighMeas__Type ;
    EventTriggerConfig__ext0 : option EventTriggerConfig__ext0__Type ;
    EventTriggerConfig__ext1 : option EventTriggerConfig__ext1__Type ;
}.
Definition EventTriggerConfig__root_list : list seq_elem := (
 Nor EventTriggerConfig__eventId__Type EventTriggerConfig__eventId__cond ::
 Nor NR_RS_Type__Type NR_RS_Type__cond ::
 Nor ReportInterval__Type ReportInterval__cond ::
 Nor EventTriggerConfig__reportAmount__Type EventTriggerConfig__reportAmount__cond ::
 Nor MeasReportQuantity__Type MeasReportQuantity__cond ::
 Nor Z EventTriggerConfig__maxReportCells__cond ::
 Opt MeasReportQuantity__Type MeasReportQuantity__cond ::
 Opt Z EventTriggerConfig__maxNrofRS_IndexesToReport__cond ::
 Nor bool (fun _ => True) ::
 Opt EventTriggerConfig__reportAddNeighMeas__Type EventTriggerConfig__reportAddNeighMeas__cond ::
 nil).
Definition EventTriggerConfig__ext_list : list typ := (
  typ_cons EventTriggerConfig__ext0__Type EventTriggerConfig__ext0__cond ::
  typ_cons EventTriggerConfig__ext1__Type EventTriggerConfig__ext1__cond ::
  nil).
Definition EventTriggerConfig__cond (z : EventTriggerConfig__Type) := 
(  EventTriggerConfig__eventId__cond (EventTriggerConfig__eventId z) /\
  NR_RS_Type__cond (EventTriggerConfig__rsType z) /\
  ReportInterval__cond (EventTriggerConfig__reportInterval z) /\
  EventTriggerConfig__reportAmount__cond (EventTriggerConfig__reportAmount z) /\
  MeasReportQuantity__cond (EventTriggerConfig__reportQuantityCell z) /\
  EventTriggerConfig__maxReportCells__cond (EventTriggerConfig__maxReportCells z) /\
  opt_cond MeasReportQuantity__cond (EventTriggerConfig__reportQuantityRS_Indexes z) /\
  opt_cond EventTriggerConfig__maxNrofRS_IndexesToReport__cond (EventTriggerConfig__maxNrofRS_IndexesToReport z) /\
  (fun _ => True) (EventTriggerConfig__includeBeamMeasurements z) /\
  opt_cond EventTriggerConfig__reportAddNeighMeas__cond (EventTriggerConfig__reportAddNeighMeas z) /\
  True) /\ 
(  opt_cond EventTriggerConfig__ext0__cond (EventTriggerConfig__ext0 z) /\
  opt_cond EventTriggerConfig__ext1__cond (EventTriggerConfig__ext1 z) /\
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

Definition EventTriggerConfig__eventId__root__eventA1__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__root__eventA1__list.
Definition EventTriggerConfig__eventId__root__eventA1__Format_list : EventTriggerConfig__eventId__root__eventA1__Format_Type :=
  (MeasTriggerQuantity__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).
Definition EventTriggerConfig__eventId__root__eventA1__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__root__eventA1__list EventTriggerConfig__eventId__root__eventA1__Format_list.
Definition EventTriggerConfig__eventId__root__eventA1__F1 z :=
  (EventTriggerConfig__eventId__root__eventA1__a1_Threshold z, (EventTriggerConfig__eventId__root__eventA1__reportOnLeave z, (EventTriggerConfig__eventId__root__eventA1__hysteresis z, (EventTriggerConfig__eventId__root__eventA1__timeToTrigger z, tt)))).
Definition EventTriggerConfig__eventId__root__eventA1__F2 (y : seq_type EventTriggerConfig__eventId__root__eventA1__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__EventTriggerConfig__eventId__root__eventA1__Type i0 i1 i2 i3
  end.
Lemma EventTriggerConfig__eventId__root__eventA1__F1F2_cond (z : EventTriggerConfig__eventId__root__eventA1__Type)
  : EventTriggerConfig__eventId__root__eventA1__cond z ->
  (seq_cond EventTriggerConfig__eventId__root__eventA1__list (EventTriggerConfig__eventId__root__eventA1__F1 z)).
intro H. unfold EventTriggerConfig__eventId__root__eventA1__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA1__F1F2_cond2 (z : EventTriggerConfig__eventId__root__eventA1__Type)
 : EventTriggerConfig__eventId__root__eventA1__F2 (EventTriggerConfig__eventId__root__eventA1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA1__F2F1_cond (y : seq_type EventTriggerConfig__eventId__root__eventA1__list)
  : seq_cond EventTriggerConfig__eventId__root__eventA1__list y ->
 (EventTriggerConfig__eventId__root__eventA1__cond (EventTriggerConfig__eventId__root__eventA1__F2 y)) /\  EventTriggerConfig__eventId__root__eventA1__F1 (EventTriggerConfig__eventId__root__eventA1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__root__eventA1__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__root__eventA1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__root__eventA1__Format : T_Format EventTriggerConfig__eventId__root__eventA1__Type EventTriggerConfig__eventId__root__eventA1__cond :=
        proj2_format  EventTriggerConfig__eventId__root__eventA1__cond EventTriggerConfig__eventId__root__eventA1__list__Format
    EventTriggerConfig__eventId__root__eventA1__F1 EventTriggerConfig__eventId__root__eventA1__F2 EventTriggerConfig__eventId__root__eventA1__F1F2_cond  EventTriggerConfig__eventId__root__eventA1__F1F2_cond2 EventTriggerConfig__eventId__root__eventA1__F2F1_cond.
Opaque EventTriggerConfig__eventId__root__eventA1__cond EventTriggerConfig__eventId__root__eventA1__Format.


Definition EventTriggerConfig__eventId__root__eventA2__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__root__eventA2__list.
Definition EventTriggerConfig__eventId__root__eventA2__Format_list : EventTriggerConfig__eventId__root__eventA2__Format_Type :=
  (MeasTriggerQuantity__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).
Definition EventTriggerConfig__eventId__root__eventA2__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__root__eventA2__list EventTriggerConfig__eventId__root__eventA2__Format_list.
Definition EventTriggerConfig__eventId__root__eventA2__F1 z :=
  (EventTriggerConfig__eventId__root__eventA2__a2_Threshold z, (EventTriggerConfig__eventId__root__eventA2__reportOnLeave z, (EventTriggerConfig__eventId__root__eventA2__hysteresis z, (EventTriggerConfig__eventId__root__eventA2__timeToTrigger z, tt)))).
Definition EventTriggerConfig__eventId__root__eventA2__F2 (y : seq_type EventTriggerConfig__eventId__root__eventA2__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__EventTriggerConfig__eventId__root__eventA2__Type i0 i1 i2 i3
  end.
Lemma EventTriggerConfig__eventId__root__eventA2__F1F2_cond (z : EventTriggerConfig__eventId__root__eventA2__Type)
  : EventTriggerConfig__eventId__root__eventA2__cond z ->
  (seq_cond EventTriggerConfig__eventId__root__eventA2__list (EventTriggerConfig__eventId__root__eventA2__F1 z)).
intro H. unfold EventTriggerConfig__eventId__root__eventA2__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA2__F1F2_cond2 (z : EventTriggerConfig__eventId__root__eventA2__Type)
 : EventTriggerConfig__eventId__root__eventA2__F2 (EventTriggerConfig__eventId__root__eventA2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA2__F2F1_cond (y : seq_type EventTriggerConfig__eventId__root__eventA2__list)
  : seq_cond EventTriggerConfig__eventId__root__eventA2__list y ->
 (EventTriggerConfig__eventId__root__eventA2__cond (EventTriggerConfig__eventId__root__eventA2__F2 y)) /\  EventTriggerConfig__eventId__root__eventA2__F1 (EventTriggerConfig__eventId__root__eventA2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__root__eventA2__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__root__eventA2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__root__eventA2__Format : T_Format EventTriggerConfig__eventId__root__eventA2__Type EventTriggerConfig__eventId__root__eventA2__cond :=
        proj2_format  EventTriggerConfig__eventId__root__eventA2__cond EventTriggerConfig__eventId__root__eventA2__list__Format
    EventTriggerConfig__eventId__root__eventA2__F1 EventTriggerConfig__eventId__root__eventA2__F2 EventTriggerConfig__eventId__root__eventA2__F1F2_cond  EventTriggerConfig__eventId__root__eventA2__F1F2_cond2 EventTriggerConfig__eventId__root__eventA2__F2F1_cond.
Opaque EventTriggerConfig__eventId__root__eventA2__cond EventTriggerConfig__eventId__root__eventA2__Format.


Definition EventTriggerConfig__eventId__root__eventA3__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__root__eventA3__list.
Definition EventTriggerConfig__eventId__root__eventA3__Format_list : EventTriggerConfig__eventId__root__eventA3__Format_Type :=
  (MeasTriggerQuantityOffset__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, (bool__Format, unit_format))))).
Definition EventTriggerConfig__eventId__root__eventA3__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__root__eventA3__list EventTriggerConfig__eventId__root__eventA3__Format_list.
Definition EventTriggerConfig__eventId__root__eventA3__F1 z :=
  (EventTriggerConfig__eventId__root__eventA3__a3_Offset z, (EventTriggerConfig__eventId__root__eventA3__reportOnLeave z, (EventTriggerConfig__eventId__root__eventA3__hysteresis z, (EventTriggerConfig__eventId__root__eventA3__timeToTrigger z, (EventTriggerConfig__eventId__root__eventA3__useAllowedCellList z, tt))))).
Definition EventTriggerConfig__eventId__root__eventA3__F2 (y : seq_type EventTriggerConfig__eventId__root__eventA3__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__EventTriggerConfig__eventId__root__eventA3__Type i0 i1 i2 i3 i4
  end.
Lemma EventTriggerConfig__eventId__root__eventA3__F1F2_cond (z : EventTriggerConfig__eventId__root__eventA3__Type)
  : EventTriggerConfig__eventId__root__eventA3__cond z ->
  (seq_cond EventTriggerConfig__eventId__root__eventA3__list (EventTriggerConfig__eventId__root__eventA3__F1 z)).
intro H. unfold EventTriggerConfig__eventId__root__eventA3__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA3__F1F2_cond2 (z : EventTriggerConfig__eventId__root__eventA3__Type)
 : EventTriggerConfig__eventId__root__eventA3__F2 (EventTriggerConfig__eventId__root__eventA3__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA3__F2F1_cond (y : seq_type EventTriggerConfig__eventId__root__eventA3__list)
  : seq_cond EventTriggerConfig__eventId__root__eventA3__list y ->
 (EventTriggerConfig__eventId__root__eventA3__cond (EventTriggerConfig__eventId__root__eventA3__F2 y)) /\  EventTriggerConfig__eventId__root__eventA3__F1 (EventTriggerConfig__eventId__root__eventA3__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__root__eventA3__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__root__eventA3__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__root__eventA3__Format : T_Format EventTriggerConfig__eventId__root__eventA3__Type EventTriggerConfig__eventId__root__eventA3__cond :=
        proj2_format  EventTriggerConfig__eventId__root__eventA3__cond EventTriggerConfig__eventId__root__eventA3__list__Format
    EventTriggerConfig__eventId__root__eventA3__F1 EventTriggerConfig__eventId__root__eventA3__F2 EventTriggerConfig__eventId__root__eventA3__F1F2_cond  EventTriggerConfig__eventId__root__eventA3__F1F2_cond2 EventTriggerConfig__eventId__root__eventA3__F2F1_cond.
Opaque EventTriggerConfig__eventId__root__eventA3__cond EventTriggerConfig__eventId__root__eventA3__Format.


Definition EventTriggerConfig__eventId__root__eventA4__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__root__eventA4__list.
Definition EventTriggerConfig__eventId__root__eventA4__Format_list : EventTriggerConfig__eventId__root__eventA4__Format_Type :=
  (MeasTriggerQuantity__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, (bool__Format, unit_format))))).
Definition EventTriggerConfig__eventId__root__eventA4__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__root__eventA4__list EventTriggerConfig__eventId__root__eventA4__Format_list.
Definition EventTriggerConfig__eventId__root__eventA4__F1 z :=
  (EventTriggerConfig__eventId__root__eventA4__a4_Threshold z, (EventTriggerConfig__eventId__root__eventA4__reportOnLeave z, (EventTriggerConfig__eventId__root__eventA4__hysteresis z, (EventTriggerConfig__eventId__root__eventA4__timeToTrigger z, (EventTriggerConfig__eventId__root__eventA4__useAllowedCellList z, tt))))).
Definition EventTriggerConfig__eventId__root__eventA4__F2 (y : seq_type EventTriggerConfig__eventId__root__eventA4__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__EventTriggerConfig__eventId__root__eventA4__Type i0 i1 i2 i3 i4
  end.
Lemma EventTriggerConfig__eventId__root__eventA4__F1F2_cond (z : EventTriggerConfig__eventId__root__eventA4__Type)
  : EventTriggerConfig__eventId__root__eventA4__cond z ->
  (seq_cond EventTriggerConfig__eventId__root__eventA4__list (EventTriggerConfig__eventId__root__eventA4__F1 z)).
intro H. unfold EventTriggerConfig__eventId__root__eventA4__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA4__F1F2_cond2 (z : EventTriggerConfig__eventId__root__eventA4__Type)
 : EventTriggerConfig__eventId__root__eventA4__F2 (EventTriggerConfig__eventId__root__eventA4__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA4__F2F1_cond (y : seq_type EventTriggerConfig__eventId__root__eventA4__list)
  : seq_cond EventTriggerConfig__eventId__root__eventA4__list y ->
 (EventTriggerConfig__eventId__root__eventA4__cond (EventTriggerConfig__eventId__root__eventA4__F2 y)) /\  EventTriggerConfig__eventId__root__eventA4__F1 (EventTriggerConfig__eventId__root__eventA4__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__root__eventA4__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__root__eventA4__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__root__eventA4__Format : T_Format EventTriggerConfig__eventId__root__eventA4__Type EventTriggerConfig__eventId__root__eventA4__cond :=
        proj2_format  EventTriggerConfig__eventId__root__eventA4__cond EventTriggerConfig__eventId__root__eventA4__list__Format
    EventTriggerConfig__eventId__root__eventA4__F1 EventTriggerConfig__eventId__root__eventA4__F2 EventTriggerConfig__eventId__root__eventA4__F1F2_cond  EventTriggerConfig__eventId__root__eventA4__F1F2_cond2 EventTriggerConfig__eventId__root__eventA4__F2F1_cond.
Opaque EventTriggerConfig__eventId__root__eventA4__cond EventTriggerConfig__eventId__root__eventA4__Format.


Definition EventTriggerConfig__eventId__root__eventA5__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__root__eventA5__list.
Definition EventTriggerConfig__eventId__root__eventA5__Format_list : EventTriggerConfig__eventId__root__eventA5__Format_Type :=
  (MeasTriggerQuantity__Format, (MeasTriggerQuantity__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, (bool__Format, unit_format)))))).
Definition EventTriggerConfig__eventId__root__eventA5__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__root__eventA5__list EventTriggerConfig__eventId__root__eventA5__Format_list.
Definition EventTriggerConfig__eventId__root__eventA5__F1 z :=
  (EventTriggerConfig__eventId__root__eventA5__a5_Threshold1 z, (EventTriggerConfig__eventId__root__eventA5__a5_Threshold2 z, (EventTriggerConfig__eventId__root__eventA5__reportOnLeave z, (EventTriggerConfig__eventId__root__eventA5__hysteresis z, (EventTriggerConfig__eventId__root__eventA5__timeToTrigger z, (EventTriggerConfig__eventId__root__eventA5__useAllowedCellList z, tt)))))).
Definition EventTriggerConfig__eventId__root__eventA5__F2 (y : seq_type EventTriggerConfig__eventId__root__eventA5__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__EventTriggerConfig__eventId__root__eventA5__Type i0 i1 i2 i3 i4 i5
  end.
Lemma EventTriggerConfig__eventId__root__eventA5__F1F2_cond (z : EventTriggerConfig__eventId__root__eventA5__Type)
  : EventTriggerConfig__eventId__root__eventA5__cond z ->
  (seq_cond EventTriggerConfig__eventId__root__eventA5__list (EventTriggerConfig__eventId__root__eventA5__F1 z)).
intro H. unfold EventTriggerConfig__eventId__root__eventA5__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA5__F1F2_cond2 (z : EventTriggerConfig__eventId__root__eventA5__Type)
 : EventTriggerConfig__eventId__root__eventA5__F2 (EventTriggerConfig__eventId__root__eventA5__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA5__F2F1_cond (y : seq_type EventTriggerConfig__eventId__root__eventA5__list)
  : seq_cond EventTriggerConfig__eventId__root__eventA5__list y ->
 (EventTriggerConfig__eventId__root__eventA5__cond (EventTriggerConfig__eventId__root__eventA5__F2 y)) /\  EventTriggerConfig__eventId__root__eventA5__F1 (EventTriggerConfig__eventId__root__eventA5__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__root__eventA5__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__root__eventA5__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__root__eventA5__Format : T_Format EventTriggerConfig__eventId__root__eventA5__Type EventTriggerConfig__eventId__root__eventA5__cond :=
        proj2_format  EventTriggerConfig__eventId__root__eventA5__cond EventTriggerConfig__eventId__root__eventA5__list__Format
    EventTriggerConfig__eventId__root__eventA5__F1 EventTriggerConfig__eventId__root__eventA5__F2 EventTriggerConfig__eventId__root__eventA5__F1F2_cond  EventTriggerConfig__eventId__root__eventA5__F1F2_cond2 EventTriggerConfig__eventId__root__eventA5__F2F1_cond.
Opaque EventTriggerConfig__eventId__root__eventA5__cond EventTriggerConfig__eventId__root__eventA5__Format.


Definition EventTriggerConfig__eventId__root__eventA6__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__root__eventA6__list.
Definition EventTriggerConfig__eventId__root__eventA6__Format_list : EventTriggerConfig__eventId__root__eventA6__Format_Type :=
  (MeasTriggerQuantityOffset__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, (bool__Format, unit_format))))).
Definition EventTriggerConfig__eventId__root__eventA6__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__root__eventA6__list EventTriggerConfig__eventId__root__eventA6__Format_list.
Definition EventTriggerConfig__eventId__root__eventA6__F1 z :=
  (EventTriggerConfig__eventId__root__eventA6__a6_Offset z, (EventTriggerConfig__eventId__root__eventA6__reportOnLeave z, (EventTriggerConfig__eventId__root__eventA6__hysteresis z, (EventTriggerConfig__eventId__root__eventA6__timeToTrigger z, (EventTriggerConfig__eventId__root__eventA6__useAllowedCellList z, tt))))).
Definition EventTriggerConfig__eventId__root__eventA6__F2 (y : seq_type EventTriggerConfig__eventId__root__eventA6__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__EventTriggerConfig__eventId__root__eventA6__Type i0 i1 i2 i3 i4
  end.
Lemma EventTriggerConfig__eventId__root__eventA6__F1F2_cond (z : EventTriggerConfig__eventId__root__eventA6__Type)
  : EventTriggerConfig__eventId__root__eventA6__cond z ->
  (seq_cond EventTriggerConfig__eventId__root__eventA6__list (EventTriggerConfig__eventId__root__eventA6__F1 z)).
intro H. unfold EventTriggerConfig__eventId__root__eventA6__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA6__F1F2_cond2 (z : EventTriggerConfig__eventId__root__eventA6__Type)
 : EventTriggerConfig__eventId__root__eventA6__F2 (EventTriggerConfig__eventId__root__eventA6__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__root__eventA6__F2F1_cond (y : seq_type EventTriggerConfig__eventId__root__eventA6__list)
  : seq_cond EventTriggerConfig__eventId__root__eventA6__list y ->
 (EventTriggerConfig__eventId__root__eventA6__cond (EventTriggerConfig__eventId__root__eventA6__F2 y)) /\  EventTriggerConfig__eventId__root__eventA6__F1 (EventTriggerConfig__eventId__root__eventA6__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__root__eventA6__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__root__eventA6__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__root__eventA6__Format : T_Format EventTriggerConfig__eventId__root__eventA6__Type EventTriggerConfig__eventId__root__eventA6__cond :=
        proj2_format  EventTriggerConfig__eventId__root__eventA6__cond EventTriggerConfig__eventId__root__eventA6__list__Format
    EventTriggerConfig__eventId__root__eventA6__F1 EventTriggerConfig__eventId__root__eventA6__F2 EventTriggerConfig__eventId__root__eventA6__F1F2_cond  EventTriggerConfig__eventId__root__eventA6__F1F2_cond2 EventTriggerConfig__eventId__root__eventA6__F2F1_cond.
Opaque EventTriggerConfig__eventId__root__eventA6__cond EventTriggerConfig__eventId__root__eventA6__Format.


Definition EventTriggerConfig__eventId__root__Format_Type := Eval cbn in get_formats EventTriggerConfig__eventId__root__list.
Definition EventTriggerConfig__eventId__root__Format_list : EventTriggerConfig__eventId__root__Format_Type :=
  (EventTriggerConfig__eventId__root__eventA1__Format, (EventTriggerConfig__eventId__root__eventA2__Format, (EventTriggerConfig__eventId__root__eventA3__Format, (EventTriggerConfig__eventId__root__eventA4__Format, (EventTriggerConfig__eventId__root__eventA5__Format, (EventTriggerConfig__eventId__root__eventA6__Format, unit__Format)))))).
Definition EventTriggerConfig__eventId__root__list__Format := Eval compute in choice_format EventTriggerConfig__eventId__root__list EventTriggerConfig__eventId__root__len_helper1 EventTriggerConfig__eventId__root__len_helper2  EventTriggerConfig__eventId__root__Format_list.
Definition EventTriggerConfig__eventId__root__F1 (z : EventTriggerConfig__eventId__root__Type) : (choice EventTriggerConfig__eventId__root__list) :=
  match z with
   | EventTriggerConfig__eventId__root__eventA1 t => existT _ 0 t
  | EventTriggerConfig__eventId__root__eventA2 t => existT _ 1 t
  | EventTriggerConfig__eventId__root__eventA3 t => existT _ 2 t
  | EventTriggerConfig__eventId__root__eventA4 t => existT _ 3 t
  | EventTriggerConfig__eventId__root__eventA5 t => existT _ 4 t
  | EventTriggerConfig__eventId__root__eventA6 t => existT _ 5 t
  end.
Definition EventTriggerConfig__eventId__root__g := (fun n => typ_set (get_nth_typ EventTriggerConfig__eventId__root__list n)).
Definition EventTriggerConfig__eventId__root__F2 (y : choice EventTriggerConfig__eventId__root__list) : EventTriggerConfig__eventId__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EventTriggerConfig__eventId__root__g n -> EventTriggerConfig__eventId__root__Type) with
    | 0 => fun (t : EventTriggerConfig__eventId__root__eventA1__Type) => EventTriggerConfig__eventId__root__eventA1 t 
    | 1 => fun (t : EventTriggerConfig__eventId__root__eventA2__Type) => EventTriggerConfig__eventId__root__eventA2 t 
    | 2 => fun (t : EventTriggerConfig__eventId__root__eventA3__Type) => EventTriggerConfig__eventId__root__eventA3 t 
    | 3 => fun (t : EventTriggerConfig__eventId__root__eventA4__Type) => EventTriggerConfig__eventId__root__eventA4 t 
    | 4 => fun (t : EventTriggerConfig__eventId__root__eventA5__Type) => EventTriggerConfig__eventId__root__eventA5 t 
    | 5 => fun (t : EventTriggerConfig__eventId__root__eventA6__Type) => EventTriggerConfig__eventId__root__eventA6 t 
 | (S (S (S (S (S (S n0)))))) => (fun (x' : nat) (t'' : EventTriggerConfig__eventId__root__g (S (S (S (S (S (S x'))))))) =>let t' :=
           eq_rect (get_nth_typ EventTriggerConfig__eventId__root__list (S (S (S (S (S (S x')))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len EventTriggerConfig__eventId__root__list (S (S (S (S (S (S x'))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))) in match t' return EventTriggerConfig__eventId__root__Type with end) n0
           end t0).

Lemma EventTriggerConfig__eventId__root__helper2 :  forall (y : EventTriggerConfig__eventId__root__Type), EventTriggerConfig__eventId__root__cond y -> choice_cond EventTriggerConfig__eventId__root__list (EventTriggerConfig__eventId__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EventTriggerConfig__eventId__root__helper3 :  forall (y : EventTriggerConfig__eventId__root__Type), EventTriggerConfig__eventId__root__F2 (EventTriggerConfig__eventId__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EventTriggerConfig__eventId__root__helper4 : (forall b : choice EventTriggerConfig__eventId__root__list, choice_cond EventTriggerConfig__eventId__root__list b -> EventTriggerConfig__eventId__root__cond (EventTriggerConfig__eventId__root__F2 b) /\ EventTriggerConfig__eventId__root__F1 (EventTriggerConfig__eventId__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EventTriggerConfig__eventId__root__F1 EventTriggerConfig__eventId__root__F2.
Definition EventTriggerConfig__eventId__root__Format : T_Format EventTriggerConfig__eventId__root__Type EventTriggerConfig__eventId__root__cond :=
  (* Eval compute in *) proj2_format EventTriggerConfig__eventId__root__cond EventTriggerConfig__eventId__root__list__Format EventTriggerConfig__eventId__root__F1 EventTriggerConfig__eventId__root__F2 EventTriggerConfig__eventId__root__helper2 EventTriggerConfig__eventId__root__helper3 EventTriggerConfig__eventId__root__helper4.
Opaque EventTriggerConfig__eventId__root__cond EventTriggerConfig__eventId__root__Format.


Definition EventTriggerConfig__eventId__ext__eventX1_r17__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__ext__eventX1_r17__list.
Definition EventTriggerConfig__eventId__ext__eventX1_r17__Format_list : EventTriggerConfig__eventId__ext__eventX1_r17__Format_Type :=
  (SL_MeasTriggerQuantity_r16__Format, (MeasTriggerQuantity__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, (bool__Format, unit_format)))))).
Definition EventTriggerConfig__eventId__ext__eventX1_r17__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__ext__eventX1_r17__list EventTriggerConfig__eventId__ext__eventX1_r17__Format_list.
Definition EventTriggerConfig__eventId__ext__eventX1_r17__F1 z :=
  (EventTriggerConfig__eventId__ext__eventX1_r17__x1_Threshold1_Relay_r17 z, (EventTriggerConfig__eventId__ext__eventX1_r17__x1_Threshold2_r17 z, (EventTriggerConfig__eventId__ext__eventX1_r17__reportOnLeave_r17 z, (EventTriggerConfig__eventId__ext__eventX1_r17__hysteresis_r17 z, (EventTriggerConfig__eventId__ext__eventX1_r17__timeToTrigger_r17 z, (EventTriggerConfig__eventId__ext__eventX1_r17__useAllowedCellList_r17 z, tt)))))).
Definition EventTriggerConfig__eventId__ext__eventX1_r17__F2 (y : seq_type EventTriggerConfig__eventId__ext__eventX1_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__EventTriggerConfig__eventId__ext__eventX1_r17__Type i0 i1 i2 i3 i4 i5
  end.
Lemma EventTriggerConfig__eventId__ext__eventX1_r17__F1F2_cond (z : EventTriggerConfig__eventId__ext__eventX1_r17__Type)
  : EventTriggerConfig__eventId__ext__eventX1_r17__cond z ->
  (seq_cond EventTriggerConfig__eventId__ext__eventX1_r17__list (EventTriggerConfig__eventId__ext__eventX1_r17__F1 z)).
intro H. unfold EventTriggerConfig__eventId__ext__eventX1_r17__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__ext__eventX1_r17__F1F2_cond2 (z : EventTriggerConfig__eventId__ext__eventX1_r17__Type)
 : EventTriggerConfig__eventId__ext__eventX1_r17__F2 (EventTriggerConfig__eventId__ext__eventX1_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__ext__eventX1_r17__F2F1_cond (y : seq_type EventTriggerConfig__eventId__ext__eventX1_r17__list)
  : seq_cond EventTriggerConfig__eventId__ext__eventX1_r17__list y ->
 (EventTriggerConfig__eventId__ext__eventX1_r17__cond (EventTriggerConfig__eventId__ext__eventX1_r17__F2 y)) /\  EventTriggerConfig__eventId__ext__eventX1_r17__F1 (EventTriggerConfig__eventId__ext__eventX1_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__ext__eventX1_r17__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__ext__eventX1_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__ext__eventX1_r17__Format : T_Format EventTriggerConfig__eventId__ext__eventX1_r17__Type EventTriggerConfig__eventId__ext__eventX1_r17__cond :=
        proj2_format  EventTriggerConfig__eventId__ext__eventX1_r17__cond EventTriggerConfig__eventId__ext__eventX1_r17__list__Format
    EventTriggerConfig__eventId__ext__eventX1_r17__F1 EventTriggerConfig__eventId__ext__eventX1_r17__F2 EventTriggerConfig__eventId__ext__eventX1_r17__F1F2_cond  EventTriggerConfig__eventId__ext__eventX1_r17__F1F2_cond2 EventTriggerConfig__eventId__ext__eventX1_r17__F2F1_cond.
Opaque EventTriggerConfig__eventId__ext__eventX1_r17__cond EventTriggerConfig__eventId__ext__eventX1_r17__Format.


Definition EventTriggerConfig__eventId__ext__eventX2_r17__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__ext__eventX2_r17__list.
Definition EventTriggerConfig__eventId__ext__eventX2_r17__Format_list : EventTriggerConfig__eventId__ext__eventX2_r17__Format_Type :=
  (SL_MeasTriggerQuantity_r16__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).
Definition EventTriggerConfig__eventId__ext__eventX2_r17__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__ext__eventX2_r17__list EventTriggerConfig__eventId__ext__eventX2_r17__Format_list.
Definition EventTriggerConfig__eventId__ext__eventX2_r17__F1 z :=
  (EventTriggerConfig__eventId__ext__eventX2_r17__x2_Threshold_Relay_r17 z, (EventTriggerConfig__eventId__ext__eventX2_r17__reportOnLeave_r17 z, (EventTriggerConfig__eventId__ext__eventX2_r17__hysteresis_r17 z, (EventTriggerConfig__eventId__ext__eventX2_r17__timeToTrigger_r17 z, tt)))).
Definition EventTriggerConfig__eventId__ext__eventX2_r17__F2 (y : seq_type EventTriggerConfig__eventId__ext__eventX2_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__EventTriggerConfig__eventId__ext__eventX2_r17__Type i0 i1 i2 i3
  end.
Lemma EventTriggerConfig__eventId__ext__eventX2_r17__F1F2_cond (z : EventTriggerConfig__eventId__ext__eventX2_r17__Type)
  : EventTriggerConfig__eventId__ext__eventX2_r17__cond z ->
  (seq_cond EventTriggerConfig__eventId__ext__eventX2_r17__list (EventTriggerConfig__eventId__ext__eventX2_r17__F1 z)).
intro H. unfold EventTriggerConfig__eventId__ext__eventX2_r17__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__ext__eventX2_r17__F1F2_cond2 (z : EventTriggerConfig__eventId__ext__eventX2_r17__Type)
 : EventTriggerConfig__eventId__ext__eventX2_r17__F2 (EventTriggerConfig__eventId__ext__eventX2_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__ext__eventX2_r17__F2F1_cond (y : seq_type EventTriggerConfig__eventId__ext__eventX2_r17__list)
  : seq_cond EventTriggerConfig__eventId__ext__eventX2_r17__list y ->
 (EventTriggerConfig__eventId__ext__eventX2_r17__cond (EventTriggerConfig__eventId__ext__eventX2_r17__F2 y)) /\  EventTriggerConfig__eventId__ext__eventX2_r17__F1 (EventTriggerConfig__eventId__ext__eventX2_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__ext__eventX2_r17__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__ext__eventX2_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__ext__eventX2_r17__Format : T_Format EventTriggerConfig__eventId__ext__eventX2_r17__Type EventTriggerConfig__eventId__ext__eventX2_r17__cond :=
        proj2_format  EventTriggerConfig__eventId__ext__eventX2_r17__cond EventTriggerConfig__eventId__ext__eventX2_r17__list__Format
    EventTriggerConfig__eventId__ext__eventX2_r17__F1 EventTriggerConfig__eventId__ext__eventX2_r17__F2 EventTriggerConfig__eventId__ext__eventX2_r17__F1F2_cond  EventTriggerConfig__eventId__ext__eventX2_r17__F1F2_cond2 EventTriggerConfig__eventId__ext__eventX2_r17__F2F1_cond.
Opaque EventTriggerConfig__eventId__ext__eventX2_r17__cond EventTriggerConfig__eventId__ext__eventX2_r17__Format.

Definition EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__Format : T_Format Z EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__cond :=
 ranged_int_format (1) (65525) EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__helper1 EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__helper2.

Opaque EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__cond EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__Format.

Definition EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__Format : T_Format Z EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__cond :=
 ranged_int_format (1) (65525) EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__helper1 EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__helper2.

Opaque EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__cond EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__Format.


Definition EventTriggerConfig__eventId__ext__eventD1_r17__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__eventId__ext__eventD1_r17__list.
Definition EventTriggerConfig__eventId__ext__eventD1_r17__Format_list : EventTriggerConfig__eventId__ext__eventD1_r17__Format_Type :=
  (EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17__Format, (EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17__Format, (ReferenceLocation_r17__Format, (ReferenceLocation_r17__Format, (bool__Format, (HysteresisLocation_r17__Format, (TimeToTrigger__Format, unit_format))))))).
Definition EventTriggerConfig__eventId__ext__eventD1_r17__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__eventId__ext__eventD1_r17__list EventTriggerConfig__eventId__ext__eventD1_r17__Format_list.
Definition EventTriggerConfig__eventId__ext__eventD1_r17__F1 z :=
  (EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference1_r17 z, (EventTriggerConfig__eventId__ext__eventD1_r17__distanceThreshFromReference2_r17 z, (EventTriggerConfig__eventId__ext__eventD1_r17__referenceLocation1_r17 z, (EventTriggerConfig__eventId__ext__eventD1_r17__referenceLocation2_r17 z, (EventTriggerConfig__eventId__ext__eventD1_r17__reportOnLeave_r17 z, (EventTriggerConfig__eventId__ext__eventD1_r17__hysteresisLocation_r17 z, (EventTriggerConfig__eventId__ext__eventD1_r17__timeToTrigger_r17 z, tt))))))).
Definition EventTriggerConfig__eventId__ext__eventD1_r17__F2 (y : seq_type EventTriggerConfig__eventId__ext__eventD1_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__EventTriggerConfig__eventId__ext__eventD1_r17__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma EventTriggerConfig__eventId__ext__eventD1_r17__F1F2_cond (z : EventTriggerConfig__eventId__ext__eventD1_r17__Type)
  : EventTriggerConfig__eventId__ext__eventD1_r17__cond z ->
  (seq_cond EventTriggerConfig__eventId__ext__eventD1_r17__list (EventTriggerConfig__eventId__ext__eventD1_r17__F1 z)).
intro H. unfold EventTriggerConfig__eventId__ext__eventD1_r17__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__ext__eventD1_r17__F1F2_cond2 (z : EventTriggerConfig__eventId__ext__eventD1_r17__Type)
 : EventTriggerConfig__eventId__ext__eventD1_r17__F2 (EventTriggerConfig__eventId__ext__eventD1_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__eventId__ext__eventD1_r17__F2F1_cond (y : seq_type EventTriggerConfig__eventId__ext__eventD1_r17__list)
  : seq_cond EventTriggerConfig__eventId__ext__eventD1_r17__list y ->
 (EventTriggerConfig__eventId__ext__eventD1_r17__cond (EventTriggerConfig__eventId__ext__eventD1_r17__F2 y)) /\  EventTriggerConfig__eventId__ext__eventD1_r17__F1 (EventTriggerConfig__eventId__ext__eventD1_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__eventId__ext__eventD1_r17__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__eventId__ext__eventD1_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__eventId__ext__eventD1_r17__Format : T_Format EventTriggerConfig__eventId__ext__eventD1_r17__Type EventTriggerConfig__eventId__ext__eventD1_r17__cond :=
        proj2_format  EventTriggerConfig__eventId__ext__eventD1_r17__cond EventTriggerConfig__eventId__ext__eventD1_r17__list__Format
    EventTriggerConfig__eventId__ext__eventD1_r17__F1 EventTriggerConfig__eventId__ext__eventD1_r17__F2 EventTriggerConfig__eventId__ext__eventD1_r17__F1F2_cond  EventTriggerConfig__eventId__ext__eventD1_r17__F1F2_cond2 EventTriggerConfig__eventId__ext__eventD1_r17__F2F1_cond.
Opaque EventTriggerConfig__eventId__ext__eventD1_r17__cond EventTriggerConfig__eventId__ext__eventD1_r17__Format.


Definition EventTriggerConfig__eventId__ext__Format_Type := Eval cbn in get_formats EventTriggerConfig__eventId__ext__list.
Definition EventTriggerConfig__eventId__ext__Format_list : EventTriggerConfig__eventId__ext__Format_Type :=
  (EventTriggerConfig__eventId__ext__eventX1_r17__Format, (EventTriggerConfig__eventId__ext__eventX2_r17__Format, (EventTriggerConfig__eventId__ext__eventD1_r17__Format, unit__Format))).
Definition EventTriggerConfig__eventId__ext__list__Format := Eval compute in choice_ext_format EventTriggerConfig__eventId__ext__list EventTriggerConfig__eventId__ext__Format_list.
Definition EventTriggerConfig__eventId__ext__F1 (z : EventTriggerConfig__eventId__ext__Type) : (choice EventTriggerConfig__eventId__ext__list) :=
  match z with
   | EventTriggerConfig__eventId__ext__eventX1_r17 t => existT _ 0 t
  | EventTriggerConfig__eventId__ext__eventX2_r17 t => existT _ 1 t
  | EventTriggerConfig__eventId__ext__eventD1_r17 t => existT _ 2 t
  end.
Definition EventTriggerConfig__eventId__ext__g := (fun n => typ_set (get_nth_typ EventTriggerConfig__eventId__ext__list n)).
Definition EventTriggerConfig__eventId__ext__F2 (y : choice EventTriggerConfig__eventId__ext__list) : EventTriggerConfig__eventId__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EventTriggerConfig__eventId__ext__g n -> EventTriggerConfig__eventId__ext__Type) with
    | 0 => fun (t : EventTriggerConfig__eventId__ext__eventX1_r17__Type) => EventTriggerConfig__eventId__ext__eventX1_r17 t 
    | 1 => fun (t : EventTriggerConfig__eventId__ext__eventX2_r17__Type) => EventTriggerConfig__eventId__ext__eventX2_r17 t 
    | 2 => fun (t : EventTriggerConfig__eventId__ext__eventD1_r17__Type) => EventTriggerConfig__eventId__ext__eventD1_r17 t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : EventTriggerConfig__eventId__ext__g (S (S (S x')))) =>let t' :=
                       eq_rect (get_nth_typ EventTriggerConfig__eventId__ext__list (S (S (S x'))))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len EventTriggerConfig__eventId__ext__list (S (S (S x')))
                       (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return EventTriggerConfig__eventId__ext__Type with end) n0
                       end t0).

Lemma EventTriggerConfig__eventId__ext__helper2 :  forall (y : EventTriggerConfig__eventId__ext__Type), EventTriggerConfig__eventId__ext__cond y -> choice_cond EventTriggerConfig__eventId__ext__list (EventTriggerConfig__eventId__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EventTriggerConfig__eventId__ext__helper3 :  forall (y : EventTriggerConfig__eventId__ext__Type), EventTriggerConfig__eventId__ext__F2 (EventTriggerConfig__eventId__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EventTriggerConfig__eventId__ext__helper4 : (forall b : choice EventTriggerConfig__eventId__ext__list, choice_cond EventTriggerConfig__eventId__ext__list b -> EventTriggerConfig__eventId__ext__cond (EventTriggerConfig__eventId__ext__F2 b) /\ EventTriggerConfig__eventId__ext__F1 (EventTriggerConfig__eventId__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EventTriggerConfig__eventId__ext__F1 EventTriggerConfig__eventId__ext__F2.
Definition EventTriggerConfig__eventId__ext__Format : T_Format EventTriggerConfig__eventId__ext__Type EventTriggerConfig__eventId__ext__cond :=
          proj2_format EventTriggerConfig__eventId__ext__cond EventTriggerConfig__eventId__ext__list__Format EventTriggerConfig__eventId__ext__F1 EventTriggerConfig__eventId__ext__F2 EventTriggerConfig__eventId__ext__helper2 EventTriggerConfig__eventId__ext__helper3 EventTriggerConfig__eventId__ext__helper4.
Opaque EventTriggerConfig__eventId__ext__cond EventTriggerConfig__eventId__ext__Format.

Definition EventTriggerConfig__eventId__Format : T_Format EventTriggerConfig__eventId__Type EventTriggerConfig__eventId__cond := sum_format EventTriggerConfig__eventId__root__Format EventTriggerConfig__eventId__ext__Format.
Opaque EventTriggerConfig__eventId__cond EventTriggerConfig__eventId__Format.

Definition EventTriggerConfig__reportAmount__Format : T_Format EventTriggerConfig__reportAmount__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EventTriggerConfig__reportAmount__nat__Format EventTriggerConfig__reportAmount__F1 EventTriggerConfig__reportAmount__F2 EventTriggerConfig__reportAmount__F1F2 EventTriggerConfig__reportAmount__F2F1.

Opaque EventTriggerConfig__reportAmount__cond EventTriggerConfig__reportAmount__Format.

Definition EventTriggerConfig__maxReportCells__Format : T_Format Z EventTriggerConfig__maxReportCells__cond :=
 ranged_int_format (1) (maxCellReport) EventTriggerConfig__maxReportCells__helper1 EventTriggerConfig__maxReportCells__helper2.

Opaque EventTriggerConfig__maxReportCells__cond EventTriggerConfig__maxReportCells__Format.

Definition EventTriggerConfig__maxNrofRS_IndexesToReport__Format : T_Format Z EventTriggerConfig__maxNrofRS_IndexesToReport__cond :=
 ranged_int_format (1) (maxNrofIndexesToReport) EventTriggerConfig__maxNrofRS_IndexesToReport__helper1 EventTriggerConfig__maxNrofRS_IndexesToReport__helper2.

Opaque EventTriggerConfig__maxNrofRS_IndexesToReport__cond EventTriggerConfig__maxNrofRS_IndexesToReport__Format.

Definition EventTriggerConfig__reportAddNeighMeas__Format : T_Format EventTriggerConfig__reportAddNeighMeas__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EventTriggerConfig__reportAddNeighMeas__nat__Format EventTriggerConfig__reportAddNeighMeas__F1 EventTriggerConfig__reportAddNeighMeas__F2 EventTriggerConfig__reportAddNeighMeas__F1F2 EventTriggerConfig__reportAddNeighMeas__F2F1.

Opaque EventTriggerConfig__reportAddNeighMeas__cond EventTriggerConfig__reportAddNeighMeas__Format.

Definition EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Format : T_Format EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__nat__Format EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F1 EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F2 EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F1F2 EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__F2F1.

Opaque EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__cond EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Format.

Opaque EventTriggerConfig__ext0O__includeBT_Meas_r16__cond EventTriggerConfig__ext0O__includeBT_Meas_r16__Format.

Opaque EventTriggerConfig__ext0O__includeWLAN_Meas_r16__cond EventTriggerConfig__ext0O__includeWLAN_Meas_r16__Format.

Opaque EventTriggerConfig__ext0O__includeSensor_Meas_r16__cond EventTriggerConfig__ext0O__includeSensor_Meas_r16__Format.


Definition EventTriggerConfig__ext0O__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__ext0O__list.
Definition EventTriggerConfig__ext0O__Format_list : EventTriggerConfig__ext0O__Format_Type :=
  (MeasRSSI_ReportConfig_r16__Format, (bool__Format, (EventTriggerConfig__ext0O__includeCommonLocationInfo_r16__Format, (EventTriggerConfig__ext0O__includeBT_Meas_r16__Format, (EventTriggerConfig__ext0O__includeWLAN_Meas_r16__Format, (EventTriggerConfig__ext0O__includeSensor_Meas_r16__Format, unit_format)))))).
Definition EventTriggerConfig__ext0O__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__ext0O__list EventTriggerConfig__ext0O__Format_list.
Definition EventTriggerConfig__ext0O__F1 z :=
  (EventTriggerConfig__ext0O__measRSSI_ReportConfig_r16 z, (EventTriggerConfig__ext0O__useT312_r16 z, (EventTriggerConfig__ext0O__includeCommonLocationInfo_r16 z, (EventTriggerConfig__ext0O__includeBT_Meas_r16 z, (EventTriggerConfig__ext0O__includeWLAN_Meas_r16 z, (EventTriggerConfig__ext0O__includeSensor_Meas_r16 z, tt)))))).
Definition EventTriggerConfig__ext0O__F2 (y : seq_type EventTriggerConfig__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__EventTriggerConfig__ext0O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma EventTriggerConfig__ext0O__F1F2_cond (z : EventTriggerConfig__ext0O__Type)
  : EventTriggerConfig__ext0O__cond z ->
  (seq_cond EventTriggerConfig__ext0O__list (EventTriggerConfig__ext0O__F1 z)).
intro H. unfold EventTriggerConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__ext0O__F1F2_cond2 (z : EventTriggerConfig__ext0O__Type)
 : EventTriggerConfig__ext0O__F2 (EventTriggerConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__ext0O__F2F1_cond (y : seq_type EventTriggerConfig__ext0O__list)
  : seq_cond EventTriggerConfig__ext0O__list y ->
 (EventTriggerConfig__ext0O__cond (EventTriggerConfig__ext0O__F2 y)) /\  EventTriggerConfig__ext0O__F1 (EventTriggerConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__ext0O__Format : T_Format EventTriggerConfig__ext0O__Type EventTriggerConfig__ext0O__cond :=
        proj2_format  EventTriggerConfig__ext0O__cond EventTriggerConfig__ext0O__list__Format
    EventTriggerConfig__ext0O__F1 EventTriggerConfig__ext0O__F2 EventTriggerConfig__ext0O__F1F2_cond  EventTriggerConfig__ext0O__F1F2_cond2 EventTriggerConfig__ext0O__F2F1_cond.
Opaque EventTriggerConfig__ext0O__cond EventTriggerConfig__ext0O__Format.

Definition EventTriggerConfig__ext0__check_all_none (b : EventTriggerConfig__ext0O__Type) : bool :=
match b with 
  | make__EventTriggerConfig__ext0O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition EventTriggerConfig__ext0__Format : T_Format EventTriggerConfig__ext0__Type EventTriggerConfig__ext0__cond :=
  restrict_add_format EventTriggerConfig__ext0__check_all_none EventTriggerConfig__ext0O__Format.

Opaque EventTriggerConfig__ext0__cond EventTriggerConfig__ext0__Format.

Definition EventTriggerConfig__ext1O__coarseLocationRequest_r17__Format : T_Format EventTriggerConfig__ext1O__coarseLocationRequest_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EventTriggerConfig__ext1O__coarseLocationRequest_r17__nat__Format EventTriggerConfig__ext1O__coarseLocationRequest_r17__F1 EventTriggerConfig__ext1O__coarseLocationRequest_r17__F2 EventTriggerConfig__ext1O__coarseLocationRequest_r17__F1F2 EventTriggerConfig__ext1O__coarseLocationRequest_r17__F2F1.

Opaque EventTriggerConfig__ext1O__coarseLocationRequest_r17__cond EventTriggerConfig__ext1O__coarseLocationRequest_r17__Format.


Definition EventTriggerConfig__ext1O__Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__ext1O__list.
Definition EventTriggerConfig__ext1O__Format_list : EventTriggerConfig__ext1O__Format_Type :=
  (EventTriggerConfig__ext1O__coarseLocationRequest_r17__Format, (SL_MeasReportQuantity_r16__Format, unit_format)).
Definition EventTriggerConfig__ext1O__list__Format := (*Eval compute in *) seq_format EventTriggerConfig__ext1O__list EventTriggerConfig__ext1O__Format_list.
Definition EventTriggerConfig__ext1O__F1 z :=
  (EventTriggerConfig__ext1O__coarseLocationRequest_r17 z, (EventTriggerConfig__ext1O__reportQuantityRelay_r17 z, tt)).
Definition EventTriggerConfig__ext1O__F2 (y : seq_type EventTriggerConfig__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__EventTriggerConfig__ext1O__Type i0 i1
  end.
Lemma EventTriggerConfig__ext1O__F1F2_cond (z : EventTriggerConfig__ext1O__Type)
  : EventTriggerConfig__ext1O__cond z ->
  (seq_cond EventTriggerConfig__ext1O__list (EventTriggerConfig__ext1O__F1 z)).
intro H. unfold EventTriggerConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfig__ext1O__F1F2_cond2 (z : EventTriggerConfig__ext1O__Type)
 : EventTriggerConfig__ext1O__F2 (EventTriggerConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfig__ext1O__F2F1_cond (y : seq_type EventTriggerConfig__ext1O__list)
  : seq_cond EventTriggerConfig__ext1O__list y ->
 (EventTriggerConfig__ext1O__cond (EventTriggerConfig__ext1O__F2 y)) /\  EventTriggerConfig__ext1O__F1 (EventTriggerConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfig__ext1O__Format : T_Format EventTriggerConfig__ext1O__Type EventTriggerConfig__ext1O__cond :=
        proj2_format  EventTriggerConfig__ext1O__cond EventTriggerConfig__ext1O__list__Format
    EventTriggerConfig__ext1O__F1 EventTriggerConfig__ext1O__F2 EventTriggerConfig__ext1O__F1F2_cond  EventTriggerConfig__ext1O__F1F2_cond2 EventTriggerConfig__ext1O__F2F1_cond.
Opaque EventTriggerConfig__ext1O__cond EventTriggerConfig__ext1O__Format.

Definition EventTriggerConfig__ext1__check_all_none (b : EventTriggerConfig__ext1O__Type) : bool :=
match b with 
  | make__EventTriggerConfig__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition EventTriggerConfig__ext1__Format : T_Format EventTriggerConfig__ext1__Type EventTriggerConfig__ext1__cond :=
  restrict_add_format EventTriggerConfig__ext1__check_all_none EventTriggerConfig__ext1O__Format.

Opaque EventTriggerConfig__ext1__cond EventTriggerConfig__ext1__Format.


Definition EventTriggerConfig__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfig__root_list.
Definition EventTriggerConfig__root_Format_list : EventTriggerConfig__root_Format_Type :=
  (EventTriggerConfig__eventId__Format, (NR_RS_Type__Format, (ReportInterval__Format, (EventTriggerConfig__reportAmount__Format, (MeasReportQuantity__Format, (EventTriggerConfig__maxReportCells__Format, (MeasReportQuantity__Format, (EventTriggerConfig__maxNrofRS_IndexesToReport__Format, (bool__Format, (EventTriggerConfig__reportAddNeighMeas__Format, unit_format)))))))))).

Definition EventTriggerConfig__ext_Format_Type := Eval cbn in get_formats EventTriggerConfig__ext_list.
Definition EventTriggerConfig__ext_Format_list : EventTriggerConfig__ext_Format_Type :=
  (EventTriggerConfig__ext0__Format, (EventTriggerConfig__ext1__Format, unit__Format)).

Definition EventTriggerConfig__list_type : Set := (seq_type EventTriggerConfig__root_list) * (seq_ext_type EventTriggerConfig__ext_list).
Definition EventTriggerConfig__list_cond (z : EventTriggerConfig__list_type) : Prop :=
        (seq_cond EventTriggerConfig__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfig__ext_list (snd z)).
Definition EventTriggerConfig__list_format : T_Format EventTriggerConfig__list_type EventTriggerConfig__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfig__root_list EventTriggerConfig__root_Format_list EventTriggerConfig__ext_list EventTriggerConfig__ext_Format_list.

Opaque EventTriggerConfig__list_format.
Definition EventTriggerConfig__F1 (z : EventTriggerConfig__Type) : EventTriggerConfig__list_type :=
  (((EventTriggerConfig__eventId z, (EventTriggerConfig__rsType z, (EventTriggerConfig__reportInterval z, (EventTriggerConfig__reportAmount z, (EventTriggerConfig__reportQuantityCell z, (EventTriggerConfig__maxReportCells z, (EventTriggerConfig__reportQuantityRS_Indexes z, (EventTriggerConfig__maxNrofRS_IndexesToReport z, (EventTriggerConfig__includeBeamMeasurements z, (EventTriggerConfig__reportAddNeighMeas z, tt))))))))))), (
(EventTriggerConfig__ext0 z, (EventTriggerConfig__ext1 z, tt)))).
Definition EventTriggerConfig__F2 (y : EventTriggerConfig__list_type) : EventTriggerConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, _)))))))))), (i0, (i1, _)))=>
    make__EventTriggerConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i0 i1
  end.
Definition EventTriggerConfig__helper1 : (forall a : EventTriggerConfig__Type, EventTriggerConfig__cond a -> EventTriggerConfig__list_cond (EventTriggerConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfig__helper2 : (forall a : EventTriggerConfig__Type, EventTriggerConfig__F2 (EventTriggerConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfig__helper3 : (forall b : EventTriggerConfig__list_type, EventTriggerConfig__list_cond b -> EventTriggerConfig__cond (EventTriggerConfig__F2 b) /\ EventTriggerConfig__F1 (EventTriggerConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfig__cond, EventTriggerConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfig__Format : T_Format EventTriggerConfig__Type EventTriggerConfig__cond :=
 proj2_format EventTriggerConfig__cond EventTriggerConfig__list_format  EventTriggerConfig__F1 EventTriggerConfig__F2 EventTriggerConfig__helper1 EventTriggerConfig__helper2 EventTriggerConfig__helper3.

Opaque EventTriggerConfig__cond EventTriggerConfig__Format.

