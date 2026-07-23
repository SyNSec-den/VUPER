Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasTriggerQuantityEUTRA.

Opaque MeasTriggerQuantityEUTRA__cond MeasTriggerQuantityEUTRA__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfigInterRAT__eventId__root__eventB1__Type : Set :=
  make__EventTriggerConfigInterRAT__eventId__root__eventB1__Type {
    EventTriggerConfigInterRAT__eventId__root__eventB1__b1_ThresholdEUTRA : MeasTriggerQuantityEUTRA__Type ;
    EventTriggerConfigInterRAT__eventId__root__eventB1__reportOnLeave : bool ;
    EventTriggerConfigInterRAT__eventId__root__eventB1__hysteresis : Hysteresis__Type ;
    EventTriggerConfigInterRAT__eventId__root__eventB1__timeToTrigger : TimeToTrigger__Type ;
}.
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__root_list : list seq_elem := (
 Nor MeasTriggerQuantityEUTRA__Type MeasTriggerQuantityEUTRA__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__ext_list : list typ := (
  nil).
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__cond (z : EventTriggerConfigInterRAT__eventId__root__eventB1__Type) := 
(  MeasTriggerQuantityEUTRA__cond (EventTriggerConfigInterRAT__eventId__root__eventB1__b1_ThresholdEUTRA z) /\
  (fun _ => True) (EventTriggerConfigInterRAT__eventId__root__eventB1__reportOnLeave z) /\
  Hysteresis__cond (EventTriggerConfigInterRAT__eventId__root__eventB1__hysteresis z) /\
  TimeToTrigger__cond (EventTriggerConfigInterRAT__eventId__root__eventB1__timeToTrigger z) /\
  True) /\ 
(  True).

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.MeasTriggerQuantityEUTRA.

Opaque MeasTriggerQuantityEUTRA__cond MeasTriggerQuantityEUTRA__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfigInterRAT__eventId__root__eventB2__Type : Set :=
  make__EventTriggerConfigInterRAT__eventId__root__eventB2__Type {
    EventTriggerConfigInterRAT__eventId__root__eventB2__b2_Threshold1 : MeasTriggerQuantity__Type ;
    EventTriggerConfigInterRAT__eventId__root__eventB2__b2_Threshold2EUTRA : MeasTriggerQuantityEUTRA__Type ;
    EventTriggerConfigInterRAT__eventId__root__eventB2__reportOnLeave : bool ;
    EventTriggerConfigInterRAT__eventId__root__eventB2__hysteresis : Hysteresis__Type ;
    EventTriggerConfigInterRAT__eventId__root__eventB2__timeToTrigger : TimeToTrigger__Type ;
}.
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__root_list : list seq_elem := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor MeasTriggerQuantityEUTRA__Type MeasTriggerQuantityEUTRA__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__ext_list : list typ := (
  nil).
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__cond (z : EventTriggerConfigInterRAT__eventId__root__eventB2__Type) := 
(  MeasTriggerQuantity__cond (EventTriggerConfigInterRAT__eventId__root__eventB2__b2_Threshold1 z) /\
  MeasTriggerQuantityEUTRA__cond (EventTriggerConfigInterRAT__eventId__root__eventB2__b2_Threshold2EUTRA z) /\
  (fun _ => True) (EventTriggerConfigInterRAT__eventId__root__eventB2__reportOnLeave z) /\
  Hysteresis__cond (EventTriggerConfigInterRAT__eventId__root__eventB2__hysteresis z) /\
  TimeToTrigger__cond (EventTriggerConfigInterRAT__eventId__root__eventB2__timeToTrigger z) /\
  True) /\ 
(  True).


Inductive EventTriggerConfigInterRAT__eventId__root__Type : Set :=
  | EventTriggerConfigInterRAT__eventId__root__eventB1 : EventTriggerConfigInterRAT__eventId__root__eventB1__Type -> EventTriggerConfigInterRAT__eventId__root__Type
  | EventTriggerConfigInterRAT__eventId__root__eventB2 : EventTriggerConfigInterRAT__eventId__root__eventB2__Type -> EventTriggerConfigInterRAT__eventId__root__Type
.
Definition EventTriggerConfigInterRAT__eventId__root__list : list typ := (
typ_cons EventTriggerConfigInterRAT__eventId__root__eventB1__Type EventTriggerConfigInterRAT__eventId__root__eventB1__cond ::
typ_cons EventTriggerConfigInterRAT__eventId__root__eventB2__Type EventTriggerConfigInterRAT__eventId__root__eventB2__cond ::
 nil).
Definition EventTriggerConfigInterRAT__eventId__root__cond (c : EventTriggerConfigInterRAT__eventId__root__Type) := 
  match c with
  | EventTriggerConfigInterRAT__eventId__root__eventB1 t => EventTriggerConfigInterRAT__eventId__root__eventB1__cond t 
  | EventTriggerConfigInterRAT__eventId__root__eventB2 t => EventTriggerConfigInterRAT__eventId__root__eventB2__cond t 
  end.

Lemma EventTriggerConfigInterRAT__eventId__root__len_helper1 : to_bit_sz (length EventTriggerConfigInterRAT__eventId__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma EventTriggerConfigInterRAT__eventId__root__len_helper2 : 2 <= length2 EventTriggerConfigInterRAT__eventId__root__list.
 simpl. lia. Qed.
Require Import NR.MeasTriggerQuantityUTRA_FDD_r16.

Opaque MeasTriggerQuantityUTRA_FDD_r16__cond MeasTriggerQuantityUTRA_FDD_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type : Set :=
  make__EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type {
    EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__b1_ThresholdUTRA_FDD_r16 : MeasTriggerQuantityUTRA_FDD_r16__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__reportOnLeave_r16 : bool ;
    EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__hysteresis_r16 : Hysteresis__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__timeToTrigger_r16 : TimeToTrigger__Type ;
}.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_list : list seq_elem := (
 Nor MeasTriggerQuantityUTRA_FDD_r16__Type MeasTriggerQuantityUTRA_FDD_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_list : list typ := (
  nil).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond (z : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type) := 
(  MeasTriggerQuantityUTRA_FDD_r16__cond (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__b1_ThresholdUTRA_FDD_r16 z) /\
  (fun _ => True) (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__reportOnLeave_r16 z) /\
  Hysteresis__cond (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__hysteresis_r16 z) /\
  TimeToTrigger__cond (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__timeToTrigger_r16 z) /\
  True) /\ 
(  True).

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.MeasTriggerQuantityUTRA_FDD_r16.

Opaque MeasTriggerQuantityUTRA_FDD_r16__cond MeasTriggerQuantityUTRA_FDD_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type : Set :=
  make__EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type {
    EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__b2_Threshold1_r16 : MeasTriggerQuantity__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__b2_Threshold2UTRA_FDD_r16 : MeasTriggerQuantityUTRA_FDD_r16__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__reportOnLeave_r16 : bool ;
    EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__hysteresis_r16 : Hysteresis__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__timeToTrigger_r16 : TimeToTrigger__Type ;
}.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_list : list seq_elem := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor MeasTriggerQuantityUTRA_FDD_r16__Type MeasTriggerQuantityUTRA_FDD_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_list : list typ := (
  nil).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond (z : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type) := 
(  MeasTriggerQuantity__cond (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__b2_Threshold1_r16 z) /\
  MeasTriggerQuantityUTRA_FDD_r16__cond (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__b2_Threshold2UTRA_FDD_r16 z) /\
  (fun _ => True) (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__reportOnLeave_r16 z) /\
  Hysteresis__cond (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__hysteresis_r16 z) /\
  TimeToTrigger__cond (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__timeToTrigger_r16 z) /\
  True) /\ 
(  True).

Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.SL_MeasTriggerQuantity_r16.

Opaque SL_MeasTriggerQuantity_r16__cond SL_MeasTriggerQuantity_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type : Set :=
  make__EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type {
    EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__y1_Threshold1_r17 : MeasTriggerQuantity__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__y1_Threshold2_Relay_r17 : SL_MeasTriggerQuantity_r16__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__reportOnLeave_r17 : bool ;
    EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__hysteresis_r17 : Hysteresis__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__timeToTrigger_r17 : TimeToTrigger__Type ;
}.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_list : list seq_elem := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor SL_MeasTriggerQuantity_r16__Type SL_MeasTriggerQuantity_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_list : list typ := (
  nil).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond (z : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type) := 
(  MeasTriggerQuantity__cond (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__y1_Threshold1_r17 z) /\
  SL_MeasTriggerQuantity_r16__cond (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__y1_Threshold2_Relay_r17 z) /\
  (fun _ => True) (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__reportOnLeave_r17 z) /\
  Hysteresis__cond (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__hysteresis_r17 z) /\
  TimeToTrigger__cond (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__timeToTrigger_r17 z) /\
  True) /\ 
(  True).

Require Import NR.SL_MeasTriggerQuantity_r16.

Opaque SL_MeasTriggerQuantity_r16__cond SL_MeasTriggerQuantity_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type : Set :=
  make__EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type {
    EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__y2_Threshold_Relay_r17 : SL_MeasTriggerQuantity_r16__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__reportOnLeave_r17 : bool ;
    EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__hysteresis_r17 : Hysteresis__Type ;
    EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__timeToTrigger_r17 : TimeToTrigger__Type ;
}.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_list : list seq_elem := (
 Nor SL_MeasTriggerQuantity_r16__Type SL_MeasTriggerQuantity_r16__cond ::
 Nor bool (fun _ => True) ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_list : list typ := (
  nil).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond (z : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type) := 
(  SL_MeasTriggerQuantity_r16__cond (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__y2_Threshold_Relay_r17 z) /\
  (fun _ => True) (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__reportOnLeave_r17 z) /\
  Hysteresis__cond (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__hysteresis_r17 z) /\
  TimeToTrigger__cond (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__timeToTrigger_r17 z) /\
  True) /\ 
(  True).


Inductive EventTriggerConfigInterRAT__eventId__ext__Type : Set :=
  | EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16 : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type -> EventTriggerConfigInterRAT__eventId__ext__Type
  | EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16 : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type -> EventTriggerConfigInterRAT__eventId__ext__Type
  | EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17 : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type -> EventTriggerConfigInterRAT__eventId__ext__Type
  | EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17 : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type -> EventTriggerConfigInterRAT__eventId__ext__Type
.
Definition EventTriggerConfigInterRAT__eventId__ext__list : list typ := (
typ_cons EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond ::
typ_cons EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond ::
typ_cons EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond ::
typ_cons EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond ::
 nil).
Definition EventTriggerConfigInterRAT__eventId__ext__cond (c : EventTriggerConfigInterRAT__eventId__ext__Type) := 
  match c with
  | EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16 t => EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond t 
  | EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16 t => EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond t 
  | EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17 t => EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond t 
  | EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17 t => EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond t 
  end.

Lemma EventTriggerConfigInterRAT__eventId__ext__len_helper1 : to_bit_sz (length EventTriggerConfigInterRAT__eventId__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition EventTriggerConfigInterRAT__eventId__Type : Set := EventTriggerConfigInterRAT__eventId__root__Type + EventTriggerConfigInterRAT__eventId__ext__Type.
Definition EventTriggerConfigInterRAT__eventId__cond :=
  sum_cond EventTriggerConfigInterRAT__eventId__root__cond EventTriggerConfigInterRAT__eventId__ext__cond.
Require Import NR.NR_RS_Type.

Opaque NR_RS_Type__cond NR_RS_Type__Format.

Require Import NR.ReportInterval.

Opaque ReportInterval__cond ReportInterval__Format.

Inductive EventTriggerConfigInterRAT__reportAmount__Type : Set :=
 | EventTriggerConfigInterRAT__reportAmount__r1
 | EventTriggerConfigInterRAT__reportAmount__r2
 | EventTriggerConfigInterRAT__reportAmount__r4
 | EventTriggerConfigInterRAT__reportAmount__r8
 | EventTriggerConfigInterRAT__reportAmount__r16
 | EventTriggerConfigInterRAT__reportAmount__r32
 | EventTriggerConfigInterRAT__reportAmount__r64
 | EventTriggerConfigInterRAT__reportAmount__infinity
.
Definition EventTriggerConfigInterRAT__reportAmount__cond := (fun (_ : EventTriggerConfigInterRAT__reportAmount__Type) => True).
Lemma EventTriggerConfigInterRAT__reportAmount__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EventTriggerConfigInterRAT__reportAmount__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 EventTriggerConfigInterRAT__reportAmount__nat__helper.

Definition EventTriggerConfigInterRAT__reportAmount__F1 t :=
  match t with
  | EventTriggerConfigInterRAT__reportAmount__r1 => 0
  | EventTriggerConfigInterRAT__reportAmount__r2 => 1
  | EventTriggerConfigInterRAT__reportAmount__r4 => 2
  | EventTriggerConfigInterRAT__reportAmount__r8 => 3
  | EventTriggerConfigInterRAT__reportAmount__r16 => 4
  | EventTriggerConfigInterRAT__reportAmount__r32 => 5
  | EventTriggerConfigInterRAT__reportAmount__r64 => 6
  | EventTriggerConfigInterRAT__reportAmount__infinity => 7
  end.
Definition EventTriggerConfigInterRAT__reportAmount__F2 n :=
  match n with
  | 0 => EventTriggerConfigInterRAT__reportAmount__r1
  | 1 => EventTriggerConfigInterRAT__reportAmount__r2
  | 2 => EventTriggerConfigInterRAT__reportAmount__r4
  | 3 => EventTriggerConfigInterRAT__reportAmount__r8
  | 4 => EventTriggerConfigInterRAT__reportAmount__r16
  | 5 => EventTriggerConfigInterRAT__reportAmount__r32
  | 6 => EventTriggerConfigInterRAT__reportAmount__r64
  | 7 => EventTriggerConfigInterRAT__reportAmount__infinity
  | _ => EventTriggerConfigInterRAT__reportAmount__r1
  end.
Lemma EventTriggerConfigInterRAT__reportAmount__F1F2 : forall x : EventTriggerConfigInterRAT__reportAmount__Type, (EventTriggerConfigInterRAT__reportAmount__F1 x <= 7) /\ EventTriggerConfigInterRAT__reportAmount__F2 (EventTriggerConfigInterRAT__reportAmount__F1 x) = x. imp_solve. Qed.
Lemma EventTriggerConfigInterRAT__reportAmount__F2F1 : forall (y : nat) (H : y <= 7), EventTriggerConfigInterRAT__reportAmount__F1 (EventTriggerConfigInterRAT__reportAmount__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasReportQuantity.

Opaque MeasReportQuantity__cond MeasReportQuantity__Format.

Lemma EventTriggerConfigInterRAT__maxReportCells__helper1 : (1 <= maxCellReport)%Z. unfold maxCellReport.
 lia. Qed.
Lemma EventTriggerConfigInterRAT__maxReportCells__helper2 : to_bit_sz (Z.to_nat (maxCellReport - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellReport - 1))%Z). { apply Zorder.Zle_minus_le_0. apply EventTriggerConfigInterRAT__maxReportCells__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EventTriggerConfigInterRAT__maxReportCells__Type := Z.
Definition EventTriggerConfigInterRAT__maxReportCells__cond := (fun z => (1 <= z <= maxCellReport)%Z).
Require Import NR.MeasReportQuantityUTRA_FDD_r16.

Opaque MeasReportQuantityUTRA_FDD_r16__cond MeasReportQuantityUTRA_FDD_r16__Format.

Record EventTriggerConfigInterRAT__ext0O__Type : Set :=
  make__EventTriggerConfigInterRAT__ext0O__Type {
    EventTriggerConfigInterRAT__ext0O__reportQuantityUTRA_FDD_r16 : option MeasReportQuantityUTRA_FDD_r16__Type ;
}.
Definition EventTriggerConfigInterRAT__ext0O__list := (
 Opt MeasReportQuantityUTRA_FDD_r16__Type MeasReportQuantityUTRA_FDD_r16__cond ::
 nil).
Definition EventTriggerConfigInterRAT__ext0O__cond z := 
  opt_cond MeasReportQuantityUTRA_FDD_r16__cond (EventTriggerConfigInterRAT__ext0O__reportQuantityUTRA_FDD_r16 z) /\
  True.

Definition EventTriggerConfigInterRAT__ext0__Type := EventTriggerConfigInterRAT__ext0O__Type.
Definition EventTriggerConfigInterRAT__ext0__cond := EventTriggerConfigInterRAT__ext0O__cond.

Inductive EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type : Set :=
 | EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__true
.
Definition EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__cond := (fun (_ : EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type) => True).
Lemma EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__nat__helper.

Definition EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 t :=
  match t with
  | EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__true => 0
  end.
Definition EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2 n :=
  match n with
  | 0 => EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__true
  | _ => EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__true
  end.
Lemma EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1F2 : forall x : EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type, (EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 x <= 0) /\ EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2 (EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 x) = x. imp_solve. Qed.
Lemma EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2F1 : forall (y : nat) (H : y <= 0), EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 (EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.BT_NameList_r16.
Definition EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__Type := SetupRelease__Type BT_NameList_r16__Type.
Definition EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__cond := SetupRelease__cond _ BT_NameList_r16__cond.
Definition EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__Format : T_Format EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__Type EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__cond := SetupRelease__Format _ _ BT_NameList_r16__Format.
Opaque EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__cond EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.WLAN_NameList_r16.
Definition EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__Type := SetupRelease__Type WLAN_NameList_r16__Type.
Definition EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond := SetupRelease__cond _ WLAN_NameList_r16__cond.
Definition EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__Format : T_Format EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__Type EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond := SetupRelease__Format _ _ WLAN_NameList_r16__Format.
Opaque EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.Sensor_NameList_r16.
Definition EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__Type := SetupRelease__Type Sensor_NameList_r16__Type.
Definition EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__cond := SetupRelease__cond _ Sensor_NameList_r16__cond.
Definition EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__Format : T_Format EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__Type EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__cond := SetupRelease__Format _ _ Sensor_NameList_r16__Format.
Opaque EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__cond EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__Format.

Record EventTriggerConfigInterRAT__ext1O__Type : Set :=
  make__EventTriggerConfigInterRAT__ext1O__Type {
    EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16 : option EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type ;
    EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16 : option EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__Type ;
    EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16 : option EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__Type ;
    EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16 : option EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__Type ;
}.
Definition EventTriggerConfigInterRAT__ext1O__list := (
 Opt EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__cond ::
 Opt EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__Type EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__cond ::
 Opt EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__Type EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond ::
 Opt EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__Type EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__cond ::
 nil).
Definition EventTriggerConfigInterRAT__ext1O__cond z := 
  opt_cond EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__cond (EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16 z) /\
  opt_cond EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__cond (EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16 z) /\
  opt_cond EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond (EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16 z) /\
  opt_cond EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__cond (EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16 z) /\
  True.

Definition EventTriggerConfigInterRAT__ext1__Type := EventTriggerConfigInterRAT__ext1O__Type.
Definition EventTriggerConfigInterRAT__ext1__cond := EventTriggerConfigInterRAT__ext1O__cond.

Require Import NR.SL_MeasReportQuantity_r16.

Opaque SL_MeasReportQuantity_r16__cond SL_MeasReportQuantity_r16__Format.

Record EventTriggerConfigInterRAT__ext2O__Type : Set :=
  make__EventTriggerConfigInterRAT__ext2O__Type {
    EventTriggerConfigInterRAT__ext2O__reportQuantityRelay_r17 : option SL_MeasReportQuantity_r16__Type ;
}.
Definition EventTriggerConfigInterRAT__ext2O__list := (
 Opt SL_MeasReportQuantity_r16__Type SL_MeasReportQuantity_r16__cond ::
 nil).
Definition EventTriggerConfigInterRAT__ext2O__cond z := 
  opt_cond SL_MeasReportQuantity_r16__cond (EventTriggerConfigInterRAT__ext2O__reportQuantityRelay_r17 z) /\
  True.

Definition EventTriggerConfigInterRAT__ext2__Type := EventTriggerConfigInterRAT__ext2O__Type.
Definition EventTriggerConfigInterRAT__ext2__cond := EventTriggerConfigInterRAT__ext2O__cond.

Record EventTriggerConfigInterRAT__Type : Set :=
  make__EventTriggerConfigInterRAT__Type {
    EventTriggerConfigInterRAT__eventId : EventTriggerConfigInterRAT__eventId__Type ;
    EventTriggerConfigInterRAT__rsType : NR_RS_Type__Type ;
    EventTriggerConfigInterRAT__reportInterval : ReportInterval__Type ;
    EventTriggerConfigInterRAT__reportAmount : EventTriggerConfigInterRAT__reportAmount__Type ;
    EventTriggerConfigInterRAT__reportQuantity : MeasReportQuantity__Type ;
    EventTriggerConfigInterRAT__maxReportCells : Z ;
    EventTriggerConfigInterRAT__ext0 : option EventTriggerConfigInterRAT__ext0__Type ;
    EventTriggerConfigInterRAT__ext1 : option EventTriggerConfigInterRAT__ext1__Type ;
    EventTriggerConfigInterRAT__ext2 : option EventTriggerConfigInterRAT__ext2__Type ;
}.
Definition EventTriggerConfigInterRAT__root_list : list seq_elem := (
 Nor EventTriggerConfigInterRAT__eventId__Type EventTriggerConfigInterRAT__eventId__cond ::
 Nor NR_RS_Type__Type NR_RS_Type__cond ::
 Nor ReportInterval__Type ReportInterval__cond ::
 Nor EventTriggerConfigInterRAT__reportAmount__Type EventTriggerConfigInterRAT__reportAmount__cond ::
 Nor MeasReportQuantity__Type MeasReportQuantity__cond ::
 Nor Z EventTriggerConfigInterRAT__maxReportCells__cond ::
 nil).
Definition EventTriggerConfigInterRAT__ext_list : list typ := (
  typ_cons EventTriggerConfigInterRAT__ext0__Type EventTriggerConfigInterRAT__ext0__cond ::
  typ_cons EventTriggerConfigInterRAT__ext1__Type EventTriggerConfigInterRAT__ext1__cond ::
  typ_cons EventTriggerConfigInterRAT__ext2__Type EventTriggerConfigInterRAT__ext2__cond ::
  nil).
Definition EventTriggerConfigInterRAT__cond (z : EventTriggerConfigInterRAT__Type) := 
(  EventTriggerConfigInterRAT__eventId__cond (EventTriggerConfigInterRAT__eventId z) /\
  NR_RS_Type__cond (EventTriggerConfigInterRAT__rsType z) /\
  ReportInterval__cond (EventTriggerConfigInterRAT__reportInterval z) /\
  EventTriggerConfigInterRAT__reportAmount__cond (EventTriggerConfigInterRAT__reportAmount z) /\
  MeasReportQuantity__cond (EventTriggerConfigInterRAT__reportQuantity z) /\
  EventTriggerConfigInterRAT__maxReportCells__cond (EventTriggerConfigInterRAT__maxReportCells z) /\
  True) /\ 
(  opt_cond EventTriggerConfigInterRAT__ext0__cond (EventTriggerConfigInterRAT__ext0 z) /\
  opt_cond EventTriggerConfigInterRAT__ext1__cond (EventTriggerConfigInterRAT__ext1 z) /\
  opt_cond EventTriggerConfigInterRAT__ext2__cond (EventTriggerConfigInterRAT__ext2 z) /\
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

Definition EventTriggerConfigInterRAT__eventId__root__eventB1__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__eventId__root__eventB1__root_list.
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__root_Format_list : EventTriggerConfigInterRAT__eventId__root__eventB1__root_Format_Type :=
  (MeasTriggerQuantityEUTRA__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).

Definition EventTriggerConfigInterRAT__eventId__root__eventB1__ext_Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__eventId__root__eventB1__ext_list.
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__ext_Format_list : EventTriggerConfigInterRAT__eventId__root__eventB1__ext_Format_Type :=
  unit__Format.

Definition EventTriggerConfigInterRAT__eventId__root__eventB1__list_type : Set := (seq_type EventTriggerConfigInterRAT__eventId__root__eventB1__root_list) * (seq_ext_type EventTriggerConfigInterRAT__eventId__root__eventB1__ext_list).
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__list_cond (z : EventTriggerConfigInterRAT__eventId__root__eventB1__list_type) : Prop :=
        (seq_cond EventTriggerConfigInterRAT__eventId__root__eventB1__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfigInterRAT__eventId__root__eventB1__ext_list (snd z)).
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__list_format : T_Format EventTriggerConfigInterRAT__eventId__root__eventB1__list_type EventTriggerConfigInterRAT__eventId__root__eventB1__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfigInterRAT__eventId__root__eventB1__root_list EventTriggerConfigInterRAT__eventId__root__eventB1__root_Format_list EventTriggerConfigInterRAT__eventId__root__eventB1__ext_list EventTriggerConfigInterRAT__eventId__root__eventB1__ext_Format_list.

Opaque EventTriggerConfigInterRAT__eventId__root__eventB1__list_format.
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__F1 (z : EventTriggerConfigInterRAT__eventId__root__eventB1__Type) : EventTriggerConfigInterRAT__eventId__root__eventB1__list_type :=
  (((EventTriggerConfigInterRAT__eventId__root__eventB1__b1_ThresholdEUTRA z, (EventTriggerConfigInterRAT__eventId__root__eventB1__reportOnLeave z, (EventTriggerConfigInterRAT__eventId__root__eventB1__hysteresis z, (EventTriggerConfigInterRAT__eventId__root__eventB1__timeToTrigger z, tt))))), (
tt)).
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__F2 (y : EventTriggerConfigInterRAT__eventId__root__eventB1__list_type) : EventTriggerConfigInterRAT__eventId__root__eventB1__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__EventTriggerConfigInterRAT__eventId__root__eventB1__Type j0 j1 j2 j3
  end.
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__helper1 : (forall a : EventTriggerConfigInterRAT__eventId__root__eventB1__Type, EventTriggerConfigInterRAT__eventId__root__eventB1__cond a -> EventTriggerConfigInterRAT__eventId__root__eventB1__list_cond (EventTriggerConfigInterRAT__eventId__root__eventB1__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__helper2 : (forall a : EventTriggerConfigInterRAT__eventId__root__eventB1__Type, EventTriggerConfigInterRAT__eventId__root__eventB1__F2 (EventTriggerConfigInterRAT__eventId__root__eventB1__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__helper3 : (forall b : EventTriggerConfigInterRAT__eventId__root__eventB1__list_type, EventTriggerConfigInterRAT__eventId__root__eventB1__list_cond b -> EventTriggerConfigInterRAT__eventId__root__eventB1__cond (EventTriggerConfigInterRAT__eventId__root__eventB1__F2 b) /\ EventTriggerConfigInterRAT__eventId__root__eventB1__F1 (EventTriggerConfigInterRAT__eventId__root__eventB1__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfigInterRAT__eventId__root__eventB1__cond, EventTriggerConfigInterRAT__eventId__root__eventB1__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfigInterRAT__eventId__root__eventB1__Format : T_Format EventTriggerConfigInterRAT__eventId__root__eventB1__Type EventTriggerConfigInterRAT__eventId__root__eventB1__cond :=
 proj2_format EventTriggerConfigInterRAT__eventId__root__eventB1__cond EventTriggerConfigInterRAT__eventId__root__eventB1__list_format  EventTriggerConfigInterRAT__eventId__root__eventB1__F1 EventTriggerConfigInterRAT__eventId__root__eventB1__F2 EventTriggerConfigInterRAT__eventId__root__eventB1__helper1 EventTriggerConfigInterRAT__eventId__root__eventB1__helper2 EventTriggerConfigInterRAT__eventId__root__eventB1__helper3.

Opaque EventTriggerConfigInterRAT__eventId__root__eventB1__cond EventTriggerConfigInterRAT__eventId__root__eventB1__Format.


Definition EventTriggerConfigInterRAT__eventId__root__eventB2__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__eventId__root__eventB2__root_list.
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__root_Format_list : EventTriggerConfigInterRAT__eventId__root__eventB2__root_Format_Type :=
  (MeasTriggerQuantity__Format, (MeasTriggerQuantityEUTRA__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format))))).

Definition EventTriggerConfigInterRAT__eventId__root__eventB2__ext_Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__eventId__root__eventB2__ext_list.
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__ext_Format_list : EventTriggerConfigInterRAT__eventId__root__eventB2__ext_Format_Type :=
  unit__Format.

Definition EventTriggerConfigInterRAT__eventId__root__eventB2__list_type : Set := (seq_type EventTriggerConfigInterRAT__eventId__root__eventB2__root_list) * (seq_ext_type EventTriggerConfigInterRAT__eventId__root__eventB2__ext_list).
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__list_cond (z : EventTriggerConfigInterRAT__eventId__root__eventB2__list_type) : Prop :=
        (seq_cond EventTriggerConfigInterRAT__eventId__root__eventB2__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfigInterRAT__eventId__root__eventB2__ext_list (snd z)).
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__list_format : T_Format EventTriggerConfigInterRAT__eventId__root__eventB2__list_type EventTriggerConfigInterRAT__eventId__root__eventB2__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfigInterRAT__eventId__root__eventB2__root_list EventTriggerConfigInterRAT__eventId__root__eventB2__root_Format_list EventTriggerConfigInterRAT__eventId__root__eventB2__ext_list EventTriggerConfigInterRAT__eventId__root__eventB2__ext_Format_list.

Opaque EventTriggerConfigInterRAT__eventId__root__eventB2__list_format.
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__F1 (z : EventTriggerConfigInterRAT__eventId__root__eventB2__Type) : EventTriggerConfigInterRAT__eventId__root__eventB2__list_type :=
  (((EventTriggerConfigInterRAT__eventId__root__eventB2__b2_Threshold1 z, (EventTriggerConfigInterRAT__eventId__root__eventB2__b2_Threshold2EUTRA z, (EventTriggerConfigInterRAT__eventId__root__eventB2__reportOnLeave z, (EventTriggerConfigInterRAT__eventId__root__eventB2__hysteresis z, (EventTriggerConfigInterRAT__eventId__root__eventB2__timeToTrigger z, tt)))))), (
tt)).
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__F2 (y : EventTriggerConfigInterRAT__eventId__root__eventB2__list_type) : EventTriggerConfigInterRAT__eventId__root__eventB2__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__EventTriggerConfigInterRAT__eventId__root__eventB2__Type j0 j1 j2 j3 j4
  end.
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__helper1 : (forall a : EventTriggerConfigInterRAT__eventId__root__eventB2__Type, EventTriggerConfigInterRAT__eventId__root__eventB2__cond a -> EventTriggerConfigInterRAT__eventId__root__eventB2__list_cond (EventTriggerConfigInterRAT__eventId__root__eventB2__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__helper2 : (forall a : EventTriggerConfigInterRAT__eventId__root__eventB2__Type, EventTriggerConfigInterRAT__eventId__root__eventB2__F2 (EventTriggerConfigInterRAT__eventId__root__eventB2__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__helper3 : (forall b : EventTriggerConfigInterRAT__eventId__root__eventB2__list_type, EventTriggerConfigInterRAT__eventId__root__eventB2__list_cond b -> EventTriggerConfigInterRAT__eventId__root__eventB2__cond (EventTriggerConfigInterRAT__eventId__root__eventB2__F2 b) /\ EventTriggerConfigInterRAT__eventId__root__eventB2__F1 (EventTriggerConfigInterRAT__eventId__root__eventB2__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfigInterRAT__eventId__root__eventB2__cond, EventTriggerConfigInterRAT__eventId__root__eventB2__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfigInterRAT__eventId__root__eventB2__Format : T_Format EventTriggerConfigInterRAT__eventId__root__eventB2__Type EventTriggerConfigInterRAT__eventId__root__eventB2__cond :=
 proj2_format EventTriggerConfigInterRAT__eventId__root__eventB2__cond EventTriggerConfigInterRAT__eventId__root__eventB2__list_format  EventTriggerConfigInterRAT__eventId__root__eventB2__F1 EventTriggerConfigInterRAT__eventId__root__eventB2__F2 EventTriggerConfigInterRAT__eventId__root__eventB2__helper1 EventTriggerConfigInterRAT__eventId__root__eventB2__helper2 EventTriggerConfigInterRAT__eventId__root__eventB2__helper3.

Opaque EventTriggerConfigInterRAT__eventId__root__eventB2__cond EventTriggerConfigInterRAT__eventId__root__eventB2__Format.


Definition EventTriggerConfigInterRAT__eventId__root__Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__eventId__root__list.
Definition EventTriggerConfigInterRAT__eventId__root__Format_list : EventTriggerConfigInterRAT__eventId__root__Format_Type :=
  (EventTriggerConfigInterRAT__eventId__root__eventB1__Format, (EventTriggerConfigInterRAT__eventId__root__eventB2__Format, unit__Format)).
Definition EventTriggerConfigInterRAT__eventId__root__list__Format := Eval compute in choice_format EventTriggerConfigInterRAT__eventId__root__list EventTriggerConfigInterRAT__eventId__root__len_helper1 EventTriggerConfigInterRAT__eventId__root__len_helper2  EventTriggerConfigInterRAT__eventId__root__Format_list.
Definition EventTriggerConfigInterRAT__eventId__root__F1 (z : EventTriggerConfigInterRAT__eventId__root__Type) : (choice EventTriggerConfigInterRAT__eventId__root__list) :=
  match z with
   | EventTriggerConfigInterRAT__eventId__root__eventB1 t => existT _ 0 t
  | EventTriggerConfigInterRAT__eventId__root__eventB2 t => existT _ 1 t
  end.
Definition EventTriggerConfigInterRAT__eventId__root__g := (fun n => typ_set (get_nth_typ EventTriggerConfigInterRAT__eventId__root__list n)).
Definition EventTriggerConfigInterRAT__eventId__root__F2 (y : choice EventTriggerConfigInterRAT__eventId__root__list) : EventTriggerConfigInterRAT__eventId__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EventTriggerConfigInterRAT__eventId__root__g n -> EventTriggerConfigInterRAT__eventId__root__Type) with
    | 0 => fun (t : EventTriggerConfigInterRAT__eventId__root__eventB1__Type) => EventTriggerConfigInterRAT__eventId__root__eventB1 t 
    | 1 => fun (t : EventTriggerConfigInterRAT__eventId__root__eventB2__Type) => EventTriggerConfigInterRAT__eventId__root__eventB2 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : EventTriggerConfigInterRAT__eventId__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ EventTriggerConfigInterRAT__eventId__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len EventTriggerConfigInterRAT__eventId__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return EventTriggerConfigInterRAT__eventId__root__Type with end) n0
           end t0).

Lemma EventTriggerConfigInterRAT__eventId__root__helper2 :  forall (y : EventTriggerConfigInterRAT__eventId__root__Type), EventTriggerConfigInterRAT__eventId__root__cond y -> choice_cond EventTriggerConfigInterRAT__eventId__root__list (EventTriggerConfigInterRAT__eventId__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EventTriggerConfigInterRAT__eventId__root__helper3 :  forall (y : EventTriggerConfigInterRAT__eventId__root__Type), EventTriggerConfigInterRAT__eventId__root__F2 (EventTriggerConfigInterRAT__eventId__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EventTriggerConfigInterRAT__eventId__root__helper4 : (forall b : choice EventTriggerConfigInterRAT__eventId__root__list, choice_cond EventTriggerConfigInterRAT__eventId__root__list b -> EventTriggerConfigInterRAT__eventId__root__cond (EventTriggerConfigInterRAT__eventId__root__F2 b) /\ EventTriggerConfigInterRAT__eventId__root__F1 (EventTriggerConfigInterRAT__eventId__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EventTriggerConfigInterRAT__eventId__root__F1 EventTriggerConfigInterRAT__eventId__root__F2.
Definition EventTriggerConfigInterRAT__eventId__root__Format : T_Format EventTriggerConfigInterRAT__eventId__root__Type EventTriggerConfigInterRAT__eventId__root__cond :=
  (* Eval compute in *) proj2_format EventTriggerConfigInterRAT__eventId__root__cond EventTriggerConfigInterRAT__eventId__root__list__Format EventTriggerConfigInterRAT__eventId__root__F1 EventTriggerConfigInterRAT__eventId__root__F2 EventTriggerConfigInterRAT__eventId__root__helper2 EventTriggerConfigInterRAT__eventId__root__helper3 EventTriggerConfigInterRAT__eventId__root__helper4.
Opaque EventTriggerConfigInterRAT__eventId__root__cond EventTriggerConfigInterRAT__eventId__root__Format.


Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_list.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_Format_list : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_Format_Type :=
  (MeasTriggerQuantityUTRA_FDD_r16__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).

Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_list.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_Format_list : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_Format_Type :=
  unit__Format.

Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_type : Set := (seq_type EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_list) * (seq_ext_type EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_list).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_cond (z : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_type) : Prop :=
        (seq_cond EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_list (snd z)).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_format : T_Format EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_type EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_list EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__root_Format_list EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_list EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__ext_Format_list.

Opaque EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_format.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F1 (z : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type) : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_type :=
  (((EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__b1_ThresholdUTRA_FDD_r16 z, (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__reportOnLeave_r16 z, (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__hysteresis_r16 z, (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__timeToTrigger_r16 z, tt))))), (
tt)).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F2 (y : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_type) : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type j0 j1 j2 j3
  end.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__helper1 : (forall a : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type, EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond a -> EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_cond (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__helper2 : (forall a : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type, EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F2 (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__helper3 : (forall b : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_type, EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_cond b -> EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F2 b) /\ EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F1 (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond, EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Format : T_Format EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond :=
 proj2_format EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__list_format  EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F1 EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__F2 EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__helper1 EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__helper2 EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__helper3.

Opaque EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__cond EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Format.


Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_list.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_Format_list : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_Format_Type :=
  (MeasTriggerQuantity__Format, (MeasTriggerQuantityUTRA_FDD_r16__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format))))).

Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_list.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_Format_list : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_Format_Type :=
  unit__Format.

Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_type : Set := (seq_type EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_list) * (seq_ext_type EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_list).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_cond (z : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_type) : Prop :=
        (seq_cond EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_list (snd z)).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_format : T_Format EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_type EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_list EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__root_Format_list EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_list EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__ext_Format_list.

Opaque EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_format.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F1 (z : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type) : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_type :=
  (((EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__b2_Threshold1_r16 z, (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__b2_Threshold2UTRA_FDD_r16 z, (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__reportOnLeave_r16 z, (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__hysteresis_r16 z, (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__timeToTrigger_r16 z, tt)))))), (
tt)).
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F2 (y : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_type) : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type j0 j1 j2 j3 j4
  end.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__helper1 : (forall a : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type, EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond a -> EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_cond (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__helper2 : (forall a : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type, EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F2 (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__helper3 : (forall b : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_type, EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_cond b -> EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F2 b) /\ EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F1 (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond, EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Format : T_Format EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond :=
 proj2_format EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__list_format  EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F1 EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__F2 EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__helper1 EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__helper2 EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__helper3.

Opaque EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__cond EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Format.


Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_list.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_Format_list : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_Format_Type :=
  (MeasTriggerQuantity__Format, (SL_MeasTriggerQuantity_r16__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format))))).

Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_list.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_Format_list : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_Format_Type :=
  unit__Format.

Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_type : Set := (seq_type EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_list) * (seq_ext_type EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_list).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_cond (z : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_type) : Prop :=
        (seq_cond EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_list (snd z)).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_format : T_Format EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_type EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_list EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__root_Format_list EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_list EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__ext_Format_list.

Opaque EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_format.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F1 (z : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type) : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_type :=
  (((EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__y1_Threshold1_r17 z, (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__y1_Threshold2_Relay_r17 z, (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__reportOnLeave_r17 z, (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__hysteresis_r17 z, (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__timeToTrigger_r17 z, tt)))))), (
tt)).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F2 (y : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_type) : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type j0 j1 j2 j3 j4
  end.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__helper1 : (forall a : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type, EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond a -> EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_cond (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__helper2 : (forall a : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type, EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F2 (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__helper3 : (forall b : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_type, EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_cond b -> EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F2 b) /\ EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F1 (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond, EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Format : T_Format EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond :=
 proj2_format EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__list_format  EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F1 EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__F2 EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__helper1 EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__helper2 EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__helper3.

Opaque EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__cond EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Format.


Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_list.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_Format_list : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_Format_Type :=
  (SL_MeasTriggerQuantity_r16__Format, (bool__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format)))).

Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_list.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_Format_list : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_Format_Type :=
  unit__Format.

Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_type : Set := (seq_type EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_list) * (seq_ext_type EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_list).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_cond (z : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_type) : Prop :=
        (seq_cond EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_list (snd z)).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_format : T_Format EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_type EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_list EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__root_Format_list EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_list EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__ext_Format_list.

Opaque EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_format.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F1 (z : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type) : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_type :=
  (((EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__y2_Threshold_Relay_r17 z, (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__reportOnLeave_r17 z, (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__hysteresis_r17 z, (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__timeToTrigger_r17 z, tt))))), (
tt)).
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F2 (y : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_type) : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type j0 j1 j2 j3
  end.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__helper1 : (forall a : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type, EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond a -> EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_cond (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__helper2 : (forall a : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type, EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F2 (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__helper3 : (forall b : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_type, EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_cond b -> EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F2 b) /\ EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F1 (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond, EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Format : T_Format EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond :=
 proj2_format EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__list_format  EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F1 EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__F2 EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__helper1 EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__helper2 EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__helper3.

Opaque EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__cond EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Format.


Definition EventTriggerConfigInterRAT__eventId__ext__Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__eventId__ext__list.
Definition EventTriggerConfigInterRAT__eventId__ext__Format_list : EventTriggerConfigInterRAT__eventId__ext__Format_Type :=
  (EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Format, (EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Format, (EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Format, (EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Format, unit__Format)))).
Definition EventTriggerConfigInterRAT__eventId__ext__list__Format := Eval compute in choice_ext_format EventTriggerConfigInterRAT__eventId__ext__list EventTriggerConfigInterRAT__eventId__ext__Format_list.
Definition EventTriggerConfigInterRAT__eventId__ext__F1 (z : EventTriggerConfigInterRAT__eventId__ext__Type) : (choice EventTriggerConfigInterRAT__eventId__ext__list) :=
  match z with
   | EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16 t => existT _ 0 t
  | EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16 t => existT _ 1 t
  | EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17 t => existT _ 2 t
  | EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17 t => existT _ 3 t
  end.
Definition EventTriggerConfigInterRAT__eventId__ext__g := (fun n => typ_set (get_nth_typ EventTriggerConfigInterRAT__eventId__ext__list n)).
Definition EventTriggerConfigInterRAT__eventId__ext__F2 (y : choice EventTriggerConfigInterRAT__eventId__ext__list) : EventTriggerConfigInterRAT__eventId__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EventTriggerConfigInterRAT__eventId__ext__g n -> EventTriggerConfigInterRAT__eventId__ext__Type) with
    | 0 => fun (t : EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16__Type) => EventTriggerConfigInterRAT__eventId__ext__eventB1_UTRA_FDD_r16 t 
    | 1 => fun (t : EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16__Type) => EventTriggerConfigInterRAT__eventId__ext__eventB2_UTRA_FDD_r16 t 
    | 2 => fun (t : EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17__Type) => EventTriggerConfigInterRAT__eventId__ext__eventY1_Relay_r17 t 
    | 3 => fun (t : EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17__Type) => EventTriggerConfigInterRAT__eventId__ext__eventY2_Relay_r17 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : EventTriggerConfigInterRAT__eventId__ext__g (S (S (S (S x'))))) =>let t' :=
                       eq_rect (get_nth_typ EventTriggerConfigInterRAT__eventId__ext__list (S (S (S (S x')))))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len EventTriggerConfigInterRAT__eventId__ext__list (S (S (S (S x'))))
                       (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return EventTriggerConfigInterRAT__eventId__ext__Type with end) n0
                       end t0).

Lemma EventTriggerConfigInterRAT__eventId__ext__helper2 :  forall (y : EventTriggerConfigInterRAT__eventId__ext__Type), EventTriggerConfigInterRAT__eventId__ext__cond y -> choice_cond EventTriggerConfigInterRAT__eventId__ext__list (EventTriggerConfigInterRAT__eventId__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EventTriggerConfigInterRAT__eventId__ext__helper3 :  forall (y : EventTriggerConfigInterRAT__eventId__ext__Type), EventTriggerConfigInterRAT__eventId__ext__F2 (EventTriggerConfigInterRAT__eventId__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EventTriggerConfigInterRAT__eventId__ext__helper4 : (forall b : choice EventTriggerConfigInterRAT__eventId__ext__list, choice_cond EventTriggerConfigInterRAT__eventId__ext__list b -> EventTriggerConfigInterRAT__eventId__ext__cond (EventTriggerConfigInterRAT__eventId__ext__F2 b) /\ EventTriggerConfigInterRAT__eventId__ext__F1 (EventTriggerConfigInterRAT__eventId__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EventTriggerConfigInterRAT__eventId__ext__F1 EventTriggerConfigInterRAT__eventId__ext__F2.
Definition EventTriggerConfigInterRAT__eventId__ext__Format : T_Format EventTriggerConfigInterRAT__eventId__ext__Type EventTriggerConfigInterRAT__eventId__ext__cond :=
          proj2_format EventTriggerConfigInterRAT__eventId__ext__cond EventTriggerConfigInterRAT__eventId__ext__list__Format EventTriggerConfigInterRAT__eventId__ext__F1 EventTriggerConfigInterRAT__eventId__ext__F2 EventTriggerConfigInterRAT__eventId__ext__helper2 EventTriggerConfigInterRAT__eventId__ext__helper3 EventTriggerConfigInterRAT__eventId__ext__helper4.
Opaque EventTriggerConfigInterRAT__eventId__ext__cond EventTriggerConfigInterRAT__eventId__ext__Format.

Definition EventTriggerConfigInterRAT__eventId__Format : T_Format EventTriggerConfigInterRAT__eventId__Type EventTriggerConfigInterRAT__eventId__cond := sum_format EventTriggerConfigInterRAT__eventId__root__Format EventTriggerConfigInterRAT__eventId__ext__Format.
Opaque EventTriggerConfigInterRAT__eventId__cond EventTriggerConfigInterRAT__eventId__Format.

Definition EventTriggerConfigInterRAT__reportAmount__Format : T_Format EventTriggerConfigInterRAT__reportAmount__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EventTriggerConfigInterRAT__reportAmount__nat__Format EventTriggerConfigInterRAT__reportAmount__F1 EventTriggerConfigInterRAT__reportAmount__F2 EventTriggerConfigInterRAT__reportAmount__F1F2 EventTriggerConfigInterRAT__reportAmount__F2F1.

Opaque EventTriggerConfigInterRAT__reportAmount__cond EventTriggerConfigInterRAT__reportAmount__Format.

Definition EventTriggerConfigInterRAT__maxReportCells__Format : T_Format Z EventTriggerConfigInterRAT__maxReportCells__cond :=
 ranged_int_format (1) (maxCellReport) EventTriggerConfigInterRAT__maxReportCells__helper1 EventTriggerConfigInterRAT__maxReportCells__helper2.

Opaque EventTriggerConfigInterRAT__maxReportCells__cond EventTriggerConfigInterRAT__maxReportCells__Format.


Definition EventTriggerConfigInterRAT__ext0O__Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__ext0O__list.
Definition EventTriggerConfigInterRAT__ext0O__Format_list : EventTriggerConfigInterRAT__ext0O__Format_Type :=
  (MeasReportQuantityUTRA_FDD_r16__Format, unit_format).
Definition EventTriggerConfigInterRAT__ext0O__list__Format := (*Eval compute in *) seq_format EventTriggerConfigInterRAT__ext0O__list EventTriggerConfigInterRAT__ext0O__Format_list.
Definition EventTriggerConfigInterRAT__ext0O__F1 z :=
  (EventTriggerConfigInterRAT__ext0O__reportQuantityUTRA_FDD_r16 z, tt).
Definition EventTriggerConfigInterRAT__ext0O__F2 (y : seq_type EventTriggerConfigInterRAT__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__EventTriggerConfigInterRAT__ext0O__Type i0
  end.
Lemma EventTriggerConfigInterRAT__ext0O__F1F2_cond (z : EventTriggerConfigInterRAT__ext0O__Type)
  : EventTriggerConfigInterRAT__ext0O__cond z ->
  (seq_cond EventTriggerConfigInterRAT__ext0O__list (EventTriggerConfigInterRAT__ext0O__F1 z)).
intro H. unfold EventTriggerConfigInterRAT__ext0O__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfigInterRAT__ext0O__F1F2_cond2 (z : EventTriggerConfigInterRAT__ext0O__Type)
 : EventTriggerConfigInterRAT__ext0O__F2 (EventTriggerConfigInterRAT__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfigInterRAT__ext0O__F2F1_cond (y : seq_type EventTriggerConfigInterRAT__ext0O__list)
  : seq_cond EventTriggerConfigInterRAT__ext0O__list y ->
 (EventTriggerConfigInterRAT__ext0O__cond (EventTriggerConfigInterRAT__ext0O__F2 y)) /\  EventTriggerConfigInterRAT__ext0O__F1 (EventTriggerConfigInterRAT__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfigInterRAT__ext0O__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfigInterRAT__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfigInterRAT__ext0O__Format : T_Format EventTriggerConfigInterRAT__ext0O__Type EventTriggerConfigInterRAT__ext0O__cond :=
        proj2_format  EventTriggerConfigInterRAT__ext0O__cond EventTriggerConfigInterRAT__ext0O__list__Format
    EventTriggerConfigInterRAT__ext0O__F1 EventTriggerConfigInterRAT__ext0O__F2 EventTriggerConfigInterRAT__ext0O__F1F2_cond  EventTriggerConfigInterRAT__ext0O__F1F2_cond2 EventTriggerConfigInterRAT__ext0O__F2F1_cond.
Opaque EventTriggerConfigInterRAT__ext0O__cond EventTriggerConfigInterRAT__ext0O__Format.

Definition EventTriggerConfigInterRAT__ext0__check_all_none (b : EventTriggerConfigInterRAT__ext0O__Type) : bool :=
match b with 
  | make__EventTriggerConfigInterRAT__ext0O__Type None  => false 
  | _ => true 
 end.
Definition EventTriggerConfigInterRAT__ext0__Format : T_Format EventTriggerConfigInterRAT__ext0__Type EventTriggerConfigInterRAT__ext0__cond :=
  restrict_add_format EventTriggerConfigInterRAT__ext0__check_all_none EventTriggerConfigInterRAT__ext0O__Format.

Opaque EventTriggerConfigInterRAT__ext0__cond EventTriggerConfigInterRAT__ext0__Format.

Definition EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Format : T_Format EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__nat__Format EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2 EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1F2 EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2F1.

Opaque EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__cond EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Format.

Opaque EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__cond EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__Format.

Opaque EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__Format.

Opaque EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__cond EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__Format.


Definition EventTriggerConfigInterRAT__ext1O__Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__ext1O__list.
Definition EventTriggerConfigInterRAT__ext1O__Format_list : EventTriggerConfigInterRAT__ext1O__Format_Type :=
  (EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Format, (EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16__Format, (EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16__Format, (EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16__Format, unit_format)))).
Definition EventTriggerConfigInterRAT__ext1O__list__Format := (*Eval compute in *) seq_format EventTriggerConfigInterRAT__ext1O__list EventTriggerConfigInterRAT__ext1O__Format_list.
Definition EventTriggerConfigInterRAT__ext1O__F1 z :=
  (EventTriggerConfigInterRAT__ext1O__includeCommonLocationInfo_r16 z, (EventTriggerConfigInterRAT__ext1O__includeBT_Meas_r16 z, (EventTriggerConfigInterRAT__ext1O__includeWLAN_Meas_r16 z, (EventTriggerConfigInterRAT__ext1O__includeSensor_Meas_r16 z, tt)))).
Definition EventTriggerConfigInterRAT__ext1O__F2 (y : seq_type EventTriggerConfigInterRAT__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__EventTriggerConfigInterRAT__ext1O__Type i0 i1 i2 i3
  end.
Lemma EventTriggerConfigInterRAT__ext1O__F1F2_cond (z : EventTriggerConfigInterRAT__ext1O__Type)
  : EventTriggerConfigInterRAT__ext1O__cond z ->
  (seq_cond EventTriggerConfigInterRAT__ext1O__list (EventTriggerConfigInterRAT__ext1O__F1 z)).
intro H. unfold EventTriggerConfigInterRAT__ext1O__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfigInterRAT__ext1O__F1F2_cond2 (z : EventTriggerConfigInterRAT__ext1O__Type)
 : EventTriggerConfigInterRAT__ext1O__F2 (EventTriggerConfigInterRAT__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfigInterRAT__ext1O__F2F1_cond (y : seq_type EventTriggerConfigInterRAT__ext1O__list)
  : seq_cond EventTriggerConfigInterRAT__ext1O__list y ->
 (EventTriggerConfigInterRAT__ext1O__cond (EventTriggerConfigInterRAT__ext1O__F2 y)) /\  EventTriggerConfigInterRAT__ext1O__F1 (EventTriggerConfigInterRAT__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfigInterRAT__ext1O__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfigInterRAT__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfigInterRAT__ext1O__Format : T_Format EventTriggerConfigInterRAT__ext1O__Type EventTriggerConfigInterRAT__ext1O__cond :=
        proj2_format  EventTriggerConfigInterRAT__ext1O__cond EventTriggerConfigInterRAT__ext1O__list__Format
    EventTriggerConfigInterRAT__ext1O__F1 EventTriggerConfigInterRAT__ext1O__F2 EventTriggerConfigInterRAT__ext1O__F1F2_cond  EventTriggerConfigInterRAT__ext1O__F1F2_cond2 EventTriggerConfigInterRAT__ext1O__F2F1_cond.
Opaque EventTriggerConfigInterRAT__ext1O__cond EventTriggerConfigInterRAT__ext1O__Format.

Definition EventTriggerConfigInterRAT__ext1__check_all_none (b : EventTriggerConfigInterRAT__ext1O__Type) : bool :=
match b with 
  | make__EventTriggerConfigInterRAT__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition EventTriggerConfigInterRAT__ext1__Format : T_Format EventTriggerConfigInterRAT__ext1__Type EventTriggerConfigInterRAT__ext1__cond :=
  restrict_add_format EventTriggerConfigInterRAT__ext1__check_all_none EventTriggerConfigInterRAT__ext1O__Format.

Opaque EventTriggerConfigInterRAT__ext1__cond EventTriggerConfigInterRAT__ext1__Format.


Definition EventTriggerConfigInterRAT__ext2O__Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__ext2O__list.
Definition EventTriggerConfigInterRAT__ext2O__Format_list : EventTriggerConfigInterRAT__ext2O__Format_Type :=
  (SL_MeasReportQuantity_r16__Format, unit_format).
Definition EventTriggerConfigInterRAT__ext2O__list__Format := (*Eval compute in *) seq_format EventTriggerConfigInterRAT__ext2O__list EventTriggerConfigInterRAT__ext2O__Format_list.
Definition EventTriggerConfigInterRAT__ext2O__F1 z :=
  (EventTriggerConfigInterRAT__ext2O__reportQuantityRelay_r17 z, tt).
Definition EventTriggerConfigInterRAT__ext2O__F2 (y : seq_type EventTriggerConfigInterRAT__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__EventTriggerConfigInterRAT__ext2O__Type i0
  end.
Lemma EventTriggerConfigInterRAT__ext2O__F1F2_cond (z : EventTriggerConfigInterRAT__ext2O__Type)
  : EventTriggerConfigInterRAT__ext2O__cond z ->
  (seq_cond EventTriggerConfigInterRAT__ext2O__list (EventTriggerConfigInterRAT__ext2O__F1 z)).
intro H. unfold EventTriggerConfigInterRAT__ext2O__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfigInterRAT__ext2O__F1F2_cond2 (z : EventTriggerConfigInterRAT__ext2O__Type)
 : EventTriggerConfigInterRAT__ext2O__F2 (EventTriggerConfigInterRAT__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfigInterRAT__ext2O__F2F1_cond (y : seq_type EventTriggerConfigInterRAT__ext2O__list)
  : seq_cond EventTriggerConfigInterRAT__ext2O__list y ->
 (EventTriggerConfigInterRAT__ext2O__cond (EventTriggerConfigInterRAT__ext2O__F2 y)) /\  EventTriggerConfigInterRAT__ext2O__F1 (EventTriggerConfigInterRAT__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfigInterRAT__ext2O__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfigInterRAT__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfigInterRAT__ext2O__Format : T_Format EventTriggerConfigInterRAT__ext2O__Type EventTriggerConfigInterRAT__ext2O__cond :=
        proj2_format  EventTriggerConfigInterRAT__ext2O__cond EventTriggerConfigInterRAT__ext2O__list__Format
    EventTriggerConfigInterRAT__ext2O__F1 EventTriggerConfigInterRAT__ext2O__F2 EventTriggerConfigInterRAT__ext2O__F1F2_cond  EventTriggerConfigInterRAT__ext2O__F1F2_cond2 EventTriggerConfigInterRAT__ext2O__F2F1_cond.
Opaque EventTriggerConfigInterRAT__ext2O__cond EventTriggerConfigInterRAT__ext2O__Format.

Definition EventTriggerConfigInterRAT__ext2__check_all_none (b : EventTriggerConfigInterRAT__ext2O__Type) : bool :=
match b with 
  | make__EventTriggerConfigInterRAT__ext2O__Type None  => false 
  | _ => true 
 end.
Definition EventTriggerConfigInterRAT__ext2__Format : T_Format EventTriggerConfigInterRAT__ext2__Type EventTriggerConfigInterRAT__ext2__cond :=
  restrict_add_format EventTriggerConfigInterRAT__ext2__check_all_none EventTriggerConfigInterRAT__ext2O__Format.

Opaque EventTriggerConfigInterRAT__ext2__cond EventTriggerConfigInterRAT__ext2__Format.


Definition EventTriggerConfigInterRAT__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfigInterRAT__root_list.
Definition EventTriggerConfigInterRAT__root_Format_list : EventTriggerConfigInterRAT__root_Format_Type :=
  (EventTriggerConfigInterRAT__eventId__Format, (NR_RS_Type__Format, (ReportInterval__Format, (EventTriggerConfigInterRAT__reportAmount__Format, (MeasReportQuantity__Format, (EventTriggerConfigInterRAT__maxReportCells__Format, unit_format)))))).

Definition EventTriggerConfigInterRAT__ext_Format_Type := Eval cbn in get_formats EventTriggerConfigInterRAT__ext_list.
Definition EventTriggerConfigInterRAT__ext_Format_list : EventTriggerConfigInterRAT__ext_Format_Type :=
  (EventTriggerConfigInterRAT__ext0__Format, (EventTriggerConfigInterRAT__ext1__Format, (EventTriggerConfigInterRAT__ext2__Format, unit__Format))).

Definition EventTriggerConfigInterRAT__list_type : Set := (seq_type EventTriggerConfigInterRAT__root_list) * (seq_ext_type EventTriggerConfigInterRAT__ext_list).
Definition EventTriggerConfigInterRAT__list_cond (z : EventTriggerConfigInterRAT__list_type) : Prop :=
        (seq_cond EventTriggerConfigInterRAT__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfigInterRAT__ext_list (snd z)).
Definition EventTriggerConfigInterRAT__list_format : T_Format EventTriggerConfigInterRAT__list_type EventTriggerConfigInterRAT__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfigInterRAT__root_list EventTriggerConfigInterRAT__root_Format_list EventTriggerConfigInterRAT__ext_list EventTriggerConfigInterRAT__ext_Format_list.

Opaque EventTriggerConfigInterRAT__list_format.
Definition EventTriggerConfigInterRAT__F1 (z : EventTriggerConfigInterRAT__Type) : EventTriggerConfigInterRAT__list_type :=
  (((EventTriggerConfigInterRAT__eventId z, (EventTriggerConfigInterRAT__rsType z, (EventTriggerConfigInterRAT__reportInterval z, (EventTriggerConfigInterRAT__reportAmount z, (EventTriggerConfigInterRAT__reportQuantity z, (EventTriggerConfigInterRAT__maxReportCells z, tt))))))), (
(EventTriggerConfigInterRAT__ext0 z, (EventTriggerConfigInterRAT__ext1 z, (EventTriggerConfigInterRAT__ext2 z, tt))))).
Definition EventTriggerConfigInterRAT__F2 (y : EventTriggerConfigInterRAT__list_type) : EventTriggerConfigInterRAT__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), (i0, (i1, (i2, _))))=>
    make__EventTriggerConfigInterRAT__Type j0 j1 j2 j3 j4 j5 i0 i1 i2
  end.
Definition EventTriggerConfigInterRAT__helper1 : (forall a : EventTriggerConfigInterRAT__Type, EventTriggerConfigInterRAT__cond a -> EventTriggerConfigInterRAT__list_cond (EventTriggerConfigInterRAT__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__helper2 : (forall a : EventTriggerConfigInterRAT__Type, EventTriggerConfigInterRAT__F2 (EventTriggerConfigInterRAT__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigInterRAT__helper3 : (forall b : EventTriggerConfigInterRAT__list_type, EventTriggerConfigInterRAT__list_cond b -> EventTriggerConfigInterRAT__cond (EventTriggerConfigInterRAT__F2 b) /\ EventTriggerConfigInterRAT__F1 (EventTriggerConfigInterRAT__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfigInterRAT__cond, EventTriggerConfigInterRAT__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfigInterRAT__Format : T_Format EventTriggerConfigInterRAT__Type EventTriggerConfigInterRAT__cond :=
 proj2_format EventTriggerConfigInterRAT__cond EventTriggerConfigInterRAT__list_format  EventTriggerConfigInterRAT__F1 EventTriggerConfigInterRAT__F2 EventTriggerConfigInterRAT__helper1 EventTriggerConfigInterRAT__helper2 EventTriggerConfigInterRAT__helper3.

Opaque EventTriggerConfigInterRAT__cond EventTriggerConfigInterRAT__Format.

