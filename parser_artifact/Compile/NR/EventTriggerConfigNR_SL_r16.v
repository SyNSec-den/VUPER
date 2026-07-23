Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_CBR_r16.

Opaque SL_CBR_r16__cond SL_CBR_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type : Set :=
  make__EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type {
    EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__c1_Threshold_r16 : SL_CBR_r16__Type ;
    EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__hysteresis_r16 : Hysteresis__Type ;
    EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__timeToTrigger_r16 : TimeToTrigger__Type ;
}.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list := (
 Nor SL_CBR_r16__Type SL_CBR_r16__cond ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond z := 
  SL_CBR_r16__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__c1_Threshold_r16 z) /\
  Hysteresis__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__hysteresis_r16 z) /\
  TimeToTrigger__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__timeToTrigger_r16 z) /\
  True.

Require Import NR.SL_CBR_r16.

Opaque SL_CBR_r16__cond SL_CBR_r16__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type : Set :=
  make__EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type {
    EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__c2_Threshold_r16 : SL_CBR_r16__Type ;
    EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__hysteresis_r16 : Hysteresis__Type ;
    EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__timeToTrigger_r16 : TimeToTrigger__Type ;
}.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list := (
 Nor SL_CBR_r16__Type SL_CBR_r16__cond ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond z := 
  SL_CBR_r16__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__c2_Threshold_r16 z) /\
  Hysteresis__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__hysteresis_r16 z) /\
  TimeToTrigger__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__timeToTrigger_r16 z) /\
  True.


Inductive EventTriggerConfigNR_SL_r16__eventId_r16__root__Type : Set :=
  | EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1 : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type -> EventTriggerConfigNR_SL_r16__eventId_r16__root__Type
  | EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16 : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type -> EventTriggerConfigNR_SL_r16__eventId_r16__root__Type
.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__list : list typ := (
typ_cons EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond ::
typ_cons EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond ::
 nil).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__cond (c : EventTriggerConfigNR_SL_r16__eventId_r16__root__Type) := 
  match c with
  | EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1 t => EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond t 
  | EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16 t => EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond t 
  end.

Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__len_helper1 : to_bit_sz (length EventTriggerConfigNR_SL_r16__eventId_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__len_helper2 : 2 <= length2 EventTriggerConfigNR_SL_r16__eventId_r16__root__list.
 simpl. lia. Qed.

Definition EventTriggerConfigNR_SL_r16__eventId_r16__ext__Type : Set := Empty_set.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__ext__cond (c : EventTriggerConfigNR_SL_r16__eventId_r16__ext__Type) := True.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__Type : Set := EventTriggerConfigNR_SL_r16__eventId_r16__root__Type + EventTriggerConfigNR_SL_r16__eventId_r16__ext__Type.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__cond :=
  sum_cond EventTriggerConfigNR_SL_r16__eventId_r16__root__cond EventTriggerConfigNR_SL_r16__eventId_r16__ext__cond.
Require Import NR.ReportInterval.

Opaque ReportInterval__cond ReportInterval__Format.

Inductive EventTriggerConfigNR_SL_r16__reportAmount_r16__Type : Set :=
 | EventTriggerConfigNR_SL_r16__reportAmount_r16__r1
 | EventTriggerConfigNR_SL_r16__reportAmount_r16__r2
 | EventTriggerConfigNR_SL_r16__reportAmount_r16__r4
 | EventTriggerConfigNR_SL_r16__reportAmount_r16__r8
 | EventTriggerConfigNR_SL_r16__reportAmount_r16__r16
 | EventTriggerConfigNR_SL_r16__reportAmount_r16__r32
 | EventTriggerConfigNR_SL_r16__reportAmount_r16__r64
 | EventTriggerConfigNR_SL_r16__reportAmount_r16__infinity
.
Definition EventTriggerConfigNR_SL_r16__reportAmount_r16__cond := (fun (_ : EventTriggerConfigNR_SL_r16__reportAmount_r16__Type) => True).
Lemma EventTriggerConfigNR_SL_r16__reportAmount_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EventTriggerConfigNR_SL_r16__reportAmount_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 EventTriggerConfigNR_SL_r16__reportAmount_r16__nat__helper.

Definition EventTriggerConfigNR_SL_r16__reportAmount_r16__F1 t :=
  match t with
  | EventTriggerConfigNR_SL_r16__reportAmount_r16__r1 => 0
  | EventTriggerConfigNR_SL_r16__reportAmount_r16__r2 => 1
  | EventTriggerConfigNR_SL_r16__reportAmount_r16__r4 => 2
  | EventTriggerConfigNR_SL_r16__reportAmount_r16__r8 => 3
  | EventTriggerConfigNR_SL_r16__reportAmount_r16__r16 => 4
  | EventTriggerConfigNR_SL_r16__reportAmount_r16__r32 => 5
  | EventTriggerConfigNR_SL_r16__reportAmount_r16__r64 => 6
  | EventTriggerConfigNR_SL_r16__reportAmount_r16__infinity => 7
  end.
Definition EventTriggerConfigNR_SL_r16__reportAmount_r16__F2 n :=
  match n with
  | 0 => EventTriggerConfigNR_SL_r16__reportAmount_r16__r1
  | 1 => EventTriggerConfigNR_SL_r16__reportAmount_r16__r2
  | 2 => EventTriggerConfigNR_SL_r16__reportAmount_r16__r4
  | 3 => EventTriggerConfigNR_SL_r16__reportAmount_r16__r8
  | 4 => EventTriggerConfigNR_SL_r16__reportAmount_r16__r16
  | 5 => EventTriggerConfigNR_SL_r16__reportAmount_r16__r32
  | 6 => EventTriggerConfigNR_SL_r16__reportAmount_r16__r64
  | 7 => EventTriggerConfigNR_SL_r16__reportAmount_r16__infinity
  | _ => EventTriggerConfigNR_SL_r16__reportAmount_r16__r1
  end.
Lemma EventTriggerConfigNR_SL_r16__reportAmount_r16__F1F2 : forall x : EventTriggerConfigNR_SL_r16__reportAmount_r16__Type, (EventTriggerConfigNR_SL_r16__reportAmount_r16__F1 x <= 7) /\ EventTriggerConfigNR_SL_r16__reportAmount_r16__F2 (EventTriggerConfigNR_SL_r16__reportAmount_r16__F1 x) = x. imp_solve. Qed.
Lemma EventTriggerConfigNR_SL_r16__reportAmount_r16__F2F1 : forall (y : nat) (H : y <= 7), EventTriggerConfigNR_SL_r16__reportAmount_r16__F1 (EventTriggerConfigNR_SL_r16__reportAmount_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasReportQuantity_r16.

Opaque MeasReportQuantity_r16__cond MeasReportQuantity_r16__Format.

Record EventTriggerConfigNR_SL_r16__Type : Set :=
  make__EventTriggerConfigNR_SL_r16__Type {
    EventTriggerConfigNR_SL_r16__eventId_r16 : EventTriggerConfigNR_SL_r16__eventId_r16__Type ;
    EventTriggerConfigNR_SL_r16__reportInterval_r16 : ReportInterval__Type ;
    EventTriggerConfigNR_SL_r16__reportAmount_r16 : EventTriggerConfigNR_SL_r16__reportAmount_r16__Type ;
    EventTriggerConfigNR_SL_r16__reportQuantity_r16 : MeasReportQuantity_r16__Type ;
}.
Definition EventTriggerConfigNR_SL_r16__root_list : list seq_elem := (
 Nor EventTriggerConfigNR_SL_r16__eventId_r16__Type EventTriggerConfigNR_SL_r16__eventId_r16__cond ::
 Nor ReportInterval__Type ReportInterval__cond ::
 Nor EventTriggerConfigNR_SL_r16__reportAmount_r16__Type EventTriggerConfigNR_SL_r16__reportAmount_r16__cond ::
 Nor MeasReportQuantity_r16__Type MeasReportQuantity_r16__cond ::
 nil).
Definition EventTriggerConfigNR_SL_r16__ext_list : list typ := (
  nil).
Definition EventTriggerConfigNR_SL_r16__cond (z : EventTriggerConfigNR_SL_r16__Type) := 
(  EventTriggerConfigNR_SL_r16__eventId_r16__cond (EventTriggerConfigNR_SL_r16__eventId_r16 z) /\
  ReportInterval__cond (EventTriggerConfigNR_SL_r16__reportInterval_r16 z) /\
  EventTriggerConfigNR_SL_r16__reportAmount_r16__cond (EventTriggerConfigNR_SL_r16__reportAmount_r16 z) /\
  MeasReportQuantity_r16__cond (EventTriggerConfigNR_SL_r16__reportQuantity_r16 z) /\
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

Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Format_Type := Eval cbn in seq_format_prod EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Format_list : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Format_Type :=
  (SL_CBR_r16__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format))).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list__Format := (*Eval compute in *) seq_format EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Format_list.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1 z :=
  (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__c1_Threshold_r16 z, (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__hysteresis_r16 z, (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__timeToTrigger_r16 z, tt))).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F2 (y : seq_type EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type i0 i1 i2
  end.
Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1F2_cond (z : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type)
  : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond z ->
  (seq_cond EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1 z)).
intro H. unfold EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1F2_cond2 (z : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type)
 : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F2 (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F2F1_cond (y : seq_type EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list)
  : seq_cond EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list y ->
 (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F2 y)) /\  EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1 (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Format : T_Format EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond :=
        proj2_format  EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__list__Format
    EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1 EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F2 EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1F2_cond  EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F1F2_cond2 EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__F2F1_cond.
Opaque EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__cond EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Format.


Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Format_Type := Eval cbn in seq_format_prod EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Format_list : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Format_Type :=
  (SL_CBR_r16__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format))).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list__Format := (*Eval compute in *) seq_format EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Format_list.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1 z :=
  (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__c2_Threshold_r16 z, (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__hysteresis_r16 z, (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__timeToTrigger_r16 z, tt))).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F2 (y : seq_type EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type i0 i1 i2
  end.
Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1F2_cond (z : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type)
  : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond z ->
  (seq_cond EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1 z)).
intro H. unfold EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond in H. simpl. auto. Qed.
Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1F2_cond2 (z : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type)
 : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F2 (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F2F1_cond (y : seq_type EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list)
  : seq_cond EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list y ->
 (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F2 y)) /\  EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1 (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond. simpl in *. auto.
 - simpl. unfold EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Format : T_Format EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond :=
        proj2_format  EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__list__Format
    EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1 EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F2 EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1F2_cond  EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F1F2_cond2 EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__F2F1_cond.
Opaque EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__cond EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Format.


Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__Format_Type := Eval cbn in get_formats EventTriggerConfigNR_SL_r16__eventId_r16__root__list.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__Format_list : EventTriggerConfigNR_SL_r16__eventId_r16__root__Format_Type :=
  (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Format, (EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Format, unit__Format)).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__list__Format := Eval compute in choice_format EventTriggerConfigNR_SL_r16__eventId_r16__root__list EventTriggerConfigNR_SL_r16__eventId_r16__root__len_helper1 EventTriggerConfigNR_SL_r16__eventId_r16__root__len_helper2  EventTriggerConfigNR_SL_r16__eventId_r16__root__Format_list.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__F1 (z : EventTriggerConfigNR_SL_r16__eventId_r16__root__Type) : (choice EventTriggerConfigNR_SL_r16__eventId_r16__root__list) :=
  match z with
   | EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1 t => existT _ 0 t
  | EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16 t => existT _ 1 t
  end.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__g := (fun n => typ_set (get_nth_typ EventTriggerConfigNR_SL_r16__eventId_r16__root__list n)).
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__F2 (y : choice EventTriggerConfigNR_SL_r16__eventId_r16__root__list) : EventTriggerConfigNR_SL_r16__eventId_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EventTriggerConfigNR_SL_r16__eventId_r16__root__g n -> EventTriggerConfigNR_SL_r16__eventId_r16__root__Type) with
    | 0 => fun (t : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1__Type) => EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC1 t 
    | 1 => fun (t : EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16__Type) => EventTriggerConfigNR_SL_r16__eventId_r16__root__eventC2_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : EventTriggerConfigNR_SL_r16__eventId_r16__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ EventTriggerConfigNR_SL_r16__eventId_r16__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len EventTriggerConfigNR_SL_r16__eventId_r16__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return EventTriggerConfigNR_SL_r16__eventId_r16__root__Type with end) n0
           end t0).

Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__helper2 :  forall (y : EventTriggerConfigNR_SL_r16__eventId_r16__root__Type), EventTriggerConfigNR_SL_r16__eventId_r16__root__cond y -> choice_cond EventTriggerConfigNR_SL_r16__eventId_r16__root__list (EventTriggerConfigNR_SL_r16__eventId_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__helper3 :  forall (y : EventTriggerConfigNR_SL_r16__eventId_r16__root__Type), EventTriggerConfigNR_SL_r16__eventId_r16__root__F2 (EventTriggerConfigNR_SL_r16__eventId_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EventTriggerConfigNR_SL_r16__eventId_r16__root__helper4 : (forall b : choice EventTriggerConfigNR_SL_r16__eventId_r16__root__list, choice_cond EventTriggerConfigNR_SL_r16__eventId_r16__root__list b -> EventTriggerConfigNR_SL_r16__eventId_r16__root__cond (EventTriggerConfigNR_SL_r16__eventId_r16__root__F2 b) /\ EventTriggerConfigNR_SL_r16__eventId_r16__root__F1 (EventTriggerConfigNR_SL_r16__eventId_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EventTriggerConfigNR_SL_r16__eventId_r16__root__F1 EventTriggerConfigNR_SL_r16__eventId_r16__root__F2.
Definition EventTriggerConfigNR_SL_r16__eventId_r16__root__Format : T_Format EventTriggerConfigNR_SL_r16__eventId_r16__root__Type EventTriggerConfigNR_SL_r16__eventId_r16__root__cond :=
  (* Eval compute in *) proj2_format EventTriggerConfigNR_SL_r16__eventId_r16__root__cond EventTriggerConfigNR_SL_r16__eventId_r16__root__list__Format EventTriggerConfigNR_SL_r16__eventId_r16__root__F1 EventTriggerConfigNR_SL_r16__eventId_r16__root__F2 EventTriggerConfigNR_SL_r16__eventId_r16__root__helper2 EventTriggerConfigNR_SL_r16__eventId_r16__root__helper3 EventTriggerConfigNR_SL_r16__eventId_r16__root__helper4.
Opaque EventTriggerConfigNR_SL_r16__eventId_r16__root__cond EventTriggerConfigNR_SL_r16__eventId_r16__root__Format.

Definition EventTriggerConfigNR_SL_r16__eventId_r16__ext__Format : T_Format EventTriggerConfigNR_SL_r16__eventId_r16__ext__Type EventTriggerConfigNR_SL_r16__eventId_r16__ext__cond := empty_format.
Opaque EventTriggerConfigNR_SL_r16__eventId_r16__ext__cond EventTriggerConfigNR_SL_r16__eventId_r16__ext__Format.

Definition EventTriggerConfigNR_SL_r16__eventId_r16__Format : T_Format EventTriggerConfigNR_SL_r16__eventId_r16__Type EventTriggerConfigNR_SL_r16__eventId_r16__cond := sum_format EventTriggerConfigNR_SL_r16__eventId_r16__root__Format EventTriggerConfigNR_SL_r16__eventId_r16__ext__Format.
Opaque EventTriggerConfigNR_SL_r16__eventId_r16__cond EventTriggerConfigNR_SL_r16__eventId_r16__Format.

Definition EventTriggerConfigNR_SL_r16__reportAmount_r16__Format : T_Format EventTriggerConfigNR_SL_r16__reportAmount_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EventTriggerConfigNR_SL_r16__reportAmount_r16__nat__Format EventTriggerConfigNR_SL_r16__reportAmount_r16__F1 EventTriggerConfigNR_SL_r16__reportAmount_r16__F2 EventTriggerConfigNR_SL_r16__reportAmount_r16__F1F2 EventTriggerConfigNR_SL_r16__reportAmount_r16__F2F1.

Opaque EventTriggerConfigNR_SL_r16__reportAmount_r16__cond EventTriggerConfigNR_SL_r16__reportAmount_r16__Format.


Definition EventTriggerConfigNR_SL_r16__root_Format_Type := Eval cbn in seq_format_prod EventTriggerConfigNR_SL_r16__root_list.
Definition EventTriggerConfigNR_SL_r16__root_Format_list : EventTriggerConfigNR_SL_r16__root_Format_Type :=
  (EventTriggerConfigNR_SL_r16__eventId_r16__Format, (ReportInterval__Format, (EventTriggerConfigNR_SL_r16__reportAmount_r16__Format, (MeasReportQuantity_r16__Format, unit_format)))).

Definition EventTriggerConfigNR_SL_r16__ext_Format_Type := Eval cbn in get_formats EventTriggerConfigNR_SL_r16__ext_list.
Definition EventTriggerConfigNR_SL_r16__ext_Format_list : EventTriggerConfigNR_SL_r16__ext_Format_Type :=
  unit__Format.

Definition EventTriggerConfigNR_SL_r16__list_type : Set := (seq_type EventTriggerConfigNR_SL_r16__root_list) * (seq_ext_type EventTriggerConfigNR_SL_r16__ext_list).
Definition EventTriggerConfigNR_SL_r16__list_cond (z : EventTriggerConfigNR_SL_r16__list_type) : Prop :=
        (seq_cond EventTriggerConfigNR_SL_r16__root_list (fst z)) /\ (seq_ext_cond EventTriggerConfigNR_SL_r16__ext_list (snd z)).
Definition EventTriggerConfigNR_SL_r16__list_format : T_Format EventTriggerConfigNR_SL_r16__list_type EventTriggerConfigNR_SL_r16__list_cond :=
 (* Eval compute in *) seq_ext_format EventTriggerConfigNR_SL_r16__root_list EventTriggerConfigNR_SL_r16__root_Format_list EventTriggerConfigNR_SL_r16__ext_list EventTriggerConfigNR_SL_r16__ext_Format_list.

Opaque EventTriggerConfigNR_SL_r16__list_format.
Definition EventTriggerConfigNR_SL_r16__F1 (z : EventTriggerConfigNR_SL_r16__Type) : EventTriggerConfigNR_SL_r16__list_type :=
  (((EventTriggerConfigNR_SL_r16__eventId_r16 z, (EventTriggerConfigNR_SL_r16__reportInterval_r16 z, (EventTriggerConfigNR_SL_r16__reportAmount_r16 z, (EventTriggerConfigNR_SL_r16__reportQuantity_r16 z, tt))))), (
tt)).
Definition EventTriggerConfigNR_SL_r16__F2 (y : EventTriggerConfigNR_SL_r16__list_type) : EventTriggerConfigNR_SL_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__EventTriggerConfigNR_SL_r16__Type j0 j1 j2 j3
  end.
Definition EventTriggerConfigNR_SL_r16__helper1 : (forall a : EventTriggerConfigNR_SL_r16__Type, EventTriggerConfigNR_SL_r16__cond a -> EventTriggerConfigNR_SL_r16__list_cond (EventTriggerConfigNR_SL_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigNR_SL_r16__helper2 : (forall a : EventTriggerConfigNR_SL_r16__Type, EventTriggerConfigNR_SL_r16__F2 (EventTriggerConfigNR_SL_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EventTriggerConfigNR_SL_r16__helper3 : (forall b : EventTriggerConfigNR_SL_r16__list_type, EventTriggerConfigNR_SL_r16__list_cond b -> EventTriggerConfigNR_SL_r16__cond (EventTriggerConfigNR_SL_r16__F2 b) /\ EventTriggerConfigNR_SL_r16__F1 (EventTriggerConfigNR_SL_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EventTriggerConfigNR_SL_r16__cond, EventTriggerConfigNR_SL_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EventTriggerConfigNR_SL_r16__Format : T_Format EventTriggerConfigNR_SL_r16__Type EventTriggerConfigNR_SL_r16__cond :=
 proj2_format EventTriggerConfigNR_SL_r16__cond EventTriggerConfigNR_SL_r16__list_format  EventTriggerConfigNR_SL_r16__F1 EventTriggerConfigNR_SL_r16__F2 EventTriggerConfigNR_SL_r16__helper1 EventTriggerConfigNR_SL_r16__helper2 EventTriggerConfigNR_SL_r16__helper3.

Opaque EventTriggerConfigNR_SL_r16__cond EventTriggerConfigNR_SL_r16__Format.

