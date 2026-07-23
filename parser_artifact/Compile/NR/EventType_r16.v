Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasTriggerQuantity.

Opaque MeasTriggerQuantity__cond MeasTriggerQuantity__Format.

Require Import NR.Hysteresis.

Opaque Hysteresis__cond Hysteresis__Format.

Require Import NR.TimeToTrigger.

Opaque TimeToTrigger__cond TimeToTrigger__Format.

Record EventType_r16__root__eventL1__Type : Set :=
  make__EventType_r16__root__eventL1__Type {
    EventType_r16__root__eventL1__l1_Threshold : MeasTriggerQuantity__Type ;
    EventType_r16__root__eventL1__hysteresis : Hysteresis__Type ;
    EventType_r16__root__eventL1__timeToTrigger : TimeToTrigger__Type ;
}.
Definition EventType_r16__root__eventL1__list := (
 Nor MeasTriggerQuantity__Type MeasTriggerQuantity__cond ::
 Nor Hysteresis__Type Hysteresis__cond ::
 Nor TimeToTrigger__Type TimeToTrigger__cond ::
 nil).
Definition EventType_r16__root__eventL1__cond z := 
  MeasTriggerQuantity__cond (EventType_r16__root__eventL1__l1_Threshold z) /\
  Hysteresis__cond (EventType_r16__root__eventL1__hysteresis z) /\
  TimeToTrigger__cond (EventType_r16__root__eventL1__timeToTrigger z) /\
  True.


Inductive EventType_r16__root__Type : Set :=
  | EventType_r16__root__outOfCoverage : unit -> EventType_r16__root__Type
  | EventType_r16__root__eventL1 : EventType_r16__root__eventL1__Type -> EventType_r16__root__Type
.
Definition EventType_r16__root__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons EventType_r16__root__eventL1__Type EventType_r16__root__eventL1__cond ::
 nil).
Definition EventType_r16__root__cond (c : EventType_r16__root__Type) := 
  match c with
  | EventType_r16__root__outOfCoverage t => (fun _ => True) t 
  | EventType_r16__root__eventL1 t => EventType_r16__root__eventL1__cond t 
  end.

Lemma EventType_r16__root__len_helper1 : to_bit_sz (length EventType_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma EventType_r16__root__len_helper2 : 2 <= length2 EventType_r16__root__list.
 simpl. lia. Qed.

Definition EventType_r16__ext__Type : Set := Empty_set.
Definition EventType_r16__ext__cond (c : EventType_r16__ext__Type) := True.
Definition EventType_r16__Type : Set := EventType_r16__root__Type + EventType_r16__ext__Type.
Definition EventType_r16__cond :=
  sum_cond EventType_r16__root__cond EventType_r16__ext__cond.

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

Definition EventType_r16__root__eventL1__Format_Type := Eval cbn in seq_format_prod EventType_r16__root__eventL1__list.
Definition EventType_r16__root__eventL1__Format_list : EventType_r16__root__eventL1__Format_Type :=
  (MeasTriggerQuantity__Format, (Hysteresis__Format, (TimeToTrigger__Format, unit_format))).
Definition EventType_r16__root__eventL1__list__Format := (*Eval compute in *) seq_format EventType_r16__root__eventL1__list EventType_r16__root__eventL1__Format_list.
Definition EventType_r16__root__eventL1__F1 z :=
  (EventType_r16__root__eventL1__l1_Threshold z, (EventType_r16__root__eventL1__hysteresis z, (EventType_r16__root__eventL1__timeToTrigger z, tt))).
Definition EventType_r16__root__eventL1__F2 (y : seq_type EventType_r16__root__eventL1__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__EventType_r16__root__eventL1__Type i0 i1 i2
  end.
Lemma EventType_r16__root__eventL1__F1F2_cond (z : EventType_r16__root__eventL1__Type)
  : EventType_r16__root__eventL1__cond z ->
  (seq_cond EventType_r16__root__eventL1__list (EventType_r16__root__eventL1__F1 z)).
intro H. unfold EventType_r16__root__eventL1__cond in H. simpl. auto. Qed.
Lemma EventType_r16__root__eventL1__F1F2_cond2 (z : EventType_r16__root__eventL1__Type)
 : EventType_r16__root__eventL1__F2 (EventType_r16__root__eventL1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma EventType_r16__root__eventL1__F2F1_cond (y : seq_type EventType_r16__root__eventL1__list)
  : seq_cond EventType_r16__root__eventL1__list y ->
 (EventType_r16__root__eventL1__cond (EventType_r16__root__eventL1__F2 y)) /\  EventType_r16__root__eventL1__F1 (EventType_r16__root__eventL1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold EventType_r16__root__eventL1__cond. simpl in *. auto.
 - simpl. unfold EventType_r16__root__eventL1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition EventType_r16__root__eventL1__Format : T_Format EventType_r16__root__eventL1__Type EventType_r16__root__eventL1__cond :=
        proj2_format  EventType_r16__root__eventL1__cond EventType_r16__root__eventL1__list__Format
    EventType_r16__root__eventL1__F1 EventType_r16__root__eventL1__F2 EventType_r16__root__eventL1__F1F2_cond  EventType_r16__root__eventL1__F1F2_cond2 EventType_r16__root__eventL1__F2F1_cond.
Opaque EventType_r16__root__eventL1__cond EventType_r16__root__eventL1__Format.


Definition EventType_r16__root__Format_Type := Eval cbn in get_formats EventType_r16__root__list.
Definition EventType_r16__root__Format_list : EventType_r16__root__Format_Type :=
  (unit__Format, (EventType_r16__root__eventL1__Format, unit__Format)).
Definition EventType_r16__root__list__Format := Eval compute in choice_format EventType_r16__root__list EventType_r16__root__len_helper1 EventType_r16__root__len_helper2  EventType_r16__root__Format_list.
Definition EventType_r16__root__F1 (z : EventType_r16__root__Type) : (choice EventType_r16__root__list) :=
  match z with
   | EventType_r16__root__outOfCoverage t => existT _ 0 t
  | EventType_r16__root__eventL1 t => existT _ 1 t
  end.
Definition EventType_r16__root__g := (fun n => typ_set (get_nth_typ EventType_r16__root__list n)).
Definition EventType_r16__root__F2 (y : choice EventType_r16__root__list) : EventType_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (EventType_r16__root__g n -> EventType_r16__root__Type) with
    | 0 => fun (t : unit) => EventType_r16__root__outOfCoverage t 
    | 1 => fun (t : EventType_r16__root__eventL1__Type) => EventType_r16__root__eventL1 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : EventType_r16__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ EventType_r16__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len EventType_r16__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return EventType_r16__root__Type with end) n0
           end t0).

Lemma EventType_r16__root__helper2 :  forall (y : EventType_r16__root__Type), EventType_r16__root__cond y -> choice_cond EventType_r16__root__list (EventType_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma EventType_r16__root__helper3 :  forall (y : EventType_r16__root__Type), EventType_r16__root__F2 (EventType_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma EventType_r16__root__helper4 : (forall b : choice EventType_r16__root__list, choice_cond EventType_r16__root__list b -> EventType_r16__root__cond (EventType_r16__root__F2 b) /\ EventType_r16__root__F1 (EventType_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length EventType_r16__root__F1 EventType_r16__root__F2.
Definition EventType_r16__root__Format : T_Format EventType_r16__root__Type EventType_r16__root__cond :=
  (* Eval compute in *) proj2_format EventType_r16__root__cond EventType_r16__root__list__Format EventType_r16__root__F1 EventType_r16__root__F2 EventType_r16__root__helper2 EventType_r16__root__helper3 EventType_r16__root__helper4.
Opaque EventType_r16__root__cond EventType_r16__root__Format.

Definition EventType_r16__ext__Format : T_Format EventType_r16__ext__Type EventType_r16__ext__cond := empty_format.
Opaque EventType_r16__ext__cond EventType_r16__ext__Format.

Definition EventType_r16__Format : T_Format EventType_r16__Type EventType_r16__cond := sum_format EventType_r16__root__Format EventType_r16__ext__Format.
Opaque EventType_r16__cond EventType_r16__Format.

