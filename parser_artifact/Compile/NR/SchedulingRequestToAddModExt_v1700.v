Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Type : Set :=
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms192
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms256
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms320
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms384
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms448
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms512
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms576
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms640
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms1082
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare7
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare6
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare5
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare4
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare3
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare2
 | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare1
.
Definition SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__cond := (fun (_ : SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Type) => True).
Lemma SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__nat__helper.

Definition SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F1 t :=
  match t with
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms192 => 0
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms256 => 1
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms320 => 2
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms384 => 3
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms448 => 4
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms512 => 5
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms576 => 6
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms640 => 7
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms1082 => 8
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare7 => 9
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare6 => 10
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare5 => 11
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare4 => 12
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare3 => 13
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare2 => 14
  | SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare1 => 15
  end.
Definition SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F2 n :=
  match n with
  | 0 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms192
  | 1 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms256
  | 2 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms320
  | 3 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms384
  | 4 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms448
  | 5 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms512
  | 6 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms576
  | 7 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms640
  | 8 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms1082
  | 9 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare7
  | 10 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare6
  | 11 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare5
  | 12 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare4
  | 13 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare3
  | 14 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare2
  | 15 => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__spare1
  | _ => SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__ms192
  end.
Lemma SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F1F2 : forall x : SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Type, (SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F1 x <= 15) /\ SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F2 (SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F1 x) = x. imp_solve. Qed.
Lemma SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F2F1 : forall (y : nat) (H : y <= 15), SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F1 (SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F2 y) = y. enum_solve H y. Qed.

Record SchedulingRequestToAddModExt_v1700__Type : Set :=
  make__SchedulingRequestToAddModExt_v1700__Type {
    SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700 : option SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Type ;
}.
Definition SchedulingRequestToAddModExt_v1700__list := (
 Opt SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Type SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__cond ::
 nil).
Definition SchedulingRequestToAddModExt_v1700__cond z := 
  opt_cond SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__cond (SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700 z) /\
  True.


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
Definition SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Format : T_Format SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__nat__Format SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F1 SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F2 SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F1F2 SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__F2F1.

Opaque SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__cond SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Format.


Definition SchedulingRequestToAddModExt_v1700__Format_Type := Eval cbn in seq_format_prod SchedulingRequestToAddModExt_v1700__list.
Definition SchedulingRequestToAddModExt_v1700__Format_list : SchedulingRequestToAddModExt_v1700__Format_Type :=
  (SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700__Format, unit_format).
Definition SchedulingRequestToAddModExt_v1700__list__Format := (*Eval compute in *) seq_format SchedulingRequestToAddModExt_v1700__list SchedulingRequestToAddModExt_v1700__Format_list.
Definition SchedulingRequestToAddModExt_v1700__F1 z :=
  (SchedulingRequestToAddModExt_v1700__sr_ProhibitTimer_v1700 z, tt).
Definition SchedulingRequestToAddModExt_v1700__F2 (y : seq_type SchedulingRequestToAddModExt_v1700__list) :=
  match y with
  | (i0, _)=>
    make__SchedulingRequestToAddModExt_v1700__Type i0
  end.
Lemma SchedulingRequestToAddModExt_v1700__F1F2_cond (z : SchedulingRequestToAddModExt_v1700__Type)
  : SchedulingRequestToAddModExt_v1700__cond z ->
  (seq_cond SchedulingRequestToAddModExt_v1700__list (SchedulingRequestToAddModExt_v1700__F1 z)).
intro H. unfold SchedulingRequestToAddModExt_v1700__cond in H. simpl. auto. Qed.
Lemma SchedulingRequestToAddModExt_v1700__F1F2_cond2 (z : SchedulingRequestToAddModExt_v1700__Type)
 : SchedulingRequestToAddModExt_v1700__F2 (SchedulingRequestToAddModExt_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SchedulingRequestToAddModExt_v1700__F2F1_cond (y : seq_type SchedulingRequestToAddModExt_v1700__list)
  : seq_cond SchedulingRequestToAddModExt_v1700__list y ->
 (SchedulingRequestToAddModExt_v1700__cond (SchedulingRequestToAddModExt_v1700__F2 y)) /\  SchedulingRequestToAddModExt_v1700__F1 (SchedulingRequestToAddModExt_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SchedulingRequestToAddModExt_v1700__cond. simpl in *. auto.
 - simpl. unfold SchedulingRequestToAddModExt_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SchedulingRequestToAddModExt_v1700__Format : T_Format SchedulingRequestToAddModExt_v1700__Type SchedulingRequestToAddModExt_v1700__cond :=
        proj2_format  SchedulingRequestToAddModExt_v1700__cond SchedulingRequestToAddModExt_v1700__list__Format
    SchedulingRequestToAddModExt_v1700__F1 SchedulingRequestToAddModExt_v1700__F2 SchedulingRequestToAddModExt_v1700__F1F2_cond  SchedulingRequestToAddModExt_v1700__F1F2_cond2 SchedulingRequestToAddModExt_v1700__F2F1_cond.
Opaque SchedulingRequestToAddModExt_v1700__cond SchedulingRequestToAddModExt_v1700__Format.

