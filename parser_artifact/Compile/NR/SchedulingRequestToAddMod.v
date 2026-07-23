Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SchedulingRequestId.

Opaque SchedulingRequestId__cond SchedulingRequestId__Format.

Inductive SchedulingRequestToAddMod__sr_ProhibitTimer__Type : Set :=
 | SchedulingRequestToAddMod__sr_ProhibitTimer__ms1
 | SchedulingRequestToAddMod__sr_ProhibitTimer__ms2
 | SchedulingRequestToAddMod__sr_ProhibitTimer__ms4
 | SchedulingRequestToAddMod__sr_ProhibitTimer__ms8
 | SchedulingRequestToAddMod__sr_ProhibitTimer__ms16
 | SchedulingRequestToAddMod__sr_ProhibitTimer__ms32
 | SchedulingRequestToAddMod__sr_ProhibitTimer__ms64
 | SchedulingRequestToAddMod__sr_ProhibitTimer__ms128
.
Definition SchedulingRequestToAddMod__sr_ProhibitTimer__cond := (fun (_ : SchedulingRequestToAddMod__sr_ProhibitTimer__Type) => True).
Lemma SchedulingRequestToAddMod__sr_ProhibitTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SchedulingRequestToAddMod__sr_ProhibitTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SchedulingRequestToAddMod__sr_ProhibitTimer__nat__helper.

Definition SchedulingRequestToAddMod__sr_ProhibitTimer__F1 t :=
  match t with
  | SchedulingRequestToAddMod__sr_ProhibitTimer__ms1 => 0
  | SchedulingRequestToAddMod__sr_ProhibitTimer__ms2 => 1
  | SchedulingRequestToAddMod__sr_ProhibitTimer__ms4 => 2
  | SchedulingRequestToAddMod__sr_ProhibitTimer__ms8 => 3
  | SchedulingRequestToAddMod__sr_ProhibitTimer__ms16 => 4
  | SchedulingRequestToAddMod__sr_ProhibitTimer__ms32 => 5
  | SchedulingRequestToAddMod__sr_ProhibitTimer__ms64 => 6
  | SchedulingRequestToAddMod__sr_ProhibitTimer__ms128 => 7
  end.
Definition SchedulingRequestToAddMod__sr_ProhibitTimer__F2 n :=
  match n with
  | 0 => SchedulingRequestToAddMod__sr_ProhibitTimer__ms1
  | 1 => SchedulingRequestToAddMod__sr_ProhibitTimer__ms2
  | 2 => SchedulingRequestToAddMod__sr_ProhibitTimer__ms4
  | 3 => SchedulingRequestToAddMod__sr_ProhibitTimer__ms8
  | 4 => SchedulingRequestToAddMod__sr_ProhibitTimer__ms16
  | 5 => SchedulingRequestToAddMod__sr_ProhibitTimer__ms32
  | 6 => SchedulingRequestToAddMod__sr_ProhibitTimer__ms64
  | 7 => SchedulingRequestToAddMod__sr_ProhibitTimer__ms128
  | _ => SchedulingRequestToAddMod__sr_ProhibitTimer__ms1
  end.
Lemma SchedulingRequestToAddMod__sr_ProhibitTimer__F1F2 : forall x : SchedulingRequestToAddMod__sr_ProhibitTimer__Type, (SchedulingRequestToAddMod__sr_ProhibitTimer__F1 x <= 7) /\ SchedulingRequestToAddMod__sr_ProhibitTimer__F2 (SchedulingRequestToAddMod__sr_ProhibitTimer__F1 x) = x. imp_solve. Qed.
Lemma SchedulingRequestToAddMod__sr_ProhibitTimer__F2F1 : forall (y : nat) (H : y <= 7), SchedulingRequestToAddMod__sr_ProhibitTimer__F1 (SchedulingRequestToAddMod__sr_ProhibitTimer__F2 y) = y. enum_solve H y. Qed.

Inductive SchedulingRequestToAddMod__sr_TransMax__Type : Set :=
 | SchedulingRequestToAddMod__sr_TransMax__n4
 | SchedulingRequestToAddMod__sr_TransMax__n8
 | SchedulingRequestToAddMod__sr_TransMax__n16
 | SchedulingRequestToAddMod__sr_TransMax__n32
 | SchedulingRequestToAddMod__sr_TransMax__n64
 | SchedulingRequestToAddMod__sr_TransMax__spare3
 | SchedulingRequestToAddMod__sr_TransMax__spare2
 | SchedulingRequestToAddMod__sr_TransMax__spare1
.
Definition SchedulingRequestToAddMod__sr_TransMax__cond := (fun (_ : SchedulingRequestToAddMod__sr_TransMax__Type) => True).
Lemma SchedulingRequestToAddMod__sr_TransMax__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SchedulingRequestToAddMod__sr_TransMax__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SchedulingRequestToAddMod__sr_TransMax__nat__helper.

Definition SchedulingRequestToAddMod__sr_TransMax__F1 t :=
  match t with
  | SchedulingRequestToAddMod__sr_TransMax__n4 => 0
  | SchedulingRequestToAddMod__sr_TransMax__n8 => 1
  | SchedulingRequestToAddMod__sr_TransMax__n16 => 2
  | SchedulingRequestToAddMod__sr_TransMax__n32 => 3
  | SchedulingRequestToAddMod__sr_TransMax__n64 => 4
  | SchedulingRequestToAddMod__sr_TransMax__spare3 => 5
  | SchedulingRequestToAddMod__sr_TransMax__spare2 => 6
  | SchedulingRequestToAddMod__sr_TransMax__spare1 => 7
  end.
Definition SchedulingRequestToAddMod__sr_TransMax__F2 n :=
  match n with
  | 0 => SchedulingRequestToAddMod__sr_TransMax__n4
  | 1 => SchedulingRequestToAddMod__sr_TransMax__n8
  | 2 => SchedulingRequestToAddMod__sr_TransMax__n16
  | 3 => SchedulingRequestToAddMod__sr_TransMax__n32
  | 4 => SchedulingRequestToAddMod__sr_TransMax__n64
  | 5 => SchedulingRequestToAddMod__sr_TransMax__spare3
  | 6 => SchedulingRequestToAddMod__sr_TransMax__spare2
  | 7 => SchedulingRequestToAddMod__sr_TransMax__spare1
  | _ => SchedulingRequestToAddMod__sr_TransMax__n4
  end.
Lemma SchedulingRequestToAddMod__sr_TransMax__F1F2 : forall x : SchedulingRequestToAddMod__sr_TransMax__Type, (SchedulingRequestToAddMod__sr_TransMax__F1 x <= 7) /\ SchedulingRequestToAddMod__sr_TransMax__F2 (SchedulingRequestToAddMod__sr_TransMax__F1 x) = x. imp_solve. Qed.
Lemma SchedulingRequestToAddMod__sr_TransMax__F2F1 : forall (y : nat) (H : y <= 7), SchedulingRequestToAddMod__sr_TransMax__F1 (SchedulingRequestToAddMod__sr_TransMax__F2 y) = y. enum_solve H y. Qed.

Record SchedulingRequestToAddMod__Type : Set :=
  make__SchedulingRequestToAddMod__Type {
    SchedulingRequestToAddMod__schedulingRequestId : SchedulingRequestId__Type ;
    SchedulingRequestToAddMod__sr_ProhibitTimer : option SchedulingRequestToAddMod__sr_ProhibitTimer__Type ;
    SchedulingRequestToAddMod__sr_TransMax : SchedulingRequestToAddMod__sr_TransMax__Type ;
}.
Definition SchedulingRequestToAddMod__list := (
 Nor SchedulingRequestId__Type SchedulingRequestId__cond ::
 Opt SchedulingRequestToAddMod__sr_ProhibitTimer__Type SchedulingRequestToAddMod__sr_ProhibitTimer__cond ::
 Nor SchedulingRequestToAddMod__sr_TransMax__Type SchedulingRequestToAddMod__sr_TransMax__cond ::
 nil).
Definition SchedulingRequestToAddMod__cond z := 
  SchedulingRequestId__cond (SchedulingRequestToAddMod__schedulingRequestId z) /\
  opt_cond SchedulingRequestToAddMod__sr_ProhibitTimer__cond (SchedulingRequestToAddMod__sr_ProhibitTimer z) /\
  SchedulingRequestToAddMod__sr_TransMax__cond (SchedulingRequestToAddMod__sr_TransMax z) /\
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
Definition SchedulingRequestToAddMod__sr_ProhibitTimer__Format : T_Format SchedulingRequestToAddMod__sr_ProhibitTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SchedulingRequestToAddMod__sr_ProhibitTimer__nat__Format SchedulingRequestToAddMod__sr_ProhibitTimer__F1 SchedulingRequestToAddMod__sr_ProhibitTimer__F2 SchedulingRequestToAddMod__sr_ProhibitTimer__F1F2 SchedulingRequestToAddMod__sr_ProhibitTimer__F2F1.

Opaque SchedulingRequestToAddMod__sr_ProhibitTimer__cond SchedulingRequestToAddMod__sr_ProhibitTimer__Format.

Definition SchedulingRequestToAddMod__sr_TransMax__Format : T_Format SchedulingRequestToAddMod__sr_TransMax__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SchedulingRequestToAddMod__sr_TransMax__nat__Format SchedulingRequestToAddMod__sr_TransMax__F1 SchedulingRequestToAddMod__sr_TransMax__F2 SchedulingRequestToAddMod__sr_TransMax__F1F2 SchedulingRequestToAddMod__sr_TransMax__F2F1.

Opaque SchedulingRequestToAddMod__sr_TransMax__cond SchedulingRequestToAddMod__sr_TransMax__Format.


Definition SchedulingRequestToAddMod__Format_Type := Eval cbn in seq_format_prod SchedulingRequestToAddMod__list.
Definition SchedulingRequestToAddMod__Format_list : SchedulingRequestToAddMod__Format_Type :=
  (SchedulingRequestId__Format, (SchedulingRequestToAddMod__sr_ProhibitTimer__Format, (SchedulingRequestToAddMod__sr_TransMax__Format, unit_format))).
Definition SchedulingRequestToAddMod__list__Format := (*Eval compute in *) seq_format SchedulingRequestToAddMod__list SchedulingRequestToAddMod__Format_list.
Definition SchedulingRequestToAddMod__F1 z :=
  (SchedulingRequestToAddMod__schedulingRequestId z, (SchedulingRequestToAddMod__sr_ProhibitTimer z, (SchedulingRequestToAddMod__sr_TransMax z, tt))).
Definition SchedulingRequestToAddMod__F2 (y : seq_type SchedulingRequestToAddMod__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SchedulingRequestToAddMod__Type i0 i1 i2
  end.
Lemma SchedulingRequestToAddMod__F1F2_cond (z : SchedulingRequestToAddMod__Type)
  : SchedulingRequestToAddMod__cond z ->
  (seq_cond SchedulingRequestToAddMod__list (SchedulingRequestToAddMod__F1 z)).
intro H. unfold SchedulingRequestToAddMod__cond in H. simpl. auto. Qed.
Lemma SchedulingRequestToAddMod__F1F2_cond2 (z : SchedulingRequestToAddMod__Type)
 : SchedulingRequestToAddMod__F2 (SchedulingRequestToAddMod__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SchedulingRequestToAddMod__F2F1_cond (y : seq_type SchedulingRequestToAddMod__list)
  : seq_cond SchedulingRequestToAddMod__list y ->
 (SchedulingRequestToAddMod__cond (SchedulingRequestToAddMod__F2 y)) /\  SchedulingRequestToAddMod__F1 (SchedulingRequestToAddMod__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SchedulingRequestToAddMod__cond. simpl in *. auto.
 - simpl. unfold SchedulingRequestToAddMod__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SchedulingRequestToAddMod__Format : T_Format SchedulingRequestToAddMod__Type SchedulingRequestToAddMod__cond :=
        proj2_format  SchedulingRequestToAddMod__cond SchedulingRequestToAddMod__list__Format
    SchedulingRequestToAddMod__F1 SchedulingRequestToAddMod__F2 SchedulingRequestToAddMod__F1F2_cond  SchedulingRequestToAddMod__F1F2_cond2 SchedulingRequestToAddMod__F2F1_cond.
Opaque SchedulingRequestToAddMod__cond SchedulingRequestToAddMod__Format.

