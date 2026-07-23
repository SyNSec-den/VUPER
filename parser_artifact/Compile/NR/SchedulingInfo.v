Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SchedulingInfo__si_BroadcastStatus__Type : Set :=
 | SchedulingInfo__si_BroadcastStatus__broadcasting
 | SchedulingInfo__si_BroadcastStatus__notBroadcasting
.
Definition SchedulingInfo__si_BroadcastStatus__cond := (fun (_ : SchedulingInfo__si_BroadcastStatus__Type) => True).
Lemma SchedulingInfo__si_BroadcastStatus__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SchedulingInfo__si_BroadcastStatus__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SchedulingInfo__si_BroadcastStatus__nat__helper.

Definition SchedulingInfo__si_BroadcastStatus__F1 t :=
  match t with
  | SchedulingInfo__si_BroadcastStatus__broadcasting => 0
  | SchedulingInfo__si_BroadcastStatus__notBroadcasting => 1
  end.
Definition SchedulingInfo__si_BroadcastStatus__F2 n :=
  match n with
  | 0 => SchedulingInfo__si_BroadcastStatus__broadcasting
  | 1 => SchedulingInfo__si_BroadcastStatus__notBroadcasting
  | _ => SchedulingInfo__si_BroadcastStatus__broadcasting
  end.
Lemma SchedulingInfo__si_BroadcastStatus__F1F2 : forall x : SchedulingInfo__si_BroadcastStatus__Type, (SchedulingInfo__si_BroadcastStatus__F1 x <= 1) /\ SchedulingInfo__si_BroadcastStatus__F2 (SchedulingInfo__si_BroadcastStatus__F1 x) = x. imp_solve. Qed.
Lemma SchedulingInfo__si_BroadcastStatus__F2F1 : forall (y : nat) (H : y <= 1), SchedulingInfo__si_BroadcastStatus__F1 (SchedulingInfo__si_BroadcastStatus__F2 y) = y. enum_solve H y. Qed.

Inductive SchedulingInfo__si_Periodicity__Type : Set :=
 | SchedulingInfo__si_Periodicity__rf8
 | SchedulingInfo__si_Periodicity__rf16
 | SchedulingInfo__si_Periodicity__rf32
 | SchedulingInfo__si_Periodicity__rf64
 | SchedulingInfo__si_Periodicity__rf128
 | SchedulingInfo__si_Periodicity__rf256
 | SchedulingInfo__si_Periodicity__rf512
.
Definition SchedulingInfo__si_Periodicity__cond := (fun (_ : SchedulingInfo__si_Periodicity__Type) => True).
Lemma SchedulingInfo__si_Periodicity__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SchedulingInfo__si_Periodicity__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 SchedulingInfo__si_Periodicity__nat__helper.

Definition SchedulingInfo__si_Periodicity__F1 t :=
  match t with
  | SchedulingInfo__si_Periodicity__rf8 => 0
  | SchedulingInfo__si_Periodicity__rf16 => 1
  | SchedulingInfo__si_Periodicity__rf32 => 2
  | SchedulingInfo__si_Periodicity__rf64 => 3
  | SchedulingInfo__si_Periodicity__rf128 => 4
  | SchedulingInfo__si_Periodicity__rf256 => 5
  | SchedulingInfo__si_Periodicity__rf512 => 6
  end.
Definition SchedulingInfo__si_Periodicity__F2 n :=
  match n with
  | 0 => SchedulingInfo__si_Periodicity__rf8
  | 1 => SchedulingInfo__si_Periodicity__rf16
  | 2 => SchedulingInfo__si_Periodicity__rf32
  | 3 => SchedulingInfo__si_Periodicity__rf64
  | 4 => SchedulingInfo__si_Periodicity__rf128
  | 5 => SchedulingInfo__si_Periodicity__rf256
  | 6 => SchedulingInfo__si_Periodicity__rf512
  | _ => SchedulingInfo__si_Periodicity__rf8
  end.
Lemma SchedulingInfo__si_Periodicity__F1F2 : forall x : SchedulingInfo__si_Periodicity__Type, (SchedulingInfo__si_Periodicity__F1 x <= 6) /\ SchedulingInfo__si_Periodicity__F2 (SchedulingInfo__si_Periodicity__F1 x) = x. imp_solve. Qed.
Lemma SchedulingInfo__si_Periodicity__F2F1 : forall (y : nat) (H : y <= 6), SchedulingInfo__si_Periodicity__F1 (SchedulingInfo__si_Periodicity__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SIB_Mapping.

Opaque SIB_Mapping__cond SIB_Mapping__Format.

Record SchedulingInfo__Type : Set :=
  make__SchedulingInfo__Type {
    SchedulingInfo__si_BroadcastStatus : SchedulingInfo__si_BroadcastStatus__Type ;
    SchedulingInfo__si_Periodicity : SchedulingInfo__si_Periodicity__Type ;
    SchedulingInfo__sib_MappingInfo : SIB_Mapping__Type ;
}.
Definition SchedulingInfo__list := (
 Nor SchedulingInfo__si_BroadcastStatus__Type SchedulingInfo__si_BroadcastStatus__cond ::
 Nor SchedulingInfo__si_Periodicity__Type SchedulingInfo__si_Periodicity__cond ::
 Nor SIB_Mapping__Type SIB_Mapping__cond ::
 nil).
Definition SchedulingInfo__cond z := 
  SchedulingInfo__si_BroadcastStatus__cond (SchedulingInfo__si_BroadcastStatus z) /\
  SchedulingInfo__si_Periodicity__cond (SchedulingInfo__si_Periodicity z) /\
  SIB_Mapping__cond (SchedulingInfo__sib_MappingInfo z) /\
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
Definition SchedulingInfo__si_BroadcastStatus__Format : T_Format SchedulingInfo__si_BroadcastStatus__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SchedulingInfo__si_BroadcastStatus__nat__Format SchedulingInfo__si_BroadcastStatus__F1 SchedulingInfo__si_BroadcastStatus__F2 SchedulingInfo__si_BroadcastStatus__F1F2 SchedulingInfo__si_BroadcastStatus__F2F1.

Opaque SchedulingInfo__si_BroadcastStatus__cond SchedulingInfo__si_BroadcastStatus__Format.

Definition SchedulingInfo__si_Periodicity__Format : T_Format SchedulingInfo__si_Periodicity__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SchedulingInfo__si_Periodicity__nat__Format SchedulingInfo__si_Periodicity__F1 SchedulingInfo__si_Periodicity__F2 SchedulingInfo__si_Periodicity__F1F2 SchedulingInfo__si_Periodicity__F2F1.

Opaque SchedulingInfo__si_Periodicity__cond SchedulingInfo__si_Periodicity__Format.


Definition SchedulingInfo__Format_Type := Eval cbn in seq_format_prod SchedulingInfo__list.
Definition SchedulingInfo__Format_list : SchedulingInfo__Format_Type :=
  (SchedulingInfo__si_BroadcastStatus__Format, (SchedulingInfo__si_Periodicity__Format, (SIB_Mapping__Format, unit_format))).
Definition SchedulingInfo__list__Format := (*Eval compute in *) seq_format SchedulingInfo__list SchedulingInfo__Format_list.
Definition SchedulingInfo__F1 z :=
  (SchedulingInfo__si_BroadcastStatus z, (SchedulingInfo__si_Periodicity z, (SchedulingInfo__sib_MappingInfo z, tt))).
Definition SchedulingInfo__F2 (y : seq_type SchedulingInfo__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SchedulingInfo__Type i0 i1 i2
  end.
Lemma SchedulingInfo__F1F2_cond (z : SchedulingInfo__Type)
  : SchedulingInfo__cond z ->
  (seq_cond SchedulingInfo__list (SchedulingInfo__F1 z)).
intro H. unfold SchedulingInfo__cond in H. simpl. auto. Qed.
Lemma SchedulingInfo__F1F2_cond2 (z : SchedulingInfo__Type)
 : SchedulingInfo__F2 (SchedulingInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SchedulingInfo__F2F1_cond (y : seq_type SchedulingInfo__list)
  : seq_cond SchedulingInfo__list y ->
 (SchedulingInfo__cond (SchedulingInfo__F2 y)) /\  SchedulingInfo__F1 (SchedulingInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SchedulingInfo__cond. simpl in *. auto.
 - simpl. unfold SchedulingInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SchedulingInfo__Format : T_Format SchedulingInfo__Type SchedulingInfo__cond :=
        proj2_format  SchedulingInfo__cond SchedulingInfo__list__Format
    SchedulingInfo__F1 SchedulingInfo__F2 SchedulingInfo__F1F2_cond  SchedulingInfo__F1F2_cond2 SchedulingInfo__F2F1_cond.
Opaque SchedulingInfo__cond SchedulingInfo__Format.

