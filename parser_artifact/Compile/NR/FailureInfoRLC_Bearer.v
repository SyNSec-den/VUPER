Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CellGroupId.

Opaque CellGroupId__cond CellGroupId__Format.

Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Inductive FailureInfoRLC_Bearer__failureType__Type : Set :=
 | FailureInfoRLC_Bearer__failureType__rlc_failure
 | FailureInfoRLC_Bearer__failureType__spare3
 | FailureInfoRLC_Bearer__failureType__spare2
 | FailureInfoRLC_Bearer__failureType__spare1
.
Definition FailureInfoRLC_Bearer__failureType__cond := (fun (_ : FailureInfoRLC_Bearer__failureType__Type) => True).
Lemma FailureInfoRLC_Bearer__failureType__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FailureInfoRLC_Bearer__failureType__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 FailureInfoRLC_Bearer__failureType__nat__helper.

Definition FailureInfoRLC_Bearer__failureType__F1 t :=
  match t with
  | FailureInfoRLC_Bearer__failureType__rlc_failure => 0
  | FailureInfoRLC_Bearer__failureType__spare3 => 1
  | FailureInfoRLC_Bearer__failureType__spare2 => 2
  | FailureInfoRLC_Bearer__failureType__spare1 => 3
  end.
Definition FailureInfoRLC_Bearer__failureType__F2 n :=
  match n with
  | 0 => FailureInfoRLC_Bearer__failureType__rlc_failure
  | 1 => FailureInfoRLC_Bearer__failureType__spare3
  | 2 => FailureInfoRLC_Bearer__failureType__spare2
  | 3 => FailureInfoRLC_Bearer__failureType__spare1
  | _ => FailureInfoRLC_Bearer__failureType__rlc_failure
  end.
Lemma FailureInfoRLC_Bearer__failureType__F1F2 : forall x : FailureInfoRLC_Bearer__failureType__Type, (FailureInfoRLC_Bearer__failureType__F1 x <= 3) /\ FailureInfoRLC_Bearer__failureType__F2 (FailureInfoRLC_Bearer__failureType__F1 x) = x. imp_solve. Qed.
Lemma FailureInfoRLC_Bearer__failureType__F2F1 : forall (y : nat) (H : y <= 3), FailureInfoRLC_Bearer__failureType__F1 (FailureInfoRLC_Bearer__failureType__F2 y) = y. enum_solve H y. Qed.

Record FailureInfoRLC_Bearer__Type : Set :=
  make__FailureInfoRLC_Bearer__Type {
    FailureInfoRLC_Bearer__cellGroupId : CellGroupId__Type ;
    FailureInfoRLC_Bearer__logicalChannelIdentity : LogicalChannelIdentity__Type ;
    FailureInfoRLC_Bearer__failureType : FailureInfoRLC_Bearer__failureType__Type ;
}.
Definition FailureInfoRLC_Bearer__list := (
 Nor CellGroupId__Type CellGroupId__cond ::
 Nor LogicalChannelIdentity__Type LogicalChannelIdentity__cond ::
 Nor FailureInfoRLC_Bearer__failureType__Type FailureInfoRLC_Bearer__failureType__cond ::
 nil).
Definition FailureInfoRLC_Bearer__cond z := 
  CellGroupId__cond (FailureInfoRLC_Bearer__cellGroupId z) /\
  LogicalChannelIdentity__cond (FailureInfoRLC_Bearer__logicalChannelIdentity z) /\
  FailureInfoRLC_Bearer__failureType__cond (FailureInfoRLC_Bearer__failureType z) /\
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
Definition FailureInfoRLC_Bearer__failureType__Format : T_Format FailureInfoRLC_Bearer__failureType__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FailureInfoRLC_Bearer__failureType__nat__Format FailureInfoRLC_Bearer__failureType__F1 FailureInfoRLC_Bearer__failureType__F2 FailureInfoRLC_Bearer__failureType__F1F2 FailureInfoRLC_Bearer__failureType__F2F1.

Opaque FailureInfoRLC_Bearer__failureType__cond FailureInfoRLC_Bearer__failureType__Format.


Definition FailureInfoRLC_Bearer__Format_Type := Eval cbn in seq_format_prod FailureInfoRLC_Bearer__list.
Definition FailureInfoRLC_Bearer__Format_list : FailureInfoRLC_Bearer__Format_Type :=
  (CellGroupId__Format, (LogicalChannelIdentity__Format, (FailureInfoRLC_Bearer__failureType__Format, unit_format))).
Definition FailureInfoRLC_Bearer__list__Format := (*Eval compute in *) seq_format FailureInfoRLC_Bearer__list FailureInfoRLC_Bearer__Format_list.
Definition FailureInfoRLC_Bearer__F1 z :=
  (FailureInfoRLC_Bearer__cellGroupId z, (FailureInfoRLC_Bearer__logicalChannelIdentity z, (FailureInfoRLC_Bearer__failureType z, tt))).
Definition FailureInfoRLC_Bearer__F2 (y : seq_type FailureInfoRLC_Bearer__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FailureInfoRLC_Bearer__Type i0 i1 i2
  end.
Lemma FailureInfoRLC_Bearer__F1F2_cond (z : FailureInfoRLC_Bearer__Type)
  : FailureInfoRLC_Bearer__cond z ->
  (seq_cond FailureInfoRLC_Bearer__list (FailureInfoRLC_Bearer__F1 z)).
intro H. unfold FailureInfoRLC_Bearer__cond in H. simpl. auto. Qed.
Lemma FailureInfoRLC_Bearer__F1F2_cond2 (z : FailureInfoRLC_Bearer__Type)
 : FailureInfoRLC_Bearer__F2 (FailureInfoRLC_Bearer__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FailureInfoRLC_Bearer__F2F1_cond (y : seq_type FailureInfoRLC_Bearer__list)
  : seq_cond FailureInfoRLC_Bearer__list y ->
 (FailureInfoRLC_Bearer__cond (FailureInfoRLC_Bearer__F2 y)) /\  FailureInfoRLC_Bearer__F1 (FailureInfoRLC_Bearer__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FailureInfoRLC_Bearer__cond. simpl in *. auto.
 - simpl. unfold FailureInfoRLC_Bearer__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FailureInfoRLC_Bearer__Format : T_Format FailureInfoRLC_Bearer__Type FailureInfoRLC_Bearer__cond :=
        proj2_format  FailureInfoRLC_Bearer__cond FailureInfoRLC_Bearer__list__Format
    FailureInfoRLC_Bearer__F1 FailureInfoRLC_Bearer__F2 FailureInfoRLC_Bearer__F1F2_cond  FailureInfoRLC_Bearer__F1F2_cond2 FailureInfoRLC_Bearer__F2F1_cond.
Opaque FailureInfoRLC_Bearer__cond FailureInfoRLC_Bearer__Format.

