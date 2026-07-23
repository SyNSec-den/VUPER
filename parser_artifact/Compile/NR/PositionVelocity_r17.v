Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PositionStateVector_r17.

Opaque PositionStateVector_r17__cond PositionStateVector_r17__Format.

Require Import NR.PositionStateVector_r17.

Opaque PositionStateVector_r17__cond PositionStateVector_r17__Format.

Require Import NR.PositionStateVector_r17.

Opaque PositionStateVector_r17__cond PositionStateVector_r17__Format.

Require Import NR.VelocityStateVector_r17.

Opaque VelocityStateVector_r17__cond VelocityStateVector_r17__Format.

Require Import NR.VelocityStateVector_r17.

Opaque VelocityStateVector_r17__cond VelocityStateVector_r17__Format.

Require Import NR.VelocityStateVector_r17.

Opaque VelocityStateVector_r17__cond VelocityStateVector_r17__Format.

Record PositionVelocity_r17__Type : Set :=
  make__PositionVelocity_r17__Type {
    PositionVelocity_r17__positionX_r17 : PositionStateVector_r17__Type ;
    PositionVelocity_r17__positionY_r17 : PositionStateVector_r17__Type ;
    PositionVelocity_r17__positionZ_r17 : PositionStateVector_r17__Type ;
    PositionVelocity_r17__velocityVX_r17 : VelocityStateVector_r17__Type ;
    PositionVelocity_r17__velocityVY_r17 : VelocityStateVector_r17__Type ;
    PositionVelocity_r17__velocityVZ_r17 : VelocityStateVector_r17__Type ;
}.
Definition PositionVelocity_r17__list := (
 Nor PositionStateVector_r17__Type PositionStateVector_r17__cond ::
 Nor PositionStateVector_r17__Type PositionStateVector_r17__cond ::
 Nor PositionStateVector_r17__Type PositionStateVector_r17__cond ::
 Nor VelocityStateVector_r17__Type VelocityStateVector_r17__cond ::
 Nor VelocityStateVector_r17__Type VelocityStateVector_r17__cond ::
 Nor VelocityStateVector_r17__Type VelocityStateVector_r17__cond ::
 nil).
Definition PositionVelocity_r17__cond z := 
  PositionStateVector_r17__cond (PositionVelocity_r17__positionX_r17 z) /\
  PositionStateVector_r17__cond (PositionVelocity_r17__positionY_r17 z) /\
  PositionStateVector_r17__cond (PositionVelocity_r17__positionZ_r17 z) /\
  VelocityStateVector_r17__cond (PositionVelocity_r17__velocityVX_r17 z) /\
  VelocityStateVector_r17__cond (PositionVelocity_r17__velocityVY_r17 z) /\
  VelocityStateVector_r17__cond (PositionVelocity_r17__velocityVZ_r17 z) /\
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

Definition PositionVelocity_r17__Format_Type := Eval cbn in seq_format_prod PositionVelocity_r17__list.
Definition PositionVelocity_r17__Format_list : PositionVelocity_r17__Format_Type :=
  (PositionStateVector_r17__Format, (PositionStateVector_r17__Format, (PositionStateVector_r17__Format, (VelocityStateVector_r17__Format, (VelocityStateVector_r17__Format, (VelocityStateVector_r17__Format, unit_format)))))).
Definition PositionVelocity_r17__list__Format := (*Eval compute in *) seq_format PositionVelocity_r17__list PositionVelocity_r17__Format_list.
Definition PositionVelocity_r17__F1 z :=
  (PositionVelocity_r17__positionX_r17 z, (PositionVelocity_r17__positionY_r17 z, (PositionVelocity_r17__positionZ_r17 z, (PositionVelocity_r17__velocityVX_r17 z, (PositionVelocity_r17__velocityVY_r17 z, (PositionVelocity_r17__velocityVZ_r17 z, tt)))))).
Definition PositionVelocity_r17__F2 (y : seq_type PositionVelocity_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__PositionVelocity_r17__Type i0 i1 i2 i3 i4 i5
  end.
Lemma PositionVelocity_r17__F1F2_cond (z : PositionVelocity_r17__Type)
  : PositionVelocity_r17__cond z ->
  (seq_cond PositionVelocity_r17__list (PositionVelocity_r17__F1 z)).
intro H. unfold PositionVelocity_r17__cond in H. simpl. auto. Qed.
Lemma PositionVelocity_r17__F1F2_cond2 (z : PositionVelocity_r17__Type)
 : PositionVelocity_r17__F2 (PositionVelocity_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PositionVelocity_r17__F2F1_cond (y : seq_type PositionVelocity_r17__list)
  : seq_cond PositionVelocity_r17__list y ->
 (PositionVelocity_r17__cond (PositionVelocity_r17__F2 y)) /\  PositionVelocity_r17__F1 (PositionVelocity_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PositionVelocity_r17__cond. simpl in *. auto.
 - simpl. unfold PositionVelocity_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PositionVelocity_r17__Format : T_Format PositionVelocity_r17__Type PositionVelocity_r17__cond :=
        proj2_format  PositionVelocity_r17__cond PositionVelocity_r17__list__Format
    PositionVelocity_r17__F1 PositionVelocity_r17__F2 PositionVelocity_r17__F1F2_cond  PositionVelocity_r17__F1F2_cond2 PositionVelocity_r17__F2F1_cond.
Opaque PositionVelocity_r17__cond PositionVelocity_r17__Format.

