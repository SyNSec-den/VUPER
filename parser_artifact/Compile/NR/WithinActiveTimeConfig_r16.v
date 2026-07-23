Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Require Import NR.DormancyGroupID_r16.

Opaque DormancyGroupID_r16__cond DormancyGroupID_r16__Format.

Record WithinActiveTimeConfig_r16__Type : Set :=
  make__WithinActiveTimeConfig_r16__Type {
    WithinActiveTimeConfig_r16__firstWithinActiveTimeBWP_Id_r16 : option BWP_Id__Type ;
    WithinActiveTimeConfig_r16__dormancyGroupWithinActiveTime_r16 : option DormancyGroupID_r16__Type ;
}.
Definition WithinActiveTimeConfig_r16__list := (
 Opt BWP_Id__Type BWP_Id__cond ::
 Opt DormancyGroupID_r16__Type DormancyGroupID_r16__cond ::
 nil).
Definition WithinActiveTimeConfig_r16__cond z := 
  opt_cond BWP_Id__cond (WithinActiveTimeConfig_r16__firstWithinActiveTimeBWP_Id_r16 z) /\
  opt_cond DormancyGroupID_r16__cond (WithinActiveTimeConfig_r16__dormancyGroupWithinActiveTime_r16 z) /\
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

Definition WithinActiveTimeConfig_r16__Format_Type := Eval cbn in seq_format_prod WithinActiveTimeConfig_r16__list.
Definition WithinActiveTimeConfig_r16__Format_list : WithinActiveTimeConfig_r16__Format_Type :=
  (BWP_Id__Format, (DormancyGroupID_r16__Format, unit_format)).
Definition WithinActiveTimeConfig_r16__list__Format := (*Eval compute in *) seq_format WithinActiveTimeConfig_r16__list WithinActiveTimeConfig_r16__Format_list.
Definition WithinActiveTimeConfig_r16__F1 z :=
  (WithinActiveTimeConfig_r16__firstWithinActiveTimeBWP_Id_r16 z, (WithinActiveTimeConfig_r16__dormancyGroupWithinActiveTime_r16 z, tt)).
Definition WithinActiveTimeConfig_r16__F2 (y : seq_type WithinActiveTimeConfig_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__WithinActiveTimeConfig_r16__Type i0 i1
  end.
Lemma WithinActiveTimeConfig_r16__F1F2_cond (z : WithinActiveTimeConfig_r16__Type)
  : WithinActiveTimeConfig_r16__cond z ->
  (seq_cond WithinActiveTimeConfig_r16__list (WithinActiveTimeConfig_r16__F1 z)).
intro H. unfold WithinActiveTimeConfig_r16__cond in H. simpl. auto. Qed.
Lemma WithinActiveTimeConfig_r16__F1F2_cond2 (z : WithinActiveTimeConfig_r16__Type)
 : WithinActiveTimeConfig_r16__F2 (WithinActiveTimeConfig_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma WithinActiveTimeConfig_r16__F2F1_cond (y : seq_type WithinActiveTimeConfig_r16__list)
  : seq_cond WithinActiveTimeConfig_r16__list y ->
 (WithinActiveTimeConfig_r16__cond (WithinActiveTimeConfig_r16__F2 y)) /\  WithinActiveTimeConfig_r16__F1 (WithinActiveTimeConfig_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold WithinActiveTimeConfig_r16__cond. simpl in *. auto.
 - simpl. unfold WithinActiveTimeConfig_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition WithinActiveTimeConfig_r16__Format : T_Format WithinActiveTimeConfig_r16__Type WithinActiveTimeConfig_r16__cond :=
        proj2_format  WithinActiveTimeConfig_r16__cond WithinActiveTimeConfig_r16__list__Format
    WithinActiveTimeConfig_r16__F1 WithinActiveTimeConfig_r16__F2 WithinActiveTimeConfig_r16__F1F2_cond  WithinActiveTimeConfig_r16__F1F2_cond2 WithinActiveTimeConfig_r16__F2F1_cond.
Opaque WithinActiveTimeConfig_r16__cond WithinActiveTimeConfig_r16__Format.

