Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasId.

Opaque MeasId__cond MeasId__Format.

Require Import NR.MeasObjectId.

Opaque MeasObjectId__cond MeasObjectId__Format.

Require Import NR.ReportConfigId.

Opaque ReportConfigId__cond ReportConfigId__Format.

Record MeasIdToAddMod__Type : Set :=
  make__MeasIdToAddMod__Type {
    MeasIdToAddMod__measId : MeasId__Type ;
    MeasIdToAddMod__measObjectId : MeasObjectId__Type ;
    MeasIdToAddMod__reportConfigId : ReportConfigId__Type ;
}.
Definition MeasIdToAddMod__list := (
 Nor MeasId__Type MeasId__cond ::
 Nor MeasObjectId__Type MeasObjectId__cond ::
 Nor ReportConfigId__Type ReportConfigId__cond ::
 nil).
Definition MeasIdToAddMod__cond z := 
  MeasId__cond (MeasIdToAddMod__measId z) /\
  MeasObjectId__cond (MeasIdToAddMod__measObjectId z) /\
  ReportConfigId__cond (MeasIdToAddMod__reportConfigId z) /\
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

Definition MeasIdToAddMod__Format_Type := Eval cbn in seq_format_prod MeasIdToAddMod__list.
Definition MeasIdToAddMod__Format_list : MeasIdToAddMod__Format_Type :=
  (MeasId__Format, (MeasObjectId__Format, (ReportConfigId__Format, unit_format))).
Definition MeasIdToAddMod__list__Format := (*Eval compute in *) seq_format MeasIdToAddMod__list MeasIdToAddMod__Format_list.
Definition MeasIdToAddMod__F1 z :=
  (MeasIdToAddMod__measId z, (MeasIdToAddMod__measObjectId z, (MeasIdToAddMod__reportConfigId z, tt))).
Definition MeasIdToAddMod__F2 (y : seq_type MeasIdToAddMod__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasIdToAddMod__Type i0 i1 i2
  end.
Lemma MeasIdToAddMod__F1F2_cond (z : MeasIdToAddMod__Type)
  : MeasIdToAddMod__cond z ->
  (seq_cond MeasIdToAddMod__list (MeasIdToAddMod__F1 z)).
intro H. unfold MeasIdToAddMod__cond in H. simpl. auto. Qed.
Lemma MeasIdToAddMod__F1F2_cond2 (z : MeasIdToAddMod__Type)
 : MeasIdToAddMod__F2 (MeasIdToAddMod__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasIdToAddMod__F2F1_cond (y : seq_type MeasIdToAddMod__list)
  : seq_cond MeasIdToAddMod__list y ->
 (MeasIdToAddMod__cond (MeasIdToAddMod__F2 y)) /\  MeasIdToAddMod__F1 (MeasIdToAddMod__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasIdToAddMod__cond. simpl in *. auto.
 - simpl. unfold MeasIdToAddMod__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasIdToAddMod__Format : T_Format MeasIdToAddMod__Type MeasIdToAddMod__cond :=
        proj2_format  MeasIdToAddMod__cond MeasIdToAddMod__list__Format
    MeasIdToAddMod__F1 MeasIdToAddMod__F2 MeasIdToAddMod__F1F2_cond  MeasIdToAddMod__F1F2_cond2 MeasIdToAddMod__F2F1_cond.
Opaque MeasIdToAddMod__cond MeasIdToAddMod__Format.

