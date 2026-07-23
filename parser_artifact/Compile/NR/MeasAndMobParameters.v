Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasAndMobParametersCommon.

Opaque MeasAndMobParametersCommon__cond MeasAndMobParametersCommon__Format.

Require Import NR.MeasAndMobParametersXDD_Diff.

Opaque MeasAndMobParametersXDD_Diff__cond MeasAndMobParametersXDD_Diff__Format.

Require Import NR.MeasAndMobParametersFRX_Diff.

Opaque MeasAndMobParametersFRX_Diff__cond MeasAndMobParametersFRX_Diff__Format.

Record MeasAndMobParameters__Type : Set :=
  make__MeasAndMobParameters__Type {
    MeasAndMobParameters__measAndMobParametersCommon : option MeasAndMobParametersCommon__Type ;
    MeasAndMobParameters__measAndMobParametersXDD_Diff : option MeasAndMobParametersXDD_Diff__Type ;
    MeasAndMobParameters__measAndMobParametersFRX_Diff : option MeasAndMobParametersFRX_Diff__Type ;
}.
Definition MeasAndMobParameters__list := (
 Opt MeasAndMobParametersCommon__Type MeasAndMobParametersCommon__cond ::
 Opt MeasAndMobParametersXDD_Diff__Type MeasAndMobParametersXDD_Diff__cond ::
 Opt MeasAndMobParametersFRX_Diff__Type MeasAndMobParametersFRX_Diff__cond ::
 nil).
Definition MeasAndMobParameters__cond z := 
  opt_cond MeasAndMobParametersCommon__cond (MeasAndMobParameters__measAndMobParametersCommon z) /\
  opt_cond MeasAndMobParametersXDD_Diff__cond (MeasAndMobParameters__measAndMobParametersXDD_Diff z) /\
  opt_cond MeasAndMobParametersFRX_Diff__cond (MeasAndMobParameters__measAndMobParametersFRX_Diff z) /\
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

Definition MeasAndMobParameters__Format_Type := Eval cbn in seq_format_prod MeasAndMobParameters__list.
Definition MeasAndMobParameters__Format_list : MeasAndMobParameters__Format_Type :=
  (MeasAndMobParametersCommon__Format, (MeasAndMobParametersXDD_Diff__Format, (MeasAndMobParametersFRX_Diff__Format, unit_format))).
Definition MeasAndMobParameters__list__Format := (*Eval compute in *) seq_format MeasAndMobParameters__list MeasAndMobParameters__Format_list.
Definition MeasAndMobParameters__F1 z :=
  (MeasAndMobParameters__measAndMobParametersCommon z, (MeasAndMobParameters__measAndMobParametersXDD_Diff z, (MeasAndMobParameters__measAndMobParametersFRX_Diff z, tt))).
Definition MeasAndMobParameters__F2 (y : seq_type MeasAndMobParameters__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasAndMobParameters__Type i0 i1 i2
  end.
Lemma MeasAndMobParameters__F1F2_cond (z : MeasAndMobParameters__Type)
  : MeasAndMobParameters__cond z ->
  (seq_cond MeasAndMobParameters__list (MeasAndMobParameters__F1 z)).
intro H. unfold MeasAndMobParameters__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParameters__F1F2_cond2 (z : MeasAndMobParameters__Type)
 : MeasAndMobParameters__F2 (MeasAndMobParameters__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParameters__F2F1_cond (y : seq_type MeasAndMobParameters__list)
  : seq_cond MeasAndMobParameters__list y ->
 (MeasAndMobParameters__cond (MeasAndMobParameters__F2 y)) /\  MeasAndMobParameters__F1 (MeasAndMobParameters__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParameters__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParameters__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParameters__Format : T_Format MeasAndMobParameters__Type MeasAndMobParameters__cond :=
        proj2_format  MeasAndMobParameters__cond MeasAndMobParameters__list__Format
    MeasAndMobParameters__F1 MeasAndMobParameters__F2 MeasAndMobParameters__F1F2_cond  MeasAndMobParameters__F1F2_cond2 MeasAndMobParameters__F2F1_cond.
Opaque MeasAndMobParameters__cond MeasAndMobParameters__Format.

