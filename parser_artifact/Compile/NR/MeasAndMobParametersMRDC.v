Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasAndMobParametersMRDC_Common.

Opaque MeasAndMobParametersMRDC_Common__cond MeasAndMobParametersMRDC_Common__Format.

Require Import NR.MeasAndMobParametersMRDC_XDD_Diff.

Opaque MeasAndMobParametersMRDC_XDD_Diff__cond MeasAndMobParametersMRDC_XDD_Diff__Format.

Require Import NR.MeasAndMobParametersMRDC_FRX_Diff.

Opaque MeasAndMobParametersMRDC_FRX_Diff__cond MeasAndMobParametersMRDC_FRX_Diff__Format.

Record MeasAndMobParametersMRDC__Type : Set :=
  make__MeasAndMobParametersMRDC__Type {
    MeasAndMobParametersMRDC__measAndMobParametersMRDC_Common : option MeasAndMobParametersMRDC_Common__Type ;
    MeasAndMobParametersMRDC__measAndMobParametersMRDC_XDD_Diff : option MeasAndMobParametersMRDC_XDD_Diff__Type ;
    MeasAndMobParametersMRDC__measAndMobParametersMRDC_FRX_Diff : option MeasAndMobParametersMRDC_FRX_Diff__Type ;
}.
Definition MeasAndMobParametersMRDC__list := (
 Opt MeasAndMobParametersMRDC_Common__Type MeasAndMobParametersMRDC_Common__cond ::
 Opt MeasAndMobParametersMRDC_XDD_Diff__Type MeasAndMobParametersMRDC_XDD_Diff__cond ::
 Opt MeasAndMobParametersMRDC_FRX_Diff__Type MeasAndMobParametersMRDC_FRX_Diff__cond ::
 nil).
Definition MeasAndMobParametersMRDC__cond z := 
  opt_cond MeasAndMobParametersMRDC_Common__cond (MeasAndMobParametersMRDC__measAndMobParametersMRDC_Common z) /\
  opt_cond MeasAndMobParametersMRDC_XDD_Diff__cond (MeasAndMobParametersMRDC__measAndMobParametersMRDC_XDD_Diff z) /\
  opt_cond MeasAndMobParametersMRDC_FRX_Diff__cond (MeasAndMobParametersMRDC__measAndMobParametersMRDC_FRX_Diff z) /\
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

Definition MeasAndMobParametersMRDC__Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersMRDC__list.
Definition MeasAndMobParametersMRDC__Format_list : MeasAndMobParametersMRDC__Format_Type :=
  (MeasAndMobParametersMRDC_Common__Format, (MeasAndMobParametersMRDC_XDD_Diff__Format, (MeasAndMobParametersMRDC_FRX_Diff__Format, unit_format))).
Definition MeasAndMobParametersMRDC__list__Format := (*Eval compute in *) seq_format MeasAndMobParametersMRDC__list MeasAndMobParametersMRDC__Format_list.
Definition MeasAndMobParametersMRDC__F1 z :=
  (MeasAndMobParametersMRDC__measAndMobParametersMRDC_Common z, (MeasAndMobParametersMRDC__measAndMobParametersMRDC_XDD_Diff z, (MeasAndMobParametersMRDC__measAndMobParametersMRDC_FRX_Diff z, tt))).
Definition MeasAndMobParametersMRDC__F2 (y : seq_type MeasAndMobParametersMRDC__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasAndMobParametersMRDC__Type i0 i1 i2
  end.
Lemma MeasAndMobParametersMRDC__F1F2_cond (z : MeasAndMobParametersMRDC__Type)
  : MeasAndMobParametersMRDC__cond z ->
  (seq_cond MeasAndMobParametersMRDC__list (MeasAndMobParametersMRDC__F1 z)).
intro H. unfold MeasAndMobParametersMRDC__cond in H. simpl. auto. Qed.
Lemma MeasAndMobParametersMRDC__F1F2_cond2 (z : MeasAndMobParametersMRDC__Type)
 : MeasAndMobParametersMRDC__F2 (MeasAndMobParametersMRDC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasAndMobParametersMRDC__F2F1_cond (y : seq_type MeasAndMobParametersMRDC__list)
  : seq_cond MeasAndMobParametersMRDC__list y ->
 (MeasAndMobParametersMRDC__cond (MeasAndMobParametersMRDC__F2 y)) /\  MeasAndMobParametersMRDC__F1 (MeasAndMobParametersMRDC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasAndMobParametersMRDC__cond. simpl in *. auto.
 - simpl. unfold MeasAndMobParametersMRDC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasAndMobParametersMRDC__Format : T_Format MeasAndMobParametersMRDC__Type MeasAndMobParametersMRDC__cond :=
        proj2_format  MeasAndMobParametersMRDC__cond MeasAndMobParametersMRDC__list__Format
    MeasAndMobParametersMRDC__F1 MeasAndMobParametersMRDC__F2 MeasAndMobParametersMRDC__F1F2_cond  MeasAndMobParametersMRDC__F1F2_cond2 MeasAndMobParametersMRDC__F2F1_cond.
Opaque MeasAndMobParametersMRDC__cond MeasAndMobParametersMRDC__Format.

