Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasAndMobParametersMRDC_v1610.

Opaque MeasAndMobParametersMRDC_v1610__cond MeasAndMobParametersMRDC_v1610__Format.

Record NRDC_Parameters_v1610__Type : Set :=
  make__NRDC_Parameters_v1610__Type {
    NRDC_Parameters_v1610__measAndMobParametersNRDC_v1610 : option MeasAndMobParametersMRDC_v1610__Type ;
}.
Definition NRDC_Parameters_v1610__list := (
 Opt MeasAndMobParametersMRDC_v1610__Type MeasAndMobParametersMRDC_v1610__cond ::
 nil).
Definition NRDC_Parameters_v1610__cond z := 
  opt_cond MeasAndMobParametersMRDC_v1610__cond (NRDC_Parameters_v1610__measAndMobParametersNRDC_v1610 z) /\
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

Definition NRDC_Parameters_v1610__Format_Type := Eval cbn in seq_format_prod NRDC_Parameters_v1610__list.
Definition NRDC_Parameters_v1610__Format_list : NRDC_Parameters_v1610__Format_Type :=
  (MeasAndMobParametersMRDC_v1610__Format, unit_format).
Definition NRDC_Parameters_v1610__list__Format := (*Eval compute in *) seq_format NRDC_Parameters_v1610__list NRDC_Parameters_v1610__Format_list.
Definition NRDC_Parameters_v1610__F1 z :=
  (NRDC_Parameters_v1610__measAndMobParametersNRDC_v1610 z, tt).
Definition NRDC_Parameters_v1610__F2 (y : seq_type NRDC_Parameters_v1610__list) :=
  match y with
  | (i0, _)=>
    make__NRDC_Parameters_v1610__Type i0
  end.
Lemma NRDC_Parameters_v1610__F1F2_cond (z : NRDC_Parameters_v1610__Type)
  : NRDC_Parameters_v1610__cond z ->
  (seq_cond NRDC_Parameters_v1610__list (NRDC_Parameters_v1610__F1 z)).
intro H. unfold NRDC_Parameters_v1610__cond in H. simpl. auto. Qed.
Lemma NRDC_Parameters_v1610__F1F2_cond2 (z : NRDC_Parameters_v1610__Type)
 : NRDC_Parameters_v1610__F2 (NRDC_Parameters_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NRDC_Parameters_v1610__F2F1_cond (y : seq_type NRDC_Parameters_v1610__list)
  : seq_cond NRDC_Parameters_v1610__list y ->
 (NRDC_Parameters_v1610__cond (NRDC_Parameters_v1610__F2 y)) /\  NRDC_Parameters_v1610__F1 (NRDC_Parameters_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NRDC_Parameters_v1610__cond. simpl in *. auto.
 - simpl. unfold NRDC_Parameters_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NRDC_Parameters_v1610__Format : T_Format NRDC_Parameters_v1610__Type NRDC_Parameters_v1610__cond :=
        proj2_format  NRDC_Parameters_v1610__cond NRDC_Parameters_v1610__list__Format
    NRDC_Parameters_v1610__F1 NRDC_Parameters_v1610__F2 NRDC_Parameters_v1610__F1F2_cond  NRDC_Parameters_v1610__F1F2_cond2 NRDC_Parameters_v1610__F2F1_cond.
Opaque NRDC_Parameters_v1610__cond NRDC_Parameters_v1610__Format.

