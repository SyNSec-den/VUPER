Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CA_ParametersNR_v15g0.

Opaque CA_ParametersNR_v15g0__cond CA_ParametersNR_v15g0__Format.

Require Import NR.CA_ParametersNRDC_v15g0.

Opaque CA_ParametersNRDC_v15g0__cond CA_ParametersNRDC_v15g0__Format.

Require Import NR.MRDC_Parameters_v15g0.

Opaque MRDC_Parameters_v15g0__cond MRDC_Parameters_v15g0__Format.

Record BandCombination_v15g0__Type : Set :=
  make__BandCombination_v15g0__Type {
    BandCombination_v15g0__ca_ParametersNR_v15g0 : option CA_ParametersNR_v15g0__Type ;
    BandCombination_v15g0__ca_ParametersNRDC_v15g0 : option CA_ParametersNRDC_v15g0__Type ;
    BandCombination_v15g0__mrdc_Parameters_v15g0 : option MRDC_Parameters_v15g0__Type ;
}.
Definition BandCombination_v15g0__list := (
 Opt CA_ParametersNR_v15g0__Type CA_ParametersNR_v15g0__cond ::
 Opt CA_ParametersNRDC_v15g0__Type CA_ParametersNRDC_v15g0__cond ::
 Opt MRDC_Parameters_v15g0__Type MRDC_Parameters_v15g0__cond ::
 nil).
Definition BandCombination_v15g0__cond z := 
  opt_cond CA_ParametersNR_v15g0__cond (BandCombination_v15g0__ca_ParametersNR_v15g0 z) /\
  opt_cond CA_ParametersNRDC_v15g0__cond (BandCombination_v15g0__ca_ParametersNRDC_v15g0 z) /\
  opt_cond MRDC_Parameters_v15g0__cond (BandCombination_v15g0__mrdc_Parameters_v15g0 z) /\
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

Definition BandCombination_v15g0__Format_Type := Eval cbn in seq_format_prod BandCombination_v15g0__list.
Definition BandCombination_v15g0__Format_list : BandCombination_v15g0__Format_Type :=
  (CA_ParametersNR_v15g0__Format, (CA_ParametersNRDC_v15g0__Format, (MRDC_Parameters_v15g0__Format, unit_format))).
Definition BandCombination_v15g0__list__Format := (*Eval compute in *) seq_format BandCombination_v15g0__list BandCombination_v15g0__Format_list.
Definition BandCombination_v15g0__F1 z :=
  (BandCombination_v15g0__ca_ParametersNR_v15g0 z, (BandCombination_v15g0__ca_ParametersNRDC_v15g0 z, (BandCombination_v15g0__mrdc_Parameters_v15g0 z, tt))).
Definition BandCombination_v15g0__F2 (y : seq_type BandCombination_v15g0__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandCombination_v15g0__Type i0 i1 i2
  end.
Lemma BandCombination_v15g0__F1F2_cond (z : BandCombination_v15g0__Type)
  : BandCombination_v15g0__cond z ->
  (seq_cond BandCombination_v15g0__list (BandCombination_v15g0__F1 z)).
intro H. unfold BandCombination_v15g0__cond in H. simpl. auto. Qed.
Lemma BandCombination_v15g0__F1F2_cond2 (z : BandCombination_v15g0__Type)
 : BandCombination_v15g0__F2 (BandCombination_v15g0__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombination_v15g0__F2F1_cond (y : seq_type BandCombination_v15g0__list)
  : seq_cond BandCombination_v15g0__list y ->
 (BandCombination_v15g0__cond (BandCombination_v15g0__F2 y)) /\  BandCombination_v15g0__F1 (BandCombination_v15g0__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombination_v15g0__cond. simpl in *. auto.
 - simpl. unfold BandCombination_v15g0__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombination_v15g0__Format : T_Format BandCombination_v15g0__Type BandCombination_v15g0__cond :=
        proj2_format  BandCombination_v15g0__cond BandCombination_v15g0__list__Format
    BandCombination_v15g0__F1 BandCombination_v15g0__F2 BandCombination_v15g0__F1F2_cond  BandCombination_v15g0__F1F2_cond2 BandCombination_v15g0__F2F1_cond.
Opaque BandCombination_v15g0__cond BandCombination_v15g0__Format.

