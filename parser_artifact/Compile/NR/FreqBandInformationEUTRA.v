Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandIndicatorEUTRA.

Opaque FreqBandIndicatorEUTRA__cond FreqBandIndicatorEUTRA__Format.

Require Import NR.CA_BandwidthClassEUTRA.

Opaque CA_BandwidthClassEUTRA__cond CA_BandwidthClassEUTRA__Format.

Require Import NR.CA_BandwidthClassEUTRA.

Opaque CA_BandwidthClassEUTRA__cond CA_BandwidthClassEUTRA__Format.

Record FreqBandInformationEUTRA__Type : Set :=
  make__FreqBandInformationEUTRA__Type {
    FreqBandInformationEUTRA__bandEUTRA : FreqBandIndicatorEUTRA__Type ;
    FreqBandInformationEUTRA__ca_BandwidthClassDL_EUTRA : option CA_BandwidthClassEUTRA__Type ;
    FreqBandInformationEUTRA__ca_BandwidthClassUL_EUTRA : option CA_BandwidthClassEUTRA__Type ;
}.
Definition FreqBandInformationEUTRA__list := (
 Nor FreqBandIndicatorEUTRA__Type FreqBandIndicatorEUTRA__cond ::
 Opt CA_BandwidthClassEUTRA__Type CA_BandwidthClassEUTRA__cond ::
 Opt CA_BandwidthClassEUTRA__Type CA_BandwidthClassEUTRA__cond ::
 nil).
Definition FreqBandInformationEUTRA__cond z := 
  FreqBandIndicatorEUTRA__cond (FreqBandInformationEUTRA__bandEUTRA z) /\
  opt_cond CA_BandwidthClassEUTRA__cond (FreqBandInformationEUTRA__ca_BandwidthClassDL_EUTRA z) /\
  opt_cond CA_BandwidthClassEUTRA__cond (FreqBandInformationEUTRA__ca_BandwidthClassUL_EUTRA z) /\
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

Definition FreqBandInformationEUTRA__Format_Type := Eval cbn in seq_format_prod FreqBandInformationEUTRA__list.
Definition FreqBandInformationEUTRA__Format_list : FreqBandInformationEUTRA__Format_Type :=
  (FreqBandIndicatorEUTRA__Format, (CA_BandwidthClassEUTRA__Format, (CA_BandwidthClassEUTRA__Format, unit_format))).
Definition FreqBandInformationEUTRA__list__Format := (*Eval compute in *) seq_format FreqBandInformationEUTRA__list FreqBandInformationEUTRA__Format_list.
Definition FreqBandInformationEUTRA__F1 z :=
  (FreqBandInformationEUTRA__bandEUTRA z, (FreqBandInformationEUTRA__ca_BandwidthClassDL_EUTRA z, (FreqBandInformationEUTRA__ca_BandwidthClassUL_EUTRA z, tt))).
Definition FreqBandInformationEUTRA__F2 (y : seq_type FreqBandInformationEUTRA__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__FreqBandInformationEUTRA__Type i0 i1 i2
  end.
Lemma FreqBandInformationEUTRA__F1F2_cond (z : FreqBandInformationEUTRA__Type)
  : FreqBandInformationEUTRA__cond z ->
  (seq_cond FreqBandInformationEUTRA__list (FreqBandInformationEUTRA__F1 z)).
intro H. unfold FreqBandInformationEUTRA__cond in H. simpl. auto. Qed.
Lemma FreqBandInformationEUTRA__F1F2_cond2 (z : FreqBandInformationEUTRA__Type)
 : FreqBandInformationEUTRA__F2 (FreqBandInformationEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FreqBandInformationEUTRA__F2F1_cond (y : seq_type FreqBandInformationEUTRA__list)
  : seq_cond FreqBandInformationEUTRA__list y ->
 (FreqBandInformationEUTRA__cond (FreqBandInformationEUTRA__F2 y)) /\  FreqBandInformationEUTRA__F1 (FreqBandInformationEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FreqBandInformationEUTRA__cond. simpl in *. auto.
 - simpl. unfold FreqBandInformationEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FreqBandInformationEUTRA__Format : T_Format FreqBandInformationEUTRA__Type FreqBandInformationEUTRA__cond :=
        proj2_format  FreqBandInformationEUTRA__cond FreqBandInformationEUTRA__list__Format
    FreqBandInformationEUTRA__F1 FreqBandInformationEUTRA__F2 FreqBandInformationEUTRA__F1F2_cond  FreqBandInformationEUTRA__F1F2_cond2 FreqBandInformationEUTRA__F2F1_cond.
Opaque FreqBandInformationEUTRA__cond FreqBandInformationEUTRA__Format.

