Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Require Import NR.NR_NS_PmaxList.

Opaque NR_NS_PmaxList__cond NR_NS_PmaxList__Format.

Record NR_MultiBandInfo__Type : Set :=
  make__NR_MultiBandInfo__Type {
    NR_MultiBandInfo__freqBandIndicatorNR : option FreqBandIndicatorNR__Type ;
    NR_MultiBandInfo__nr_NS_PmaxList : option NR_NS_PmaxList__Type ;
}.
Definition NR_MultiBandInfo__list := (
 Opt FreqBandIndicatorNR__Type FreqBandIndicatorNR__cond ::
 Opt NR_NS_PmaxList__Type NR_NS_PmaxList__cond ::
 nil).
Definition NR_MultiBandInfo__cond z := 
  opt_cond FreqBandIndicatorNR__cond (NR_MultiBandInfo__freqBandIndicatorNR z) /\
  opt_cond NR_NS_PmaxList__cond (NR_MultiBandInfo__nr_NS_PmaxList z) /\
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

Definition NR_MultiBandInfo__Format_Type := Eval cbn in seq_format_prod NR_MultiBandInfo__list.
Definition NR_MultiBandInfo__Format_list : NR_MultiBandInfo__Format_Type :=
  (FreqBandIndicatorNR__Format, (NR_NS_PmaxList__Format, unit_format)).
Definition NR_MultiBandInfo__list__Format := (*Eval compute in *) seq_format NR_MultiBandInfo__list NR_MultiBandInfo__Format_list.
Definition NR_MultiBandInfo__F1 z :=
  (NR_MultiBandInfo__freqBandIndicatorNR z, (NR_MultiBandInfo__nr_NS_PmaxList z, tt)).
Definition NR_MultiBandInfo__F2 (y : seq_type NR_MultiBandInfo__list) :=
  match y with
  | (i0, (i1, _))=>
    make__NR_MultiBandInfo__Type i0 i1
  end.
Lemma NR_MultiBandInfo__F1F2_cond (z : NR_MultiBandInfo__Type)
  : NR_MultiBandInfo__cond z ->
  (seq_cond NR_MultiBandInfo__list (NR_MultiBandInfo__F1 z)).
intro H. unfold NR_MultiBandInfo__cond in H. simpl. auto. Qed.
Lemma NR_MultiBandInfo__F1F2_cond2 (z : NR_MultiBandInfo__Type)
 : NR_MultiBandInfo__F2 (NR_MultiBandInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NR_MultiBandInfo__F2F1_cond (y : seq_type NR_MultiBandInfo__list)
  : seq_cond NR_MultiBandInfo__list y ->
 (NR_MultiBandInfo__cond (NR_MultiBandInfo__F2 y)) /\  NR_MultiBandInfo__F1 (NR_MultiBandInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NR_MultiBandInfo__cond. simpl in *. auto.
 - simpl. unfold NR_MultiBandInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NR_MultiBandInfo__Format : T_Format NR_MultiBandInfo__Type NR_MultiBandInfo__cond :=
        proj2_format  NR_MultiBandInfo__cond NR_MultiBandInfo__list__Format
    NR_MultiBandInfo__F1 NR_MultiBandInfo__F2 NR_MultiBandInfo__F1F2_cond  NR_MultiBandInfo__F1F2_cond2 NR_MultiBandInfo__F2F1_cond.
Opaque NR_MultiBandInfo__cond NR_MultiBandInfo__Format.

