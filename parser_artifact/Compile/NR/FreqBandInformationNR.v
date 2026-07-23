Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Require Import NR.AggregatedBandwidth.

Opaque AggregatedBandwidth__cond AggregatedBandwidth__Format.

Require Import NR.AggregatedBandwidth.

Opaque AggregatedBandwidth__cond AggregatedBandwidth__Format.

Lemma FreqBandInformationNR__maxCarriersRequestedDL__helper1 : (1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma FreqBandInformationNR__maxCarriersRequestedDL__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FreqBandInformationNR__maxCarriersRequestedDL__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FreqBandInformationNR__maxCarriersRequestedDL__Type := Z.
Definition FreqBandInformationNR__maxCarriersRequestedDL__cond := (fun z => (1 <= z <= maxNrofServingCells)%Z).
Lemma FreqBandInformationNR__maxCarriersRequestedUL__helper1 : (1 <= maxNrofServingCells)%Z. unfold maxNrofServingCells.
 lia. Qed.
Lemma FreqBandInformationNR__maxCarriersRequestedUL__helper2 : to_bit_sz (Z.to_nat (maxNrofServingCells - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofServingCells - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FreqBandInformationNR__maxCarriersRequestedUL__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FreqBandInformationNR__maxCarriersRequestedUL__Type := Z.
Definition FreqBandInformationNR__maxCarriersRequestedUL__cond := (fun z => (1 <= z <= maxNrofServingCells)%Z).
Record FreqBandInformationNR__Type : Set :=
  make__FreqBandInformationNR__Type {
    FreqBandInformationNR__bandNR : FreqBandIndicatorNR__Type ;
    FreqBandInformationNR__maxBandwidthRequestedDL : option AggregatedBandwidth__Type ;
    FreqBandInformationNR__maxBandwidthRequestedUL : option AggregatedBandwidth__Type ;
    FreqBandInformationNR__maxCarriersRequestedDL : option Z ;
    FreqBandInformationNR__maxCarriersRequestedUL : option Z ;
}.
Definition FreqBandInformationNR__list := (
 Nor FreqBandIndicatorNR__Type FreqBandIndicatorNR__cond ::
 Opt AggregatedBandwidth__Type AggregatedBandwidth__cond ::
 Opt AggregatedBandwidth__Type AggregatedBandwidth__cond ::
 Opt Z FreqBandInformationNR__maxCarriersRequestedDL__cond ::
 Opt Z FreqBandInformationNR__maxCarriersRequestedUL__cond ::
 nil).
Definition FreqBandInformationNR__cond z := 
  FreqBandIndicatorNR__cond (FreqBandInformationNR__bandNR z) /\
  opt_cond AggregatedBandwidth__cond (FreqBandInformationNR__maxBandwidthRequestedDL z) /\
  opt_cond AggregatedBandwidth__cond (FreqBandInformationNR__maxBandwidthRequestedUL z) /\
  opt_cond FreqBandInformationNR__maxCarriersRequestedDL__cond (FreqBandInformationNR__maxCarriersRequestedDL z) /\
  opt_cond FreqBandInformationNR__maxCarriersRequestedUL__cond (FreqBandInformationNR__maxCarriersRequestedUL z) /\
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
Definition FreqBandInformationNR__maxCarriersRequestedDL__Format : T_Format Z FreqBandInformationNR__maxCarriersRequestedDL__cond :=
 ranged_int_format (1) (maxNrofServingCells) FreqBandInformationNR__maxCarriersRequestedDL__helper1 FreqBandInformationNR__maxCarriersRequestedDL__helper2.

Opaque FreqBandInformationNR__maxCarriersRequestedDL__cond FreqBandInformationNR__maxCarriersRequestedDL__Format.

Definition FreqBandInformationNR__maxCarriersRequestedUL__Format : T_Format Z FreqBandInformationNR__maxCarriersRequestedUL__cond :=
 ranged_int_format (1) (maxNrofServingCells) FreqBandInformationNR__maxCarriersRequestedUL__helper1 FreqBandInformationNR__maxCarriersRequestedUL__helper2.

Opaque FreqBandInformationNR__maxCarriersRequestedUL__cond FreqBandInformationNR__maxCarriersRequestedUL__Format.


Definition FreqBandInformationNR__Format_Type := Eval cbn in seq_format_prod FreqBandInformationNR__list.
Definition FreqBandInformationNR__Format_list : FreqBandInformationNR__Format_Type :=
  (FreqBandIndicatorNR__Format, (AggregatedBandwidth__Format, (AggregatedBandwidth__Format, (FreqBandInformationNR__maxCarriersRequestedDL__Format, (FreqBandInformationNR__maxCarriersRequestedUL__Format, unit_format))))).
Definition FreqBandInformationNR__list__Format := (*Eval compute in *) seq_format FreqBandInformationNR__list FreqBandInformationNR__Format_list.
Definition FreqBandInformationNR__F1 z :=
  (FreqBandInformationNR__bandNR z, (FreqBandInformationNR__maxBandwidthRequestedDL z, (FreqBandInformationNR__maxBandwidthRequestedUL z, (FreqBandInformationNR__maxCarriersRequestedDL z, (FreqBandInformationNR__maxCarriersRequestedUL z, tt))))).
Definition FreqBandInformationNR__F2 (y : seq_type FreqBandInformationNR__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__FreqBandInformationNR__Type i0 i1 i2 i3 i4
  end.
Lemma FreqBandInformationNR__F1F2_cond (z : FreqBandInformationNR__Type)
  : FreqBandInformationNR__cond z ->
  (seq_cond FreqBandInformationNR__list (FreqBandInformationNR__F1 z)).
intro H. unfold FreqBandInformationNR__cond in H. simpl. auto. Qed.
Lemma FreqBandInformationNR__F1F2_cond2 (z : FreqBandInformationNR__Type)
 : FreqBandInformationNR__F2 (FreqBandInformationNR__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FreqBandInformationNR__F2F1_cond (y : seq_type FreqBandInformationNR__list)
  : seq_cond FreqBandInformationNR__list y ->
 (FreqBandInformationNR__cond (FreqBandInformationNR__F2 y)) /\  FreqBandInformationNR__F1 (FreqBandInformationNR__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FreqBandInformationNR__cond. simpl in *. auto.
 - simpl. unfold FreqBandInformationNR__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FreqBandInformationNR__Format : T_Format FreqBandInformationNR__Type FreqBandInformationNR__cond :=
        proj2_format  FreqBandInformationNR__cond FreqBandInformationNR__list__Format
    FreqBandInformationNR__F1 FreqBandInformationNR__F2 FreqBandInformationNR__F1F2_cond  FreqBandInformationNR__F1F2_cond2 FreqBandInformationNR__F2F1_cond.
Opaque FreqBandInformationNR__cond FreqBandInformationNR__Format.

