Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Lemma FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__helper1 : (1 <= maxNrofPhysicalResourceBlocks)%Z. unfold maxNrofPhysicalResourceBlocks.
 lia. Qed.
Lemma FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__Type := Z.
Definition FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__cond := (fun z => (1 <= z <= maxNrofPhysicalResourceBlocks)%Z).
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Record FrequencyConfig_NR_r16__Type : Set :=
  make__FrequencyConfig_NR_r16__Type {
    FrequencyConfig_NR_r16__freqBandIndicatorNR_r16 : FreqBandIndicatorNR__Type ;
    FrequencyConfig_NR_r16__carrierCenterFreq_NR_r16 : ARFCN_ValueNR__Type ;
    FrequencyConfig_NR_r16__carrierBandwidth_NR_r16 : Z ;
    FrequencyConfig_NR_r16__subcarrierSpacing_NR_r16 : SubcarrierSpacing__Type ;
}.
Definition FrequencyConfig_NR_r16__list := (
 Nor FreqBandIndicatorNR__Type FreqBandIndicatorNR__cond ::
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor Z FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 nil).
Definition FrequencyConfig_NR_r16__cond z := 
  FreqBandIndicatorNR__cond (FrequencyConfig_NR_r16__freqBandIndicatorNR_r16 z) /\
  ARFCN_ValueNR__cond (FrequencyConfig_NR_r16__carrierCenterFreq_NR_r16 z) /\
  FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__cond (FrequencyConfig_NR_r16__carrierBandwidth_NR_r16 z) /\
  SubcarrierSpacing__cond (FrequencyConfig_NR_r16__subcarrierSpacing_NR_r16 z) /\
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
Definition FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__Format : T_Format Z FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__cond :=
 ranged_int_format (1) (maxNrofPhysicalResourceBlocks) FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__helper1 FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__helper2.

Opaque FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__cond FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__Format.


Definition FrequencyConfig_NR_r16__Format_Type := Eval cbn in seq_format_prod FrequencyConfig_NR_r16__list.
Definition FrequencyConfig_NR_r16__Format_list : FrequencyConfig_NR_r16__Format_Type :=
  (FreqBandIndicatorNR__Format, (ARFCN_ValueNR__Format, (FrequencyConfig_NR_r16__carrierBandwidth_NR_r16__Format, (SubcarrierSpacing__Format, unit_format)))).
Definition FrequencyConfig_NR_r16__list__Format := (*Eval compute in *) seq_format FrequencyConfig_NR_r16__list FrequencyConfig_NR_r16__Format_list.
Definition FrequencyConfig_NR_r16__F1 z :=
  (FrequencyConfig_NR_r16__freqBandIndicatorNR_r16 z, (FrequencyConfig_NR_r16__carrierCenterFreq_NR_r16 z, (FrequencyConfig_NR_r16__carrierBandwidth_NR_r16 z, (FrequencyConfig_NR_r16__subcarrierSpacing_NR_r16 z, tt)))).
Definition FrequencyConfig_NR_r16__F2 (y : seq_type FrequencyConfig_NR_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__FrequencyConfig_NR_r16__Type i0 i1 i2 i3
  end.
Lemma FrequencyConfig_NR_r16__F1F2_cond (z : FrequencyConfig_NR_r16__Type)
  : FrequencyConfig_NR_r16__cond z ->
  (seq_cond FrequencyConfig_NR_r16__list (FrequencyConfig_NR_r16__F1 z)).
intro H. unfold FrequencyConfig_NR_r16__cond in H. simpl. auto. Qed.
Lemma FrequencyConfig_NR_r16__F1F2_cond2 (z : FrequencyConfig_NR_r16__Type)
 : FrequencyConfig_NR_r16__F2 (FrequencyConfig_NR_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FrequencyConfig_NR_r16__F2F1_cond (y : seq_type FrequencyConfig_NR_r16__list)
  : seq_cond FrequencyConfig_NR_r16__list y ->
 (FrequencyConfig_NR_r16__cond (FrequencyConfig_NR_r16__F2 y)) /\  FrequencyConfig_NR_r16__F1 (FrequencyConfig_NR_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FrequencyConfig_NR_r16__cond. simpl in *. auto.
 - simpl. unfold FrequencyConfig_NR_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FrequencyConfig_NR_r16__Format : T_Format FrequencyConfig_NR_r16__Type FrequencyConfig_NR_r16__cond :=
        proj2_format  FrequencyConfig_NR_r16__cond FrequencyConfig_NR_r16__list__Format
    FrequencyConfig_NR_r16__F1 FrequencyConfig_NR_r16__F2 FrequencyConfig_NR_r16__F1F2_cond  FrequencyConfig_NR_r16__F1F2_cond2 FrequencyConfig_NR_r16__F2F1_cond.
Opaque FrequencyConfig_NR_r16__cond FrequencyConfig_NR_r16__Format.

