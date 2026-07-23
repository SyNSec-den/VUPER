Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CA_ParametersNR_v1700.

Opaque CA_ParametersNR_v1700__cond CA_ParametersNR_v1700__Format.

Require Import NR.CA_ParametersNRDC_v1700.

Opaque CA_ParametersNRDC_v1700__cond CA_ParametersNRDC_v1700__Format.

Require Import NR.MRDC_Parameters_v1700.

Opaque MRDC_Parameters_v1700__cond MRDC_Parameters_v1700__Format.

Require Import NR.BandParameters_v1710.

Opaque BandParameters_v1710__cond BandParameters_v1710__Format.

Definition BandCombination_v1700__bandList_v1710__Type := list BandParameters_v1710__Type.

Lemma BandCombination_v1700__bandList_v1710__helper1 : (0 <= 1 <= maxSimultaneousBands)%Z. unfold maxSimultaneousBands.
 lia. Qed.
Lemma BandCombination_v1700__bandList_v1710__helper2 : to_bit_sz (Z.to_nat (maxSimultaneousBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSimultaneousBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombination_v1700__bandList_v1710__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombination_v1700__bandList_v1710__cond (z : BandCombination_v1700__bandList_v1710__Type) :=  (1 <= Z.of_nat (length z) <= maxSimultaneousBands)%Z /\ (list_and BandParameters_v1710__cond z) .

Lemma BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__helper1 : (0 <= 1 <= maxBandComb)%Z. unfold maxBandComb.
 lia. Qed.
Lemma BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__helper2 : to_bit_sz (Z.to_nat (maxBandComb - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBandComb - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__Type := bit_string.
Definition BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= maxBandComb)%Z /\ bit_string_len_prop (fst z) (snd z)).
Lemma BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__helper1 : (0 <= 1 <= maxBandComb)%Z. unfold maxBandComb.
 lia. Qed.
Lemma BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__helper2 : to_bit_sz (Z.to_nat (maxBandComb - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBandComb - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__Type := bit_string.
Definition BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= maxBandComb)%Z /\ bit_string_len_prop (fst z) (snd z)).
Record BandCombination_v1700__Type : Set :=
  make__BandCombination_v1700__Type {
    BandCombination_v1700__ca_ParametersNR_v1700 : option CA_ParametersNR_v1700__Type ;
    BandCombination_v1700__ca_ParametersNRDC_v1700 : option CA_ParametersNRDC_v1700__Type ;
    BandCombination_v1700__mrdc_Parameters_v1700 : option MRDC_Parameters_v1700__Type ;
    BandCombination_v1700__bandList_v1710 : option BandCombination_v1700__bandList_v1710__Type ;
    BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17 : option BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__Type ;
    BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17 : option BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__Type ;
}.
Definition BandCombination_v1700__list := (
 Opt CA_ParametersNR_v1700__Type CA_ParametersNR_v1700__cond ::
 Opt CA_ParametersNRDC_v1700__Type CA_ParametersNRDC_v1700__cond ::
 Opt MRDC_Parameters_v1700__Type MRDC_Parameters_v1700__cond ::
 Opt BandCombination_v1700__bandList_v1710__Type BandCombination_v1700__bandList_v1710__cond ::
 Opt BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__Type BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__cond ::
 Opt BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__Type BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__cond ::
 nil).
Definition BandCombination_v1700__cond z := 
  opt_cond CA_ParametersNR_v1700__cond (BandCombination_v1700__ca_ParametersNR_v1700 z) /\
  opt_cond CA_ParametersNRDC_v1700__cond (BandCombination_v1700__ca_ParametersNRDC_v1700 z) /\
  opt_cond MRDC_Parameters_v1700__cond (BandCombination_v1700__mrdc_Parameters_v1700 z) /\
  opt_cond BandCombination_v1700__bandList_v1710__cond (BandCombination_v1700__bandList_v1710 z) /\
  opt_cond BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__cond (BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17 z) /\
  opt_cond BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__cond (BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17 z) /\
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
Definition BandCombination_v1700__bandList_v1710__Format : T_Format BandCombination_v1700__bandList_v1710__Type BandCombination_v1700__bandList_v1710__cond := seq_of_format BandParameters_v1710__Format 1 maxSimultaneousBands BandCombination_v1700__bandList_v1710__helper1 BandCombination_v1700__bandList_v1710__helper2.

Opaque BandCombination_v1700__bandList_v1710__cond BandCombination_v1700__bandList_v1710__Format.

Definition BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__Format : T_Format BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__Type BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 maxBandComb BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__helper1 BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__helper2.
Opaque BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__cond BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__Format.

Definition BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__Format : T_Format BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__Type BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 maxBandComb BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__helper1 BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__helper2.
Opaque BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__cond BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__Format.


Definition BandCombination_v1700__Format_Type := Eval cbn in seq_format_prod BandCombination_v1700__list.
Definition BandCombination_v1700__Format_list : BandCombination_v1700__Format_Type :=
  (CA_ParametersNR_v1700__Format, (CA_ParametersNRDC_v1700__Format, (MRDC_Parameters_v1700__Format, (BandCombination_v1700__bandList_v1710__Format, (BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17__Format, (BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17__Format, unit_format)))))).
Definition BandCombination_v1700__list__Format := (*Eval compute in *) seq_format BandCombination_v1700__list BandCombination_v1700__Format_list.
Definition BandCombination_v1700__F1 z :=
  (BandCombination_v1700__ca_ParametersNR_v1700 z, (BandCombination_v1700__ca_ParametersNRDC_v1700 z, (BandCombination_v1700__mrdc_Parameters_v1700 z, (BandCombination_v1700__bandList_v1710 z, (BandCombination_v1700__supportedBandCombListPerBC_SL_RelayDiscovery_r17 z, (BandCombination_v1700__supportedBandCombListPerBC_SL_NonRelayDiscovery_r17 z, tt)))))).
Definition BandCombination_v1700__F2 (y : seq_type BandCombination_v1700__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__BandCombination_v1700__Type i0 i1 i2 i3 i4 i5
  end.
Lemma BandCombination_v1700__F1F2_cond (z : BandCombination_v1700__Type)
  : BandCombination_v1700__cond z ->
  (seq_cond BandCombination_v1700__list (BandCombination_v1700__F1 z)).
intro H. unfold BandCombination_v1700__cond in H. simpl. auto. Qed.
Lemma BandCombination_v1700__F1F2_cond2 (z : BandCombination_v1700__Type)
 : BandCombination_v1700__F2 (BandCombination_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombination_v1700__F2F1_cond (y : seq_type BandCombination_v1700__list)
  : seq_cond BandCombination_v1700__list y ->
 (BandCombination_v1700__cond (BandCombination_v1700__F2 y)) /\  BandCombination_v1700__F1 (BandCombination_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombination_v1700__cond. simpl in *. auto.
 - simpl. unfold BandCombination_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombination_v1700__Format : T_Format BandCombination_v1700__Type BandCombination_v1700__cond :=
        proj2_format  BandCombination_v1700__cond BandCombination_v1700__list__Format
    BandCombination_v1700__F1 BandCombination_v1700__F2 BandCombination_v1700__F1F2_cond  BandCombination_v1700__F1F2_cond2 BandCombination_v1700__F2F1_cond.
Opaque BandCombination_v1700__cond BandCombination_v1700__Format.

