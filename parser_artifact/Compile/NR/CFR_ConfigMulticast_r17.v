Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__helper1 : (0 <= 37949)%Z.  lia. Qed.
Lemma CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__helper2 : to_bit_sz (Z.to_nat (37949 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (37949 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__Type := Z.
Definition CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__cond := (fun z => (0 <= z <= 37949)%Z).
Require Import NR.PDCCH_Config.

Opaque PDCCH_Config__cond PDCCH_Config__Format.

Require Import NR.PDSCH_Config.

Opaque PDSCH_Config__cond PDSCH_Config__Format.

Require Import NR.SPS_ConfigMulticastToAddModList_r17.

Opaque SPS_ConfigMulticastToAddModList_r17__cond SPS_ConfigMulticastToAddModList_r17__Format.

Require Import NR.SPS_ConfigMulticastToReleaseList_r17.

Opaque SPS_ConfigMulticastToReleaseList_r17__cond SPS_ConfigMulticastToReleaseList_r17__Format.

Record CFR_ConfigMulticast_r17__Type : Set :=
  make__CFR_ConfigMulticast_r17__Type {
    CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17 : option Z ;
    CFR_ConfigMulticast_r17__pdcch_ConfigMulticast_r17 : option PDCCH_Config__Type ;
    CFR_ConfigMulticast_r17__pdsch_ConfigMulticast_r17 : option PDSCH_Config__Type ;
    CFR_ConfigMulticast_r17__sps_ConfigMulticastToAddModList_r17 : option SPS_ConfigMulticastToAddModList_r17__Type ;
    CFR_ConfigMulticast_r17__sps_ConfigMulticastToReleaseList_r17 : option SPS_ConfigMulticastToReleaseList_r17__Type ;
}.
Definition CFR_ConfigMulticast_r17__list := (
 Opt Z CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__cond ::
 Opt PDCCH_Config__Type PDCCH_Config__cond ::
 Opt PDSCH_Config__Type PDSCH_Config__cond ::
 Opt SPS_ConfigMulticastToAddModList_r17__Type SPS_ConfigMulticastToAddModList_r17__cond ::
 Opt SPS_ConfigMulticastToReleaseList_r17__Type SPS_ConfigMulticastToReleaseList_r17__cond ::
 nil).
Definition CFR_ConfigMulticast_r17__cond z := 
  opt_cond CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__cond (CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17 z) /\
  opt_cond PDCCH_Config__cond (CFR_ConfigMulticast_r17__pdcch_ConfigMulticast_r17 z) /\
  opt_cond PDSCH_Config__cond (CFR_ConfigMulticast_r17__pdsch_ConfigMulticast_r17 z) /\
  opt_cond SPS_ConfigMulticastToAddModList_r17__cond (CFR_ConfigMulticast_r17__sps_ConfigMulticastToAddModList_r17 z) /\
  opt_cond SPS_ConfigMulticastToReleaseList_r17__cond (CFR_ConfigMulticast_r17__sps_ConfigMulticastToReleaseList_r17 z) /\
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
Definition CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__Format : T_Format Z CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__cond :=
 ranged_int_format (0) (37949) CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__helper1 CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__helper2.

Opaque CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__cond CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__Format.


Definition CFR_ConfigMulticast_r17__Format_Type := Eval cbn in seq_format_prod CFR_ConfigMulticast_r17__list.
Definition CFR_ConfigMulticast_r17__Format_list : CFR_ConfigMulticast_r17__Format_Type :=
  (CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17__Format, (PDCCH_Config__Format, (PDSCH_Config__Format, (SPS_ConfigMulticastToAddModList_r17__Format, (SPS_ConfigMulticastToReleaseList_r17__Format, unit_format))))).
Definition CFR_ConfigMulticast_r17__list__Format := (*Eval compute in *) seq_format CFR_ConfigMulticast_r17__list CFR_ConfigMulticast_r17__Format_list.
Definition CFR_ConfigMulticast_r17__F1 z :=
  (CFR_ConfigMulticast_r17__locationAndBandwidthMulticast_r17 z, (CFR_ConfigMulticast_r17__pdcch_ConfigMulticast_r17 z, (CFR_ConfigMulticast_r17__pdsch_ConfigMulticast_r17 z, (CFR_ConfigMulticast_r17__sps_ConfigMulticastToAddModList_r17 z, (CFR_ConfigMulticast_r17__sps_ConfigMulticastToReleaseList_r17 z, tt))))).
Definition CFR_ConfigMulticast_r17__F2 (y : seq_type CFR_ConfigMulticast_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__CFR_ConfigMulticast_r17__Type i0 i1 i2 i3 i4
  end.
Lemma CFR_ConfigMulticast_r17__F1F2_cond (z : CFR_ConfigMulticast_r17__Type)
  : CFR_ConfigMulticast_r17__cond z ->
  (seq_cond CFR_ConfigMulticast_r17__list (CFR_ConfigMulticast_r17__F1 z)).
intro H. unfold CFR_ConfigMulticast_r17__cond in H. simpl. auto. Qed.
Lemma CFR_ConfigMulticast_r17__F1F2_cond2 (z : CFR_ConfigMulticast_r17__Type)
 : CFR_ConfigMulticast_r17__F2 (CFR_ConfigMulticast_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CFR_ConfigMulticast_r17__F2F1_cond (y : seq_type CFR_ConfigMulticast_r17__list)
  : seq_cond CFR_ConfigMulticast_r17__list y ->
 (CFR_ConfigMulticast_r17__cond (CFR_ConfigMulticast_r17__F2 y)) /\  CFR_ConfigMulticast_r17__F1 (CFR_ConfigMulticast_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CFR_ConfigMulticast_r17__cond. simpl in *. auto.
 - simpl. unfold CFR_ConfigMulticast_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CFR_ConfigMulticast_r17__Format : T_Format CFR_ConfigMulticast_r17__Type CFR_ConfigMulticast_r17__cond :=
        proj2_format  CFR_ConfigMulticast_r17__cond CFR_ConfigMulticast_r17__list__Format
    CFR_ConfigMulticast_r17__F1 CFR_ConfigMulticast_r17__F2 CFR_ConfigMulticast_r17__F1F2_cond  CFR_ConfigMulticast_r17__F1F2_cond2 CFR_ConfigMulticast_r17__F2F1_cond.
Opaque CFR_ConfigMulticast_r17__cond CFR_ConfigMulticast_r17__Format.

