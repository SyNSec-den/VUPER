Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.AccessStratumReleaseSidelink_r16.

Opaque AccessStratumReleaseSidelink_r16__cond AccessStratumReleaseSidelink_r16__Format.

Require Import NR.PDCP_ParametersSidelink_r16.

Opaque PDCP_ParametersSidelink_r16__cond PDCP_ParametersSidelink_r16__Format.

Require Import NR.RLC_ParametersSidelink_r16.

Opaque RLC_ParametersSidelink_r16__cond RLC_ParametersSidelink_r16__Format.

Require Import NR.BandCombinationListSidelinkNR_r16.

Opaque BandCombinationListSidelinkNR_r16__cond BandCombinationListSidelinkNR_r16__Format.

Require Import NR.BandSidelinkPC5_r16.

Opaque BandSidelinkPC5_r16__cond BandSidelinkPC5_r16__Format.

Definition UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__Type := list BandSidelinkPC5_r16__Type.

Lemma UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__helper1 : (0 <= 1 <= maxBands)%Z. unfold maxBands.
 lia. Qed.
Lemma UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__helper2 : to_bit_sz (Z.to_nat (maxBands - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBands - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__cond (z : UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxBands)%Z /\ (list_and BandSidelinkPC5_r16__cond z) .

Require Import NR.FreqBandList.

Opaque FreqBandList__cond FreqBandList__Format.

Require Import NR.UECapabilityInformationSidelink_v1700_IEs.

Opaque UECapabilityInformationSidelink_v1700_IEs__cond UECapabilityInformationSidelink_v1700_IEs__Format.

Record UECapabilityInformationSidelink_r16_IEs__Type : Set :=
  make__UECapabilityInformationSidelink_r16_IEs__Type {
    UECapabilityInformationSidelink_r16_IEs__accessStratumReleaseSidelink_r16 : AccessStratumReleaseSidelink_r16__Type ;
    UECapabilityInformationSidelink_r16_IEs__pdcp_ParametersSidelink_r16 : option PDCP_ParametersSidelink_r16__Type ;
    UECapabilityInformationSidelink_r16_IEs__rlc_ParametersSidelink_r16 : option RLC_ParametersSidelink_r16__Type ;
    UECapabilityInformationSidelink_r16_IEs__supportedBandCombinationListSidelinkNR_r16 : option BandCombinationListSidelinkNR_r16__Type ;
    UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16 : option UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__Type ;
    UECapabilityInformationSidelink_r16_IEs__appliedFreqBandListFilter_r16 : option FreqBandList__Type ;
    UECapabilityInformationSidelink_r16_IEs__lateNonCriticalExtension : option octet_string ;
    UECapabilityInformationSidelink_r16_IEs__nonCriticalExtension : option UECapabilityInformationSidelink_v1700_IEs__Type ;
}.
Definition UECapabilityInformationSidelink_r16_IEs__list := (
 Nor AccessStratumReleaseSidelink_r16__Type AccessStratumReleaseSidelink_r16__cond ::
 Opt PDCP_ParametersSidelink_r16__Type PDCP_ParametersSidelink_r16__cond ::
 Opt RLC_ParametersSidelink_r16__Type RLC_ParametersSidelink_r16__cond ::
 Opt BandCombinationListSidelinkNR_r16__Type BandCombinationListSidelinkNR_r16__cond ::
 Opt UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__Type UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__cond ::
 Opt FreqBandList__Type FreqBandList__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UECapabilityInformationSidelink_v1700_IEs__Type UECapabilityInformationSidelink_v1700_IEs__cond ::
 nil).
Definition UECapabilityInformationSidelink_r16_IEs__cond z := 
  AccessStratumReleaseSidelink_r16__cond (UECapabilityInformationSidelink_r16_IEs__accessStratumReleaseSidelink_r16 z) /\
  opt_cond PDCP_ParametersSidelink_r16__cond (UECapabilityInformationSidelink_r16_IEs__pdcp_ParametersSidelink_r16 z) /\
  opt_cond RLC_ParametersSidelink_r16__cond (UECapabilityInformationSidelink_r16_IEs__rlc_ParametersSidelink_r16 z) /\
  opt_cond BandCombinationListSidelinkNR_r16__cond (UECapabilityInformationSidelink_r16_IEs__supportedBandCombinationListSidelinkNR_r16 z) /\
  opt_cond UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__cond (UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16 z) /\
  opt_cond FreqBandList__cond (UECapabilityInformationSidelink_r16_IEs__appliedFreqBandListFilter_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UECapabilityInformationSidelink_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond UECapabilityInformationSidelink_v1700_IEs__cond (UECapabilityInformationSidelink_r16_IEs__nonCriticalExtension z) /\
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
Definition UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__Format : T_Format UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__Type UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__cond := seq_of_format BandSidelinkPC5_r16__Format 1 maxBands UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__helper1 UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__helper2.

Opaque UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__cond UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__Format.


Definition UECapabilityInformationSidelink_r16_IEs__Format_Type := Eval cbn in seq_format_prod UECapabilityInformationSidelink_r16_IEs__list.
Definition UECapabilityInformationSidelink_r16_IEs__Format_list : UECapabilityInformationSidelink_r16_IEs__Format_Type :=
  (AccessStratumReleaseSidelink_r16__Format, (PDCP_ParametersSidelink_r16__Format, (RLC_ParametersSidelink_r16__Format, (BandCombinationListSidelinkNR_r16__Format, (UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16__Format, (FreqBandList__Format, (octet_string_nc__Format, (UECapabilityInformationSidelink_v1700_IEs__Format, unit_format)))))))).
Definition UECapabilityInformationSidelink_r16_IEs__list__Format := (*Eval compute in *) seq_format UECapabilityInformationSidelink_r16_IEs__list UECapabilityInformationSidelink_r16_IEs__Format_list.
Definition UECapabilityInformationSidelink_r16_IEs__F1 z :=
  (UECapabilityInformationSidelink_r16_IEs__accessStratumReleaseSidelink_r16 z, (UECapabilityInformationSidelink_r16_IEs__pdcp_ParametersSidelink_r16 z, (UECapabilityInformationSidelink_r16_IEs__rlc_ParametersSidelink_r16 z, (UECapabilityInformationSidelink_r16_IEs__supportedBandCombinationListSidelinkNR_r16 z, (UECapabilityInformationSidelink_r16_IEs__supportedBandListSidelink_r16 z, (UECapabilityInformationSidelink_r16_IEs__appliedFreqBandListFilter_r16 z, (UECapabilityInformationSidelink_r16_IEs__lateNonCriticalExtension z, (UECapabilityInformationSidelink_r16_IEs__nonCriticalExtension z, tt)))))))).
Definition UECapabilityInformationSidelink_r16_IEs__F2 (y : seq_type UECapabilityInformationSidelink_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__UECapabilityInformationSidelink_r16_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma UECapabilityInformationSidelink_r16_IEs__F1F2_cond (z : UECapabilityInformationSidelink_r16_IEs__Type)
  : UECapabilityInformationSidelink_r16_IEs__cond z ->
  (seq_cond UECapabilityInformationSidelink_r16_IEs__list (UECapabilityInformationSidelink_r16_IEs__F1 z)).
intro H. unfold UECapabilityInformationSidelink_r16_IEs__cond in H. simpl. auto. Qed.
Lemma UECapabilityInformationSidelink_r16_IEs__F1F2_cond2 (z : UECapabilityInformationSidelink_r16_IEs__Type)
 : UECapabilityInformationSidelink_r16_IEs__F2 (UECapabilityInformationSidelink_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UECapabilityInformationSidelink_r16_IEs__F2F1_cond (y : seq_type UECapabilityInformationSidelink_r16_IEs__list)
  : seq_cond UECapabilityInformationSidelink_r16_IEs__list y ->
 (UECapabilityInformationSidelink_r16_IEs__cond (UECapabilityInformationSidelink_r16_IEs__F2 y)) /\  UECapabilityInformationSidelink_r16_IEs__F1 (UECapabilityInformationSidelink_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UECapabilityInformationSidelink_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold UECapabilityInformationSidelink_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UECapabilityInformationSidelink_r16_IEs__Format : T_Format UECapabilityInformationSidelink_r16_IEs__Type UECapabilityInformationSidelink_r16_IEs__cond :=
        proj2_format  UECapabilityInformationSidelink_r16_IEs__cond UECapabilityInformationSidelink_r16_IEs__list__Format
    UECapabilityInformationSidelink_r16_IEs__F1 UECapabilityInformationSidelink_r16_IEs__F2 UECapabilityInformationSidelink_r16_IEs__F1F2_cond  UECapabilityInformationSidelink_r16_IEs__F1F2_cond2 UECapabilityInformationSidelink_r16_IEs__F2F1_cond.
Opaque UECapabilityInformationSidelink_r16_IEs__cond UECapabilityInformationSidelink_r16_IEs__Format.

