Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.AccessStratumRelease.

Opaque AccessStratumRelease__cond AccessStratumRelease__Format.

Require Import NR.PDCP_Parameters.

Opaque PDCP_Parameters__cond PDCP_Parameters__Format.

Require Import NR.RLC_Parameters.

Opaque RLC_Parameters__cond RLC_Parameters__Format.

Require Import NR.MAC_Parameters.

Opaque MAC_Parameters__cond MAC_Parameters__Format.

Require Import NR.Phy_Parameters.

Opaque Phy_Parameters__cond Phy_Parameters__Format.

Require Import NR.RF_Parameters.

Opaque RF_Parameters__cond RF_Parameters__Format.

Require Import NR.MeasAndMobParameters.

Opaque MeasAndMobParameters__cond MeasAndMobParameters__Format.

Require Import NR.UE_NR_CapabilityAddXDD_Mode.

Opaque UE_NR_CapabilityAddXDD_Mode__cond UE_NR_CapabilityAddXDD_Mode__Format.

Require Import NR.UE_NR_CapabilityAddXDD_Mode.

Opaque UE_NR_CapabilityAddXDD_Mode__cond UE_NR_CapabilityAddXDD_Mode__Format.

Require Import NR.UE_NR_CapabilityAddFRX_Mode.

Opaque UE_NR_CapabilityAddFRX_Mode__cond UE_NR_CapabilityAddFRX_Mode__Format.

Require Import NR.UE_NR_CapabilityAddFRX_Mode.

Opaque UE_NR_CapabilityAddFRX_Mode__cond UE_NR_CapabilityAddFRX_Mode__Format.

Require Import NR.FeatureSets.

Opaque FeatureSets__cond FeatureSets__Format.

Require Import NR.FeatureSetCombination.

Opaque FeatureSetCombination__cond FeatureSetCombination__Format.

Definition UE_NR_Capability__featureSetCombinations__Type := list FeatureSetCombination__Type.

Lemma UE_NR_Capability__featureSetCombinations__helper1 : (0 <= 1 <= maxFeatureSetCombinations)%Z. unfold maxFeatureSetCombinations.
 lia. Qed.
Lemma UE_NR_Capability__featureSetCombinations__helper2 : to_bit_sz (Z.to_nat (maxFeatureSetCombinations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxFeatureSetCombinations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UE_NR_Capability__featureSetCombinations__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UE_NR_Capability__featureSetCombinations__cond (z : UE_NR_Capability__featureSetCombinations__Type) :=  (1 <= Z.of_nat (length z) <= maxFeatureSetCombinations)%Z /\ (list_and FeatureSetCombination__cond z) .

Require Import NR.UE_NR_Capability_v1530.

Opaque UE_NR_Capability_v1530__cond UE_NR_Capability_v1530__Format.

Record UE_NR_Capability__Type : Set :=
  make__UE_NR_Capability__Type {
    UE_NR_Capability__accessStratumRelease : AccessStratumRelease__Type ;
    UE_NR_Capability__pdcp_Parameters : PDCP_Parameters__Type ;
    UE_NR_Capability__rlc_Parameters : option RLC_Parameters__Type ;
    UE_NR_Capability__mac_Parameters : option MAC_Parameters__Type ;
    UE_NR_Capability__phy_Parameters : Phy_Parameters__Type ;
    UE_NR_Capability__rf_Parameters : RF_Parameters__Type ;
    UE_NR_Capability__measAndMobParameters : option MeasAndMobParameters__Type ;
    UE_NR_Capability__fdd_Add_UE_NR_Capabilities : option UE_NR_CapabilityAddXDD_Mode__Type ;
    UE_NR_Capability__tdd_Add_UE_NR_Capabilities : option UE_NR_CapabilityAddXDD_Mode__Type ;
    UE_NR_Capability__fr1_Add_UE_NR_Capabilities : option UE_NR_CapabilityAddFRX_Mode__Type ;
    UE_NR_Capability__fr2_Add_UE_NR_Capabilities : option UE_NR_CapabilityAddFRX_Mode__Type ;
    UE_NR_Capability__featureSets : option FeatureSets__Type ;
    UE_NR_Capability__featureSetCombinations : option UE_NR_Capability__featureSetCombinations__Type ;
    UE_NR_Capability__lateNonCriticalExtension : option octet_string ;
    UE_NR_Capability__nonCriticalExtension : option UE_NR_Capability_v1530__Type ;
}.
Definition UE_NR_Capability__list := (
 Nor AccessStratumRelease__Type AccessStratumRelease__cond ::
 Nor PDCP_Parameters__Type PDCP_Parameters__cond ::
 Opt RLC_Parameters__Type RLC_Parameters__cond ::
 Opt MAC_Parameters__Type MAC_Parameters__cond ::
 Nor Phy_Parameters__Type Phy_Parameters__cond ::
 Nor RF_Parameters__Type RF_Parameters__cond ::
 Opt MeasAndMobParameters__Type MeasAndMobParameters__cond ::
 Opt UE_NR_CapabilityAddXDD_Mode__Type UE_NR_CapabilityAddXDD_Mode__cond ::
 Opt UE_NR_CapabilityAddXDD_Mode__Type UE_NR_CapabilityAddXDD_Mode__cond ::
 Opt UE_NR_CapabilityAddFRX_Mode__Type UE_NR_CapabilityAddFRX_Mode__cond ::
 Opt UE_NR_CapabilityAddFRX_Mode__Type UE_NR_CapabilityAddFRX_Mode__cond ::
 Opt FeatureSets__Type FeatureSets__cond ::
 Opt UE_NR_Capability__featureSetCombinations__Type UE_NR_Capability__featureSetCombinations__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UE_NR_Capability_v1530__Type UE_NR_Capability_v1530__cond ::
 nil).
Definition UE_NR_Capability__cond z := 
  AccessStratumRelease__cond (UE_NR_Capability__accessStratumRelease z) /\
  PDCP_Parameters__cond (UE_NR_Capability__pdcp_Parameters z) /\
  opt_cond RLC_Parameters__cond (UE_NR_Capability__rlc_Parameters z) /\
  opt_cond MAC_Parameters__cond (UE_NR_Capability__mac_Parameters z) /\
  Phy_Parameters__cond (UE_NR_Capability__phy_Parameters z) /\
  RF_Parameters__cond (UE_NR_Capability__rf_Parameters z) /\
  opt_cond MeasAndMobParameters__cond (UE_NR_Capability__measAndMobParameters z) /\
  opt_cond UE_NR_CapabilityAddXDD_Mode__cond (UE_NR_Capability__fdd_Add_UE_NR_Capabilities z) /\
  opt_cond UE_NR_CapabilityAddXDD_Mode__cond (UE_NR_Capability__tdd_Add_UE_NR_Capabilities z) /\
  opt_cond UE_NR_CapabilityAddFRX_Mode__cond (UE_NR_Capability__fr1_Add_UE_NR_Capabilities z) /\
  opt_cond UE_NR_CapabilityAddFRX_Mode__cond (UE_NR_Capability__fr2_Add_UE_NR_Capabilities z) /\
  opt_cond FeatureSets__cond (UE_NR_Capability__featureSets z) /\
  opt_cond UE_NR_Capability__featureSetCombinations__cond (UE_NR_Capability__featureSetCombinations z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UE_NR_Capability__lateNonCriticalExtension z) /\
  opt_cond UE_NR_Capability_v1530__cond (UE_NR_Capability__nonCriticalExtension z) /\
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
Definition UE_NR_Capability__featureSetCombinations__Format : T_Format UE_NR_Capability__featureSetCombinations__Type UE_NR_Capability__featureSetCombinations__cond := seq_of_format FeatureSetCombination__Format 1 maxFeatureSetCombinations UE_NR_Capability__featureSetCombinations__helper1 UE_NR_Capability__featureSetCombinations__helper2.

Opaque UE_NR_Capability__featureSetCombinations__cond UE_NR_Capability__featureSetCombinations__Format.


Definition UE_NR_Capability__Format_Type := Eval cbn in seq_format_prod UE_NR_Capability__list.
Definition UE_NR_Capability__Format_list : UE_NR_Capability__Format_Type :=
  (AccessStratumRelease__Format, (PDCP_Parameters__Format, (RLC_Parameters__Format, (MAC_Parameters__Format, (Phy_Parameters__Format, (RF_Parameters__Format, (MeasAndMobParameters__Format, (UE_NR_CapabilityAddXDD_Mode__Format, (UE_NR_CapabilityAddXDD_Mode__Format, (UE_NR_CapabilityAddFRX_Mode__Format, (UE_NR_CapabilityAddFRX_Mode__Format, (FeatureSets__Format, (UE_NR_Capability__featureSetCombinations__Format, (octet_string_nc__Format, (UE_NR_Capability_v1530__Format, unit_format))))))))))))))).
Definition UE_NR_Capability__list__Format := (*Eval compute in *) seq_format UE_NR_Capability__list UE_NR_Capability__Format_list.
Definition UE_NR_Capability__F1 z :=
  (UE_NR_Capability__accessStratumRelease z, (UE_NR_Capability__pdcp_Parameters z, (UE_NR_Capability__rlc_Parameters z, (UE_NR_Capability__mac_Parameters z, (UE_NR_Capability__phy_Parameters z, (UE_NR_Capability__rf_Parameters z, (UE_NR_Capability__measAndMobParameters z, (UE_NR_Capability__fdd_Add_UE_NR_Capabilities z, (UE_NR_Capability__tdd_Add_UE_NR_Capabilities z, (UE_NR_Capability__fr1_Add_UE_NR_Capabilities z, (UE_NR_Capability__fr2_Add_UE_NR_Capabilities z, (UE_NR_Capability__featureSets z, (UE_NR_Capability__featureSetCombinations z, (UE_NR_Capability__lateNonCriticalExtension z, (UE_NR_Capability__nonCriticalExtension z, tt))))))))))))))).
Definition UE_NR_Capability__F2 (y : seq_type UE_NR_Capability__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, _)))))))))))))))=>
    make__UE_NR_Capability__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14
  end.
Lemma UE_NR_Capability__F1F2_cond (z : UE_NR_Capability__Type)
  : UE_NR_Capability__cond z ->
  (seq_cond UE_NR_Capability__list (UE_NR_Capability__F1 z)).
intro H. unfold UE_NR_Capability__cond in H. simpl. auto. Qed.
Lemma UE_NR_Capability__F1F2_cond2 (z : UE_NR_Capability__Type)
 : UE_NR_Capability__F2 (UE_NR_Capability__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_NR_Capability__F2F1_cond (y : seq_type UE_NR_Capability__list)
  : seq_cond UE_NR_Capability__list y ->
 (UE_NR_Capability__cond (UE_NR_Capability__F2 y)) /\  UE_NR_Capability__F1 (UE_NR_Capability__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_NR_Capability__cond. simpl in *. auto.
 - simpl. unfold UE_NR_Capability__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_NR_Capability__Format : T_Format UE_NR_Capability__Type UE_NR_Capability__cond :=
        proj2_format  UE_NR_Capability__cond UE_NR_Capability__list__Format
    UE_NR_Capability__F1 UE_NR_Capability__F2 UE_NR_Capability__F1F2_cond  UE_NR_Capability__F1F2_cond2 UE_NR_Capability__F2F1_cond.
Opaque UE_NR_Capability__cond UE_NR_Capability__Format.

