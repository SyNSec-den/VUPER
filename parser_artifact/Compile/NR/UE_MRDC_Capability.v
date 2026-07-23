Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasAndMobParametersMRDC.

Opaque MeasAndMobParametersMRDC__cond MeasAndMobParametersMRDC__Format.

Require Import NR.Phy_ParametersMRDC.

Opaque Phy_ParametersMRDC__cond Phy_ParametersMRDC__Format.

Require Import NR.RF_ParametersMRDC.

Opaque RF_ParametersMRDC__cond RF_ParametersMRDC__Format.

Require Import NR.GeneralParametersMRDC_XDD_Diff.

Opaque GeneralParametersMRDC_XDD_Diff__cond GeneralParametersMRDC_XDD_Diff__Format.

Require Import NR.UE_MRDC_CapabilityAddXDD_Mode.

Opaque UE_MRDC_CapabilityAddXDD_Mode__cond UE_MRDC_CapabilityAddXDD_Mode__Format.

Require Import NR.UE_MRDC_CapabilityAddXDD_Mode.

Opaque UE_MRDC_CapabilityAddXDD_Mode__cond UE_MRDC_CapabilityAddXDD_Mode__Format.

Require Import NR.UE_MRDC_CapabilityAddFRX_Mode.

Opaque UE_MRDC_CapabilityAddFRX_Mode__cond UE_MRDC_CapabilityAddFRX_Mode__Format.

Require Import NR.UE_MRDC_CapabilityAddFRX_Mode.

Opaque UE_MRDC_CapabilityAddFRX_Mode__cond UE_MRDC_CapabilityAddFRX_Mode__Format.

Require Import NR.FeatureSetCombination.

Opaque FeatureSetCombination__cond FeatureSetCombination__Format.

Definition UE_MRDC_Capability__featureSetCombinations__Type := list FeatureSetCombination__Type.

Lemma UE_MRDC_Capability__featureSetCombinations__helper1 : (0 <= 1 <= maxFeatureSetCombinations)%Z. unfold maxFeatureSetCombinations.
 lia. Qed.
Lemma UE_MRDC_Capability__featureSetCombinations__helper2 : to_bit_sz (Z.to_nat (maxFeatureSetCombinations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxFeatureSetCombinations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply UE_MRDC_Capability__featureSetCombinations__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UE_MRDC_Capability__featureSetCombinations__cond (z : UE_MRDC_Capability__featureSetCombinations__Type) :=  (1 <= Z.of_nat (length z) <= maxFeatureSetCombinations)%Z /\ (list_and FeatureSetCombination__cond z) .

Require Import NR.PDCP_ParametersMRDC.

Opaque PDCP_ParametersMRDC__cond PDCP_ParametersMRDC__Format.

Require Import NR.UE_MRDC_Capability_v1560.

Opaque UE_MRDC_Capability_v1560__cond UE_MRDC_Capability_v1560__Format.

Record UE_MRDC_Capability__Type : Set :=
  make__UE_MRDC_Capability__Type {
    UE_MRDC_Capability__measAndMobParametersMRDC : option MeasAndMobParametersMRDC__Type ;
    UE_MRDC_Capability__phy_ParametersMRDC_v1530 : option Phy_ParametersMRDC__Type ;
    UE_MRDC_Capability__rf_ParametersMRDC : RF_ParametersMRDC__Type ;
    UE_MRDC_Capability__generalParametersMRDC : option GeneralParametersMRDC_XDD_Diff__Type ;
    UE_MRDC_Capability__fdd_Add_UE_MRDC_Capabilities : option UE_MRDC_CapabilityAddXDD_Mode__Type ;
    UE_MRDC_Capability__tdd_Add_UE_MRDC_Capabilities : option UE_MRDC_CapabilityAddXDD_Mode__Type ;
    UE_MRDC_Capability__fr1_Add_UE_MRDC_Capabilities : option UE_MRDC_CapabilityAddFRX_Mode__Type ;
    UE_MRDC_Capability__fr2_Add_UE_MRDC_Capabilities : option UE_MRDC_CapabilityAddFRX_Mode__Type ;
    UE_MRDC_Capability__featureSetCombinations : option UE_MRDC_Capability__featureSetCombinations__Type ;
    UE_MRDC_Capability__pdcp_ParametersMRDC_v1530 : option PDCP_ParametersMRDC__Type ;
    UE_MRDC_Capability__lateNonCriticalExtension : option octet_string ;
    UE_MRDC_Capability__nonCriticalExtension : option UE_MRDC_Capability_v1560__Type ;
}.
Definition UE_MRDC_Capability__list := (
 Opt MeasAndMobParametersMRDC__Type MeasAndMobParametersMRDC__cond ::
 Opt Phy_ParametersMRDC__Type Phy_ParametersMRDC__cond ::
 Nor RF_ParametersMRDC__Type RF_ParametersMRDC__cond ::
 Opt GeneralParametersMRDC_XDD_Diff__Type GeneralParametersMRDC_XDD_Diff__cond ::
 Opt UE_MRDC_CapabilityAddXDD_Mode__Type UE_MRDC_CapabilityAddXDD_Mode__cond ::
 Opt UE_MRDC_CapabilityAddXDD_Mode__Type UE_MRDC_CapabilityAddXDD_Mode__cond ::
 Opt UE_MRDC_CapabilityAddFRX_Mode__Type UE_MRDC_CapabilityAddFRX_Mode__cond ::
 Opt UE_MRDC_CapabilityAddFRX_Mode__Type UE_MRDC_CapabilityAddFRX_Mode__cond ::
 Opt UE_MRDC_Capability__featureSetCombinations__Type UE_MRDC_Capability__featureSetCombinations__cond ::
 Opt PDCP_ParametersMRDC__Type PDCP_ParametersMRDC__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UE_MRDC_Capability_v1560__Type UE_MRDC_Capability_v1560__cond ::
 nil).
Definition UE_MRDC_Capability__cond z := 
  opt_cond MeasAndMobParametersMRDC__cond (UE_MRDC_Capability__measAndMobParametersMRDC z) /\
  opt_cond Phy_ParametersMRDC__cond (UE_MRDC_Capability__phy_ParametersMRDC_v1530 z) /\
  RF_ParametersMRDC__cond (UE_MRDC_Capability__rf_ParametersMRDC z) /\
  opt_cond GeneralParametersMRDC_XDD_Diff__cond (UE_MRDC_Capability__generalParametersMRDC z) /\
  opt_cond UE_MRDC_CapabilityAddXDD_Mode__cond (UE_MRDC_Capability__fdd_Add_UE_MRDC_Capabilities z) /\
  opt_cond UE_MRDC_CapabilityAddXDD_Mode__cond (UE_MRDC_Capability__tdd_Add_UE_MRDC_Capabilities z) /\
  opt_cond UE_MRDC_CapabilityAddFRX_Mode__cond (UE_MRDC_Capability__fr1_Add_UE_MRDC_Capabilities z) /\
  opt_cond UE_MRDC_CapabilityAddFRX_Mode__cond (UE_MRDC_Capability__fr2_Add_UE_MRDC_Capabilities z) /\
  opt_cond UE_MRDC_Capability__featureSetCombinations__cond (UE_MRDC_Capability__featureSetCombinations z) /\
  opt_cond PDCP_ParametersMRDC__cond (UE_MRDC_Capability__pdcp_ParametersMRDC_v1530 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UE_MRDC_Capability__lateNonCriticalExtension z) /\
  opt_cond UE_MRDC_Capability_v1560__cond (UE_MRDC_Capability__nonCriticalExtension z) /\
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
Definition UE_MRDC_Capability__featureSetCombinations__Format : T_Format UE_MRDC_Capability__featureSetCombinations__Type UE_MRDC_Capability__featureSetCombinations__cond := seq_of_format FeatureSetCombination__Format 1 maxFeatureSetCombinations UE_MRDC_Capability__featureSetCombinations__helper1 UE_MRDC_Capability__featureSetCombinations__helper2.

Opaque UE_MRDC_Capability__featureSetCombinations__cond UE_MRDC_Capability__featureSetCombinations__Format.


Definition UE_MRDC_Capability__Format_Type := Eval cbn in seq_format_prod UE_MRDC_Capability__list.
Definition UE_MRDC_Capability__Format_list : UE_MRDC_Capability__Format_Type :=
  (MeasAndMobParametersMRDC__Format, (Phy_ParametersMRDC__Format, (RF_ParametersMRDC__Format, (GeneralParametersMRDC_XDD_Diff__Format, (UE_MRDC_CapabilityAddXDD_Mode__Format, (UE_MRDC_CapabilityAddXDD_Mode__Format, (UE_MRDC_CapabilityAddFRX_Mode__Format, (UE_MRDC_CapabilityAddFRX_Mode__Format, (UE_MRDC_Capability__featureSetCombinations__Format, (PDCP_ParametersMRDC__Format, (octet_string_nc__Format, (UE_MRDC_Capability_v1560__Format, unit_format)))))))))))).
Definition UE_MRDC_Capability__list__Format := (*Eval compute in *) seq_format UE_MRDC_Capability__list UE_MRDC_Capability__Format_list.
Definition UE_MRDC_Capability__F1 z :=
  (UE_MRDC_Capability__measAndMobParametersMRDC z, (UE_MRDC_Capability__phy_ParametersMRDC_v1530 z, (UE_MRDC_Capability__rf_ParametersMRDC z, (UE_MRDC_Capability__generalParametersMRDC z, (UE_MRDC_Capability__fdd_Add_UE_MRDC_Capabilities z, (UE_MRDC_Capability__tdd_Add_UE_MRDC_Capabilities z, (UE_MRDC_Capability__fr1_Add_UE_MRDC_Capabilities z, (UE_MRDC_Capability__fr2_Add_UE_MRDC_Capabilities z, (UE_MRDC_Capability__featureSetCombinations z, (UE_MRDC_Capability__pdcp_ParametersMRDC_v1530 z, (UE_MRDC_Capability__lateNonCriticalExtension z, (UE_MRDC_Capability__nonCriticalExtension z, tt)))))))))))).
Definition UE_MRDC_Capability__F2 (y : seq_type UE_MRDC_Capability__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, _))))))))))))=>
    make__UE_MRDC_Capability__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  end.
Lemma UE_MRDC_Capability__F1F2_cond (z : UE_MRDC_Capability__Type)
  : UE_MRDC_Capability__cond z ->
  (seq_cond UE_MRDC_Capability__list (UE_MRDC_Capability__F1 z)).
intro H. unfold UE_MRDC_Capability__cond in H. simpl. auto. Qed.
Lemma UE_MRDC_Capability__F1F2_cond2 (z : UE_MRDC_Capability__Type)
 : UE_MRDC_Capability__F2 (UE_MRDC_Capability__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_MRDC_Capability__F2F1_cond (y : seq_type UE_MRDC_Capability__list)
  : seq_cond UE_MRDC_Capability__list y ->
 (UE_MRDC_Capability__cond (UE_MRDC_Capability__F2 y)) /\  UE_MRDC_Capability__F1 (UE_MRDC_Capability__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_MRDC_Capability__cond. simpl in *. auto.
 - simpl. unfold UE_MRDC_Capability__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_MRDC_Capability__Format : T_Format UE_MRDC_Capability__Type UE_MRDC_Capability__cond :=
        proj2_format  UE_MRDC_Capability__cond UE_MRDC_Capability__list__Format
    UE_MRDC_Capability__F1 UE_MRDC_Capability__F2 UE_MRDC_Capability__F1F2_cond  UE_MRDC_Capability__F1F2_cond2 UE_MRDC_Capability__F2F1_cond.
Opaque UE_MRDC_Capability__cond UE_MRDC_Capability__Format.

