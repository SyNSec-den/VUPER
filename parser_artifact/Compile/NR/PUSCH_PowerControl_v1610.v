Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUSCH_PathlossReferenceRS_r16.

Opaque PUSCH_PathlossReferenceRS_r16__cond PUSCH_PathlossReferenceRS_r16__Format.

Definition PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__Type := list PUSCH_PathlossReferenceRS_r16__Type.

Lemma PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__helper1 : (0 <= 1 <= maxNrofPUSCH_PathlossReferenceRSsDiff_r16)%Z. unfold maxNrofPUSCH_PathlossReferenceRSsDiff_r16.
 lia. Qed.
Lemma PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__helper2 : to_bit_sz (Z.to_nat (maxNrofPUSCH_PathlossReferenceRSsDiff_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUSCH_PathlossReferenceRSsDiff_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__cond (z : PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUSCH_PathlossReferenceRSsDiff_r16)%Z /\ (list_and PUSCH_PathlossReferenceRS_r16__cond z) .

Require Import NR.PUSCH_PathlossReferenceRS_Id_v1610.

Opaque PUSCH_PathlossReferenceRS_Id_v1610__cond PUSCH_PathlossReferenceRS_Id_v1610__Format.

Definition PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__Type := list PUSCH_PathlossReferenceRS_Id_v1610__Type.

Lemma PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__helper1 : (0 <= 1 <= maxNrofPUSCH_PathlossReferenceRSsDiff_r16)%Z. unfold maxNrofPUSCH_PathlossReferenceRSsDiff_r16.
 lia. Qed.
Lemma PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__helper2 : to_bit_sz (Z.to_nat (maxNrofPUSCH_PathlossReferenceRSsDiff_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUSCH_PathlossReferenceRSsDiff_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__cond (z : PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUSCH_PathlossReferenceRSsDiff_r16)%Z /\ (list_and PUSCH_PathlossReferenceRS_Id_v1610__cond z) .

Require Import NR.P0_PUSCH_Set_r16.

Opaque P0_PUSCH_Set_r16__cond P0_PUSCH_Set_r16__Format.

Definition PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__Type := list P0_PUSCH_Set_r16__Type.

Lemma PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__helper1 : (0 <= 1 <= maxNrofSRI_PUSCH_Mappings)%Z. unfold maxNrofSRI_PUSCH_Mappings.
 lia. Qed.
Lemma PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofSRI_PUSCH_Mappings - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRI_PUSCH_Mappings - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__cond (z : PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRI_PUSCH_Mappings)%Z /\ (list_and P0_PUSCH_Set_r16__cond z) .

Lemma PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__Type := Z.
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__cond := (fun z => (1 <= z <= 2)%Z).
Lemma PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__Type := Z.
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__cond := (fun z => (1 <= z <= 2)%Z).
Record PUSCH_PowerControl_v1610__olpc_ParameterSet__Type : Set :=
  make__PUSCH_PowerControl_v1610__olpc_ParameterSet__Type {
    PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16 : option Z ;
    PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16 : option Z ;
}.
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__list := (
 Opt Z PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__cond ::
 Opt Z PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__cond ::
 nil).
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__cond z := 
  opt_cond PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__cond (PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16 z) /\
  opt_cond PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__cond (PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16 z) /\
  True.

Require Import NR.SRI_PUSCH_PowerControl.

Opaque SRI_PUSCH_PowerControl__cond SRI_PUSCH_PowerControl__Format.

Definition PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__Type := list SRI_PUSCH_PowerControl__Type.

Lemma PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__helper1 : (0 <= 1 <= maxNrofSRI_PUSCH_Mappings)%Z. unfold maxNrofSRI_PUSCH_Mappings.
 lia. Qed.
Lemma PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSRI_PUSCH_Mappings - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRI_PUSCH_Mappings - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__cond (z : PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRI_PUSCH_Mappings)%Z /\ (list_and SRI_PUSCH_PowerControl__cond z) .

Require Import NR.SRI_PUSCH_PowerControlId.

Opaque SRI_PUSCH_PowerControlId__cond SRI_PUSCH_PowerControlId__Format.

Definition PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__Type := list SRI_PUSCH_PowerControlId__Type.

Lemma PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__helper1 : (0 <= 1 <= maxNrofSRI_PUSCH_Mappings)%Z. unfold maxNrofSRI_PUSCH_Mappings.
 lia. Qed.
Lemma PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSRI_PUSCH_Mappings - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRI_PUSCH_Mappings - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__cond (z : PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRI_PUSCH_Mappings)%Z /\ (list_and SRI_PUSCH_PowerControlId__cond z) .

Require Import NR.P0_PUSCH_Set_r16.

Opaque P0_PUSCH_Set_r16__cond P0_PUSCH_Set_r16__Format.

Definition PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__Type := list P0_PUSCH_Set_r16__Type.

Lemma PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__helper1 : (0 <= 1 <= maxNrofSRI_PUSCH_Mappings)%Z. unfold maxNrofSRI_PUSCH_Mappings.
 lia. Qed.
Lemma PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSRI_PUSCH_Mappings - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRI_PUSCH_Mappings - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__cond (z : PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRI_PUSCH_Mappings)%Z /\ (list_and P0_PUSCH_Set_r16__cond z) .

Require Import NR.DummyPathlossReferenceRS_v1710.

Opaque DummyPathlossReferenceRS_v1710__cond DummyPathlossReferenceRS_v1710__Format.

Definition PUSCH_PowerControl_v1610__ext0O__dummy__Type := list DummyPathlossReferenceRS_v1710__Type.

Lemma PUSCH_PowerControl_v1610__ext0O__dummy__helper1 : (0 <= 1 <= maxNrofPUSCH_PathlossReferenceRSs_r16)%Z. unfold maxNrofPUSCH_PathlossReferenceRSs_r16.
 lia. Qed.
Lemma PUSCH_PowerControl_v1610__ext0O__dummy__helper2 : to_bit_sz (Z.to_nat (maxNrofPUSCH_PathlossReferenceRSs_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPUSCH_PathlossReferenceRSs_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PUSCH_PowerControl_v1610__ext0O__dummy__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PUSCH_PowerControl_v1610__ext0O__dummy__cond (z : PUSCH_PowerControl_v1610__ext0O__dummy__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofPUSCH_PathlossReferenceRSs_r16)%Z /\ (list_and DummyPathlossReferenceRS_v1710__cond z) .

Record PUSCH_PowerControl_v1610__ext0O__Type : Set :=
  make__PUSCH_PowerControl_v1610__ext0O__Type {
    PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17 : option PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__Type ;
    PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17 : option PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__Type ;
    PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17 : option PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__Type ;
    PUSCH_PowerControl_v1610__ext0O__dummy : option PUSCH_PowerControl_v1610__ext0O__dummy__Type ;
}.
Definition PUSCH_PowerControl_v1610__ext0O__list := (
 Opt PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__Type PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__cond ::
 Opt PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__Type PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__cond ::
 Opt PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__Type PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__cond ::
 Opt PUSCH_PowerControl_v1610__ext0O__dummy__Type PUSCH_PowerControl_v1610__ext0O__dummy__cond ::
 nil).
Definition PUSCH_PowerControl_v1610__ext0O__cond z := 
  opt_cond PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__cond (PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17 z) /\
  opt_cond PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__cond (PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17 z) /\
  opt_cond PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__cond (PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17 z) /\
  opt_cond PUSCH_PowerControl_v1610__ext0O__dummy__cond (PUSCH_PowerControl_v1610__ext0O__dummy z) /\
  True.

Definition PUSCH_PowerControl_v1610__ext0__Type := PUSCH_PowerControl_v1610__ext0O__Type.
Definition PUSCH_PowerControl_v1610__ext0__cond := PUSCH_PowerControl_v1610__ext0O__cond.

Record PUSCH_PowerControl_v1610__Type : Set :=
  make__PUSCH_PowerControl_v1610__Type {
    PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610 : option PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__Type ;
    PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610 : option PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__Type ;
    PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16 : option PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__Type ;
    PUSCH_PowerControl_v1610__olpc_ParameterSet : option PUSCH_PowerControl_v1610__olpc_ParameterSet__Type ;
    PUSCH_PowerControl_v1610__ext0 : option PUSCH_PowerControl_v1610__ext0__Type ;
}.
Definition PUSCH_PowerControl_v1610__root_list : list seq_elem := (
 Opt PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__Type PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__cond ::
 Opt PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__Type PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__cond ::
 Opt PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__Type PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__cond ::
 Opt PUSCH_PowerControl_v1610__olpc_ParameterSet__Type PUSCH_PowerControl_v1610__olpc_ParameterSet__cond ::
 nil).
Definition PUSCH_PowerControl_v1610__ext_list : list typ := (
  typ_cons PUSCH_PowerControl_v1610__ext0__Type PUSCH_PowerControl_v1610__ext0__cond ::
  nil).
Definition PUSCH_PowerControl_v1610__cond (z : PUSCH_PowerControl_v1610__Type) := 
(  opt_cond PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__cond (PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610 z) /\
  opt_cond PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__cond (PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610 z) /\
  opt_cond PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__cond (PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16 z) /\
  opt_cond PUSCH_PowerControl_v1610__olpc_ParameterSet__cond (PUSCH_PowerControl_v1610__olpc_ParameterSet z) /\
  True) /\ 
(  opt_cond PUSCH_PowerControl_v1610__ext0__cond (PUSCH_PowerControl_v1610__ext0 z) /\
  True).


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
Definition PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__Format : T_Format PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__Type PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__cond := seq_of_format PUSCH_PathlossReferenceRS_r16__Format 1 maxNrofPUSCH_PathlossReferenceRSsDiff_r16 PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__helper1 PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__helper2.

Opaque PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__cond PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__Format.

Definition PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__Format : T_Format PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__Type PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__cond := seq_of_format PUSCH_PathlossReferenceRS_Id_v1610__Format 1 maxNrofPUSCH_PathlossReferenceRSsDiff_r16 PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__helper1 PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__helper2.

Opaque PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__cond PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__Format.

Definition PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__Format : T_Format PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__Type PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__cond := seq_of_format P0_PUSCH_Set_r16__Format 1 maxNrofSRI_PUSCH_Mappings PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__helper1 PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__helper2.

Opaque PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__cond PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__Format.

Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__Format : T_Format Z PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__cond :=
 ranged_int_format (1) (2) PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__helper1 PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__helper2.

Opaque PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__cond PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__Format.

Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__Format : T_Format Z PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__cond :=
 ranged_int_format (1) (2) PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__helper1 PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__helper2.

Opaque PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__cond PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__Format.


Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__Format_Type := Eval cbn in seq_format_prod PUSCH_PowerControl_v1610__olpc_ParameterSet__list.
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__Format_list : PUSCH_PowerControl_v1610__olpc_ParameterSet__Format_Type :=
  (PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16__Format, (PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16__Format, unit_format)).
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__list__Format := (*Eval compute in *) seq_format PUSCH_PowerControl_v1610__olpc_ParameterSet__list PUSCH_PowerControl_v1610__olpc_ParameterSet__Format_list.
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__F1 z :=
  (PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_1_r16 z, (PUSCH_PowerControl_v1610__olpc_ParameterSet__olpc_ParameterSetDCI_0_2_r16 z, tt)).
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__F2 (y : seq_type PUSCH_PowerControl_v1610__olpc_ParameterSet__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PUSCH_PowerControl_v1610__olpc_ParameterSet__Type i0 i1
  end.
Lemma PUSCH_PowerControl_v1610__olpc_ParameterSet__F1F2_cond (z : PUSCH_PowerControl_v1610__olpc_ParameterSet__Type)
  : PUSCH_PowerControl_v1610__olpc_ParameterSet__cond z ->
  (seq_cond PUSCH_PowerControl_v1610__olpc_ParameterSet__list (PUSCH_PowerControl_v1610__olpc_ParameterSet__F1 z)).
intro H. unfold PUSCH_PowerControl_v1610__olpc_ParameterSet__cond in H. simpl. auto. Qed.
Lemma PUSCH_PowerControl_v1610__olpc_ParameterSet__F1F2_cond2 (z : PUSCH_PowerControl_v1610__olpc_ParameterSet__Type)
 : PUSCH_PowerControl_v1610__olpc_ParameterSet__F2 (PUSCH_PowerControl_v1610__olpc_ParameterSet__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_PowerControl_v1610__olpc_ParameterSet__F2F1_cond (y : seq_type PUSCH_PowerControl_v1610__olpc_ParameterSet__list)
  : seq_cond PUSCH_PowerControl_v1610__olpc_ParameterSet__list y ->
 (PUSCH_PowerControl_v1610__olpc_ParameterSet__cond (PUSCH_PowerControl_v1610__olpc_ParameterSet__F2 y)) /\  PUSCH_PowerControl_v1610__olpc_ParameterSet__F1 (PUSCH_PowerControl_v1610__olpc_ParameterSet__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_PowerControl_v1610__olpc_ParameterSet__cond. simpl in *. auto.
 - simpl. unfold PUSCH_PowerControl_v1610__olpc_ParameterSet__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_PowerControl_v1610__olpc_ParameterSet__Format : T_Format PUSCH_PowerControl_v1610__olpc_ParameterSet__Type PUSCH_PowerControl_v1610__olpc_ParameterSet__cond :=
        proj2_format  PUSCH_PowerControl_v1610__olpc_ParameterSet__cond PUSCH_PowerControl_v1610__olpc_ParameterSet__list__Format
    PUSCH_PowerControl_v1610__olpc_ParameterSet__F1 PUSCH_PowerControl_v1610__olpc_ParameterSet__F2 PUSCH_PowerControl_v1610__olpc_ParameterSet__F1F2_cond  PUSCH_PowerControl_v1610__olpc_ParameterSet__F1F2_cond2 PUSCH_PowerControl_v1610__olpc_ParameterSet__F2F1_cond.
Opaque PUSCH_PowerControl_v1610__olpc_ParameterSet__cond PUSCH_PowerControl_v1610__olpc_ParameterSet__Format.

Definition PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__Format : T_Format PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__Type PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__cond := seq_of_format SRI_PUSCH_PowerControl__Format 1 maxNrofSRI_PUSCH_Mappings PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__helper1 PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__helper2.

Opaque PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__cond PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__Format.

Definition PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__Format : T_Format PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__Type PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__cond := seq_of_format SRI_PUSCH_PowerControlId__Format 1 maxNrofSRI_PUSCH_Mappings PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__helper1 PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__helper2.

Opaque PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__cond PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__Format.

Definition PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__Format : T_Format PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__Type PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__cond := seq_of_format P0_PUSCH_Set_r16__Format 1 maxNrofSRI_PUSCH_Mappings PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__helper1 PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__helper2.

Opaque PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__cond PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__Format.

Definition PUSCH_PowerControl_v1610__ext0O__dummy__Format : T_Format PUSCH_PowerControl_v1610__ext0O__dummy__Type PUSCH_PowerControl_v1610__ext0O__dummy__cond := seq_of_format DummyPathlossReferenceRS_v1710__Format 1 maxNrofPUSCH_PathlossReferenceRSs_r16 PUSCH_PowerControl_v1610__ext0O__dummy__helper1 PUSCH_PowerControl_v1610__ext0O__dummy__helper2.

Opaque PUSCH_PowerControl_v1610__ext0O__dummy__cond PUSCH_PowerControl_v1610__ext0O__dummy__Format.


Definition PUSCH_PowerControl_v1610__ext0O__Format_Type := Eval cbn in seq_format_prod PUSCH_PowerControl_v1610__ext0O__list.
Definition PUSCH_PowerControl_v1610__ext0O__Format_list : PUSCH_PowerControl_v1610__ext0O__Format_Type :=
  (PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17__Format, (PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17__Format, (PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17__Format, (PUSCH_PowerControl_v1610__ext0O__dummy__Format, unit_format)))).
Definition PUSCH_PowerControl_v1610__ext0O__list__Format := (*Eval compute in *) seq_format PUSCH_PowerControl_v1610__ext0O__list PUSCH_PowerControl_v1610__ext0O__Format_list.
Definition PUSCH_PowerControl_v1610__ext0O__F1 z :=
  (PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToAddModList2_r17 z, (PUSCH_PowerControl_v1610__ext0O__sri_PUSCH_MappingToReleaseList2_r17 z, (PUSCH_PowerControl_v1610__ext0O__p0_PUSCH_SetList2_r17 z, (PUSCH_PowerControl_v1610__ext0O__dummy z, tt)))).
Definition PUSCH_PowerControl_v1610__ext0O__F2 (y : seq_type PUSCH_PowerControl_v1610__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PUSCH_PowerControl_v1610__ext0O__Type i0 i1 i2 i3
  end.
Lemma PUSCH_PowerControl_v1610__ext0O__F1F2_cond (z : PUSCH_PowerControl_v1610__ext0O__Type)
  : PUSCH_PowerControl_v1610__ext0O__cond z ->
  (seq_cond PUSCH_PowerControl_v1610__ext0O__list (PUSCH_PowerControl_v1610__ext0O__F1 z)).
intro H. unfold PUSCH_PowerControl_v1610__ext0O__cond in H. simpl. auto. Qed.
Lemma PUSCH_PowerControl_v1610__ext0O__F1F2_cond2 (z : PUSCH_PowerControl_v1610__ext0O__Type)
 : PUSCH_PowerControl_v1610__ext0O__F2 (PUSCH_PowerControl_v1610__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUSCH_PowerControl_v1610__ext0O__F2F1_cond (y : seq_type PUSCH_PowerControl_v1610__ext0O__list)
  : seq_cond PUSCH_PowerControl_v1610__ext0O__list y ->
 (PUSCH_PowerControl_v1610__ext0O__cond (PUSCH_PowerControl_v1610__ext0O__F2 y)) /\  PUSCH_PowerControl_v1610__ext0O__F1 (PUSCH_PowerControl_v1610__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUSCH_PowerControl_v1610__ext0O__cond. simpl in *. auto.
 - simpl. unfold PUSCH_PowerControl_v1610__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUSCH_PowerControl_v1610__ext0O__Format : T_Format PUSCH_PowerControl_v1610__ext0O__Type PUSCH_PowerControl_v1610__ext0O__cond :=
        proj2_format  PUSCH_PowerControl_v1610__ext0O__cond PUSCH_PowerControl_v1610__ext0O__list__Format
    PUSCH_PowerControl_v1610__ext0O__F1 PUSCH_PowerControl_v1610__ext0O__F2 PUSCH_PowerControl_v1610__ext0O__F1F2_cond  PUSCH_PowerControl_v1610__ext0O__F1F2_cond2 PUSCH_PowerControl_v1610__ext0O__F2F1_cond.
Opaque PUSCH_PowerControl_v1610__ext0O__cond PUSCH_PowerControl_v1610__ext0O__Format.

Definition PUSCH_PowerControl_v1610__ext0__check_all_none (b : PUSCH_PowerControl_v1610__ext0O__Type) : bool :=
match b with 
  | make__PUSCH_PowerControl_v1610__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition PUSCH_PowerControl_v1610__ext0__Format : T_Format PUSCH_PowerControl_v1610__ext0__Type PUSCH_PowerControl_v1610__ext0__cond :=
  restrict_add_format PUSCH_PowerControl_v1610__ext0__check_all_none PUSCH_PowerControl_v1610__ext0O__Format.

Opaque PUSCH_PowerControl_v1610__ext0__cond PUSCH_PowerControl_v1610__ext0__Format.


Definition PUSCH_PowerControl_v1610__root_Format_Type := Eval cbn in seq_format_prod PUSCH_PowerControl_v1610__root_list.
Definition PUSCH_PowerControl_v1610__root_Format_list : PUSCH_PowerControl_v1610__root_Format_Type :=
  (PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610__Format, (PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610__Format, (PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16__Format, (PUSCH_PowerControl_v1610__olpc_ParameterSet__Format, unit_format)))).

Definition PUSCH_PowerControl_v1610__ext_Format_Type := Eval cbn in get_formats PUSCH_PowerControl_v1610__ext_list.
Definition PUSCH_PowerControl_v1610__ext_Format_list : PUSCH_PowerControl_v1610__ext_Format_Type :=
  (PUSCH_PowerControl_v1610__ext0__Format, unit__Format).

Definition PUSCH_PowerControl_v1610__list_type : Set := (seq_type PUSCH_PowerControl_v1610__root_list) * (seq_ext_type PUSCH_PowerControl_v1610__ext_list).
Definition PUSCH_PowerControl_v1610__list_cond (z : PUSCH_PowerControl_v1610__list_type) : Prop :=
        (seq_cond PUSCH_PowerControl_v1610__root_list (fst z)) /\ (seq_ext_cond PUSCH_PowerControl_v1610__ext_list (snd z)).
Definition PUSCH_PowerControl_v1610__list_format : T_Format PUSCH_PowerControl_v1610__list_type PUSCH_PowerControl_v1610__list_cond :=
 (* Eval compute in *) seq_ext_format PUSCH_PowerControl_v1610__root_list PUSCH_PowerControl_v1610__root_Format_list PUSCH_PowerControl_v1610__ext_list PUSCH_PowerControl_v1610__ext_Format_list.

Opaque PUSCH_PowerControl_v1610__list_format.
Definition PUSCH_PowerControl_v1610__F1 (z : PUSCH_PowerControl_v1610__Type) : PUSCH_PowerControl_v1610__list_type :=
  (((PUSCH_PowerControl_v1610__pathlossReferenceRSToAddModListSizeExt_v1610 z, (PUSCH_PowerControl_v1610__pathlossReferenceRSToReleaseListSizeExt_v1610 z, (PUSCH_PowerControl_v1610__p0_PUSCH_SetList_r16 z, (PUSCH_PowerControl_v1610__olpc_ParameterSet z, tt))))), (
(PUSCH_PowerControl_v1610__ext0 z, tt))).
Definition PUSCH_PowerControl_v1610__F2 (y : PUSCH_PowerControl_v1610__list_type) : PUSCH_PowerControl_v1610__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__PUSCH_PowerControl_v1610__Type j0 j1 j2 j3 i0
  end.
Definition PUSCH_PowerControl_v1610__helper1 : (forall a : PUSCH_PowerControl_v1610__Type, PUSCH_PowerControl_v1610__cond a -> PUSCH_PowerControl_v1610__list_cond (PUSCH_PowerControl_v1610__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PUSCH_PowerControl_v1610__helper2 : (forall a : PUSCH_PowerControl_v1610__Type, PUSCH_PowerControl_v1610__F2 (PUSCH_PowerControl_v1610__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PUSCH_PowerControl_v1610__helper3 : (forall b : PUSCH_PowerControl_v1610__list_type, PUSCH_PowerControl_v1610__list_cond b -> PUSCH_PowerControl_v1610__cond (PUSCH_PowerControl_v1610__F2 b) /\ PUSCH_PowerControl_v1610__F1 (PUSCH_PowerControl_v1610__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PUSCH_PowerControl_v1610__cond, PUSCH_PowerControl_v1610__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PUSCH_PowerControl_v1610__Format : T_Format PUSCH_PowerControl_v1610__Type PUSCH_PowerControl_v1610__cond :=
 proj2_format PUSCH_PowerControl_v1610__cond PUSCH_PowerControl_v1610__list_format  PUSCH_PowerControl_v1610__F1 PUSCH_PowerControl_v1610__F2 PUSCH_PowerControl_v1610__helper1 PUSCH_PowerControl_v1610__helper2 PUSCH_PowerControl_v1610__helper3.

Opaque PUSCH_PowerControl_v1610__cond PUSCH_PowerControl_v1610__Format.

