Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CG_SDT_ConfigLCH_Restriction_r17.

Opaque CG_SDT_ConfigLCH_Restriction_r17__cond CG_SDT_ConfigLCH_Restriction_r17__Format.

Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__Type := list CG_SDT_ConfigLCH_Restriction_r17__Type.

Lemma SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__helper1 : (0 <= 1 <= maxLC_ID)%Z. unfold maxLC_ID.
 lia. Qed.
Lemma SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxLC_ID - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxLC_ID - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__cond (z : SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxLC_ID)%Z /\ (list_and CG_SDT_ConfigLCH_Restriction_r17__cond z) .

Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__Type := list LogicalChannelIdentity__Type.

Lemma SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__helper1 : (0 <= 1 <= maxLC_ID)%Z. unfold maxLC_ID.
 lia. Qed.
Lemma SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxLC_ID - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxLC_ID - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__cond (z : SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxLC_ID)%Z /\ (list_and LogicalChannelIdentity__cond z) .

Require Import NR.SetupRelease.
Require Import NR.BWP_UplinkDedicatedSDT_r17.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__Type := SetupRelease__Type BWP_UplinkDedicatedSDT_r17__Type.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__cond := SetupRelease__cond _ BWP_UplinkDedicatedSDT_r17__cond.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__Format : T_Format SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__cond := SetupRelease__Format _ _ BWP_UplinkDedicatedSDT_r17__Format.
Opaque SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.BWP_UplinkDedicatedSDT_r17.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__Type := SetupRelease__Type BWP_UplinkDedicatedSDT_r17__Type.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__cond := SetupRelease__cond _ BWP_UplinkDedicatedSDT_r17__cond.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__Format : T_Format SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__cond := SetupRelease__Format _ _ BWP_UplinkDedicatedSDT_r17__Format.
Opaque SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__Format.

Require Import NR.BWP_DownlinkDedicatedSDT_r17.

Opaque BWP_DownlinkDedicatedSDT_r17__cond BWP_DownlinkDedicatedSDT_r17__Format.

Require Import NR.TimeAlignmentTimer.

Opaque TimeAlignmentTimer__cond TimeAlignmentTimer__Format.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.SetupRelease.
Require Import NR.CG_SDT_TA_ValidationConfig_r17.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__Type := SetupRelease__Type CG_SDT_TA_ValidationConfig_r17__Type.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__cond := SetupRelease__cond _ CG_SDT_TA_ValidationConfig_r17__cond.
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__Format : T_Format SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__cond := SetupRelease__Format _ _ CG_SDT_TA_ValidationConfig_r17__Format.
Opaque SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Record SDT_MAC_PHY_CG_Config_r17__Type : Set :=
  make__SDT_MAC_PHY_CG_Config_r17__Type {
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17 : option SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__Type ;
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17 : option SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__Type ;
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17 : option SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__Type ;
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17 : option SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__Type ;
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_DL_r17 : option BWP_DownlinkDedicatedSDT_r17__Type ;
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_TimeAlignmentTimer_r17 : option TimeAlignmentTimer__Type ;
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_RSRP_ThresholdSSB_r17 : option RSRP_Range__Type ;
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17 : option SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__Type ;
    SDT_MAC_PHY_CG_Config_r17__cg_SDT_CS_RNTI_r17 : option RNTI_Value__Type ;
}.
Definition SDT_MAC_PHY_CG_Config_r17__root_list : list seq_elem := (
 Opt SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__cond ::
 Opt SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__cond ::
 Opt SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__cond ::
 Opt SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__cond ::
 Opt BWP_DownlinkDedicatedSDT_r17__Type BWP_DownlinkDedicatedSDT_r17__cond ::
 Opt TimeAlignmentTimer__Type TimeAlignmentTimer__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__cond ::
 Opt RNTI_Value__Type RNTI_Value__cond ::
 nil).
Definition SDT_MAC_PHY_CG_Config_r17__ext_list : list typ := (
  nil).
Definition SDT_MAC_PHY_CG_Config_r17__cond (z : SDT_MAC_PHY_CG_Config_r17__Type) := 
(  opt_cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17 z) /\
  opt_cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17 z) /\
  opt_cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17 z) /\
  opt_cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17 z) /\
  opt_cond BWP_DownlinkDedicatedSDT_r17__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_DL_r17 z) /\
  opt_cond TimeAlignmentTimer__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_TimeAlignmentTimer_r17 z) /\
  opt_cond RSRP_Range__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_RSRP_ThresholdSSB_r17 z) /\
  opt_cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17 z) /\
  opt_cond RNTI_Value__cond (SDT_MAC_PHY_CG_Config_r17__cg_SDT_CS_RNTI_r17 z) /\
  True) /\ 
(  True).


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
Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__Format : T_Format SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__cond := seq_of_format CG_SDT_ConfigLCH_Restriction_r17__Format 1 maxLC_ID SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__helper1 SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__helper2.

Opaque SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__Format.

Definition SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__Format : T_Format SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__Type SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__cond := seq_of_format LogicalChannelIdentity__Format 1 maxLC_ID SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__helper1 SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__helper2.

Opaque SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__Format.

Opaque SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__Format.

Opaque SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__Format.

Opaque SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__cond SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__Format.


Definition SDT_MAC_PHY_CG_Config_r17__root_Format_Type := Eval cbn in seq_format_prod SDT_MAC_PHY_CG_Config_r17__root_list.
Definition SDT_MAC_PHY_CG_Config_r17__root_Format_list : SDT_MAC_PHY_CG_Config_r17__root_Format_Type :=
  (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17__Format, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17__Format, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17__Format, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17__Format, (BWP_DownlinkDedicatedSDT_r17__Format, (TimeAlignmentTimer__Format, (RSRP_Range__Format, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17__Format, (RNTI_Value__Format, unit_format))))))))).

Definition SDT_MAC_PHY_CG_Config_r17__ext_Format_Type := Eval cbn in get_formats SDT_MAC_PHY_CG_Config_r17__ext_list.
Definition SDT_MAC_PHY_CG_Config_r17__ext_Format_list : SDT_MAC_PHY_CG_Config_r17__ext_Format_Type :=
  unit__Format.

Definition SDT_MAC_PHY_CG_Config_r17__list_type : Set := (seq_type SDT_MAC_PHY_CG_Config_r17__root_list) * (seq_ext_type SDT_MAC_PHY_CG_Config_r17__ext_list).
Definition SDT_MAC_PHY_CG_Config_r17__list_cond (z : SDT_MAC_PHY_CG_Config_r17__list_type) : Prop :=
        (seq_cond SDT_MAC_PHY_CG_Config_r17__root_list (fst z)) /\ (seq_ext_cond SDT_MAC_PHY_CG_Config_r17__ext_list (snd z)).
Definition SDT_MAC_PHY_CG_Config_r17__list_format : T_Format SDT_MAC_PHY_CG_Config_r17__list_type SDT_MAC_PHY_CG_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SDT_MAC_PHY_CG_Config_r17__root_list SDT_MAC_PHY_CG_Config_r17__root_Format_list SDT_MAC_PHY_CG_Config_r17__ext_list SDT_MAC_PHY_CG_Config_r17__ext_Format_list.

Opaque SDT_MAC_PHY_CG_Config_r17__list_format.
Definition SDT_MAC_PHY_CG_Config_r17__F1 (z : SDT_MAC_PHY_CG_Config_r17__Type) : SDT_MAC_PHY_CG_Config_r17__list_type :=
  (((SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToAddModList_r17 z, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigLCH_RestrictionToReleaseList_r17 z, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_NUL_r17 z, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_SUL_r17 z, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_ConfigInitialBWP_DL_r17 z, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_TimeAlignmentTimer_r17 z, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_RSRP_ThresholdSSB_r17 z, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_TA_ValidationConfig_r17 z, (SDT_MAC_PHY_CG_Config_r17__cg_SDT_CS_RNTI_r17 z, tt)))))))))), (
tt)).
Definition SDT_MAC_PHY_CG_Config_r17__F2 (y : SDT_MAC_PHY_CG_Config_r17__list_type) : SDT_MAC_PHY_CG_Config_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), _)=>
    make__SDT_MAC_PHY_CG_Config_r17__Type j0 j1 j2 j3 j4 j5 j6 j7 j8
  end.
Definition SDT_MAC_PHY_CG_Config_r17__helper1 : (forall a : SDT_MAC_PHY_CG_Config_r17__Type, SDT_MAC_PHY_CG_Config_r17__cond a -> SDT_MAC_PHY_CG_Config_r17__list_cond (SDT_MAC_PHY_CG_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SDT_MAC_PHY_CG_Config_r17__helper2 : (forall a : SDT_MAC_PHY_CG_Config_r17__Type, SDT_MAC_PHY_CG_Config_r17__F2 (SDT_MAC_PHY_CG_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SDT_MAC_PHY_CG_Config_r17__helper3 : (forall b : SDT_MAC_PHY_CG_Config_r17__list_type, SDT_MAC_PHY_CG_Config_r17__list_cond b -> SDT_MAC_PHY_CG_Config_r17__cond (SDT_MAC_PHY_CG_Config_r17__F2 b) /\ SDT_MAC_PHY_CG_Config_r17__F1 (SDT_MAC_PHY_CG_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SDT_MAC_PHY_CG_Config_r17__cond, SDT_MAC_PHY_CG_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SDT_MAC_PHY_CG_Config_r17__Format : T_Format SDT_MAC_PHY_CG_Config_r17__Type SDT_MAC_PHY_CG_Config_r17__cond :=
 proj2_format SDT_MAC_PHY_CG_Config_r17__cond SDT_MAC_PHY_CG_Config_r17__list_format  SDT_MAC_PHY_CG_Config_r17__F1 SDT_MAC_PHY_CG_Config_r17__F2 SDT_MAC_PHY_CG_Config_r17__helper1 SDT_MAC_PHY_CG_Config_r17__helper2 SDT_MAC_PHY_CG_Config_r17__helper3.

Opaque SDT_MAC_PHY_CG_Config_r17__cond SDT_MAC_PHY_CG_Config_r17__Format.

