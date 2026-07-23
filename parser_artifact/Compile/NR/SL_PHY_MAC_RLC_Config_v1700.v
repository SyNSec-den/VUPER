Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SL_DRX_Config_r17.

Opaque SL_DRX_Config_r17__cond SL_DRX_Config_r17__Format.

Require Import NR.SL_RLC_ChannelID_r17.

Opaque SL_RLC_ChannelID_r17__cond SL_RLC_ChannelID_r17__Format.

Definition SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__Type := list SL_RLC_ChannelID_r17__Type.

Lemma SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__helper1 : (0 <= 1 <= maxSL_LCID_r16)%Z. unfold maxSL_LCID_r16.
 lia. Qed.
Lemma SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxSL_LCID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSL_LCID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__cond (z : SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxSL_LCID_r16)%Z /\ (list_and SL_RLC_ChannelID_r17__cond z) .

Require Import NR.SL_RLC_ChannelConfig_r17.

Opaque SL_RLC_ChannelConfig_r17__cond SL_RLC_ChannelConfig_r17__Format.

Definition SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__Type := list SL_RLC_ChannelConfig_r17__Type.

Lemma SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__helper1 : (0 <= 1 <= maxSL_LCID_r16)%Z. unfold maxSL_LCID_r16.
 lia. Qed.
Lemma SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxSL_LCID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSL_LCID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__cond (z : SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxSL_LCID_r16)%Z /\ (list_and SL_RLC_ChannelConfig_r17__cond z) .

Record SL_PHY_MAC_RLC_Config_v1700__Type : Set :=
  make__SL_PHY_MAC_RLC_Config_v1700__Type {
    SL_PHY_MAC_RLC_Config_v1700__sl_DRX_Config_r17 : option SL_DRX_Config_r17__Type ;
    SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17 : option SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__Type ;
    SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17 : option SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__Type ;
}.
Definition SL_PHY_MAC_RLC_Config_v1700__root_list : list seq_elem := (
 Opt SL_DRX_Config_r17__Type SL_DRX_Config_r17__cond ::
 Opt SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__Type SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__cond ::
 Opt SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__Type SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__cond ::
 nil).
Definition SL_PHY_MAC_RLC_Config_v1700__ext_list : list typ := (
  nil).
Definition SL_PHY_MAC_RLC_Config_v1700__cond (z : SL_PHY_MAC_RLC_Config_v1700__Type) := 
(  opt_cond SL_DRX_Config_r17__cond (SL_PHY_MAC_RLC_Config_v1700__sl_DRX_Config_r17 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__cond (SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17 z) /\
  opt_cond SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__cond (SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17 z) /\
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
Definition SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__Format : T_Format SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__Type SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__cond := seq_of_format SL_RLC_ChannelID_r17__Format 1 maxSL_LCID_r16 SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__helper1 SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__helper2.

Opaque SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__cond SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__Format.

Definition SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__Format : T_Format SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__Type SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__cond := seq_of_format SL_RLC_ChannelConfig_r17__Format 1 maxSL_LCID_r16 SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__helper1 SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__helper2.

Opaque SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__cond SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__Format.


Definition SL_PHY_MAC_RLC_Config_v1700__root_Format_Type := Eval cbn in seq_format_prod SL_PHY_MAC_RLC_Config_v1700__root_list.
Definition SL_PHY_MAC_RLC_Config_v1700__root_Format_list : SL_PHY_MAC_RLC_Config_v1700__root_Format_Type :=
  (SL_DRX_Config_r17__Format, (SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17__Format, (SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17__Format, unit_format))).

Definition SL_PHY_MAC_RLC_Config_v1700__ext_Format_Type := Eval cbn in get_formats SL_PHY_MAC_RLC_Config_v1700__ext_list.
Definition SL_PHY_MAC_RLC_Config_v1700__ext_Format_list : SL_PHY_MAC_RLC_Config_v1700__ext_Format_Type :=
  unit__Format.

Definition SL_PHY_MAC_RLC_Config_v1700__list_type : Set := (seq_type SL_PHY_MAC_RLC_Config_v1700__root_list) * (seq_ext_type SL_PHY_MAC_RLC_Config_v1700__ext_list).
Definition SL_PHY_MAC_RLC_Config_v1700__list_cond (z : SL_PHY_MAC_RLC_Config_v1700__list_type) : Prop :=
        (seq_cond SL_PHY_MAC_RLC_Config_v1700__root_list (fst z)) /\ (seq_ext_cond SL_PHY_MAC_RLC_Config_v1700__ext_list (snd z)).
Definition SL_PHY_MAC_RLC_Config_v1700__list_format : T_Format SL_PHY_MAC_RLC_Config_v1700__list_type SL_PHY_MAC_RLC_Config_v1700__list_cond :=
 (* Eval compute in *) seq_ext_format SL_PHY_MAC_RLC_Config_v1700__root_list SL_PHY_MAC_RLC_Config_v1700__root_Format_list SL_PHY_MAC_RLC_Config_v1700__ext_list SL_PHY_MAC_RLC_Config_v1700__ext_Format_list.

Opaque SL_PHY_MAC_RLC_Config_v1700__list_format.
Definition SL_PHY_MAC_RLC_Config_v1700__F1 (z : SL_PHY_MAC_RLC_Config_v1700__Type) : SL_PHY_MAC_RLC_Config_v1700__list_type :=
  (((SL_PHY_MAC_RLC_Config_v1700__sl_DRX_Config_r17 z, (SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToReleaseList_r17 z, (SL_PHY_MAC_RLC_Config_v1700__sl_RLC_ChannelToAddModList_r17 z, tt)))), (
tt)).
Definition SL_PHY_MAC_RLC_Config_v1700__F2 (y : SL_PHY_MAC_RLC_Config_v1700__list_type) : SL_PHY_MAC_RLC_Config_v1700__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__SL_PHY_MAC_RLC_Config_v1700__Type j0 j1 j2
  end.
Definition SL_PHY_MAC_RLC_Config_v1700__helper1 : (forall a : SL_PHY_MAC_RLC_Config_v1700__Type, SL_PHY_MAC_RLC_Config_v1700__cond a -> SL_PHY_MAC_RLC_Config_v1700__list_cond (SL_PHY_MAC_RLC_Config_v1700__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_PHY_MAC_RLC_Config_v1700__helper2 : (forall a : SL_PHY_MAC_RLC_Config_v1700__Type, SL_PHY_MAC_RLC_Config_v1700__F2 (SL_PHY_MAC_RLC_Config_v1700__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_PHY_MAC_RLC_Config_v1700__helper3 : (forall b : SL_PHY_MAC_RLC_Config_v1700__list_type, SL_PHY_MAC_RLC_Config_v1700__list_cond b -> SL_PHY_MAC_RLC_Config_v1700__cond (SL_PHY_MAC_RLC_Config_v1700__F2 b) /\ SL_PHY_MAC_RLC_Config_v1700__F1 (SL_PHY_MAC_RLC_Config_v1700__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_PHY_MAC_RLC_Config_v1700__cond, SL_PHY_MAC_RLC_Config_v1700__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_PHY_MAC_RLC_Config_v1700__Format : T_Format SL_PHY_MAC_RLC_Config_v1700__Type SL_PHY_MAC_RLC_Config_v1700__cond :=
 proj2_format SL_PHY_MAC_RLC_Config_v1700__cond SL_PHY_MAC_RLC_Config_v1700__list_format  SL_PHY_MAC_RLC_Config_v1700__F1 SL_PHY_MAC_RLC_Config_v1700__F2 SL_PHY_MAC_RLC_Config_v1700__helper1 SL_PHY_MAC_RLC_Config_v1700__helper2 SL_PHY_MAC_RLC_Config_v1700__helper3.

Opaque SL_PHY_MAC_RLC_Config_v1700__cond SL_PHY_MAC_RLC_Config_v1700__Format.

