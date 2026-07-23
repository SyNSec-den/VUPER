Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SL_DRX_ConfigUC_r17.
Definition RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__Type := SetupRelease__Type SL_DRX_ConfigUC_r17__Type.
Definition RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__cond := SetupRelease__cond _ SL_DRX_ConfigUC_r17__cond.
Definition RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__Format : T_Format RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__Type RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__cond := SetupRelease__Format _ _ SL_DRX_ConfigUC_r17__Format.
Opaque RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__cond RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_LatencyBoundIUC_Report_r17.
Definition RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__Type := SetupRelease__Type SL_LatencyBoundIUC_Report_r17__Type.
Definition RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__cond := SetupRelease__cond _ SL_LatencyBoundIUC_Report_r17__cond.
Definition RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__Format : T_Format RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__Type RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__cond := SetupRelease__Format _ _ SL_LatencyBoundIUC_Report_r17__Format.
Opaque RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__cond RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__Format.

Require Import NR.SL_RLC_ChannelID_r17.

Opaque SL_RLC_ChannelID_r17__cond SL_RLC_ChannelID_r17__Format.

Definition RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__Type := list SL_RLC_ChannelID_r17__Type.

Lemma RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__helper1 : (0 <= 1 <= maxSL_LCID_r16)%Z. unfold maxSL_LCID_r16.
 lia. Qed.
Lemma RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__helper2 : to_bit_sz (Z.to_nat (maxSL_LCID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSL_LCID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__cond (z : RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxSL_LCID_r16)%Z /\ (list_and SL_RLC_ChannelID_r17__cond z) .

Require Import NR.SL_RLC_ChannelConfigPC5_r17.

Opaque SL_RLC_ChannelConfigPC5_r17__cond SL_RLC_ChannelConfigPC5_r17__Format.

Definition RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__Type := list SL_RLC_ChannelConfigPC5_r17__Type.

Lemma RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__helper1 : (0 <= 1 <= maxSL_LCID_r16)%Z. unfold maxSL_LCID_r16.
 lia. Qed.
Lemma RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__helper2 : to_bit_sz (Z.to_nat (maxSL_LCID_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSL_LCID_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__cond (z : RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxSL_LCID_r16)%Z /\ (list_and SL_RLC_ChannelConfigPC5_r17__cond z) .

Record RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type : Set := make__RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type {}.
Definition RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__cond (z : RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type) := True.
Record RRCReconfigurationSidelink_v1700_IEs__Type : Set :=
  make__RRCReconfigurationSidelink_v1700_IEs__Type {
    RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17 : option RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__Type ;
    RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17 : option RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__Type ;
    RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17 : option RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__Type ;
    RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17 : option RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__Type ;
    RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension : option RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition RRCReconfigurationSidelink_v1700_IEs__list := (
 Opt RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__Type RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__cond ::
 Opt RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__Type RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__cond ::
 Opt RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__Type RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__cond ::
 Opt RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__Type RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__cond ::
 Opt RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition RRCReconfigurationSidelink_v1700_IEs__cond z := 
  opt_cond RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__cond (RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17 z) /\
  opt_cond RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__cond (RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17 z) /\
  opt_cond RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__cond (RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17 z) /\
  opt_cond RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__cond (RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17 z) /\
  opt_cond RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__cond (RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension z) /\
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
Opaque RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__cond RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__Format.

Opaque RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__cond RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__Format.

Definition RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__Format : T_Format RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__Type RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__cond := seq_of_format SL_RLC_ChannelID_r17__Format 1 maxSL_LCID_r16 RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__helper1 RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__helper2.

Opaque RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__cond RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__Format.

Definition RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__Format : T_Format RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__Type RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__cond := seq_of_format SL_RLC_ChannelConfigPC5_r17__Format 1 maxSL_LCID_r16 RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__helper1 RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__helper2.

Opaque RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__cond RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__Format.

Definition RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__helper : forall a : RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Format : T_Format RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Type)
    RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__cond RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Format.


Definition RRCReconfigurationSidelink_v1700_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationSidelink_v1700_IEs__list.
Definition RRCReconfigurationSidelink_v1700_IEs__Format_list : RRCReconfigurationSidelink_v1700_IEs__Format_Type :=
  (RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17__Format, (RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17__Format, (RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17__Format, (RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17__Format, (RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension__Format, unit_format))))).
Definition RRCReconfigurationSidelink_v1700_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfigurationSidelink_v1700_IEs__list RRCReconfigurationSidelink_v1700_IEs__Format_list.
Definition RRCReconfigurationSidelink_v1700_IEs__F1 z :=
  (RRCReconfigurationSidelink_v1700_IEs__sl_DRX_ConfigUC_PC5_r17 z, (RRCReconfigurationSidelink_v1700_IEs__sl_LatencyBoundIUC_Report_r17 z, (RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToReleaseListPC5_r17 z, (RRCReconfigurationSidelink_v1700_IEs__sl_RLC_ChannelToAddModListPC5_r17 z, (RRCReconfigurationSidelink_v1700_IEs__nonCriticalExtension z, tt))))).
Definition RRCReconfigurationSidelink_v1700_IEs__F2 (y : seq_type RRCReconfigurationSidelink_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__RRCReconfigurationSidelink_v1700_IEs__Type i0 i1 i2 i3 i4
  end.
Lemma RRCReconfigurationSidelink_v1700_IEs__F1F2_cond (z : RRCReconfigurationSidelink_v1700_IEs__Type)
  : RRCReconfigurationSidelink_v1700_IEs__cond z ->
  (seq_cond RRCReconfigurationSidelink_v1700_IEs__list (RRCReconfigurationSidelink_v1700_IEs__F1 z)).
intro H. unfold RRCReconfigurationSidelink_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationSidelink_v1700_IEs__F1F2_cond2 (z : RRCReconfigurationSidelink_v1700_IEs__Type)
 : RRCReconfigurationSidelink_v1700_IEs__F2 (RRCReconfigurationSidelink_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationSidelink_v1700_IEs__F2F1_cond (y : seq_type RRCReconfigurationSidelink_v1700_IEs__list)
  : seq_cond RRCReconfigurationSidelink_v1700_IEs__list y ->
 (RRCReconfigurationSidelink_v1700_IEs__cond (RRCReconfigurationSidelink_v1700_IEs__F2 y)) /\  RRCReconfigurationSidelink_v1700_IEs__F1 (RRCReconfigurationSidelink_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationSidelink_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationSidelink_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationSidelink_v1700_IEs__Format : T_Format RRCReconfigurationSidelink_v1700_IEs__Type RRCReconfigurationSidelink_v1700_IEs__cond :=
        proj2_format  RRCReconfigurationSidelink_v1700_IEs__cond RRCReconfigurationSidelink_v1700_IEs__list__Format
    RRCReconfigurationSidelink_v1700_IEs__F1 RRCReconfigurationSidelink_v1700_IEs__F2 RRCReconfigurationSidelink_v1700_IEs__F1F2_cond  RRCReconfigurationSidelink_v1700_IEs__F1F2_cond2 RRCReconfigurationSidelink_v1700_IEs__F2F1_cond.
Opaque RRCReconfigurationSidelink_v1700_IEs__cond RRCReconfigurationSidelink_v1700_IEs__Format.

