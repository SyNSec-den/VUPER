Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.PDCCH_Config.
Definition BWP_DownlinkDedicated__pdcch_Config__Type := SetupRelease__Type PDCCH_Config__Type.
Definition BWP_DownlinkDedicated__pdcch_Config__cond := SetupRelease__cond _ PDCCH_Config__cond.
Definition BWP_DownlinkDedicated__pdcch_Config__Format : T_Format BWP_DownlinkDedicated__pdcch_Config__Type BWP_DownlinkDedicated__pdcch_Config__cond := SetupRelease__Format _ _ PDCCH_Config__Format.
Opaque BWP_DownlinkDedicated__pdcch_Config__cond BWP_DownlinkDedicated__pdcch_Config__Format.

Require Import NR.SetupRelease.
Require Import NR.PDSCH_Config.
Definition BWP_DownlinkDedicated__pdsch_Config__Type := SetupRelease__Type PDSCH_Config__Type.
Definition BWP_DownlinkDedicated__pdsch_Config__cond := SetupRelease__cond _ PDSCH_Config__cond.
Definition BWP_DownlinkDedicated__pdsch_Config__Format : T_Format BWP_DownlinkDedicated__pdsch_Config__Type BWP_DownlinkDedicated__pdsch_Config__cond := SetupRelease__Format _ _ PDSCH_Config__Format.
Opaque BWP_DownlinkDedicated__pdsch_Config__cond BWP_DownlinkDedicated__pdsch_Config__Format.

Require Import NR.SetupRelease.
Require Import NR.SPS_Config.
Definition BWP_DownlinkDedicated__sps_Config__Type := SetupRelease__Type SPS_Config__Type.
Definition BWP_DownlinkDedicated__sps_Config__cond := SetupRelease__cond _ SPS_Config__cond.
Definition BWP_DownlinkDedicated__sps_Config__Format : T_Format BWP_DownlinkDedicated__sps_Config__Type BWP_DownlinkDedicated__sps_Config__cond := SetupRelease__Format _ _ SPS_Config__Format.
Opaque BWP_DownlinkDedicated__sps_Config__cond BWP_DownlinkDedicated__sps_Config__Format.

Require Import NR.SetupRelease.
Require Import NR.RadioLinkMonitoringConfig.
Definition BWP_DownlinkDedicated__radioLinkMonitoringConfig__Type := SetupRelease__Type RadioLinkMonitoringConfig__Type.
Definition BWP_DownlinkDedicated__radioLinkMonitoringConfig__cond := SetupRelease__cond _ RadioLinkMonitoringConfig__cond.
Definition BWP_DownlinkDedicated__radioLinkMonitoringConfig__Format : T_Format BWP_DownlinkDedicated__radioLinkMonitoringConfig__Type BWP_DownlinkDedicated__radioLinkMonitoringConfig__cond := SetupRelease__Format _ _ RadioLinkMonitoringConfig__Format.
Opaque BWP_DownlinkDedicated__radioLinkMonitoringConfig__cond BWP_DownlinkDedicated__radioLinkMonitoringConfig__Format.

Require Import NR.SPS_ConfigToAddModList_r16.

Opaque SPS_ConfigToAddModList_r16__cond SPS_ConfigToAddModList_r16__Format.

Require Import NR.SPS_ConfigToReleaseList_r16.

Opaque SPS_ConfigToReleaseList_r16__cond SPS_ConfigToReleaseList_r16__Format.

Require Import NR.SPS_ConfigDeactivationStateList_r16.

Opaque SPS_ConfigDeactivationStateList_r16__cond SPS_ConfigDeactivationStateList_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.BeamFailureRecoveryRSConfig_r16.
Definition BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__Type := SetupRelease__Type BeamFailureRecoveryRSConfig_r16__Type.
Definition BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__cond := SetupRelease__cond _ BeamFailureRecoveryRSConfig_r16__cond.
Definition BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__Format : T_Format BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__Type BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__cond := SetupRelease__Format _ _ BeamFailureRecoveryRSConfig_r16__Format.
Opaque BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__cond BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.PDCCH_Config.
Definition BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__Type := SetupRelease__Type PDCCH_Config__Type.
Definition BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__cond := SetupRelease__cond _ PDCCH_Config__cond.
Definition BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__Format : T_Format BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__Type BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__cond := SetupRelease__Format _ _ PDCCH_Config__Format.
Opaque BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__cond BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.PDCCH_Config.
Definition BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__Type := SetupRelease__Type PDCCH_Config__Type.
Definition BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__cond := SetupRelease__cond _ PDCCH_Config__cond.
Definition BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__Format : T_Format BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__Type BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__cond := SetupRelease__Format _ _ PDCCH_Config__Format.
Opaque BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__cond BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__Format.

Record BWP_DownlinkDedicated__ext0O__Type : Set :=
  make__BWP_DownlinkDedicated__ext0O__Type {
    BWP_DownlinkDedicated__ext0O__sps_ConfigToAddModList_r16 : option SPS_ConfigToAddModList_r16__Type ;
    BWP_DownlinkDedicated__ext0O__sps_ConfigToReleaseList_r16 : option SPS_ConfigToReleaseList_r16__Type ;
    BWP_DownlinkDedicated__ext0O__sps_ConfigDeactivationStateList_r16 : option SPS_ConfigDeactivationStateList_r16__Type ;
    BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16 : option BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__Type ;
    BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16 : option BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__Type ;
    BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16 : option BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__Type ;
}.
Definition BWP_DownlinkDedicated__ext0O__list := (
 Opt SPS_ConfigToAddModList_r16__Type SPS_ConfigToAddModList_r16__cond ::
 Opt SPS_ConfigToReleaseList_r16__Type SPS_ConfigToReleaseList_r16__cond ::
 Opt SPS_ConfigDeactivationStateList_r16__Type SPS_ConfigDeactivationStateList_r16__cond ::
 Opt BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__Type BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__cond ::
 Opt BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__Type BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__cond ::
 Opt BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__Type BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__cond ::
 nil).
Definition BWP_DownlinkDedicated__ext0O__cond z := 
  opt_cond SPS_ConfigToAddModList_r16__cond (BWP_DownlinkDedicated__ext0O__sps_ConfigToAddModList_r16 z) /\
  opt_cond SPS_ConfigToReleaseList_r16__cond (BWP_DownlinkDedicated__ext0O__sps_ConfigToReleaseList_r16 z) /\
  opt_cond SPS_ConfigDeactivationStateList_r16__cond (BWP_DownlinkDedicated__ext0O__sps_ConfigDeactivationStateList_r16 z) /\
  opt_cond BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__cond (BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16 z) /\
  opt_cond BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__cond (BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16 z) /\
  opt_cond BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__cond (BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16 z) /\
  True.

Definition BWP_DownlinkDedicated__ext0__Type := BWP_DownlinkDedicated__ext0O__Type.
Definition BWP_DownlinkDedicated__ext0__cond := BWP_DownlinkDedicated__ext0O__cond.

Definition BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__Type := bit_string_fixed.
Definition BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat maxNrofGapId_r17 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.SetupRelease.
Require Import NR.BeamFailureRecoveryRSConfig_r16.
Definition BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__Type := SetupRelease__Type BeamFailureRecoveryRSConfig_r16__Type.
Definition BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__cond := SetupRelease__cond _ BeamFailureRecoveryRSConfig_r16__cond.
Definition BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__Format : T_Format BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__Type BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__cond := SetupRelease__Format _ _ BeamFailureRecoveryRSConfig_r16__Format.
Opaque BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__cond BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.CFR_ConfigMulticast_r17.
Definition BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__Type := SetupRelease__Type CFR_ConfigMulticast_r17__Type.
Definition BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__cond := SetupRelease__cond _ CFR_ConfigMulticast_r17__cond.
Definition BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__Format : T_Format BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__Type BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__cond := SetupRelease__Format _ _ CFR_ConfigMulticast_r17__Format.
Opaque BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__cond BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__Format.

Require Import NR.DL_PPW_PreConfigToAddModList_r17.

Opaque DL_PPW_PreConfigToAddModList_r17__cond DL_PPW_PreConfigToAddModList_r17__Format.

Require Import NR.DL_PPW_PreConfigToReleaseList_r17.

Opaque DL_PPW_PreConfigToReleaseList_r17__cond DL_PPW_PreConfigToReleaseList_r17__Format.

Require Import NR.NonCellDefiningSSB_r17.

Opaque NonCellDefiningSSB_r17__cond NonCellDefiningSSB_r17__Format.

Require Import NR.MeasObjectId.

Opaque MeasObjectId__cond MeasObjectId__Format.

Record BWP_DownlinkDedicated__ext1O__Type : Set :=
  make__BWP_DownlinkDedicated__ext1O__Type {
    BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17 : option BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__Type ;
    BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17 : option BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__Type ;
    BWP_DownlinkDedicated__ext1O__harq_FeedbackEnablingforSPSactive_r17 : option bool ;
    BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17 : option BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__Type ;
    BWP_DownlinkDedicated__ext1O__dl_PPW_PreConfigToAddModList_r17 : option DL_PPW_PreConfigToAddModList_r17__Type ;
    BWP_DownlinkDedicated__ext1O__dl_PPW_PreConfigToReleaseList_r17 : option DL_PPW_PreConfigToReleaseList_r17__Type ;
    BWP_DownlinkDedicated__ext1O__nonCellDefiningSSB_r17 : option NonCellDefiningSSB_r17__Type ;
    BWP_DownlinkDedicated__ext1O__servingCellMO_r17 : option MeasObjectId__Type ;
}.
Definition BWP_DownlinkDedicated__ext1O__list := (
 Opt BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__Type BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__cond ::
 Opt BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__Type BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__cond ::
 Opt bool (fun _ => True) ::
 Opt BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__Type BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__cond ::
 Opt DL_PPW_PreConfigToAddModList_r17__Type DL_PPW_PreConfigToAddModList_r17__cond ::
 Opt DL_PPW_PreConfigToReleaseList_r17__Type DL_PPW_PreConfigToReleaseList_r17__cond ::
 Opt NonCellDefiningSSB_r17__Type NonCellDefiningSSB_r17__cond ::
 Opt MeasObjectId__Type MeasObjectId__cond ::
 nil).
Definition BWP_DownlinkDedicated__ext1O__cond z := 
  opt_cond BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__cond (BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17 z) /\
  opt_cond BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__cond (BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17 z) /\
  opt_cond (fun _ => True) (BWP_DownlinkDedicated__ext1O__harq_FeedbackEnablingforSPSactive_r17 z) /\
  opt_cond BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__cond (BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17 z) /\
  opt_cond DL_PPW_PreConfigToAddModList_r17__cond (BWP_DownlinkDedicated__ext1O__dl_PPW_PreConfigToAddModList_r17 z) /\
  opt_cond DL_PPW_PreConfigToReleaseList_r17__cond (BWP_DownlinkDedicated__ext1O__dl_PPW_PreConfigToReleaseList_r17 z) /\
  opt_cond NonCellDefiningSSB_r17__cond (BWP_DownlinkDedicated__ext1O__nonCellDefiningSSB_r17 z) /\
  opt_cond MeasObjectId__cond (BWP_DownlinkDedicated__ext1O__servingCellMO_r17 z) /\
  True.

Definition BWP_DownlinkDedicated__ext1__Type := BWP_DownlinkDedicated__ext1O__Type.
Definition BWP_DownlinkDedicated__ext1__cond := BWP_DownlinkDedicated__ext1O__cond.

Record BWP_DownlinkDedicated__Type : Set :=
  make__BWP_DownlinkDedicated__Type {
    BWP_DownlinkDedicated__pdcch_Config : option BWP_DownlinkDedicated__pdcch_Config__Type ;
    BWP_DownlinkDedicated__pdsch_Config : option BWP_DownlinkDedicated__pdsch_Config__Type ;
    BWP_DownlinkDedicated__sps_Config : option BWP_DownlinkDedicated__sps_Config__Type ;
    BWP_DownlinkDedicated__radioLinkMonitoringConfig : option BWP_DownlinkDedicated__radioLinkMonitoringConfig__Type ;
    BWP_DownlinkDedicated__ext0 : option BWP_DownlinkDedicated__ext0__Type ;
    BWP_DownlinkDedicated__ext1 : option BWP_DownlinkDedicated__ext1__Type ;
}.
Definition BWP_DownlinkDedicated__root_list : list seq_elem := (
 Opt BWP_DownlinkDedicated__pdcch_Config__Type BWP_DownlinkDedicated__pdcch_Config__cond ::
 Opt BWP_DownlinkDedicated__pdsch_Config__Type BWP_DownlinkDedicated__pdsch_Config__cond ::
 Opt BWP_DownlinkDedicated__sps_Config__Type BWP_DownlinkDedicated__sps_Config__cond ::
 Opt BWP_DownlinkDedicated__radioLinkMonitoringConfig__Type BWP_DownlinkDedicated__radioLinkMonitoringConfig__cond ::
 nil).
Definition BWP_DownlinkDedicated__ext_list : list typ := (
  typ_cons BWP_DownlinkDedicated__ext0__Type BWP_DownlinkDedicated__ext0__cond ::
  typ_cons BWP_DownlinkDedicated__ext1__Type BWP_DownlinkDedicated__ext1__cond ::
  nil).
Definition BWP_DownlinkDedicated__cond (z : BWP_DownlinkDedicated__Type) := 
(  opt_cond BWP_DownlinkDedicated__pdcch_Config__cond (BWP_DownlinkDedicated__pdcch_Config z) /\
  opt_cond BWP_DownlinkDedicated__pdsch_Config__cond (BWP_DownlinkDedicated__pdsch_Config z) /\
  opt_cond BWP_DownlinkDedicated__sps_Config__cond (BWP_DownlinkDedicated__sps_Config z) /\
  opt_cond BWP_DownlinkDedicated__radioLinkMonitoringConfig__cond (BWP_DownlinkDedicated__radioLinkMonitoringConfig z) /\
  True) /\ 
(  opt_cond BWP_DownlinkDedicated__ext0__cond (BWP_DownlinkDedicated__ext0 z) /\
  opt_cond BWP_DownlinkDedicated__ext1__cond (BWP_DownlinkDedicated__ext1 z) /\
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
Opaque BWP_DownlinkDedicated__pdcch_Config__cond BWP_DownlinkDedicated__pdcch_Config__Format.

Opaque BWP_DownlinkDedicated__pdsch_Config__cond BWP_DownlinkDedicated__pdsch_Config__Format.

Opaque BWP_DownlinkDedicated__sps_Config__cond BWP_DownlinkDedicated__sps_Config__Format.

Opaque BWP_DownlinkDedicated__radioLinkMonitoringConfig__cond BWP_DownlinkDedicated__radioLinkMonitoringConfig__Format.

Opaque BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__cond BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__Format.

Opaque BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__cond BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__Format.

Opaque BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__cond BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__Format.


Definition BWP_DownlinkDedicated__ext0O__Format_Type := Eval cbn in seq_format_prod BWP_DownlinkDedicated__ext0O__list.
Definition BWP_DownlinkDedicated__ext0O__Format_list : BWP_DownlinkDedicated__ext0O__Format_Type :=
  (SPS_ConfigToAddModList_r16__Format, (SPS_ConfigToReleaseList_r16__Format, (SPS_ConfigDeactivationStateList_r16__Format, (BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16__Format, (BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16__Format, (BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16__Format, unit_format)))))).
Definition BWP_DownlinkDedicated__ext0O__list__Format := (*Eval compute in *) seq_format BWP_DownlinkDedicated__ext0O__list BWP_DownlinkDedicated__ext0O__Format_list.
Definition BWP_DownlinkDedicated__ext0O__F1 z :=
  (BWP_DownlinkDedicated__ext0O__sps_ConfigToAddModList_r16 z, (BWP_DownlinkDedicated__ext0O__sps_ConfigToReleaseList_r16 z, (BWP_DownlinkDedicated__ext0O__sps_ConfigDeactivationStateList_r16 z, (BWP_DownlinkDedicated__ext0O__beamFailureRecoverySCellConfig_r16 z, (BWP_DownlinkDedicated__ext0O__sl_PDCCH_Config_r16 z, (BWP_DownlinkDedicated__ext0O__sl_V2X_PDCCH_Config_r16 z, tt)))))).
Definition BWP_DownlinkDedicated__ext0O__F2 (y : seq_type BWP_DownlinkDedicated__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__BWP_DownlinkDedicated__ext0O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma BWP_DownlinkDedicated__ext0O__F1F2_cond (z : BWP_DownlinkDedicated__ext0O__Type)
  : BWP_DownlinkDedicated__ext0O__cond z ->
  (seq_cond BWP_DownlinkDedicated__ext0O__list (BWP_DownlinkDedicated__ext0O__F1 z)).
intro H. unfold BWP_DownlinkDedicated__ext0O__cond in H. simpl. auto. Qed.
Lemma BWP_DownlinkDedicated__ext0O__F1F2_cond2 (z : BWP_DownlinkDedicated__ext0O__Type)
 : BWP_DownlinkDedicated__ext0O__F2 (BWP_DownlinkDedicated__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_DownlinkDedicated__ext0O__F2F1_cond (y : seq_type BWP_DownlinkDedicated__ext0O__list)
  : seq_cond BWP_DownlinkDedicated__ext0O__list y ->
 (BWP_DownlinkDedicated__ext0O__cond (BWP_DownlinkDedicated__ext0O__F2 y)) /\  BWP_DownlinkDedicated__ext0O__F1 (BWP_DownlinkDedicated__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_DownlinkDedicated__ext0O__cond. simpl in *. auto.
 - simpl. unfold BWP_DownlinkDedicated__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_DownlinkDedicated__ext0O__Format : T_Format BWP_DownlinkDedicated__ext0O__Type BWP_DownlinkDedicated__ext0O__cond :=
        proj2_format  BWP_DownlinkDedicated__ext0O__cond BWP_DownlinkDedicated__ext0O__list__Format
    BWP_DownlinkDedicated__ext0O__F1 BWP_DownlinkDedicated__ext0O__F2 BWP_DownlinkDedicated__ext0O__F1F2_cond  BWP_DownlinkDedicated__ext0O__F1F2_cond2 BWP_DownlinkDedicated__ext0O__F2F1_cond.
Opaque BWP_DownlinkDedicated__ext0O__cond BWP_DownlinkDedicated__ext0O__Format.

Definition BWP_DownlinkDedicated__ext0__check_all_none (b : BWP_DownlinkDedicated__ext0O__Type) : bool :=
match b with 
  | make__BWP_DownlinkDedicated__ext0O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition BWP_DownlinkDedicated__ext0__Format : T_Format BWP_DownlinkDedicated__ext0__Type BWP_DownlinkDedicated__ext0__cond :=
  restrict_add_format BWP_DownlinkDedicated__ext0__check_all_none BWP_DownlinkDedicated__ext0O__Format.

Opaque BWP_DownlinkDedicated__ext0__cond BWP_DownlinkDedicated__ext0__Format.

Definition BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__Format : T_Format BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__Type BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__cond := (* Eval compute in *) bit_string_fixed_format maxNrofGapId_r17.
Opaque BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__cond BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__Format.

Opaque BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__cond BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__Format.

Opaque BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__cond BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__Format.


Definition BWP_DownlinkDedicated__ext1O__Format_Type := Eval cbn in seq_format_prod BWP_DownlinkDedicated__ext1O__list.
Definition BWP_DownlinkDedicated__ext1O__Format_list : BWP_DownlinkDedicated__ext1O__Format_Type :=
  (BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17__Format, (BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17__Format, (bool__Format, (BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17__Format, (DL_PPW_PreConfigToAddModList_r17__Format, (DL_PPW_PreConfigToReleaseList_r17__Format, (NonCellDefiningSSB_r17__Format, (MeasObjectId__Format, unit_format)))))))).
Definition BWP_DownlinkDedicated__ext1O__list__Format := (*Eval compute in *) seq_format BWP_DownlinkDedicated__ext1O__list BWP_DownlinkDedicated__ext1O__Format_list.
Definition BWP_DownlinkDedicated__ext1O__F1 z :=
  (BWP_DownlinkDedicated__ext1O__preConfGapStatus_r17 z, (BWP_DownlinkDedicated__ext1O__beamFailureRecoverySpCellConfig_r17 z, (BWP_DownlinkDedicated__ext1O__harq_FeedbackEnablingforSPSactive_r17 z, (BWP_DownlinkDedicated__ext1O__cfr_ConfigMulticast_r17 z, (BWP_DownlinkDedicated__ext1O__dl_PPW_PreConfigToAddModList_r17 z, (BWP_DownlinkDedicated__ext1O__dl_PPW_PreConfigToReleaseList_r17 z, (BWP_DownlinkDedicated__ext1O__nonCellDefiningSSB_r17 z, (BWP_DownlinkDedicated__ext1O__servingCellMO_r17 z, tt)))))))).
Definition BWP_DownlinkDedicated__ext1O__F2 (y : seq_type BWP_DownlinkDedicated__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__BWP_DownlinkDedicated__ext1O__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma BWP_DownlinkDedicated__ext1O__F1F2_cond (z : BWP_DownlinkDedicated__ext1O__Type)
  : BWP_DownlinkDedicated__ext1O__cond z ->
  (seq_cond BWP_DownlinkDedicated__ext1O__list (BWP_DownlinkDedicated__ext1O__F1 z)).
intro H. unfold BWP_DownlinkDedicated__ext1O__cond in H. simpl. auto. Qed.
Lemma BWP_DownlinkDedicated__ext1O__F1F2_cond2 (z : BWP_DownlinkDedicated__ext1O__Type)
 : BWP_DownlinkDedicated__ext1O__F2 (BWP_DownlinkDedicated__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP_DownlinkDedicated__ext1O__F2F1_cond (y : seq_type BWP_DownlinkDedicated__ext1O__list)
  : seq_cond BWP_DownlinkDedicated__ext1O__list y ->
 (BWP_DownlinkDedicated__ext1O__cond (BWP_DownlinkDedicated__ext1O__F2 y)) /\  BWP_DownlinkDedicated__ext1O__F1 (BWP_DownlinkDedicated__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP_DownlinkDedicated__ext1O__cond. simpl in *. auto.
 - simpl. unfold BWP_DownlinkDedicated__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP_DownlinkDedicated__ext1O__Format : T_Format BWP_DownlinkDedicated__ext1O__Type BWP_DownlinkDedicated__ext1O__cond :=
        proj2_format  BWP_DownlinkDedicated__ext1O__cond BWP_DownlinkDedicated__ext1O__list__Format
    BWP_DownlinkDedicated__ext1O__F1 BWP_DownlinkDedicated__ext1O__F2 BWP_DownlinkDedicated__ext1O__F1F2_cond  BWP_DownlinkDedicated__ext1O__F1F2_cond2 BWP_DownlinkDedicated__ext1O__F2F1_cond.
Opaque BWP_DownlinkDedicated__ext1O__cond BWP_DownlinkDedicated__ext1O__Format.

Definition BWP_DownlinkDedicated__ext1__check_all_none (b : BWP_DownlinkDedicated__ext1O__Type) : bool :=
match b with 
  | make__BWP_DownlinkDedicated__ext1O__Type None None None None None None None None  => false 
  | _ => true 
 end.
Definition BWP_DownlinkDedicated__ext1__Format : T_Format BWP_DownlinkDedicated__ext1__Type BWP_DownlinkDedicated__ext1__cond :=
  restrict_add_format BWP_DownlinkDedicated__ext1__check_all_none BWP_DownlinkDedicated__ext1O__Format.

Opaque BWP_DownlinkDedicated__ext1__cond BWP_DownlinkDedicated__ext1__Format.


Definition BWP_DownlinkDedicated__root_Format_Type := Eval cbn in seq_format_prod BWP_DownlinkDedicated__root_list.
Definition BWP_DownlinkDedicated__root_Format_list : BWP_DownlinkDedicated__root_Format_Type :=
  (BWP_DownlinkDedicated__pdcch_Config__Format, (BWP_DownlinkDedicated__pdsch_Config__Format, (BWP_DownlinkDedicated__sps_Config__Format, (BWP_DownlinkDedicated__radioLinkMonitoringConfig__Format, unit_format)))).

Definition BWP_DownlinkDedicated__ext_Format_Type := Eval cbn in get_formats BWP_DownlinkDedicated__ext_list.
Definition BWP_DownlinkDedicated__ext_Format_list : BWP_DownlinkDedicated__ext_Format_Type :=
  (BWP_DownlinkDedicated__ext0__Format, (BWP_DownlinkDedicated__ext1__Format, unit__Format)).

Definition BWP_DownlinkDedicated__list_type : Set := (seq_type BWP_DownlinkDedicated__root_list) * (seq_ext_type BWP_DownlinkDedicated__ext_list).
Definition BWP_DownlinkDedicated__list_cond (z : BWP_DownlinkDedicated__list_type) : Prop :=
        (seq_cond BWP_DownlinkDedicated__root_list (fst z)) /\ (seq_ext_cond BWP_DownlinkDedicated__ext_list (snd z)).
Definition BWP_DownlinkDedicated__list_format : T_Format BWP_DownlinkDedicated__list_type BWP_DownlinkDedicated__list_cond :=
 (* Eval compute in *) seq_ext_format BWP_DownlinkDedicated__root_list BWP_DownlinkDedicated__root_Format_list BWP_DownlinkDedicated__ext_list BWP_DownlinkDedicated__ext_Format_list.

Opaque BWP_DownlinkDedicated__list_format.
Definition BWP_DownlinkDedicated__F1 (z : BWP_DownlinkDedicated__Type) : BWP_DownlinkDedicated__list_type :=
  (((BWP_DownlinkDedicated__pdcch_Config z, (BWP_DownlinkDedicated__pdsch_Config z, (BWP_DownlinkDedicated__sps_Config z, (BWP_DownlinkDedicated__radioLinkMonitoringConfig z, tt))))), (
(BWP_DownlinkDedicated__ext0 z, (BWP_DownlinkDedicated__ext1 z, tt)))).
Definition BWP_DownlinkDedicated__F2 (y : BWP_DownlinkDedicated__list_type) : BWP_DownlinkDedicated__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__BWP_DownlinkDedicated__Type j0 j1 j2 j3 i0 i1
  end.
Definition BWP_DownlinkDedicated__helper1 : (forall a : BWP_DownlinkDedicated__Type, BWP_DownlinkDedicated__cond a -> BWP_DownlinkDedicated__list_cond (BWP_DownlinkDedicated__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BWP_DownlinkDedicated__helper2 : (forall a : BWP_DownlinkDedicated__Type, BWP_DownlinkDedicated__F2 (BWP_DownlinkDedicated__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BWP_DownlinkDedicated__helper3 : (forall b : BWP_DownlinkDedicated__list_type, BWP_DownlinkDedicated__list_cond b -> BWP_DownlinkDedicated__cond (BWP_DownlinkDedicated__F2 b) /\ BWP_DownlinkDedicated__F1 (BWP_DownlinkDedicated__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BWP_DownlinkDedicated__cond, BWP_DownlinkDedicated__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BWP_DownlinkDedicated__Format : T_Format BWP_DownlinkDedicated__Type BWP_DownlinkDedicated__cond :=
 proj2_format BWP_DownlinkDedicated__cond BWP_DownlinkDedicated__list_format  BWP_DownlinkDedicated__F1 BWP_DownlinkDedicated__F2 BWP_DownlinkDedicated__helper1 BWP_DownlinkDedicated__helper2 BWP_DownlinkDedicated__helper3.

Opaque BWP_DownlinkDedicated__cond BWP_DownlinkDedicated__Format.

