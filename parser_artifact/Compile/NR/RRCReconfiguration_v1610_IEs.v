Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.OtherConfig_v1610.

Opaque OtherConfig_v1610__cond OtherConfig_v1610__Format.

Require Import NR.SetupRelease.
Require Import NR.BAP_Config_r16.
Definition RRCReconfiguration_v1610_IEs__bap_Config_r16__Type := SetupRelease__Type BAP_Config_r16__Type.
Definition RRCReconfiguration_v1610_IEs__bap_Config_r16__cond := SetupRelease__cond _ BAP_Config_r16__cond.
Definition RRCReconfiguration_v1610_IEs__bap_Config_r16__Format : T_Format RRCReconfiguration_v1610_IEs__bap_Config_r16__Type RRCReconfiguration_v1610_IEs__bap_Config_r16__cond := SetupRelease__Format _ _ BAP_Config_r16__Format.
Opaque RRCReconfiguration_v1610_IEs__bap_Config_r16__cond RRCReconfiguration_v1610_IEs__bap_Config_r16__Format.

Require Import NR.IAB_IP_AddressConfigurationList_r16.

Opaque IAB_IP_AddressConfigurationList_r16__cond IAB_IP_AddressConfigurationList_r16__Format.

Require Import NR.ConditionalReconfiguration_r16.

Opaque ConditionalReconfiguration_r16__cond ConditionalReconfiguration_r16__Format.

Inductive RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Type : Set :=
 | RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__true
.
Definition RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__cond := (fun (_ : RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Type) => True).
Lemma RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__nat__helper.

Definition RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F1 t :=
  match t with
  | RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__true => 0
  end.
Definition RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F2 n :=
  match n with
  | 0 => RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__true
  | _ => RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__true
  end.
Lemma RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F1F2 : forall x : RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Type, (RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F1 x <= 0) /\ RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F2 (RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F1 x) = x. imp_solve. Qed.
Lemma RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F2F1 : forall (y : nat) (H : y <= 0), RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F1 (RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.T316_r16.
Definition RRCReconfiguration_v1610_IEs__t316_r16__Type := SetupRelease__Type T316_r16__Type.
Definition RRCReconfiguration_v1610_IEs__t316_r16__cond := SetupRelease__cond _ T316_r16__cond.
Definition RRCReconfiguration_v1610_IEs__t316_r16__Format : T_Format RRCReconfiguration_v1610_IEs__t316_r16__Type RRCReconfiguration_v1610_IEs__t316_r16__cond := SetupRelease__Format _ _ T316_r16__Format.
Opaque RRCReconfiguration_v1610_IEs__t316_r16__cond RRCReconfiguration_v1610_IEs__t316_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.NeedForGapsConfigNR_r16.
Definition RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__Type := SetupRelease__Type NeedForGapsConfigNR_r16__Type.
Definition RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__cond := SetupRelease__cond _ NeedForGapsConfigNR_r16__cond.
Definition RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__Format : T_Format RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__Type RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__cond := SetupRelease__Format _ _ NeedForGapsConfigNR_r16__Format.
Opaque RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__cond RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.OnDemandSIB_Request_r16.
Definition RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__Type := SetupRelease__Type OnDemandSIB_Request_r16__Type.
Definition RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__cond := SetupRelease__cond _ OnDemandSIB_Request_r16__cond.
Definition RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__Format : T_Format RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__Type RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__cond := SetupRelease__Format _ _ OnDemandSIB_Request_r16__Format.
Opaque RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__cond RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_ConfigDedicatedNR_r16.
Definition RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__Type := SetupRelease__Type SL_ConfigDedicatedNR_r16__Type.
Definition RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__cond := SetupRelease__cond _ SL_ConfigDedicatedNR_r16__cond.
Definition RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__Format : T_Format RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__Type RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__cond := SetupRelease__Format _ _ SL_ConfigDedicatedNR_r16__Format.
Opaque RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__cond RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_ConfigDedicatedEUTRA_Info_r16.
Definition RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__Type := SetupRelease__Type SL_ConfigDedicatedEUTRA_Info_r16__Type.
Definition RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__cond := SetupRelease__cond _ SL_ConfigDedicatedEUTRA_Info_r16__cond.
Definition RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__Format : T_Format RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__Type RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__cond := SetupRelease__Format _ _ SL_ConfigDedicatedEUTRA_Info_r16__Format.
Opaque RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__cond RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__Format.

Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Require Import NR.RRCReconfiguration_v1700_IEs.

Opaque RRCReconfiguration_v1700_IEs__cond RRCReconfiguration_v1700_IEs__Format.

Record RRCReconfiguration_v1610_IEs__Type : Set :=
  make__RRCReconfiguration_v1610_IEs__Type {
    RRCReconfiguration_v1610_IEs__otherConfig_v1610 : option OtherConfig_v1610__Type ;
    RRCReconfiguration_v1610_IEs__bap_Config_r16 : option RRCReconfiguration_v1610_IEs__bap_Config_r16__Type ;
    RRCReconfiguration_v1610_IEs__iab_IP_AddressConfigurationList_r16 : option IAB_IP_AddressConfigurationList_r16__Type ;
    RRCReconfiguration_v1610_IEs__conditionalReconfiguration_r16 : option ConditionalReconfiguration_r16__Type ;
    RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16 : option RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Type ;
    RRCReconfiguration_v1610_IEs__t316_r16 : option RRCReconfiguration_v1610_IEs__t316_r16__Type ;
    RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16 : option RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__Type ;
    RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16 : option RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__Type ;
    RRCReconfiguration_v1610_IEs__dedicatedPosSysInfoDelivery_r16 : option octet_string ;
    RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16 : option RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__Type ;
    RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16 : option RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__Type ;
    RRCReconfiguration_v1610_IEs__targetCellSMTC_SCG_r16 : option SSB_MTC__Type ;
    RRCReconfiguration_v1610_IEs__nonCriticalExtension : option RRCReconfiguration_v1700_IEs__Type ;
}.
Definition RRCReconfiguration_v1610_IEs__list := (
 Opt OtherConfig_v1610__Type OtherConfig_v1610__cond ::
 Opt RRCReconfiguration_v1610_IEs__bap_Config_r16__Type RRCReconfiguration_v1610_IEs__bap_Config_r16__cond ::
 Opt IAB_IP_AddressConfigurationList_r16__Type IAB_IP_AddressConfigurationList_r16__cond ::
 Opt ConditionalReconfiguration_r16__Type ConditionalReconfiguration_r16__cond ::
 Opt RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Type RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__cond ::
 Opt RRCReconfiguration_v1610_IEs__t316_r16__Type RRCReconfiguration_v1610_IEs__t316_r16__cond ::
 Opt RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__Type RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__cond ::
 Opt RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__Type RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__Type RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__cond ::
 Opt RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__Type RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__cond ::
 Opt SSB_MTC__Type SSB_MTC__cond ::
 Opt RRCReconfiguration_v1700_IEs__Type RRCReconfiguration_v1700_IEs__cond ::
 nil).
Definition RRCReconfiguration_v1610_IEs__cond z := 
  opt_cond OtherConfig_v1610__cond (RRCReconfiguration_v1610_IEs__otherConfig_v1610 z) /\
  opt_cond RRCReconfiguration_v1610_IEs__bap_Config_r16__cond (RRCReconfiguration_v1610_IEs__bap_Config_r16 z) /\
  opt_cond IAB_IP_AddressConfigurationList_r16__cond (RRCReconfiguration_v1610_IEs__iab_IP_AddressConfigurationList_r16 z) /\
  opt_cond ConditionalReconfiguration_r16__cond (RRCReconfiguration_v1610_IEs__conditionalReconfiguration_r16 z) /\
  opt_cond RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__cond (RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16 z) /\
  opt_cond RRCReconfiguration_v1610_IEs__t316_r16__cond (RRCReconfiguration_v1610_IEs__t316_r16 z) /\
  opt_cond RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__cond (RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16 z) /\
  opt_cond RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__cond (RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCReconfiguration_v1610_IEs__dedicatedPosSysInfoDelivery_r16 z) /\
  opt_cond RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__cond (RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16 z) /\
  opt_cond RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__cond (RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16 z) /\
  opt_cond SSB_MTC__cond (RRCReconfiguration_v1610_IEs__targetCellSMTC_SCG_r16 z) /\
  opt_cond RRCReconfiguration_v1700_IEs__cond (RRCReconfiguration_v1610_IEs__nonCriticalExtension z) /\
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
Opaque RRCReconfiguration_v1610_IEs__bap_Config_r16__cond RRCReconfiguration_v1610_IEs__bap_Config_r16__Format.

Definition RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Format : T_Format RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__nat__Format RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F1 RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F2 RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F1F2 RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__F2F1.

Opaque RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__cond RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Format.

Opaque RRCReconfiguration_v1610_IEs__t316_r16__cond RRCReconfiguration_v1610_IEs__t316_r16__Format.

Opaque RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__cond RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__Format.

Opaque RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__cond RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__Format.

Opaque RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__cond RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__Format.

Opaque RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__cond RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__Format.


Definition RRCReconfiguration_v1610_IEs__Format_Type := Eval cbn in seq_format_prod RRCReconfiguration_v1610_IEs__list.
Definition RRCReconfiguration_v1610_IEs__Format_list : RRCReconfiguration_v1610_IEs__Format_Type :=
  (OtherConfig_v1610__Format, (RRCReconfiguration_v1610_IEs__bap_Config_r16__Format, (IAB_IP_AddressConfigurationList_r16__Format, (ConditionalReconfiguration_r16__Format, (RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16__Format, (RRCReconfiguration_v1610_IEs__t316_r16__Format, (RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16__Format, (RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16__Format, (octet_string_nc__Format, (RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16__Format, (RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16__Format, (SSB_MTC__Format, (RRCReconfiguration_v1700_IEs__Format, unit_format))))))))))))).
Definition RRCReconfiguration_v1610_IEs__list__Format := (*Eval compute in *) seq_format RRCReconfiguration_v1610_IEs__list RRCReconfiguration_v1610_IEs__Format_list.
Definition RRCReconfiguration_v1610_IEs__F1 z :=
  (RRCReconfiguration_v1610_IEs__otherConfig_v1610 z, (RRCReconfiguration_v1610_IEs__bap_Config_r16 z, (RRCReconfiguration_v1610_IEs__iab_IP_AddressConfigurationList_r16 z, (RRCReconfiguration_v1610_IEs__conditionalReconfiguration_r16 z, (RRCReconfiguration_v1610_IEs__daps_SourceRelease_r16 z, (RRCReconfiguration_v1610_IEs__t316_r16 z, (RRCReconfiguration_v1610_IEs__needForGapsConfigNR_r16 z, (RRCReconfiguration_v1610_IEs__onDemandSIB_Request_r16 z, (RRCReconfiguration_v1610_IEs__dedicatedPosSysInfoDelivery_r16 z, (RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedNR_r16 z, (RRCReconfiguration_v1610_IEs__sl_ConfigDedicatedEUTRA_Info_r16 z, (RRCReconfiguration_v1610_IEs__targetCellSMTC_SCG_r16 z, (RRCReconfiguration_v1610_IEs__nonCriticalExtension z, tt))))))))))))).
Definition RRCReconfiguration_v1610_IEs__F2 (y : seq_type RRCReconfiguration_v1610_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, _)))))))))))))=>
    make__RRCReconfiguration_v1610_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12
  end.
Lemma RRCReconfiguration_v1610_IEs__F1F2_cond (z : RRCReconfiguration_v1610_IEs__Type)
  : RRCReconfiguration_v1610_IEs__cond z ->
  (seq_cond RRCReconfiguration_v1610_IEs__list (RRCReconfiguration_v1610_IEs__F1 z)).
intro H. unfold RRCReconfiguration_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma RRCReconfiguration_v1610_IEs__F1F2_cond2 (z : RRCReconfiguration_v1610_IEs__Type)
 : RRCReconfiguration_v1610_IEs__F2 (RRCReconfiguration_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfiguration_v1610_IEs__F2F1_cond (y : seq_type RRCReconfiguration_v1610_IEs__list)
  : seq_cond RRCReconfiguration_v1610_IEs__list y ->
 (RRCReconfiguration_v1610_IEs__cond (RRCReconfiguration_v1610_IEs__F2 y)) /\  RRCReconfiguration_v1610_IEs__F1 (RRCReconfiguration_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfiguration_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCReconfiguration_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfiguration_v1610_IEs__Format : T_Format RRCReconfiguration_v1610_IEs__Type RRCReconfiguration_v1610_IEs__cond :=
        proj2_format  RRCReconfiguration_v1610_IEs__cond RRCReconfiguration_v1610_IEs__list__Format
    RRCReconfiguration_v1610_IEs__F1 RRCReconfiguration_v1610_IEs__F2 RRCReconfiguration_v1610_IEs__F1F2_cond  RRCReconfiguration_v1610_IEs__F1F2_cond2 RRCReconfiguration_v1610_IEs__F2F1_cond.
Opaque RRCReconfiguration_v1610_IEs__cond RRCReconfiguration_v1610_IEs__Format.

