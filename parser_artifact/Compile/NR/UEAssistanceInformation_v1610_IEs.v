Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.IDC_Assistance_r16.

Opaque IDC_Assistance_r16__cond IDC_Assistance_r16__Format.

Require Import NR.DRX_Preference_r16.

Opaque DRX_Preference_r16__cond DRX_Preference_r16__Format.

Require Import NR.MaxBW_Preference_r16.

Opaque MaxBW_Preference_r16__cond MaxBW_Preference_r16__Format.

Require Import NR.MaxCC_Preference_r16.

Opaque MaxCC_Preference_r16__cond MaxCC_Preference_r16__Format.

Require Import NR.MaxMIMO_LayerPreference_r16.

Opaque MaxMIMO_LayerPreference_r16__cond MaxMIMO_LayerPreference_r16__Format.

Require Import NR.MinSchedulingOffsetPreference_r16.

Opaque MinSchedulingOffsetPreference_r16__cond MinSchedulingOffsetPreference_r16__Format.

Require Import NR.ReleasePreference_r16.

Opaque ReleasePreference_r16__cond ReleasePreference_r16__Format.

Require Import NR.SL_UE_AssistanceInformationNR_r16.

Opaque SL_UE_AssistanceInformationNR_r16__cond SL_UE_AssistanceInformationNR_r16__Format.

Require Import NR.UEAssistanceInformation_v1700_IEs.

Opaque UEAssistanceInformation_v1700_IEs__cond UEAssistanceInformation_v1700_IEs__Format.

Record UEAssistanceInformation_v1610_IEs__Type : Set :=
  make__UEAssistanceInformation_v1610_IEs__Type {
    UEAssistanceInformation_v1610_IEs__idc_Assistance_r16 : option IDC_Assistance_r16__Type ;
    UEAssistanceInformation_v1610_IEs__drx_Preference_r16 : option DRX_Preference_r16__Type ;
    UEAssistanceInformation_v1610_IEs__maxBW_Preference_r16 : option MaxBW_Preference_r16__Type ;
    UEAssistanceInformation_v1610_IEs__maxCC_Preference_r16 : option MaxCC_Preference_r16__Type ;
    UEAssistanceInformation_v1610_IEs__maxMIMO_LayerPreference_r16 : option MaxMIMO_LayerPreference_r16__Type ;
    UEAssistanceInformation_v1610_IEs__minSchedulingOffsetPreference_r16 : option MinSchedulingOffsetPreference_r16__Type ;
    UEAssistanceInformation_v1610_IEs__releasePreference_r16 : option ReleasePreference_r16__Type ;
    UEAssistanceInformation_v1610_IEs__sl_UE_AssistanceInformationNR_r16 : option SL_UE_AssistanceInformationNR_r16__Type ;
    UEAssistanceInformation_v1610_IEs__referenceTimeInfoPreference_r16 : option bool ;
    UEAssistanceInformation_v1610_IEs__nonCriticalExtension : option UEAssistanceInformation_v1700_IEs__Type ;
}.
Definition UEAssistanceInformation_v1610_IEs__list := (
 Opt IDC_Assistance_r16__Type IDC_Assistance_r16__cond ::
 Opt DRX_Preference_r16__Type DRX_Preference_r16__cond ::
 Opt MaxBW_Preference_r16__Type MaxBW_Preference_r16__cond ::
 Opt MaxCC_Preference_r16__Type MaxCC_Preference_r16__cond ::
 Opt MaxMIMO_LayerPreference_r16__Type MaxMIMO_LayerPreference_r16__cond ::
 Opt MinSchedulingOffsetPreference_r16__Type MinSchedulingOffsetPreference_r16__cond ::
 Opt ReleasePreference_r16__Type ReleasePreference_r16__cond ::
 Opt SL_UE_AssistanceInformationNR_r16__Type SL_UE_AssistanceInformationNR_r16__cond ::
 Opt bool (fun _ => True) ::
 Opt UEAssistanceInformation_v1700_IEs__Type UEAssistanceInformation_v1700_IEs__cond ::
 nil).
Definition UEAssistanceInformation_v1610_IEs__cond z := 
  opt_cond IDC_Assistance_r16__cond (UEAssistanceInformation_v1610_IEs__idc_Assistance_r16 z) /\
  opt_cond DRX_Preference_r16__cond (UEAssistanceInformation_v1610_IEs__drx_Preference_r16 z) /\
  opt_cond MaxBW_Preference_r16__cond (UEAssistanceInformation_v1610_IEs__maxBW_Preference_r16 z) /\
  opt_cond MaxCC_Preference_r16__cond (UEAssistanceInformation_v1610_IEs__maxCC_Preference_r16 z) /\
  opt_cond MaxMIMO_LayerPreference_r16__cond (UEAssistanceInformation_v1610_IEs__maxMIMO_LayerPreference_r16 z) /\
  opt_cond MinSchedulingOffsetPreference_r16__cond (UEAssistanceInformation_v1610_IEs__minSchedulingOffsetPreference_r16 z) /\
  opt_cond ReleasePreference_r16__cond (UEAssistanceInformation_v1610_IEs__releasePreference_r16 z) /\
  opt_cond SL_UE_AssistanceInformationNR_r16__cond (UEAssistanceInformation_v1610_IEs__sl_UE_AssistanceInformationNR_r16 z) /\
  opt_cond (fun _ => True) (UEAssistanceInformation_v1610_IEs__referenceTimeInfoPreference_r16 z) /\
  opt_cond UEAssistanceInformation_v1700_IEs__cond (UEAssistanceInformation_v1610_IEs__nonCriticalExtension z) /\
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

Definition UEAssistanceInformation_v1610_IEs__Format_Type := Eval cbn in seq_format_prod UEAssistanceInformation_v1610_IEs__list.
Definition UEAssistanceInformation_v1610_IEs__Format_list : UEAssistanceInformation_v1610_IEs__Format_Type :=
  (IDC_Assistance_r16__Format, (DRX_Preference_r16__Format, (MaxBW_Preference_r16__Format, (MaxCC_Preference_r16__Format, (MaxMIMO_LayerPreference_r16__Format, (MinSchedulingOffsetPreference_r16__Format, (ReleasePreference_r16__Format, (SL_UE_AssistanceInformationNR_r16__Format, (bool__Format, (UEAssistanceInformation_v1700_IEs__Format, unit_format)))))))))).
Definition UEAssistanceInformation_v1610_IEs__list__Format := (*Eval compute in *) seq_format UEAssistanceInformation_v1610_IEs__list UEAssistanceInformation_v1610_IEs__Format_list.
Definition UEAssistanceInformation_v1610_IEs__F1 z :=
  (UEAssistanceInformation_v1610_IEs__idc_Assistance_r16 z, (UEAssistanceInformation_v1610_IEs__drx_Preference_r16 z, (UEAssistanceInformation_v1610_IEs__maxBW_Preference_r16 z, (UEAssistanceInformation_v1610_IEs__maxCC_Preference_r16 z, (UEAssistanceInformation_v1610_IEs__maxMIMO_LayerPreference_r16 z, (UEAssistanceInformation_v1610_IEs__minSchedulingOffsetPreference_r16 z, (UEAssistanceInformation_v1610_IEs__releasePreference_r16 z, (UEAssistanceInformation_v1610_IEs__sl_UE_AssistanceInformationNR_r16 z, (UEAssistanceInformation_v1610_IEs__referenceTimeInfoPreference_r16 z, (UEAssistanceInformation_v1610_IEs__nonCriticalExtension z, tt)))))))))).
Definition UEAssistanceInformation_v1610_IEs__F2 (y : seq_type UEAssistanceInformation_v1610_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__UEAssistanceInformation_v1610_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma UEAssistanceInformation_v1610_IEs__F1F2_cond (z : UEAssistanceInformation_v1610_IEs__Type)
  : UEAssistanceInformation_v1610_IEs__cond z ->
  (seq_cond UEAssistanceInformation_v1610_IEs__list (UEAssistanceInformation_v1610_IEs__F1 z)).
intro H. unfold UEAssistanceInformation_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma UEAssistanceInformation_v1610_IEs__F1F2_cond2 (z : UEAssistanceInformation_v1610_IEs__Type)
 : UEAssistanceInformation_v1610_IEs__F2 (UEAssistanceInformation_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEAssistanceInformation_v1610_IEs__F2F1_cond (y : seq_type UEAssistanceInformation_v1610_IEs__list)
  : seq_cond UEAssistanceInformation_v1610_IEs__list y ->
 (UEAssistanceInformation_v1610_IEs__cond (UEAssistanceInformation_v1610_IEs__F2 y)) /\  UEAssistanceInformation_v1610_IEs__F1 (UEAssistanceInformation_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEAssistanceInformation_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold UEAssistanceInformation_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEAssistanceInformation_v1610_IEs__Format : T_Format UEAssistanceInformation_v1610_IEs__Type UEAssistanceInformation_v1610_IEs__cond :=
        proj2_format  UEAssistanceInformation_v1610_IEs__cond UEAssistanceInformation_v1610_IEs__list__Format
    UEAssistanceInformation_v1610_IEs__F1 UEAssistanceInformation_v1610_IEs__F2 UEAssistanceInformation_v1610_IEs__F1F2_cond  UEAssistanceInformation_v1610_IEs__F1F2_cond2 UEAssistanceInformation_v1610_IEs__F2F1_cond.
Opaque UEAssistanceInformation_v1610_IEs__cond UEAssistanceInformation_v1610_IEs__Format.

