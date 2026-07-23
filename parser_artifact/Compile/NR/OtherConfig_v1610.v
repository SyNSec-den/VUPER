Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.IDC_AssistanceConfig_r16.
Definition OtherConfig_v1610__idc_AssistanceConfig_r16__Type := SetupRelease__Type IDC_AssistanceConfig_r16__Type.
Definition OtherConfig_v1610__idc_AssistanceConfig_r16__cond := SetupRelease__cond _ IDC_AssistanceConfig_r16__cond.
Definition OtherConfig_v1610__idc_AssistanceConfig_r16__Format : T_Format OtherConfig_v1610__idc_AssistanceConfig_r16__Type OtherConfig_v1610__idc_AssistanceConfig_r16__cond := SetupRelease__Format _ _ IDC_AssistanceConfig_r16__Format.
Opaque OtherConfig_v1610__idc_AssistanceConfig_r16__cond OtherConfig_v1610__idc_AssistanceConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.DRX_PreferenceConfig_r16.
Definition OtherConfig_v1610__drx_PreferenceConfig_r16__Type := SetupRelease__Type DRX_PreferenceConfig_r16__Type.
Definition OtherConfig_v1610__drx_PreferenceConfig_r16__cond := SetupRelease__cond _ DRX_PreferenceConfig_r16__cond.
Definition OtherConfig_v1610__drx_PreferenceConfig_r16__Format : T_Format OtherConfig_v1610__drx_PreferenceConfig_r16__Type OtherConfig_v1610__drx_PreferenceConfig_r16__cond := SetupRelease__Format _ _ DRX_PreferenceConfig_r16__Format.
Opaque OtherConfig_v1610__drx_PreferenceConfig_r16__cond OtherConfig_v1610__drx_PreferenceConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.MaxBW_PreferenceConfig_r16.
Definition OtherConfig_v1610__maxBW_PreferenceConfig_r16__Type := SetupRelease__Type MaxBW_PreferenceConfig_r16__Type.
Definition OtherConfig_v1610__maxBW_PreferenceConfig_r16__cond := SetupRelease__cond _ MaxBW_PreferenceConfig_r16__cond.
Definition OtherConfig_v1610__maxBW_PreferenceConfig_r16__Format : T_Format OtherConfig_v1610__maxBW_PreferenceConfig_r16__Type OtherConfig_v1610__maxBW_PreferenceConfig_r16__cond := SetupRelease__Format _ _ MaxBW_PreferenceConfig_r16__Format.
Opaque OtherConfig_v1610__maxBW_PreferenceConfig_r16__cond OtherConfig_v1610__maxBW_PreferenceConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.MaxCC_PreferenceConfig_r16.
Definition OtherConfig_v1610__maxCC_PreferenceConfig_r16__Type := SetupRelease__Type MaxCC_PreferenceConfig_r16__Type.
Definition OtherConfig_v1610__maxCC_PreferenceConfig_r16__cond := SetupRelease__cond _ MaxCC_PreferenceConfig_r16__cond.
Definition OtherConfig_v1610__maxCC_PreferenceConfig_r16__Format : T_Format OtherConfig_v1610__maxCC_PreferenceConfig_r16__Type OtherConfig_v1610__maxCC_PreferenceConfig_r16__cond := SetupRelease__Format _ _ MaxCC_PreferenceConfig_r16__Format.
Opaque OtherConfig_v1610__maxCC_PreferenceConfig_r16__cond OtherConfig_v1610__maxCC_PreferenceConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.MaxMIMO_LayerPreferenceConfig_r16.
Definition OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__Type := SetupRelease__Type MaxMIMO_LayerPreferenceConfig_r16__Type.
Definition OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__cond := SetupRelease__cond _ MaxMIMO_LayerPreferenceConfig_r16__cond.
Definition OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__Format : T_Format OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__Type OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__cond := SetupRelease__Format _ _ MaxMIMO_LayerPreferenceConfig_r16__Format.
Opaque OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__cond OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.MinSchedulingOffsetPreferenceConfig_r16.
Definition OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__Type := SetupRelease__Type MinSchedulingOffsetPreferenceConfig_r16__Type.
Definition OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__cond := SetupRelease__cond _ MinSchedulingOffsetPreferenceConfig_r16__cond.
Definition OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__Format : T_Format OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__Type OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__cond := SetupRelease__Format _ _ MinSchedulingOffsetPreferenceConfig_r16__Format.
Opaque OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__cond OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.ReleasePreferenceConfig_r16.
Definition OtherConfig_v1610__releasePreferenceConfig_r16__Type := SetupRelease__Type ReleasePreferenceConfig_r16__Type.
Definition OtherConfig_v1610__releasePreferenceConfig_r16__cond := SetupRelease__cond _ ReleasePreferenceConfig_r16__cond.
Definition OtherConfig_v1610__releasePreferenceConfig_r16__Format : T_Format OtherConfig_v1610__releasePreferenceConfig_r16__Type OtherConfig_v1610__releasePreferenceConfig_r16__cond := SetupRelease__Format _ _ ReleasePreferenceConfig_r16__Format.
Opaque OtherConfig_v1610__releasePreferenceConfig_r16__cond OtherConfig_v1610__releasePreferenceConfig_r16__Format.

Inductive OtherConfig_v1610__referenceTimePreferenceReporting_r16__Type : Set :=
 | OtherConfig_v1610__referenceTimePreferenceReporting_r16__true
.
Definition OtherConfig_v1610__referenceTimePreferenceReporting_r16__cond := (fun (_ : OtherConfig_v1610__referenceTimePreferenceReporting_r16__Type) => True).
Lemma OtherConfig_v1610__referenceTimePreferenceReporting_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition OtherConfig_v1610__referenceTimePreferenceReporting_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 OtherConfig_v1610__referenceTimePreferenceReporting_r16__nat__helper.

Definition OtherConfig_v1610__referenceTimePreferenceReporting_r16__F1 t :=
  match t with
  | OtherConfig_v1610__referenceTimePreferenceReporting_r16__true => 0
  end.
Definition OtherConfig_v1610__referenceTimePreferenceReporting_r16__F2 n :=
  match n with
  | 0 => OtherConfig_v1610__referenceTimePreferenceReporting_r16__true
  | _ => OtherConfig_v1610__referenceTimePreferenceReporting_r16__true
  end.
Lemma OtherConfig_v1610__referenceTimePreferenceReporting_r16__F1F2 : forall x : OtherConfig_v1610__referenceTimePreferenceReporting_r16__Type, (OtherConfig_v1610__referenceTimePreferenceReporting_r16__F1 x <= 0) /\ OtherConfig_v1610__referenceTimePreferenceReporting_r16__F2 (OtherConfig_v1610__referenceTimePreferenceReporting_r16__F1 x) = x. imp_solve. Qed.
Lemma OtherConfig_v1610__referenceTimePreferenceReporting_r16__F2F1 : forall (y : nat) (H : y <= 0), OtherConfig_v1610__referenceTimePreferenceReporting_r16__F1 (OtherConfig_v1610__referenceTimePreferenceReporting_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.BT_NameList_r16.
Definition OtherConfig_v1610__btNameList_r16__Type := SetupRelease__Type BT_NameList_r16__Type.
Definition OtherConfig_v1610__btNameList_r16__cond := SetupRelease__cond _ BT_NameList_r16__cond.
Definition OtherConfig_v1610__btNameList_r16__Format : T_Format OtherConfig_v1610__btNameList_r16__Type OtherConfig_v1610__btNameList_r16__cond := SetupRelease__Format _ _ BT_NameList_r16__Format.
Opaque OtherConfig_v1610__btNameList_r16__cond OtherConfig_v1610__btNameList_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.WLAN_NameList_r16.
Definition OtherConfig_v1610__wlanNameList_r16__Type := SetupRelease__Type WLAN_NameList_r16__Type.
Definition OtherConfig_v1610__wlanNameList_r16__cond := SetupRelease__cond _ WLAN_NameList_r16__cond.
Definition OtherConfig_v1610__wlanNameList_r16__Format : T_Format OtherConfig_v1610__wlanNameList_r16__Type OtherConfig_v1610__wlanNameList_r16__cond := SetupRelease__Format _ _ WLAN_NameList_r16__Format.
Opaque OtherConfig_v1610__wlanNameList_r16__cond OtherConfig_v1610__wlanNameList_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.Sensor_NameList_r16.
Definition OtherConfig_v1610__sensorNameList_r16__Type := SetupRelease__Type Sensor_NameList_r16__Type.
Definition OtherConfig_v1610__sensorNameList_r16__cond := SetupRelease__cond _ Sensor_NameList_r16__cond.
Definition OtherConfig_v1610__sensorNameList_r16__Format : T_Format OtherConfig_v1610__sensorNameList_r16__Type OtherConfig_v1610__sensorNameList_r16__cond := SetupRelease__Format _ _ Sensor_NameList_r16__Format.
Opaque OtherConfig_v1610__sensorNameList_r16__cond OtherConfig_v1610__sensorNameList_r16__Format.

Inductive OtherConfig_v1610__obtainCommonLocation_r16__Type : Set :=
 | OtherConfig_v1610__obtainCommonLocation_r16__true
.
Definition OtherConfig_v1610__obtainCommonLocation_r16__cond := (fun (_ : OtherConfig_v1610__obtainCommonLocation_r16__Type) => True).
Lemma OtherConfig_v1610__obtainCommonLocation_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition OtherConfig_v1610__obtainCommonLocation_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 OtherConfig_v1610__obtainCommonLocation_r16__nat__helper.

Definition OtherConfig_v1610__obtainCommonLocation_r16__F1 t :=
  match t with
  | OtherConfig_v1610__obtainCommonLocation_r16__true => 0
  end.
Definition OtherConfig_v1610__obtainCommonLocation_r16__F2 n :=
  match n with
  | 0 => OtherConfig_v1610__obtainCommonLocation_r16__true
  | _ => OtherConfig_v1610__obtainCommonLocation_r16__true
  end.
Lemma OtherConfig_v1610__obtainCommonLocation_r16__F1F2 : forall x : OtherConfig_v1610__obtainCommonLocation_r16__Type, (OtherConfig_v1610__obtainCommonLocation_r16__F1 x <= 0) /\ OtherConfig_v1610__obtainCommonLocation_r16__F2 (OtherConfig_v1610__obtainCommonLocation_r16__F1 x) = x. imp_solve. Qed.
Lemma OtherConfig_v1610__obtainCommonLocation_r16__F2F1 : forall (y : nat) (H : y <= 0), OtherConfig_v1610__obtainCommonLocation_r16__F1 (OtherConfig_v1610__obtainCommonLocation_r16__F2 y) = y. enum_solve H y. Qed.

Inductive OtherConfig_v1610__sl_AssistanceConfigNR_r16__Type : Set :=
 | OtherConfig_v1610__sl_AssistanceConfigNR_r16__true
.
Definition OtherConfig_v1610__sl_AssistanceConfigNR_r16__cond := (fun (_ : OtherConfig_v1610__sl_AssistanceConfigNR_r16__Type) => True).
Lemma OtherConfig_v1610__sl_AssistanceConfigNR_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition OtherConfig_v1610__sl_AssistanceConfigNR_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 OtherConfig_v1610__sl_AssistanceConfigNR_r16__nat__helper.

Definition OtherConfig_v1610__sl_AssistanceConfigNR_r16__F1 t :=
  match t with
  | OtherConfig_v1610__sl_AssistanceConfigNR_r16__true => 0
  end.
Definition OtherConfig_v1610__sl_AssistanceConfigNR_r16__F2 n :=
  match n with
  | 0 => OtherConfig_v1610__sl_AssistanceConfigNR_r16__true
  | _ => OtherConfig_v1610__sl_AssistanceConfigNR_r16__true
  end.
Lemma OtherConfig_v1610__sl_AssistanceConfigNR_r16__F1F2 : forall x : OtherConfig_v1610__sl_AssistanceConfigNR_r16__Type, (OtherConfig_v1610__sl_AssistanceConfigNR_r16__F1 x <= 0) /\ OtherConfig_v1610__sl_AssistanceConfigNR_r16__F2 (OtherConfig_v1610__sl_AssistanceConfigNR_r16__F1 x) = x. imp_solve. Qed.
Lemma OtherConfig_v1610__sl_AssistanceConfigNR_r16__F2F1 : forall (y : nat) (H : y <= 0), OtherConfig_v1610__sl_AssistanceConfigNR_r16__F1 (OtherConfig_v1610__sl_AssistanceConfigNR_r16__F2 y) = y. enum_solve H y. Qed.

Record OtherConfig_v1610__Type : Set :=
  make__OtherConfig_v1610__Type {
    OtherConfig_v1610__idc_AssistanceConfig_r16 : option OtherConfig_v1610__idc_AssistanceConfig_r16__Type ;
    OtherConfig_v1610__drx_PreferenceConfig_r16 : option OtherConfig_v1610__drx_PreferenceConfig_r16__Type ;
    OtherConfig_v1610__maxBW_PreferenceConfig_r16 : option OtherConfig_v1610__maxBW_PreferenceConfig_r16__Type ;
    OtherConfig_v1610__maxCC_PreferenceConfig_r16 : option OtherConfig_v1610__maxCC_PreferenceConfig_r16__Type ;
    OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16 : option OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__Type ;
    OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16 : option OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__Type ;
    OtherConfig_v1610__releasePreferenceConfig_r16 : option OtherConfig_v1610__releasePreferenceConfig_r16__Type ;
    OtherConfig_v1610__referenceTimePreferenceReporting_r16 : option OtherConfig_v1610__referenceTimePreferenceReporting_r16__Type ;
    OtherConfig_v1610__btNameList_r16 : option OtherConfig_v1610__btNameList_r16__Type ;
    OtherConfig_v1610__wlanNameList_r16 : option OtherConfig_v1610__wlanNameList_r16__Type ;
    OtherConfig_v1610__sensorNameList_r16 : option OtherConfig_v1610__sensorNameList_r16__Type ;
    OtherConfig_v1610__obtainCommonLocation_r16 : option OtherConfig_v1610__obtainCommonLocation_r16__Type ;
    OtherConfig_v1610__sl_AssistanceConfigNR_r16 : option OtherConfig_v1610__sl_AssistanceConfigNR_r16__Type ;
}.
Definition OtherConfig_v1610__list := (
 Opt OtherConfig_v1610__idc_AssistanceConfig_r16__Type OtherConfig_v1610__idc_AssistanceConfig_r16__cond ::
 Opt OtherConfig_v1610__drx_PreferenceConfig_r16__Type OtherConfig_v1610__drx_PreferenceConfig_r16__cond ::
 Opt OtherConfig_v1610__maxBW_PreferenceConfig_r16__Type OtherConfig_v1610__maxBW_PreferenceConfig_r16__cond ::
 Opt OtherConfig_v1610__maxCC_PreferenceConfig_r16__Type OtherConfig_v1610__maxCC_PreferenceConfig_r16__cond ::
 Opt OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__Type OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__cond ::
 Opt OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__Type OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__cond ::
 Opt OtherConfig_v1610__releasePreferenceConfig_r16__Type OtherConfig_v1610__releasePreferenceConfig_r16__cond ::
 Opt OtherConfig_v1610__referenceTimePreferenceReporting_r16__Type OtherConfig_v1610__referenceTimePreferenceReporting_r16__cond ::
 Opt OtherConfig_v1610__btNameList_r16__Type OtherConfig_v1610__btNameList_r16__cond ::
 Opt OtherConfig_v1610__wlanNameList_r16__Type OtherConfig_v1610__wlanNameList_r16__cond ::
 Opt OtherConfig_v1610__sensorNameList_r16__Type OtherConfig_v1610__sensorNameList_r16__cond ::
 Opt OtherConfig_v1610__obtainCommonLocation_r16__Type OtherConfig_v1610__obtainCommonLocation_r16__cond ::
 Opt OtherConfig_v1610__sl_AssistanceConfigNR_r16__Type OtherConfig_v1610__sl_AssistanceConfigNR_r16__cond ::
 nil).
Definition OtherConfig_v1610__cond z := 
  opt_cond OtherConfig_v1610__idc_AssistanceConfig_r16__cond (OtherConfig_v1610__idc_AssistanceConfig_r16 z) /\
  opt_cond OtherConfig_v1610__drx_PreferenceConfig_r16__cond (OtherConfig_v1610__drx_PreferenceConfig_r16 z) /\
  opt_cond OtherConfig_v1610__maxBW_PreferenceConfig_r16__cond (OtherConfig_v1610__maxBW_PreferenceConfig_r16 z) /\
  opt_cond OtherConfig_v1610__maxCC_PreferenceConfig_r16__cond (OtherConfig_v1610__maxCC_PreferenceConfig_r16 z) /\
  opt_cond OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__cond (OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16 z) /\
  opt_cond OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__cond (OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16 z) /\
  opt_cond OtherConfig_v1610__releasePreferenceConfig_r16__cond (OtherConfig_v1610__releasePreferenceConfig_r16 z) /\
  opt_cond OtherConfig_v1610__referenceTimePreferenceReporting_r16__cond (OtherConfig_v1610__referenceTimePreferenceReporting_r16 z) /\
  opt_cond OtherConfig_v1610__btNameList_r16__cond (OtherConfig_v1610__btNameList_r16 z) /\
  opt_cond OtherConfig_v1610__wlanNameList_r16__cond (OtherConfig_v1610__wlanNameList_r16 z) /\
  opt_cond OtherConfig_v1610__sensorNameList_r16__cond (OtherConfig_v1610__sensorNameList_r16 z) /\
  opt_cond OtherConfig_v1610__obtainCommonLocation_r16__cond (OtherConfig_v1610__obtainCommonLocation_r16 z) /\
  opt_cond OtherConfig_v1610__sl_AssistanceConfigNR_r16__cond (OtherConfig_v1610__sl_AssistanceConfigNR_r16 z) /\
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
Opaque OtherConfig_v1610__idc_AssistanceConfig_r16__cond OtherConfig_v1610__idc_AssistanceConfig_r16__Format.

Opaque OtherConfig_v1610__drx_PreferenceConfig_r16__cond OtherConfig_v1610__drx_PreferenceConfig_r16__Format.

Opaque OtherConfig_v1610__maxBW_PreferenceConfig_r16__cond OtherConfig_v1610__maxBW_PreferenceConfig_r16__Format.

Opaque OtherConfig_v1610__maxCC_PreferenceConfig_r16__cond OtherConfig_v1610__maxCC_PreferenceConfig_r16__Format.

Opaque OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__cond OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__Format.

Opaque OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__cond OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__Format.

Opaque OtherConfig_v1610__releasePreferenceConfig_r16__cond OtherConfig_v1610__releasePreferenceConfig_r16__Format.

Definition OtherConfig_v1610__referenceTimePreferenceReporting_r16__Format : T_Format OtherConfig_v1610__referenceTimePreferenceReporting_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format OtherConfig_v1610__referenceTimePreferenceReporting_r16__nat__Format OtherConfig_v1610__referenceTimePreferenceReporting_r16__F1 OtherConfig_v1610__referenceTimePreferenceReporting_r16__F2 OtherConfig_v1610__referenceTimePreferenceReporting_r16__F1F2 OtherConfig_v1610__referenceTimePreferenceReporting_r16__F2F1.

Opaque OtherConfig_v1610__referenceTimePreferenceReporting_r16__cond OtherConfig_v1610__referenceTimePreferenceReporting_r16__Format.

Opaque OtherConfig_v1610__btNameList_r16__cond OtherConfig_v1610__btNameList_r16__Format.

Opaque OtherConfig_v1610__wlanNameList_r16__cond OtherConfig_v1610__wlanNameList_r16__Format.

Opaque OtherConfig_v1610__sensorNameList_r16__cond OtherConfig_v1610__sensorNameList_r16__Format.

Definition OtherConfig_v1610__obtainCommonLocation_r16__Format : T_Format OtherConfig_v1610__obtainCommonLocation_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format OtherConfig_v1610__obtainCommonLocation_r16__nat__Format OtherConfig_v1610__obtainCommonLocation_r16__F1 OtherConfig_v1610__obtainCommonLocation_r16__F2 OtherConfig_v1610__obtainCommonLocation_r16__F1F2 OtherConfig_v1610__obtainCommonLocation_r16__F2F1.

Opaque OtherConfig_v1610__obtainCommonLocation_r16__cond OtherConfig_v1610__obtainCommonLocation_r16__Format.

Definition OtherConfig_v1610__sl_AssistanceConfigNR_r16__Format : T_Format OtherConfig_v1610__sl_AssistanceConfigNR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format OtherConfig_v1610__sl_AssistanceConfigNR_r16__nat__Format OtherConfig_v1610__sl_AssistanceConfigNR_r16__F1 OtherConfig_v1610__sl_AssistanceConfigNR_r16__F2 OtherConfig_v1610__sl_AssistanceConfigNR_r16__F1F2 OtherConfig_v1610__sl_AssistanceConfigNR_r16__F2F1.

Opaque OtherConfig_v1610__sl_AssistanceConfigNR_r16__cond OtherConfig_v1610__sl_AssistanceConfigNR_r16__Format.


Definition OtherConfig_v1610__Format_Type := Eval cbn in seq_format_prod OtherConfig_v1610__list.
Definition OtherConfig_v1610__Format_list : OtherConfig_v1610__Format_Type :=
  (OtherConfig_v1610__idc_AssistanceConfig_r16__Format, (OtherConfig_v1610__drx_PreferenceConfig_r16__Format, (OtherConfig_v1610__maxBW_PreferenceConfig_r16__Format, (OtherConfig_v1610__maxCC_PreferenceConfig_r16__Format, (OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16__Format, (OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16__Format, (OtherConfig_v1610__releasePreferenceConfig_r16__Format, (OtherConfig_v1610__referenceTimePreferenceReporting_r16__Format, (OtherConfig_v1610__btNameList_r16__Format, (OtherConfig_v1610__wlanNameList_r16__Format, (OtherConfig_v1610__sensorNameList_r16__Format, (OtherConfig_v1610__obtainCommonLocation_r16__Format, (OtherConfig_v1610__sl_AssistanceConfigNR_r16__Format, unit_format))))))))))))).
Definition OtherConfig_v1610__list__Format := (*Eval compute in *) seq_format OtherConfig_v1610__list OtherConfig_v1610__Format_list.
Definition OtherConfig_v1610__F1 z :=
  (OtherConfig_v1610__idc_AssistanceConfig_r16 z, (OtherConfig_v1610__drx_PreferenceConfig_r16 z, (OtherConfig_v1610__maxBW_PreferenceConfig_r16 z, (OtherConfig_v1610__maxCC_PreferenceConfig_r16 z, (OtherConfig_v1610__maxMIMO_LayerPreferenceConfig_r16 z, (OtherConfig_v1610__minSchedulingOffsetPreferenceConfig_r16 z, (OtherConfig_v1610__releasePreferenceConfig_r16 z, (OtherConfig_v1610__referenceTimePreferenceReporting_r16 z, (OtherConfig_v1610__btNameList_r16 z, (OtherConfig_v1610__wlanNameList_r16 z, (OtherConfig_v1610__sensorNameList_r16 z, (OtherConfig_v1610__obtainCommonLocation_r16 z, (OtherConfig_v1610__sl_AssistanceConfigNR_r16 z, tt))))))))))))).
Definition OtherConfig_v1610__F2 (y : seq_type OtherConfig_v1610__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, _)))))))))))))=>
    make__OtherConfig_v1610__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12
  end.
Lemma OtherConfig_v1610__F1F2_cond (z : OtherConfig_v1610__Type)
  : OtherConfig_v1610__cond z ->
  (seq_cond OtherConfig_v1610__list (OtherConfig_v1610__F1 z)).
intro H. unfold OtherConfig_v1610__cond in H. simpl. auto. Qed.
Lemma OtherConfig_v1610__F1F2_cond2 (z : OtherConfig_v1610__Type)
 : OtherConfig_v1610__F2 (OtherConfig_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OtherConfig_v1610__F2F1_cond (y : seq_type OtherConfig_v1610__list)
  : seq_cond OtherConfig_v1610__list y ->
 (OtherConfig_v1610__cond (OtherConfig_v1610__F2 y)) /\  OtherConfig_v1610__F1 (OtherConfig_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OtherConfig_v1610__cond. simpl in *. auto.
 - simpl. unfold OtherConfig_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OtherConfig_v1610__Format : T_Format OtherConfig_v1610__Type OtherConfig_v1610__cond :=
        proj2_format  OtherConfig_v1610__cond OtherConfig_v1610__list__Format
    OtherConfig_v1610__F1 OtherConfig_v1610__F2 OtherConfig_v1610__F1F2_cond  OtherConfig_v1610__F1F2_cond2 OtherConfig_v1610__F2F1_cond.
Opaque OtherConfig_v1610__cond OtherConfig_v1610__Format.

