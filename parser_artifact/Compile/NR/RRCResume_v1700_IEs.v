Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SetupRelease.
Require Import NR.SL_ConfigDedicatedNR_r16.
Definition RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__Type := SetupRelease__Type SL_ConfigDedicatedNR_r16__Type.
Definition RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__cond := SetupRelease__cond _ SL_ConfigDedicatedNR_r16__cond.
Definition RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__Format : T_Format RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__Type RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__cond := SetupRelease__Format _ _ SL_ConfigDedicatedNR_r16__Format.
Opaque RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__cond RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.SL_L2RemoteUE_Config_r17.
Definition RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__Type := SetupRelease__Type SL_L2RemoteUE_Config_r17__Type.
Definition RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__cond := SetupRelease__cond _ SL_L2RemoteUE_Config_r17__cond.
Definition RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__Format : T_Format RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__Type RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__cond := SetupRelease__Format _ _ SL_L2RemoteUE_Config_r17__Format.
Opaque RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__cond RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.NeedForGapNCSG_ConfigNR_r17.
Definition RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__Type := SetupRelease__Type NeedForGapNCSG_ConfigNR_r17__Type.
Definition RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__cond := SetupRelease__cond _ NeedForGapNCSG_ConfigNR_r17__cond.
Definition RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__Format : T_Format RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__Type RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__cond := SetupRelease__Format _ _ NeedForGapNCSG_ConfigNR_r17__Format.
Opaque RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__cond RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.NeedForGapNCSG_ConfigEUTRA_r17.
Definition RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__Type := SetupRelease__Type NeedForGapNCSG_ConfigEUTRA_r17__Type.
Definition RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__cond := SetupRelease__cond _ NeedForGapNCSG_ConfigEUTRA_r17__cond.
Definition RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__Format : T_Format RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__Type RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__cond := SetupRelease__Format _ _ NeedForGapNCSG_ConfigEUTRA_r17__Format.
Opaque RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__cond RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__Format.

Inductive RRCResume_v1700_IEs__scg_State_r17__Type : Set :=
 | RRCResume_v1700_IEs__scg_State_r17__deactivated
.
Definition RRCResume_v1700_IEs__scg_State_r17__cond := (fun (_ : RRCResume_v1700_IEs__scg_State_r17__Type) => True).
Lemma RRCResume_v1700_IEs__scg_State_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCResume_v1700_IEs__scg_State_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCResume_v1700_IEs__scg_State_r17__nat__helper.

Definition RRCResume_v1700_IEs__scg_State_r17__F1 t :=
  match t with
  | RRCResume_v1700_IEs__scg_State_r17__deactivated => 0
  end.
Definition RRCResume_v1700_IEs__scg_State_r17__F2 n :=
  match n with
  | 0 => RRCResume_v1700_IEs__scg_State_r17__deactivated
  | _ => RRCResume_v1700_IEs__scg_State_r17__deactivated
  end.
Lemma RRCResume_v1700_IEs__scg_State_r17__F1F2 : forall x : RRCResume_v1700_IEs__scg_State_r17__Type, (RRCResume_v1700_IEs__scg_State_r17__F1 x <= 0) /\ RRCResume_v1700_IEs__scg_State_r17__F2 (RRCResume_v1700_IEs__scg_State_r17__F1 x) = x. imp_solve. Qed.
Lemma RRCResume_v1700_IEs__scg_State_r17__F2F1 : forall (y : nat) (H : y <= 0), RRCResume_v1700_IEs__scg_State_r17__F1 (RRCResume_v1700_IEs__scg_State_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.AppLayerMeasConfig_r17.

Opaque AppLayerMeasConfig_r17__cond AppLayerMeasConfig_r17__Format.

Record RRCResume_v1700_IEs__nonCriticalExtension__Type : Set := make__RRCResume_v1700_IEs__nonCriticalExtension__Type {}.
Definition RRCResume_v1700_IEs__nonCriticalExtension__cond (z : RRCResume_v1700_IEs__nonCriticalExtension__Type) := True.
Record RRCResume_v1700_IEs__Type : Set :=
  make__RRCResume_v1700_IEs__Type {
    RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17 : option RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__Type ;
    RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17 : option RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__Type ;
    RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17 : option RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__Type ;
    RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17 : option RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__Type ;
    RRCResume_v1700_IEs__scg_State_r17 : option RRCResume_v1700_IEs__scg_State_r17__Type ;
    RRCResume_v1700_IEs__appLayerMeasConfig_r17 : option AppLayerMeasConfig_r17__Type ;
    RRCResume_v1700_IEs__nonCriticalExtension : option RRCResume_v1700_IEs__nonCriticalExtension__Type ;
}.
Definition RRCResume_v1700_IEs__list := (
 Opt RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__Type RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__cond ::
 Opt RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__Type RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__cond ::
 Opt RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__Type RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__cond ::
 Opt RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__Type RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__cond ::
 Opt RRCResume_v1700_IEs__scg_State_r17__Type RRCResume_v1700_IEs__scg_State_r17__cond ::
 Opt AppLayerMeasConfig_r17__Type AppLayerMeasConfig_r17__cond ::
 Opt RRCResume_v1700_IEs__nonCriticalExtension__Type RRCResume_v1700_IEs__nonCriticalExtension__cond ::
 nil).
Definition RRCResume_v1700_IEs__cond z := 
  opt_cond RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__cond (RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17 z) /\
  opt_cond RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__cond (RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17 z) /\
  opt_cond RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__cond (RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17 z) /\
  opt_cond RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__cond (RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17 z) /\
  opt_cond RRCResume_v1700_IEs__scg_State_r17__cond (RRCResume_v1700_IEs__scg_State_r17 z) /\
  opt_cond AppLayerMeasConfig_r17__cond (RRCResume_v1700_IEs__appLayerMeasConfig_r17 z) /\
  opt_cond RRCResume_v1700_IEs__nonCriticalExtension__cond (RRCResume_v1700_IEs__nonCriticalExtension z) /\
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
Opaque RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__cond RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__Format.

Opaque RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__cond RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__Format.

Opaque RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__cond RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__Format.

Opaque RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__cond RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__Format.

Definition RRCResume_v1700_IEs__scg_State_r17__Format : T_Format RRCResume_v1700_IEs__scg_State_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCResume_v1700_IEs__scg_State_r17__nat__Format RRCResume_v1700_IEs__scg_State_r17__F1 RRCResume_v1700_IEs__scg_State_r17__F2 RRCResume_v1700_IEs__scg_State_r17__F1F2 RRCResume_v1700_IEs__scg_State_r17__F2F1.

Opaque RRCResume_v1700_IEs__scg_State_r17__cond RRCResume_v1700_IEs__scg_State_r17__Format.

Definition RRCResume_v1700_IEs__nonCriticalExtension__helper : forall a : RRCResume_v1700_IEs__nonCriticalExtension__Type, True -> True /\ make__RRCResume_v1700_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCResume_v1700_IEs__nonCriticalExtension__Format : T_Format RRCResume_v1700_IEs__nonCriticalExtension__Type RRCResume_v1700_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCResume_v1700_IEs__nonCriticalExtension__Type)
    RRCResume_v1700_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque RRCResume_v1700_IEs__nonCriticalExtension__cond RRCResume_v1700_IEs__nonCriticalExtension__Format.


Definition RRCResume_v1700_IEs__Format_Type := Eval cbn in seq_format_prod RRCResume_v1700_IEs__list.
Definition RRCResume_v1700_IEs__Format_list : RRCResume_v1700_IEs__Format_Type :=
  (RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17__Format, (RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17__Format, (RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17__Format, (RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17__Format, (RRCResume_v1700_IEs__scg_State_r17__Format, (AppLayerMeasConfig_r17__Format, (RRCResume_v1700_IEs__nonCriticalExtension__Format, unit_format))))))).
Definition RRCResume_v1700_IEs__list__Format := (*Eval compute in *) seq_format RRCResume_v1700_IEs__list RRCResume_v1700_IEs__Format_list.
Definition RRCResume_v1700_IEs__F1 z :=
  (RRCResume_v1700_IEs__sl_ConfigDedicatedNR_r17 z, (RRCResume_v1700_IEs__sl_L2RemoteUE_Config_r17 z, (RRCResume_v1700_IEs__needForGapNCSG_ConfigNR_r17 z, (RRCResume_v1700_IEs__needForGapNCSG_ConfigEUTRA_r17 z, (RRCResume_v1700_IEs__scg_State_r17 z, (RRCResume_v1700_IEs__appLayerMeasConfig_r17 z, (RRCResume_v1700_IEs__nonCriticalExtension z, tt))))))).
Definition RRCResume_v1700_IEs__F2 (y : seq_type RRCResume_v1700_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__RRCResume_v1700_IEs__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma RRCResume_v1700_IEs__F1F2_cond (z : RRCResume_v1700_IEs__Type)
  : RRCResume_v1700_IEs__cond z ->
  (seq_cond RRCResume_v1700_IEs__list (RRCResume_v1700_IEs__F1 z)).
intro H. unfold RRCResume_v1700_IEs__cond in H. simpl. auto. Qed.
Lemma RRCResume_v1700_IEs__F1F2_cond2 (z : RRCResume_v1700_IEs__Type)
 : RRCResume_v1700_IEs__F2 (RRCResume_v1700_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCResume_v1700_IEs__F2F1_cond (y : seq_type RRCResume_v1700_IEs__list)
  : seq_cond RRCResume_v1700_IEs__list y ->
 (RRCResume_v1700_IEs__cond (RRCResume_v1700_IEs__F2 y)) /\  RRCResume_v1700_IEs__F1 (RRCResume_v1700_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCResume_v1700_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCResume_v1700_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCResume_v1700_IEs__Format : T_Format RRCResume_v1700_IEs__Type RRCResume_v1700_IEs__cond :=
        proj2_format  RRCResume_v1700_IEs__cond RRCResume_v1700_IEs__list__Format
    RRCResume_v1700_IEs__F1 RRCResume_v1700_IEs__F2 RRCResume_v1700_IEs__F1F2_cond  RRCResume_v1700_IEs__F1F2_cond2 RRCResume_v1700_IEs__F2F1_cond.
Opaque RRCResume_v1700_IEs__cond RRCResume_v1700_IEs__Format.

