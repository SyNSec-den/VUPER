Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.CSI_RS_CellMobility.

Opaque CSI_RS_CellMobility__cond CSI_RS_CellMobility__Format.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Record MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Type : Set :=
  make__MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Type {
    MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__csi_RS_SubcarrierSpacing_r16 : SubcarrierSpacing__Type ;
    MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__csi_RS_CellMobility_r16 : CSI_RS_CellMobility__Type ;
    MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__refSSBFreq_r16 : ARFCN_ValueNR__Type ;
}.
Definition MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list := (
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor CSI_RS_CellMobility__Type CSI_RS_CellMobility__cond ::
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 nil).
Definition MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond z := 
  SubcarrierSpacing__cond (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__csi_RS_SubcarrierSpacing_r16 z) /\
  CSI_RS_CellMobility__cond (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__csi_RS_CellMobility_r16 z) /\
  ARFCN_ValueNR__cond (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__refSSBFreq_r16 z) /\
  True.

Record MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type : Set := make__MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type {}.
Definition MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__cond (z : MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type) := True.
Record MeasurementTimingConfiguration_v1610_IEs__Type : Set :=
  make__MeasurementTimingConfiguration_v1610_IEs__Type {
    MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16 : MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Type ;
    MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension : option MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type ;
}.
Definition MeasurementTimingConfiguration_v1610_IEs__list := (
 Nor MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Type MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond ::
 Opt MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__cond ::
 nil).
Definition MeasurementTimingConfiguration_v1610_IEs__cond z := 
  MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16 z) /\
  opt_cond MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__cond (MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension z) /\
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

Definition MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Format_Type := Eval cbn in seq_format_prod MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list.
Definition MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Format_list : MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Format_Type :=
  (SubcarrierSpacing__Format, (CSI_RS_CellMobility__Format, (ARFCN_ValueNR__Format, unit_format))).
Definition MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list__Format := (*Eval compute in *) seq_format MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Format_list.
Definition MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1 z :=
  (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__csi_RS_SubcarrierSpacing_r16 z, (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__csi_RS_CellMobility_r16 z, (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__refSSBFreq_r16 z, tt))).
Definition MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F2 (y : seq_type MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Type i0 i1 i2
  end.
Lemma MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1F2_cond (z : MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Type)
  : MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond z ->
  (seq_cond MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1 z)).
intro H. unfold MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond in H. simpl. auto. Qed.
Lemma MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1F2_cond2 (z : MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Type)
 : MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F2 (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F2F1_cond (y : seq_type MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list)
  : seq_cond MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list y ->
 (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F2 y)) /\  MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1 (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond. simpl in *. auto.
 - simpl. unfold MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Format : T_Format MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Type MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond :=
        proj2_format  MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__list__Format
    MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1 MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F2 MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1F2_cond  MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F1F2_cond2 MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__F2F1_cond.
Opaque MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__cond MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Format.

Definition MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__helper : forall a : MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type, True -> True /\ make__MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Format : T_Format MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Type)
    MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__cond MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Format.


Definition MeasurementTimingConfiguration_v1610_IEs__Format_Type := Eval cbn in seq_format_prod MeasurementTimingConfiguration_v1610_IEs__list.
Definition MeasurementTimingConfiguration_v1610_IEs__Format_list : MeasurementTimingConfiguration_v1610_IEs__Format_Type :=
  (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16__Format, (MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension__Format, unit_format)).
Definition MeasurementTimingConfiguration_v1610_IEs__list__Format := (*Eval compute in *) seq_format MeasurementTimingConfiguration_v1610_IEs__list MeasurementTimingConfiguration_v1610_IEs__Format_list.
Definition MeasurementTimingConfiguration_v1610_IEs__F1 z :=
  (MeasurementTimingConfiguration_v1610_IEs__csi_RS_Config_r16 z, (MeasurementTimingConfiguration_v1610_IEs__nonCriticalExtension z, tt)).
Definition MeasurementTimingConfiguration_v1610_IEs__F2 (y : seq_type MeasurementTimingConfiguration_v1610_IEs__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasurementTimingConfiguration_v1610_IEs__Type i0 i1
  end.
Lemma MeasurementTimingConfiguration_v1610_IEs__F1F2_cond (z : MeasurementTimingConfiguration_v1610_IEs__Type)
  : MeasurementTimingConfiguration_v1610_IEs__cond z ->
  (seq_cond MeasurementTimingConfiguration_v1610_IEs__list (MeasurementTimingConfiguration_v1610_IEs__F1 z)).
intro H. unfold MeasurementTimingConfiguration_v1610_IEs__cond in H. simpl. auto. Qed.
Lemma MeasurementTimingConfiguration_v1610_IEs__F1F2_cond2 (z : MeasurementTimingConfiguration_v1610_IEs__Type)
 : MeasurementTimingConfiguration_v1610_IEs__F2 (MeasurementTimingConfiguration_v1610_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasurementTimingConfiguration_v1610_IEs__F2F1_cond (y : seq_type MeasurementTimingConfiguration_v1610_IEs__list)
  : seq_cond MeasurementTimingConfiguration_v1610_IEs__list y ->
 (MeasurementTimingConfiguration_v1610_IEs__cond (MeasurementTimingConfiguration_v1610_IEs__F2 y)) /\  MeasurementTimingConfiguration_v1610_IEs__F1 (MeasurementTimingConfiguration_v1610_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasurementTimingConfiguration_v1610_IEs__cond. simpl in *. auto.
 - simpl. unfold MeasurementTimingConfiguration_v1610_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasurementTimingConfiguration_v1610_IEs__Format : T_Format MeasurementTimingConfiguration_v1610_IEs__Type MeasurementTimingConfiguration_v1610_IEs__cond :=
        proj2_format  MeasurementTimingConfiguration_v1610_IEs__cond MeasurementTimingConfiguration_v1610_IEs__list__Format
    MeasurementTimingConfiguration_v1610_IEs__F1 MeasurementTimingConfiguration_v1610_IEs__F2 MeasurementTimingConfiguration_v1610_IEs__F1F2_cond  MeasurementTimingConfiguration_v1610_IEs__F1F2_cond2 MeasurementTimingConfiguration_v1610_IEs__F2F1_cond.
Opaque MeasurementTimingConfiguration_v1610_IEs__cond MeasurementTimingConfiguration_v1610_IEs__Format.

