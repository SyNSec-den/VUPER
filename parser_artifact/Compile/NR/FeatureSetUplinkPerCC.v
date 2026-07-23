Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SupportedBandwidth.

Opaque SupportedBandwidth__cond SupportedBandwidth__Format.

Inductive FeatureSetUplinkPerCC__channelBW_90mhz__Type : Set :=
 | FeatureSetUplinkPerCC__channelBW_90mhz__supported
.
Definition FeatureSetUplinkPerCC__channelBW_90mhz__cond := (fun (_ : FeatureSetUplinkPerCC__channelBW_90mhz__Type) => True).
Lemma FeatureSetUplinkPerCC__channelBW_90mhz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetUplinkPerCC__channelBW_90mhz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetUplinkPerCC__channelBW_90mhz__nat__helper.

Definition FeatureSetUplinkPerCC__channelBW_90mhz__F1 t :=
  match t with
  | FeatureSetUplinkPerCC__channelBW_90mhz__supported => 0
  end.
Definition FeatureSetUplinkPerCC__channelBW_90mhz__F2 n :=
  match n with
  | 0 => FeatureSetUplinkPerCC__channelBW_90mhz__supported
  | _ => FeatureSetUplinkPerCC__channelBW_90mhz__supported
  end.
Lemma FeatureSetUplinkPerCC__channelBW_90mhz__F1F2 : forall x : FeatureSetUplinkPerCC__channelBW_90mhz__Type, (FeatureSetUplinkPerCC__channelBW_90mhz__F1 x <= 0) /\ FeatureSetUplinkPerCC__channelBW_90mhz__F2 (FeatureSetUplinkPerCC__channelBW_90mhz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetUplinkPerCC__channelBW_90mhz__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetUplinkPerCC__channelBW_90mhz__F1 (FeatureSetUplinkPerCC__channelBW_90mhz__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MIMO_LayersUL.

Opaque MIMO_LayersUL__cond MIMO_LayersUL__Format.

Lemma FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__Type := Z.
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__cond := (fun z => (1 <= z <= 2)%Z).
Record FeatureSetUplinkPerCC__mimo_CB_PUSCH__Type : Set :=
  make__FeatureSetUplinkPerCC__mimo_CB_PUSCH__Type {
    FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberMIMO_LayersCB_PUSCH : option MIMO_LayersUL__Type ;
    FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet : Z ;
}.
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__list := (
 Opt MIMO_LayersUL__Type MIMO_LayersUL__cond ::
 Nor Z FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__cond ::
 nil).
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond z := 
  opt_cond MIMO_LayersUL__cond (FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberMIMO_LayersCB_PUSCH z) /\
  FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__cond (FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet z) /\
  True.

Require Import NR.MIMO_LayersUL.

Opaque MIMO_LayersUL__cond MIMO_LayersUL__Format.

Require Import NR.ModulationOrder.

Opaque ModulationOrder__cond ModulationOrder__Format.

Record FeatureSetUplinkPerCC__Type : Set :=
  make__FeatureSetUplinkPerCC__Type {
    FeatureSetUplinkPerCC__supportedSubcarrierSpacingUL : SubcarrierSpacing__Type ;
    FeatureSetUplinkPerCC__supportedBandwidthUL : SupportedBandwidth__Type ;
    FeatureSetUplinkPerCC__channelBW_90mhz : option FeatureSetUplinkPerCC__channelBW_90mhz__Type ;
    FeatureSetUplinkPerCC__mimo_CB_PUSCH : option FeatureSetUplinkPerCC__mimo_CB_PUSCH__Type ;
    FeatureSetUplinkPerCC__maxNumberMIMO_LayersNonCB_PUSCH : option MIMO_LayersUL__Type ;
    FeatureSetUplinkPerCC__supportedModulationOrderUL : option ModulationOrder__Type ;
}.
Definition FeatureSetUplinkPerCC__list := (
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor SupportedBandwidth__Type SupportedBandwidth__cond ::
 Opt FeatureSetUplinkPerCC__channelBW_90mhz__Type FeatureSetUplinkPerCC__channelBW_90mhz__cond ::
 Opt FeatureSetUplinkPerCC__mimo_CB_PUSCH__Type FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond ::
 Opt MIMO_LayersUL__Type MIMO_LayersUL__cond ::
 Opt ModulationOrder__Type ModulationOrder__cond ::
 nil).
Definition FeatureSetUplinkPerCC__cond z := 
  SubcarrierSpacing__cond (FeatureSetUplinkPerCC__supportedSubcarrierSpacingUL z) /\
  SupportedBandwidth__cond (FeatureSetUplinkPerCC__supportedBandwidthUL z) /\
  opt_cond FeatureSetUplinkPerCC__channelBW_90mhz__cond (FeatureSetUplinkPerCC__channelBW_90mhz z) /\
  opt_cond FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond (FeatureSetUplinkPerCC__mimo_CB_PUSCH z) /\
  opt_cond MIMO_LayersUL__cond (FeatureSetUplinkPerCC__maxNumberMIMO_LayersNonCB_PUSCH z) /\
  opt_cond ModulationOrder__cond (FeatureSetUplinkPerCC__supportedModulationOrderUL z) /\
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
Definition FeatureSetUplinkPerCC__channelBW_90mhz__Format : T_Format FeatureSetUplinkPerCC__channelBW_90mhz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetUplinkPerCC__channelBW_90mhz__nat__Format FeatureSetUplinkPerCC__channelBW_90mhz__F1 FeatureSetUplinkPerCC__channelBW_90mhz__F2 FeatureSetUplinkPerCC__channelBW_90mhz__F1F2 FeatureSetUplinkPerCC__channelBW_90mhz__F2F1.

Opaque FeatureSetUplinkPerCC__channelBW_90mhz__cond FeatureSetUplinkPerCC__channelBW_90mhz__Format.

Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__Format : T_Format Z FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__cond :=
 ranged_int_format (1) (2) FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__helper1 FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__helper2.

Opaque FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__cond FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__Format.


Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__Format_Type := Eval cbn in seq_format_prod FeatureSetUplinkPerCC__mimo_CB_PUSCH__list.
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__Format_list : FeatureSetUplinkPerCC__mimo_CB_PUSCH__Format_Type :=
  (MIMO_LayersUL__Format, (FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet__Format, unit_format)).
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__list__Format := (*Eval compute in *) seq_format FeatureSetUplinkPerCC__mimo_CB_PUSCH__list FeatureSetUplinkPerCC__mimo_CB_PUSCH__Format_list.
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1 z :=
  (FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberMIMO_LayersCB_PUSCH z, (FeatureSetUplinkPerCC__mimo_CB_PUSCH__maxNumberSRS_ResourcePerSet z, tt)).
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__F2 (y : seq_type FeatureSetUplinkPerCC__mimo_CB_PUSCH__list) :=
  match y with
  | (i0, (i1, _))=>
    make__FeatureSetUplinkPerCC__mimo_CB_PUSCH__Type i0 i1
  end.
Lemma FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1F2_cond (z : FeatureSetUplinkPerCC__mimo_CB_PUSCH__Type)
  : FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond z ->
  (seq_cond FeatureSetUplinkPerCC__mimo_CB_PUSCH__list (FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1 z)).
intro H. unfold FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1F2_cond2 (z : FeatureSetUplinkPerCC__mimo_CB_PUSCH__Type)
 : FeatureSetUplinkPerCC__mimo_CB_PUSCH__F2 (FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC__mimo_CB_PUSCH__F2F1_cond (y : seq_type FeatureSetUplinkPerCC__mimo_CB_PUSCH__list)
  : seq_cond FeatureSetUplinkPerCC__mimo_CB_PUSCH__list y ->
 (FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond (FeatureSetUplinkPerCC__mimo_CB_PUSCH__F2 y)) /\  FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1 (FeatureSetUplinkPerCC__mimo_CB_PUSCH__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplinkPerCC__mimo_CB_PUSCH__Format : T_Format FeatureSetUplinkPerCC__mimo_CB_PUSCH__Type FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond :=
        proj2_format  FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond FeatureSetUplinkPerCC__mimo_CB_PUSCH__list__Format
    FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1 FeatureSetUplinkPerCC__mimo_CB_PUSCH__F2 FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1F2_cond  FeatureSetUplinkPerCC__mimo_CB_PUSCH__F1F2_cond2 FeatureSetUplinkPerCC__mimo_CB_PUSCH__F2F1_cond.
Opaque FeatureSetUplinkPerCC__mimo_CB_PUSCH__cond FeatureSetUplinkPerCC__mimo_CB_PUSCH__Format.


Definition FeatureSetUplinkPerCC__Format_Type := Eval cbn in seq_format_prod FeatureSetUplinkPerCC__list.
Definition FeatureSetUplinkPerCC__Format_list : FeatureSetUplinkPerCC__Format_Type :=
  (SubcarrierSpacing__Format, (SupportedBandwidth__Format, (FeatureSetUplinkPerCC__channelBW_90mhz__Format, (FeatureSetUplinkPerCC__mimo_CB_PUSCH__Format, (MIMO_LayersUL__Format, (ModulationOrder__Format, unit_format)))))).
Definition FeatureSetUplinkPerCC__list__Format := (*Eval compute in *) seq_format FeatureSetUplinkPerCC__list FeatureSetUplinkPerCC__Format_list.
Definition FeatureSetUplinkPerCC__F1 z :=
  (FeatureSetUplinkPerCC__supportedSubcarrierSpacingUL z, (FeatureSetUplinkPerCC__supportedBandwidthUL z, (FeatureSetUplinkPerCC__channelBW_90mhz z, (FeatureSetUplinkPerCC__mimo_CB_PUSCH z, (FeatureSetUplinkPerCC__maxNumberMIMO_LayersNonCB_PUSCH z, (FeatureSetUplinkPerCC__supportedModulationOrderUL z, tt)))))).
Definition FeatureSetUplinkPerCC__F2 (y : seq_type FeatureSetUplinkPerCC__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__FeatureSetUplinkPerCC__Type i0 i1 i2 i3 i4 i5
  end.
Lemma FeatureSetUplinkPerCC__F1F2_cond (z : FeatureSetUplinkPerCC__Type)
  : FeatureSetUplinkPerCC__cond z ->
  (seq_cond FeatureSetUplinkPerCC__list (FeatureSetUplinkPerCC__F1 z)).
intro H. unfold FeatureSetUplinkPerCC__cond in H. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC__F1F2_cond2 (z : FeatureSetUplinkPerCC__Type)
 : FeatureSetUplinkPerCC__F2 (FeatureSetUplinkPerCC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetUplinkPerCC__F2F1_cond (y : seq_type FeatureSetUplinkPerCC__list)
  : seq_cond FeatureSetUplinkPerCC__list y ->
 (FeatureSetUplinkPerCC__cond (FeatureSetUplinkPerCC__F2 y)) /\  FeatureSetUplinkPerCC__F1 (FeatureSetUplinkPerCC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetUplinkPerCC__cond. simpl in *. auto.
 - simpl. unfold FeatureSetUplinkPerCC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetUplinkPerCC__Format : T_Format FeatureSetUplinkPerCC__Type FeatureSetUplinkPerCC__cond :=
        proj2_format  FeatureSetUplinkPerCC__cond FeatureSetUplinkPerCC__list__Format
    FeatureSetUplinkPerCC__F1 FeatureSetUplinkPerCC__F2 FeatureSetUplinkPerCC__F1F2_cond  FeatureSetUplinkPerCC__F1F2_cond2 FeatureSetUplinkPerCC__F2F1_cond.
Opaque FeatureSetUplinkPerCC__cond FeatureSetUplinkPerCC__Format.

