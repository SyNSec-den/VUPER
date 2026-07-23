Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SupportedBandwidth.

Opaque SupportedBandwidth__cond SupportedBandwidth__Format.

Inductive FeatureSetDownlinkPerCC__channelBW_90mhz__Type : Set :=
 | FeatureSetDownlinkPerCC__channelBW_90mhz__supported
.
Definition FeatureSetDownlinkPerCC__channelBW_90mhz__cond := (fun (_ : FeatureSetDownlinkPerCC__channelBW_90mhz__Type) => True).
Lemma FeatureSetDownlinkPerCC__channelBW_90mhz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition FeatureSetDownlinkPerCC__channelBW_90mhz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 FeatureSetDownlinkPerCC__channelBW_90mhz__nat__helper.

Definition FeatureSetDownlinkPerCC__channelBW_90mhz__F1 t :=
  match t with
  | FeatureSetDownlinkPerCC__channelBW_90mhz__supported => 0
  end.
Definition FeatureSetDownlinkPerCC__channelBW_90mhz__F2 n :=
  match n with
  | 0 => FeatureSetDownlinkPerCC__channelBW_90mhz__supported
  | _ => FeatureSetDownlinkPerCC__channelBW_90mhz__supported
  end.
Lemma FeatureSetDownlinkPerCC__channelBW_90mhz__F1F2 : forall x : FeatureSetDownlinkPerCC__channelBW_90mhz__Type, (FeatureSetDownlinkPerCC__channelBW_90mhz__F1 x <= 0) /\ FeatureSetDownlinkPerCC__channelBW_90mhz__F2 (FeatureSetDownlinkPerCC__channelBW_90mhz__F1 x) = x. imp_solve. Qed.
Lemma FeatureSetDownlinkPerCC__channelBW_90mhz__F2F1 : forall (y : nat) (H : y <= 0), FeatureSetDownlinkPerCC__channelBW_90mhz__F1 (FeatureSetDownlinkPerCC__channelBW_90mhz__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MIMO_LayersDL.

Opaque MIMO_LayersDL__cond MIMO_LayersDL__Format.

Require Import NR.ModulationOrder.

Opaque ModulationOrder__cond ModulationOrder__Format.

Record FeatureSetDownlinkPerCC__Type : Set :=
  make__FeatureSetDownlinkPerCC__Type {
    FeatureSetDownlinkPerCC__supportedSubcarrierSpacingDL : SubcarrierSpacing__Type ;
    FeatureSetDownlinkPerCC__supportedBandwidthDL : SupportedBandwidth__Type ;
    FeatureSetDownlinkPerCC__channelBW_90mhz : option FeatureSetDownlinkPerCC__channelBW_90mhz__Type ;
    FeatureSetDownlinkPerCC__maxNumberMIMO_LayersPDSCH : option MIMO_LayersDL__Type ;
    FeatureSetDownlinkPerCC__supportedModulationOrderDL : option ModulationOrder__Type ;
}.
Definition FeatureSetDownlinkPerCC__list := (
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor SupportedBandwidth__Type SupportedBandwidth__cond ::
 Opt FeatureSetDownlinkPerCC__channelBW_90mhz__Type FeatureSetDownlinkPerCC__channelBW_90mhz__cond ::
 Opt MIMO_LayersDL__Type MIMO_LayersDL__cond ::
 Opt ModulationOrder__Type ModulationOrder__cond ::
 nil).
Definition FeatureSetDownlinkPerCC__cond z := 
  SubcarrierSpacing__cond (FeatureSetDownlinkPerCC__supportedSubcarrierSpacingDL z) /\
  SupportedBandwidth__cond (FeatureSetDownlinkPerCC__supportedBandwidthDL z) /\
  opt_cond FeatureSetDownlinkPerCC__channelBW_90mhz__cond (FeatureSetDownlinkPerCC__channelBW_90mhz z) /\
  opt_cond MIMO_LayersDL__cond (FeatureSetDownlinkPerCC__maxNumberMIMO_LayersPDSCH z) /\
  opt_cond ModulationOrder__cond (FeatureSetDownlinkPerCC__supportedModulationOrderDL z) /\
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
Definition FeatureSetDownlinkPerCC__channelBW_90mhz__Format : T_Format FeatureSetDownlinkPerCC__channelBW_90mhz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format FeatureSetDownlinkPerCC__channelBW_90mhz__nat__Format FeatureSetDownlinkPerCC__channelBW_90mhz__F1 FeatureSetDownlinkPerCC__channelBW_90mhz__F2 FeatureSetDownlinkPerCC__channelBW_90mhz__F1F2 FeatureSetDownlinkPerCC__channelBW_90mhz__F2F1.

Opaque FeatureSetDownlinkPerCC__channelBW_90mhz__cond FeatureSetDownlinkPerCC__channelBW_90mhz__Format.


Definition FeatureSetDownlinkPerCC__Format_Type := Eval cbn in seq_format_prod FeatureSetDownlinkPerCC__list.
Definition FeatureSetDownlinkPerCC__Format_list : FeatureSetDownlinkPerCC__Format_Type :=
  (SubcarrierSpacing__Format, (SupportedBandwidth__Format, (FeatureSetDownlinkPerCC__channelBW_90mhz__Format, (MIMO_LayersDL__Format, (ModulationOrder__Format, unit_format))))).
Definition FeatureSetDownlinkPerCC__list__Format := (*Eval compute in *) seq_format FeatureSetDownlinkPerCC__list FeatureSetDownlinkPerCC__Format_list.
Definition FeatureSetDownlinkPerCC__F1 z :=
  (FeatureSetDownlinkPerCC__supportedSubcarrierSpacingDL z, (FeatureSetDownlinkPerCC__supportedBandwidthDL z, (FeatureSetDownlinkPerCC__channelBW_90mhz z, (FeatureSetDownlinkPerCC__maxNumberMIMO_LayersPDSCH z, (FeatureSetDownlinkPerCC__supportedModulationOrderDL z, tt))))).
Definition FeatureSetDownlinkPerCC__F2 (y : seq_type FeatureSetDownlinkPerCC__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__FeatureSetDownlinkPerCC__Type i0 i1 i2 i3 i4
  end.
Lemma FeatureSetDownlinkPerCC__F1F2_cond (z : FeatureSetDownlinkPerCC__Type)
  : FeatureSetDownlinkPerCC__cond z ->
  (seq_cond FeatureSetDownlinkPerCC__list (FeatureSetDownlinkPerCC__F1 z)).
intro H. unfold FeatureSetDownlinkPerCC__cond in H. simpl. auto. Qed.
Lemma FeatureSetDownlinkPerCC__F1F2_cond2 (z : FeatureSetDownlinkPerCC__Type)
 : FeatureSetDownlinkPerCC__F2 (FeatureSetDownlinkPerCC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FeatureSetDownlinkPerCC__F2F1_cond (y : seq_type FeatureSetDownlinkPerCC__list)
  : seq_cond FeatureSetDownlinkPerCC__list y ->
 (FeatureSetDownlinkPerCC__cond (FeatureSetDownlinkPerCC__F2 y)) /\  FeatureSetDownlinkPerCC__F1 (FeatureSetDownlinkPerCC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FeatureSetDownlinkPerCC__cond. simpl in *. auto.
 - simpl. unfold FeatureSetDownlinkPerCC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FeatureSetDownlinkPerCC__Format : T_Format FeatureSetDownlinkPerCC__Type FeatureSetDownlinkPerCC__cond :=
        proj2_format  FeatureSetDownlinkPerCC__cond FeatureSetDownlinkPerCC__list__Format
    FeatureSetDownlinkPerCC__F1 FeatureSetDownlinkPerCC__F2 FeatureSetDownlinkPerCC__F1F2_cond  FeatureSetDownlinkPerCC__F1F2_cond2 FeatureSetDownlinkPerCC__F2F1_cond.
Opaque FeatureSetDownlinkPerCC__cond FeatureSetDownlinkPerCC__Format.

