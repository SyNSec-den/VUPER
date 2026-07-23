Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ReducedAggregatedBandwidth_r17.

Opaque ReducedAggregatedBandwidth_r17__cond ReducedAggregatedBandwidth_r17__Format.

Require Import NR.ReducedAggregatedBandwidth_r17.

Opaque ReducedAggregatedBandwidth_r17__cond ReducedAggregatedBandwidth_r17__Format.

Record OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type : Set :=
  make__OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type {
    OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_DL_r17 : ReducedAggregatedBandwidth_r17__Type ;
    OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_UL_r17 : ReducedAggregatedBandwidth_r17__Type ;
}.
Definition OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list := (
 Nor ReducedAggregatedBandwidth_r17__Type ReducedAggregatedBandwidth_r17__cond ::
 Nor ReducedAggregatedBandwidth_r17__Type ReducedAggregatedBandwidth_r17__cond ::
 nil).
Definition OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond z := 
  ReducedAggregatedBandwidth_r17__cond (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_DL_r17 z) /\
  ReducedAggregatedBandwidth_r17__cond (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_UL_r17 z) /\
  True.

Require Import NR.MIMO_LayersDL.

Opaque MIMO_LayersDL__cond MIMO_LayersDL__Format.

Require Import NR.MIMO_LayersUL.

Opaque MIMO_LayersUL__cond MIMO_LayersUL__Format.

Record OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type : Set :=
  make__OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type {
    OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__reducedMIMO_LayersFR2_2_DL : MIMO_LayersDL__Type ;
    OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__reducedMIMO_LayersFR2_2_UL : MIMO_LayersUL__Type ;
}.
Definition OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list := (
 Nor MIMO_LayersDL__Type MIMO_LayersDL__cond ::
 Nor MIMO_LayersUL__Type MIMO_LayersUL__cond ::
 nil).
Definition OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond z := 
  MIMO_LayersDL__cond (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__reducedMIMO_LayersFR2_2_DL z) /\
  MIMO_LayersUL__cond (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__reducedMIMO_LayersFR2_2_UL z) /\
  True.

Record OverheatingAssistance_r17__Type : Set :=
  make__OverheatingAssistance_r17__Type {
    OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17 : option OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type ;
    OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2 : option OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type ;
}.
Definition OverheatingAssistance_r17__list := (
 Opt OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond ::
 Opt OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond ::
 nil).
Definition OverheatingAssistance_r17__cond z := 
  opt_cond OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17 z) /\
  opt_cond OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2 z) /\
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

Definition OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format_Type := Eval cbn in seq_format_prod OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list.
Definition OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format_list : OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format_Type :=
  (ReducedAggregatedBandwidth_r17__Format, (ReducedAggregatedBandwidth_r17__Format, unit_format)).
Definition OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list__Format := (*Eval compute in *) seq_format OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format_list.
Definition OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1 z :=
  (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_DL_r17 z, (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_UL_r17 z, tt)).
Definition OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F2 (y : seq_type OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type i0 i1
  end.
Lemma OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1F2_cond (z : OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type)
  : OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond z ->
  (seq_cond OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1 z)).
intro H. unfold OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond in H. simpl. auto. Qed.
Lemma OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1F2_cond2 (z : OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type)
 : OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F2 (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F2F1_cond (y : seq_type OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list)
  : seq_cond OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list y ->
 (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F2 y)) /\  OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1 (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond. simpl in *. auto.
 - simpl. unfold OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format : T_Format OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Type OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond :=
        proj2_format  OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__list__Format
    OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1 OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F2 OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1F2_cond  OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F1F2_cond2 OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__F2F1_cond.
Opaque OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__cond OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format.


Definition OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format_Type := Eval cbn in seq_format_prod OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list.
Definition OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format_list : OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format_Type :=
  (MIMO_LayersDL__Format, (MIMO_LayersUL__Format, unit_format)).
Definition OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list__Format := (*Eval compute in *) seq_format OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format_list.
Definition OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1 z :=
  (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__reducedMIMO_LayersFR2_2_DL z, (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__reducedMIMO_LayersFR2_2_UL z, tt)).
Definition OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F2 (y : seq_type OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type i0 i1
  end.
Lemma OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1F2_cond (z : OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type)
  : OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond z ->
  (seq_cond OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1 z)).
intro H. unfold OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond in H. simpl. auto. Qed.
Lemma OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1F2_cond2 (z : OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type)
 : OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F2 (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F2F1_cond (y : seq_type OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list)
  : seq_cond OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list y ->
 (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F2 y)) /\  OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1 (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond. simpl in *. auto.
 - simpl. unfold OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format : T_Format OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Type OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond :=
        proj2_format  OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__list__Format
    OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1 OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F2 OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1F2_cond  OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F1F2_cond2 OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__F2F1_cond.
Opaque OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__cond OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format.


Definition OverheatingAssistance_r17__Format_Type := Eval cbn in seq_format_prod OverheatingAssistance_r17__list.
Definition OverheatingAssistance_r17__Format_list : OverheatingAssistance_r17__Format_Type :=
  (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17__Format, (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2__Format, unit_format)).
Definition OverheatingAssistance_r17__list__Format := (*Eval compute in *) seq_format OverheatingAssistance_r17__list OverheatingAssistance_r17__Format_list.
Definition OverheatingAssistance_r17__F1 z :=
  (OverheatingAssistance_r17__reducedMaxBW_FR2_2_r17 z, (OverheatingAssistance_r17__reducedMaxMIMO_LayersFR2_2 z, tt)).
Definition OverheatingAssistance_r17__F2 (y : seq_type OverheatingAssistance_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__OverheatingAssistance_r17__Type i0 i1
  end.
Lemma OverheatingAssistance_r17__F1F2_cond (z : OverheatingAssistance_r17__Type)
  : OverheatingAssistance_r17__cond z ->
  (seq_cond OverheatingAssistance_r17__list (OverheatingAssistance_r17__F1 z)).
intro H. unfold OverheatingAssistance_r17__cond in H. simpl. auto. Qed.
Lemma OverheatingAssistance_r17__F1F2_cond2 (z : OverheatingAssistance_r17__Type)
 : OverheatingAssistance_r17__F2 (OverheatingAssistance_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OverheatingAssistance_r17__F2F1_cond (y : seq_type OverheatingAssistance_r17__list)
  : seq_cond OverheatingAssistance_r17__list y ->
 (OverheatingAssistance_r17__cond (OverheatingAssistance_r17__F2 y)) /\  OverheatingAssistance_r17__F1 (OverheatingAssistance_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OverheatingAssistance_r17__cond. simpl in *. auto.
 - simpl. unfold OverheatingAssistance_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OverheatingAssistance_r17__Format : T_Format OverheatingAssistance_r17__Type OverheatingAssistance_r17__cond :=
        proj2_format  OverheatingAssistance_r17__cond OverheatingAssistance_r17__list__Format
    OverheatingAssistance_r17__F1 OverheatingAssistance_r17__F2 OverheatingAssistance_r17__F1F2_cond  OverheatingAssistance_r17__F1F2_cond2 OverheatingAssistance_r17__F2F1_cond.
Opaque OverheatingAssistance_r17__cond OverheatingAssistance_r17__Format.

