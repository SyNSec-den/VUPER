Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ReducedMaxCCs_r16.

Opaque ReducedMaxCCs_r16__cond ReducedMaxCCs_r16__Format.

Require Import NR.ReducedMaxBW_FRx_r16.

Opaque ReducedMaxBW_FRx_r16__cond ReducedMaxBW_FRx_r16__Format.

Require Import NR.ReducedMaxBW_FRx_r16.

Opaque ReducedMaxBW_FRx_r16__cond ReducedMaxBW_FRx_r16__Format.

Require Import NR.MIMO_LayersDL.

Opaque MIMO_LayersDL__cond MIMO_LayersDL__Format.

Require Import NR.MIMO_LayersUL.

Opaque MIMO_LayersUL__cond MIMO_LayersUL__Format.

Record OverheatingAssistance__reducedMaxMIMO_LayersFR1__Type : Set :=
  make__OverheatingAssistance__reducedMaxMIMO_LayersFR1__Type {
    OverheatingAssistance__reducedMaxMIMO_LayersFR1__reducedMIMO_LayersFR1_DL : MIMO_LayersDL__Type ;
    OverheatingAssistance__reducedMaxMIMO_LayersFR1__reducedMIMO_LayersFR1_UL : MIMO_LayersUL__Type ;
}.
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR1__list := (
 Nor MIMO_LayersDL__Type MIMO_LayersDL__cond ::
 Nor MIMO_LayersUL__Type MIMO_LayersUL__cond ::
 nil).
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond z := 
  MIMO_LayersDL__cond (OverheatingAssistance__reducedMaxMIMO_LayersFR1__reducedMIMO_LayersFR1_DL z) /\
  MIMO_LayersUL__cond (OverheatingAssistance__reducedMaxMIMO_LayersFR1__reducedMIMO_LayersFR1_UL z) /\
  True.

Require Import NR.MIMO_LayersDL.

Opaque MIMO_LayersDL__cond MIMO_LayersDL__Format.

Require Import NR.MIMO_LayersUL.

Opaque MIMO_LayersUL__cond MIMO_LayersUL__Format.

Record OverheatingAssistance__reducedMaxMIMO_LayersFR2__Type : Set :=
  make__OverheatingAssistance__reducedMaxMIMO_LayersFR2__Type {
    OverheatingAssistance__reducedMaxMIMO_LayersFR2__reducedMIMO_LayersFR2_DL : MIMO_LayersDL__Type ;
    OverheatingAssistance__reducedMaxMIMO_LayersFR2__reducedMIMO_LayersFR2_UL : MIMO_LayersUL__Type ;
}.
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR2__list := (
 Nor MIMO_LayersDL__Type MIMO_LayersDL__cond ::
 Nor MIMO_LayersUL__Type MIMO_LayersUL__cond ::
 nil).
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond z := 
  MIMO_LayersDL__cond (OverheatingAssistance__reducedMaxMIMO_LayersFR2__reducedMIMO_LayersFR2_DL z) /\
  MIMO_LayersUL__cond (OverheatingAssistance__reducedMaxMIMO_LayersFR2__reducedMIMO_LayersFR2_UL z) /\
  True.

Record OverheatingAssistance__Type : Set :=
  make__OverheatingAssistance__Type {
    OverheatingAssistance__reducedMaxCCs : option ReducedMaxCCs_r16__Type ;
    OverheatingAssistance__reducedMaxBW_FR1 : option ReducedMaxBW_FRx_r16__Type ;
    OverheatingAssistance__reducedMaxBW_FR2 : option ReducedMaxBW_FRx_r16__Type ;
    OverheatingAssistance__reducedMaxMIMO_LayersFR1 : option OverheatingAssistance__reducedMaxMIMO_LayersFR1__Type ;
    OverheatingAssistance__reducedMaxMIMO_LayersFR2 : option OverheatingAssistance__reducedMaxMIMO_LayersFR2__Type ;
}.
Definition OverheatingAssistance__list := (
 Opt ReducedMaxCCs_r16__Type ReducedMaxCCs_r16__cond ::
 Opt ReducedMaxBW_FRx_r16__Type ReducedMaxBW_FRx_r16__cond ::
 Opt ReducedMaxBW_FRx_r16__Type ReducedMaxBW_FRx_r16__cond ::
 Opt OverheatingAssistance__reducedMaxMIMO_LayersFR1__Type OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond ::
 Opt OverheatingAssistance__reducedMaxMIMO_LayersFR2__Type OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond ::
 nil).
Definition OverheatingAssistance__cond z := 
  opt_cond ReducedMaxCCs_r16__cond (OverheatingAssistance__reducedMaxCCs z) /\
  opt_cond ReducedMaxBW_FRx_r16__cond (OverheatingAssistance__reducedMaxBW_FR1 z) /\
  opt_cond ReducedMaxBW_FRx_r16__cond (OverheatingAssistance__reducedMaxBW_FR2 z) /\
  opt_cond OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond (OverheatingAssistance__reducedMaxMIMO_LayersFR1 z) /\
  opt_cond OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond (OverheatingAssistance__reducedMaxMIMO_LayersFR2 z) /\
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

Definition OverheatingAssistance__reducedMaxMIMO_LayersFR1__Format_Type := Eval cbn in seq_format_prod OverheatingAssistance__reducedMaxMIMO_LayersFR1__list.
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR1__Format_list : OverheatingAssistance__reducedMaxMIMO_LayersFR1__Format_Type :=
  (MIMO_LayersDL__Format, (MIMO_LayersUL__Format, unit_format)).
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR1__list__Format := (*Eval compute in *) seq_format OverheatingAssistance__reducedMaxMIMO_LayersFR1__list OverheatingAssistance__reducedMaxMIMO_LayersFR1__Format_list.
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1 z :=
  (OverheatingAssistance__reducedMaxMIMO_LayersFR1__reducedMIMO_LayersFR1_DL z, (OverheatingAssistance__reducedMaxMIMO_LayersFR1__reducedMIMO_LayersFR1_UL z, tt)).
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR1__F2 (y : seq_type OverheatingAssistance__reducedMaxMIMO_LayersFR1__list) :=
  match y with
  | (i0, (i1, _))=>
    make__OverheatingAssistance__reducedMaxMIMO_LayersFR1__Type i0 i1
  end.
Lemma OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1F2_cond (z : OverheatingAssistance__reducedMaxMIMO_LayersFR1__Type)
  : OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond z ->
  (seq_cond OverheatingAssistance__reducedMaxMIMO_LayersFR1__list (OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1 z)).
intro H. unfold OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond in H. simpl. auto. Qed.
Lemma OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1F2_cond2 (z : OverheatingAssistance__reducedMaxMIMO_LayersFR1__Type)
 : OverheatingAssistance__reducedMaxMIMO_LayersFR1__F2 (OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OverheatingAssistance__reducedMaxMIMO_LayersFR1__F2F1_cond (y : seq_type OverheatingAssistance__reducedMaxMIMO_LayersFR1__list)
  : seq_cond OverheatingAssistance__reducedMaxMIMO_LayersFR1__list y ->
 (OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond (OverheatingAssistance__reducedMaxMIMO_LayersFR1__F2 y)) /\  OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1 (OverheatingAssistance__reducedMaxMIMO_LayersFR1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond. simpl in *. auto.
 - simpl. unfold OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR1__Format : T_Format OverheatingAssistance__reducedMaxMIMO_LayersFR1__Type OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond :=
        proj2_format  OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond OverheatingAssistance__reducedMaxMIMO_LayersFR1__list__Format
    OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1 OverheatingAssistance__reducedMaxMIMO_LayersFR1__F2 OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1F2_cond  OverheatingAssistance__reducedMaxMIMO_LayersFR1__F1F2_cond2 OverheatingAssistance__reducedMaxMIMO_LayersFR1__F2F1_cond.
Opaque OverheatingAssistance__reducedMaxMIMO_LayersFR1__cond OverheatingAssistance__reducedMaxMIMO_LayersFR1__Format.


Definition OverheatingAssistance__reducedMaxMIMO_LayersFR2__Format_Type := Eval cbn in seq_format_prod OverheatingAssistance__reducedMaxMIMO_LayersFR2__list.
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR2__Format_list : OverheatingAssistance__reducedMaxMIMO_LayersFR2__Format_Type :=
  (MIMO_LayersDL__Format, (MIMO_LayersUL__Format, unit_format)).
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR2__list__Format := (*Eval compute in *) seq_format OverheatingAssistance__reducedMaxMIMO_LayersFR2__list OverheatingAssistance__reducedMaxMIMO_LayersFR2__Format_list.
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1 z :=
  (OverheatingAssistance__reducedMaxMIMO_LayersFR2__reducedMIMO_LayersFR2_DL z, (OverheatingAssistance__reducedMaxMIMO_LayersFR2__reducedMIMO_LayersFR2_UL z, tt)).
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR2__F2 (y : seq_type OverheatingAssistance__reducedMaxMIMO_LayersFR2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__OverheatingAssistance__reducedMaxMIMO_LayersFR2__Type i0 i1
  end.
Lemma OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1F2_cond (z : OverheatingAssistance__reducedMaxMIMO_LayersFR2__Type)
  : OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond z ->
  (seq_cond OverheatingAssistance__reducedMaxMIMO_LayersFR2__list (OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1 z)).
intro H. unfold OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond in H. simpl. auto. Qed.
Lemma OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1F2_cond2 (z : OverheatingAssistance__reducedMaxMIMO_LayersFR2__Type)
 : OverheatingAssistance__reducedMaxMIMO_LayersFR2__F2 (OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OverheatingAssistance__reducedMaxMIMO_LayersFR2__F2F1_cond (y : seq_type OverheatingAssistance__reducedMaxMIMO_LayersFR2__list)
  : seq_cond OverheatingAssistance__reducedMaxMIMO_LayersFR2__list y ->
 (OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond (OverheatingAssistance__reducedMaxMIMO_LayersFR2__F2 y)) /\  OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1 (OverheatingAssistance__reducedMaxMIMO_LayersFR2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond. simpl in *. auto.
 - simpl. unfold OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OverheatingAssistance__reducedMaxMIMO_LayersFR2__Format : T_Format OverheatingAssistance__reducedMaxMIMO_LayersFR2__Type OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond :=
        proj2_format  OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond OverheatingAssistance__reducedMaxMIMO_LayersFR2__list__Format
    OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1 OverheatingAssistance__reducedMaxMIMO_LayersFR2__F2 OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1F2_cond  OverheatingAssistance__reducedMaxMIMO_LayersFR2__F1F2_cond2 OverheatingAssistance__reducedMaxMIMO_LayersFR2__F2F1_cond.
Opaque OverheatingAssistance__reducedMaxMIMO_LayersFR2__cond OverheatingAssistance__reducedMaxMIMO_LayersFR2__Format.


Definition OverheatingAssistance__Format_Type := Eval cbn in seq_format_prod OverheatingAssistance__list.
Definition OverheatingAssistance__Format_list : OverheatingAssistance__Format_Type :=
  (ReducedMaxCCs_r16__Format, (ReducedMaxBW_FRx_r16__Format, (ReducedMaxBW_FRx_r16__Format, (OverheatingAssistance__reducedMaxMIMO_LayersFR1__Format, (OverheatingAssistance__reducedMaxMIMO_LayersFR2__Format, unit_format))))).
Definition OverheatingAssistance__list__Format := (*Eval compute in *) seq_format OverheatingAssistance__list OverheatingAssistance__Format_list.
Definition OverheatingAssistance__F1 z :=
  (OverheatingAssistance__reducedMaxCCs z, (OverheatingAssistance__reducedMaxBW_FR1 z, (OverheatingAssistance__reducedMaxBW_FR2 z, (OverheatingAssistance__reducedMaxMIMO_LayersFR1 z, (OverheatingAssistance__reducedMaxMIMO_LayersFR2 z, tt))))).
Definition OverheatingAssistance__F2 (y : seq_type OverheatingAssistance__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__OverheatingAssistance__Type i0 i1 i2 i3 i4
  end.
Lemma OverheatingAssistance__F1F2_cond (z : OverheatingAssistance__Type)
  : OverheatingAssistance__cond z ->
  (seq_cond OverheatingAssistance__list (OverheatingAssistance__F1 z)).
intro H. unfold OverheatingAssistance__cond in H. simpl. auto. Qed.
Lemma OverheatingAssistance__F1F2_cond2 (z : OverheatingAssistance__Type)
 : OverheatingAssistance__F2 (OverheatingAssistance__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OverheatingAssistance__F2F1_cond (y : seq_type OverheatingAssistance__list)
  : seq_cond OverheatingAssistance__list y ->
 (OverheatingAssistance__cond (OverheatingAssistance__F2 y)) /\  OverheatingAssistance__F1 (OverheatingAssistance__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OverheatingAssistance__cond. simpl in *. auto.
 - simpl. unfold OverheatingAssistance__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OverheatingAssistance__Format : T_Format OverheatingAssistance__Type OverheatingAssistance__cond :=
        proj2_format  OverheatingAssistance__cond OverheatingAssistance__list__Format
    OverheatingAssistance__F1 OverheatingAssistance__F2 OverheatingAssistance__F1F2_cond  OverheatingAssistance__F1F2_cond2 OverheatingAssistance__F2F1_cond.
Opaque OverheatingAssistance__cond OverheatingAssistance__Format.

