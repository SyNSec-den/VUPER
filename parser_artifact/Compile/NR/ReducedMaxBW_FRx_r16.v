Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ReducedAggregatedBandwidth.

Opaque ReducedAggregatedBandwidth__cond ReducedAggregatedBandwidth__Format.

Require Import NR.ReducedAggregatedBandwidth.

Opaque ReducedAggregatedBandwidth__cond ReducedAggregatedBandwidth__Format.

Record ReducedMaxBW_FRx_r16__Type : Set :=
  make__ReducedMaxBW_FRx_r16__Type {
    ReducedMaxBW_FRx_r16__reducedBW_DL_r16 : ReducedAggregatedBandwidth__Type ;
    ReducedMaxBW_FRx_r16__reducedBW_UL_r16 : ReducedAggregatedBandwidth__Type ;
}.
Definition ReducedMaxBW_FRx_r16__list := (
 Nor ReducedAggregatedBandwidth__Type ReducedAggregatedBandwidth__cond ::
 Nor ReducedAggregatedBandwidth__Type ReducedAggregatedBandwidth__cond ::
 nil).
Definition ReducedMaxBW_FRx_r16__cond z := 
  ReducedAggregatedBandwidth__cond (ReducedMaxBW_FRx_r16__reducedBW_DL_r16 z) /\
  ReducedAggregatedBandwidth__cond (ReducedMaxBW_FRx_r16__reducedBW_UL_r16 z) /\
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

Definition ReducedMaxBW_FRx_r16__Format_Type := Eval cbn in seq_format_prod ReducedMaxBW_FRx_r16__list.
Definition ReducedMaxBW_FRx_r16__Format_list : ReducedMaxBW_FRx_r16__Format_Type :=
  (ReducedAggregatedBandwidth__Format, (ReducedAggregatedBandwidth__Format, unit_format)).
Definition ReducedMaxBW_FRx_r16__list__Format := (*Eval compute in *) seq_format ReducedMaxBW_FRx_r16__list ReducedMaxBW_FRx_r16__Format_list.
Definition ReducedMaxBW_FRx_r16__F1 z :=
  (ReducedMaxBW_FRx_r16__reducedBW_DL_r16 z, (ReducedMaxBW_FRx_r16__reducedBW_UL_r16 z, tt)).
Definition ReducedMaxBW_FRx_r16__F2 (y : seq_type ReducedMaxBW_FRx_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ReducedMaxBW_FRx_r16__Type i0 i1
  end.
Lemma ReducedMaxBW_FRx_r16__F1F2_cond (z : ReducedMaxBW_FRx_r16__Type)
  : ReducedMaxBW_FRx_r16__cond z ->
  (seq_cond ReducedMaxBW_FRx_r16__list (ReducedMaxBW_FRx_r16__F1 z)).
intro H. unfold ReducedMaxBW_FRx_r16__cond in H. simpl. auto. Qed.
Lemma ReducedMaxBW_FRx_r16__F1F2_cond2 (z : ReducedMaxBW_FRx_r16__Type)
 : ReducedMaxBW_FRx_r16__F2 (ReducedMaxBW_FRx_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReducedMaxBW_FRx_r16__F2F1_cond (y : seq_type ReducedMaxBW_FRx_r16__list)
  : seq_cond ReducedMaxBW_FRx_r16__list y ->
 (ReducedMaxBW_FRx_r16__cond (ReducedMaxBW_FRx_r16__F2 y)) /\  ReducedMaxBW_FRx_r16__F1 (ReducedMaxBW_FRx_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReducedMaxBW_FRx_r16__cond. simpl in *. auto.
 - simpl. unfold ReducedMaxBW_FRx_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReducedMaxBW_FRx_r16__Format : T_Format ReducedMaxBW_FRx_r16__Type ReducedMaxBW_FRx_r16__cond :=
        proj2_format  ReducedMaxBW_FRx_r16__cond ReducedMaxBW_FRx_r16__list__Format
    ReducedMaxBW_FRx_r16__F1 ReducedMaxBW_FRx_r16__F2 ReducedMaxBW_FRx_r16__F1F2_cond  ReducedMaxBW_FRx_r16__F1F2_cond2 ReducedMaxBW_FRx_r16__F2F1_cond.
Opaque ReducedMaxBW_FRx_r16__cond ReducedMaxBW_FRx_r16__Format.

