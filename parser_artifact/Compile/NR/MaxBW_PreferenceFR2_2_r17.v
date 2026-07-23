Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ReducedAggregatedBandwidth_r17.

Opaque ReducedAggregatedBandwidth_r17__cond ReducedAggregatedBandwidth_r17__Format.

Require Import NR.ReducedAggregatedBandwidth_r17.

Opaque ReducedAggregatedBandwidth_r17__cond ReducedAggregatedBandwidth_r17__Format.

Record MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type : Set :=
  make__MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type {
    MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_DL_r17 : option ReducedAggregatedBandwidth_r17__Type ;
    MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_UL_r17 : option ReducedAggregatedBandwidth_r17__Type ;
}.
Definition MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list := (
 Opt ReducedAggregatedBandwidth_r17__Type ReducedAggregatedBandwidth_r17__cond ::
 Opt ReducedAggregatedBandwidth_r17__Type ReducedAggregatedBandwidth_r17__cond ::
 nil).
Definition MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond z := 
  opt_cond ReducedAggregatedBandwidth_r17__cond (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_DL_r17 z) /\
  opt_cond ReducedAggregatedBandwidth_r17__cond (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_UL_r17 z) /\
  True.

Record MaxBW_PreferenceFR2_2_r17__Type : Set :=
  make__MaxBW_PreferenceFR2_2_r17__Type {
    MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17 : option MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type ;
}.
Definition MaxBW_PreferenceFR2_2_r17__list := (
 Opt MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond ::
 nil).
Definition MaxBW_PreferenceFR2_2_r17__cond z := 
  opt_cond MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17 z) /\
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

Definition MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format_Type := Eval cbn in seq_format_prod MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list.
Definition MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format_list : MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format_Type :=
  (ReducedAggregatedBandwidth_r17__Format, (ReducedAggregatedBandwidth_r17__Format, unit_format)).
Definition MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list__Format := (*Eval compute in *) seq_format MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format_list.
Definition MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1 z :=
  (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_DL_r17 z, (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__reducedBW_FR2_2_UL_r17 z, tt)).
Definition MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F2 (y : seq_type MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type i0 i1
  end.
Lemma MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1F2_cond (z : MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type)
  : MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond z ->
  (seq_cond MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1 z)).
intro H. unfold MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond in H. simpl. auto. Qed.
Lemma MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1F2_cond2 (z : MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type)
 : MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F2 (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F2F1_cond (y : seq_type MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list)
  : seq_cond MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list y ->
 (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F2 y)) /\  MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1 (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond. simpl in *. auto.
 - simpl. unfold MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format : T_Format MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Type MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond :=
        proj2_format  MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__list__Format
    MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1 MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F2 MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1F2_cond  MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F1F2_cond2 MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__F2F1_cond.
Opaque MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__cond MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format.


Definition MaxBW_PreferenceFR2_2_r17__Format_Type := Eval cbn in seq_format_prod MaxBW_PreferenceFR2_2_r17__list.
Definition MaxBW_PreferenceFR2_2_r17__Format_list : MaxBW_PreferenceFR2_2_r17__Format_Type :=
  (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17__Format, unit_format).
Definition MaxBW_PreferenceFR2_2_r17__list__Format := (*Eval compute in *) seq_format MaxBW_PreferenceFR2_2_r17__list MaxBW_PreferenceFR2_2_r17__Format_list.
Definition MaxBW_PreferenceFR2_2_r17__F1 z :=
  (MaxBW_PreferenceFR2_2_r17__reducedMaxBW_FR2_2_r17 z, tt).
Definition MaxBW_PreferenceFR2_2_r17__F2 (y : seq_type MaxBW_PreferenceFR2_2_r17__list) :=
  match y with
  | (i0, _)=>
    make__MaxBW_PreferenceFR2_2_r17__Type i0
  end.
Lemma MaxBW_PreferenceFR2_2_r17__F1F2_cond (z : MaxBW_PreferenceFR2_2_r17__Type)
  : MaxBW_PreferenceFR2_2_r17__cond z ->
  (seq_cond MaxBW_PreferenceFR2_2_r17__list (MaxBW_PreferenceFR2_2_r17__F1 z)).
intro H. unfold MaxBW_PreferenceFR2_2_r17__cond in H. simpl. auto. Qed.
Lemma MaxBW_PreferenceFR2_2_r17__F1F2_cond2 (z : MaxBW_PreferenceFR2_2_r17__Type)
 : MaxBW_PreferenceFR2_2_r17__F2 (MaxBW_PreferenceFR2_2_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MaxBW_PreferenceFR2_2_r17__F2F1_cond (y : seq_type MaxBW_PreferenceFR2_2_r17__list)
  : seq_cond MaxBW_PreferenceFR2_2_r17__list y ->
 (MaxBW_PreferenceFR2_2_r17__cond (MaxBW_PreferenceFR2_2_r17__F2 y)) /\  MaxBW_PreferenceFR2_2_r17__F1 (MaxBW_PreferenceFR2_2_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MaxBW_PreferenceFR2_2_r17__cond. simpl in *. auto.
 - simpl. unfold MaxBW_PreferenceFR2_2_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MaxBW_PreferenceFR2_2_r17__Format : T_Format MaxBW_PreferenceFR2_2_r17__Type MaxBW_PreferenceFR2_2_r17__cond :=
        proj2_format  MaxBW_PreferenceFR2_2_r17__cond MaxBW_PreferenceFR2_2_r17__list__Format
    MaxBW_PreferenceFR2_2_r17__F1 MaxBW_PreferenceFR2_2_r17__F2 MaxBW_PreferenceFR2_2_r17__F1F2_cond  MaxBW_PreferenceFR2_2_r17__F1F2_cond2 MaxBW_PreferenceFR2_2_r17__F2F1_cond.
Opaque MaxBW_PreferenceFR2_2_r17__cond MaxBW_PreferenceFR2_2_r17__Format.

