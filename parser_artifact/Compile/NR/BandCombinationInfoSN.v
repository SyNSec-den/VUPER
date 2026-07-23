Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.BandCombinationIndex.

Opaque BandCombinationIndex__cond BandCombinationIndex__Format.

Require Import NR.FeatureSetEntryIndex.

Opaque FeatureSetEntryIndex__cond FeatureSetEntryIndex__Format.

Record BandCombinationInfoSN__Type : Set :=
  make__BandCombinationInfoSN__Type {
    BandCombinationInfoSN__bandCombinationIndex : BandCombinationIndex__Type ;
    BandCombinationInfoSN__requestedFeatureSets : FeatureSetEntryIndex__Type ;
}.
Definition BandCombinationInfoSN__list := (
 Nor BandCombinationIndex__Type BandCombinationIndex__cond ::
 Nor FeatureSetEntryIndex__Type FeatureSetEntryIndex__cond ::
 nil).
Definition BandCombinationInfoSN__cond z := 
  BandCombinationIndex__cond (BandCombinationInfoSN__bandCombinationIndex z) /\
  FeatureSetEntryIndex__cond (BandCombinationInfoSN__requestedFeatureSets z) /\
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

Definition BandCombinationInfoSN__Format_Type := Eval cbn in seq_format_prod BandCombinationInfoSN__list.
Definition BandCombinationInfoSN__Format_list : BandCombinationInfoSN__Format_Type :=
  (BandCombinationIndex__Format, (FeatureSetEntryIndex__Format, unit_format)).
Definition BandCombinationInfoSN__list__Format := (*Eval compute in *) seq_format BandCombinationInfoSN__list BandCombinationInfoSN__Format_list.
Definition BandCombinationInfoSN__F1 z :=
  (BandCombinationInfoSN__bandCombinationIndex z, (BandCombinationInfoSN__requestedFeatureSets z, tt)).
Definition BandCombinationInfoSN__F2 (y : seq_type BandCombinationInfoSN__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandCombinationInfoSN__Type i0 i1
  end.
Lemma BandCombinationInfoSN__F1F2_cond (z : BandCombinationInfoSN__Type)
  : BandCombinationInfoSN__cond z ->
  (seq_cond BandCombinationInfoSN__list (BandCombinationInfoSN__F1 z)).
intro H. unfold BandCombinationInfoSN__cond in H. simpl. auto. Qed.
Lemma BandCombinationInfoSN__F1F2_cond2 (z : BandCombinationInfoSN__Type)
 : BandCombinationInfoSN__F2 (BandCombinationInfoSN__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombinationInfoSN__F2F1_cond (y : seq_type BandCombinationInfoSN__list)
  : seq_cond BandCombinationInfoSN__list y ->
 (BandCombinationInfoSN__cond (BandCombinationInfoSN__F2 y)) /\  BandCombinationInfoSN__F1 (BandCombinationInfoSN__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombinationInfoSN__cond. simpl in *. auto.
 - simpl. unfold BandCombinationInfoSN__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombinationInfoSN__Format : T_Format BandCombinationInfoSN__Type BandCombinationInfoSN__cond :=
        proj2_format  BandCombinationInfoSN__cond BandCombinationInfoSN__list__Format
    BandCombinationInfoSN__F1 BandCombinationInfoSN__F2 BandCombinationInfoSN__F1F2_cond  BandCombinationInfoSN__F1F2_cond2 BandCombinationInfoSN__F2F1_cond.
Opaque BandCombinationInfoSN__cond BandCombinationInfoSN__Format.

