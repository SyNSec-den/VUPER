Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.BandCombinationIndex.

Opaque BandCombinationIndex__cond BandCombinationIndex__Format.

Require Import NR.FeatureSetEntryIndex.

Opaque FeatureSetEntryIndex__cond FeatureSetEntryIndex__Format.

Definition BandCombinationInfo__allowedFeatureSetsList__Type := list FeatureSetEntryIndex__Type.

Lemma BandCombinationInfo__allowedFeatureSetsList__helper1 : (0 <= 1 <= maxFeatureSetsPerBand)%Z. unfold maxFeatureSetsPerBand.
 lia. Qed.
Lemma BandCombinationInfo__allowedFeatureSetsList__helper2 : to_bit_sz (Z.to_nat (maxFeatureSetsPerBand - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxFeatureSetsPerBand - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandCombinationInfo__allowedFeatureSetsList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandCombinationInfo__allowedFeatureSetsList__cond (z : BandCombinationInfo__allowedFeatureSetsList__Type) :=  (1 <= Z.of_nat (length z) <= maxFeatureSetsPerBand)%Z /\ (list_and FeatureSetEntryIndex__cond z) .

Record BandCombinationInfo__Type : Set :=
  make__BandCombinationInfo__Type {
    BandCombinationInfo__bandCombinationIndex : BandCombinationIndex__Type ;
    BandCombinationInfo__allowedFeatureSetsList : BandCombinationInfo__allowedFeatureSetsList__Type ;
}.
Definition BandCombinationInfo__list := (
 Nor BandCombinationIndex__Type BandCombinationIndex__cond ::
 Nor BandCombinationInfo__allowedFeatureSetsList__Type BandCombinationInfo__allowedFeatureSetsList__cond ::
 nil).
Definition BandCombinationInfo__cond z := 
  BandCombinationIndex__cond (BandCombinationInfo__bandCombinationIndex z) /\
  BandCombinationInfo__allowedFeatureSetsList__cond (BandCombinationInfo__allowedFeatureSetsList z) /\
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
Definition BandCombinationInfo__allowedFeatureSetsList__Format : T_Format BandCombinationInfo__allowedFeatureSetsList__Type BandCombinationInfo__allowedFeatureSetsList__cond := seq_of_format FeatureSetEntryIndex__Format 1 maxFeatureSetsPerBand BandCombinationInfo__allowedFeatureSetsList__helper1 BandCombinationInfo__allowedFeatureSetsList__helper2.

Opaque BandCombinationInfo__allowedFeatureSetsList__cond BandCombinationInfo__allowedFeatureSetsList__Format.


Definition BandCombinationInfo__Format_Type := Eval cbn in seq_format_prod BandCombinationInfo__list.
Definition BandCombinationInfo__Format_list : BandCombinationInfo__Format_Type :=
  (BandCombinationIndex__Format, (BandCombinationInfo__allowedFeatureSetsList__Format, unit_format)).
Definition BandCombinationInfo__list__Format := (*Eval compute in *) seq_format BandCombinationInfo__list BandCombinationInfo__Format_list.
Definition BandCombinationInfo__F1 z :=
  (BandCombinationInfo__bandCombinationIndex z, (BandCombinationInfo__allowedFeatureSetsList z, tt)).
Definition BandCombinationInfo__F2 (y : seq_type BandCombinationInfo__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandCombinationInfo__Type i0 i1
  end.
Lemma BandCombinationInfo__F1F2_cond (z : BandCombinationInfo__Type)
  : BandCombinationInfo__cond z ->
  (seq_cond BandCombinationInfo__list (BandCombinationInfo__F1 z)).
intro H. unfold BandCombinationInfo__cond in H. simpl. auto. Qed.
Lemma BandCombinationInfo__F1F2_cond2 (z : BandCombinationInfo__Type)
 : BandCombinationInfo__F2 (BandCombinationInfo__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombinationInfo__F2F1_cond (y : seq_type BandCombinationInfo__list)
  : seq_cond BandCombinationInfo__list y ->
 (BandCombinationInfo__cond (BandCombinationInfo__F2 y)) /\  BandCombinationInfo__F1 (BandCombinationInfo__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombinationInfo__cond. simpl in *. auto.
 - simpl. unfold BandCombinationInfo__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombinationInfo__Format : T_Format BandCombinationInfo__Type BandCombinationInfo__cond :=
        proj2_format  BandCombinationInfo__cond BandCombinationInfo__list__Format
    BandCombinationInfo__F1 BandCombinationInfo__F2 BandCombinationInfo__F1F2_cond  BandCombinationInfo__F1F2_cond2 BandCombinationInfo__F2F1_cond.
Opaque BandCombinationInfo__cond BandCombinationInfo__Format.

