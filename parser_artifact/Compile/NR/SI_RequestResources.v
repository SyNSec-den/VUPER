Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SI_RequestResources__ra_PreambleStartIndex__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SI_RequestResources__ra_PreambleStartIndex__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SI_RequestResources__ra_PreambleStartIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SI_RequestResources__ra_PreambleStartIndex__Type := Z.
Definition SI_RequestResources__ra_PreambleStartIndex__cond := (fun z => (0 <= z <= 63)%Z).
Lemma SI_RequestResources__ra_AssociationPeriodIndex__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SI_RequestResources__ra_AssociationPeriodIndex__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SI_RequestResources__ra_AssociationPeriodIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SI_RequestResources__ra_AssociationPeriodIndex__Type := Z.
Definition SI_RequestResources__ra_AssociationPeriodIndex__cond := (fun z => (0 <= z <= 15)%Z).
Lemma SI_RequestResources__ra_ssb_OccasionMaskIndex__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SI_RequestResources__ra_ssb_OccasionMaskIndex__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SI_RequestResources__ra_ssb_OccasionMaskIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SI_RequestResources__ra_ssb_OccasionMaskIndex__Type := Z.
Definition SI_RequestResources__ra_ssb_OccasionMaskIndex__cond := (fun z => (0 <= z <= 15)%Z).
Record SI_RequestResources__Type : Set :=
  make__SI_RequestResources__Type {
    SI_RequestResources__ra_PreambleStartIndex : Z ;
    SI_RequestResources__ra_AssociationPeriodIndex : option Z ;
    SI_RequestResources__ra_ssb_OccasionMaskIndex : option Z ;
}.
Definition SI_RequestResources__list := (
 Nor Z SI_RequestResources__ra_PreambleStartIndex__cond ::
 Opt Z SI_RequestResources__ra_AssociationPeriodIndex__cond ::
 Opt Z SI_RequestResources__ra_ssb_OccasionMaskIndex__cond ::
 nil).
Definition SI_RequestResources__cond z := 
  SI_RequestResources__ra_PreambleStartIndex__cond (SI_RequestResources__ra_PreambleStartIndex z) /\
  opt_cond SI_RequestResources__ra_AssociationPeriodIndex__cond (SI_RequestResources__ra_AssociationPeriodIndex z) /\
  opt_cond SI_RequestResources__ra_ssb_OccasionMaskIndex__cond (SI_RequestResources__ra_ssb_OccasionMaskIndex z) /\
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
Definition SI_RequestResources__ra_PreambleStartIndex__Format : T_Format Z SI_RequestResources__ra_PreambleStartIndex__cond :=
 ranged_int_format (0) (63) SI_RequestResources__ra_PreambleStartIndex__helper1 SI_RequestResources__ra_PreambleStartIndex__helper2.

Opaque SI_RequestResources__ra_PreambleStartIndex__cond SI_RequestResources__ra_PreambleStartIndex__Format.

Definition SI_RequestResources__ra_AssociationPeriodIndex__Format : T_Format Z SI_RequestResources__ra_AssociationPeriodIndex__cond :=
 ranged_int_format (0) (15) SI_RequestResources__ra_AssociationPeriodIndex__helper1 SI_RequestResources__ra_AssociationPeriodIndex__helper2.

Opaque SI_RequestResources__ra_AssociationPeriodIndex__cond SI_RequestResources__ra_AssociationPeriodIndex__Format.

Definition SI_RequestResources__ra_ssb_OccasionMaskIndex__Format : T_Format Z SI_RequestResources__ra_ssb_OccasionMaskIndex__cond :=
 ranged_int_format (0) (15) SI_RequestResources__ra_ssb_OccasionMaskIndex__helper1 SI_RequestResources__ra_ssb_OccasionMaskIndex__helper2.

Opaque SI_RequestResources__ra_ssb_OccasionMaskIndex__cond SI_RequestResources__ra_ssb_OccasionMaskIndex__Format.


Definition SI_RequestResources__Format_Type := Eval cbn in seq_format_prod SI_RequestResources__list.
Definition SI_RequestResources__Format_list : SI_RequestResources__Format_Type :=
  (SI_RequestResources__ra_PreambleStartIndex__Format, (SI_RequestResources__ra_AssociationPeriodIndex__Format, (SI_RequestResources__ra_ssb_OccasionMaskIndex__Format, unit_format))).
Definition SI_RequestResources__list__Format := (*Eval compute in *) seq_format SI_RequestResources__list SI_RequestResources__Format_list.
Definition SI_RequestResources__F1 z :=
  (SI_RequestResources__ra_PreambleStartIndex z, (SI_RequestResources__ra_AssociationPeriodIndex z, (SI_RequestResources__ra_ssb_OccasionMaskIndex z, tt))).
Definition SI_RequestResources__F2 (y : seq_type SI_RequestResources__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SI_RequestResources__Type i0 i1 i2
  end.
Lemma SI_RequestResources__F1F2_cond (z : SI_RequestResources__Type)
  : SI_RequestResources__cond z ->
  (seq_cond SI_RequestResources__list (SI_RequestResources__F1 z)).
intro H. unfold SI_RequestResources__cond in H. simpl. auto. Qed.
Lemma SI_RequestResources__F1F2_cond2 (z : SI_RequestResources__Type)
 : SI_RequestResources__F2 (SI_RequestResources__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SI_RequestResources__F2F1_cond (y : seq_type SI_RequestResources__list)
  : seq_cond SI_RequestResources__list y ->
 (SI_RequestResources__cond (SI_RequestResources__F2 y)) /\  SI_RequestResources__F1 (SI_RequestResources__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SI_RequestResources__cond. simpl in *. auto.
 - simpl. unfold SI_RequestResources__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SI_RequestResources__Format : T_Format SI_RequestResources__Type SI_RequestResources__cond :=
        proj2_format  SI_RequestResources__cond SI_RequestResources__list__Format
    SI_RequestResources__F1 SI_RequestResources__F2 SI_RequestResources__F1F2_cond  SI_RequestResources__F1F2_cond2 SI_RequestResources__F2F1_cond.
Opaque SI_RequestResources__cond SI_RequestResources__Format.

