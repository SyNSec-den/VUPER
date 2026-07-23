Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma RB_SetGroup_r17__resourceAvailability_r17__seq_of__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma RB_SetGroup_r17__resourceAvailability_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RB_SetGroup_r17__resourceAvailability_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RB_SetGroup_r17__resourceAvailability_r17__seq_of__Type := Z.
Definition RB_SetGroup_r17__resourceAvailability_r17__seq_of__cond := (fun z => (0 <= z <= 7)%Z).
Definition RB_SetGroup_r17__resourceAvailability_r17__Type := list Z.

Lemma RB_SetGroup_r17__resourceAvailability_r17__helper1 : (0 <= 1 <= maxNrofResourceAvailabilityPerCombination_r16)%Z. unfold maxNrofResourceAvailabilityPerCombination_r16.
 lia. Qed.
Lemma RB_SetGroup_r17__resourceAvailability_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofResourceAvailabilityPerCombination_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofResourceAvailabilityPerCombination_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RB_SetGroup_r17__resourceAvailability_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RB_SetGroup_r17__resourceAvailability_r17__cond (z : RB_SetGroup_r17__resourceAvailability_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofResourceAvailabilityPerCombination_r16)%Z /\ (list_and RB_SetGroup_r17__resourceAvailability_r17__seq_of__cond z) .

Lemma RB_SetGroup_r17__rb_Sets_r17__seq_of__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma RB_SetGroup_r17__rb_Sets_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RB_SetGroup_r17__rb_Sets_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RB_SetGroup_r17__rb_Sets_r17__seq_of__Type := Z.
Definition RB_SetGroup_r17__rb_Sets_r17__seq_of__cond := (fun z => (0 <= z <= 7)%Z).
Definition RB_SetGroup_r17__rb_Sets_r17__Type := list Z.

Lemma RB_SetGroup_r17__rb_Sets_r17__helper1 : (0 <= 1 <= maxNrofRB_Sets_r17)%Z. unfold maxNrofRB_Sets_r17.
 lia. Qed.
Lemma RB_SetGroup_r17__rb_Sets_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofRB_Sets_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRB_Sets_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RB_SetGroup_r17__rb_Sets_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RB_SetGroup_r17__rb_Sets_r17__cond (z : RB_SetGroup_r17__rb_Sets_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRB_Sets_r17)%Z /\ (list_and RB_SetGroup_r17__rb_Sets_r17__seq_of__cond z) .

Record RB_SetGroup_r17__Type : Set :=
  make__RB_SetGroup_r17__Type {
    RB_SetGroup_r17__resourceAvailability_r17 : option RB_SetGroup_r17__resourceAvailability_r17__Type ;
    RB_SetGroup_r17__rb_Sets_r17 : option RB_SetGroup_r17__rb_Sets_r17__Type ;
}.
Definition RB_SetGroup_r17__list := (
 Opt RB_SetGroup_r17__resourceAvailability_r17__Type RB_SetGroup_r17__resourceAvailability_r17__cond ::
 Opt RB_SetGroup_r17__rb_Sets_r17__Type RB_SetGroup_r17__rb_Sets_r17__cond ::
 nil).
Definition RB_SetGroup_r17__cond z := 
  opt_cond RB_SetGroup_r17__resourceAvailability_r17__cond (RB_SetGroup_r17__resourceAvailability_r17 z) /\
  opt_cond RB_SetGroup_r17__rb_Sets_r17__cond (RB_SetGroup_r17__rb_Sets_r17 z) /\
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
Definition RB_SetGroup_r17__resourceAvailability_r17__seq_of__Format : T_Format Z RB_SetGroup_r17__resourceAvailability_r17__seq_of__cond :=
 ranged_int_format (0) (7) RB_SetGroup_r17__resourceAvailability_r17__seq_of__helper1 RB_SetGroup_r17__resourceAvailability_r17__seq_of__helper2.

Opaque RB_SetGroup_r17__resourceAvailability_r17__seq_of__cond RB_SetGroup_r17__resourceAvailability_r17__seq_of__Format.

Definition RB_SetGroup_r17__resourceAvailability_r17__Format : T_Format RB_SetGroup_r17__resourceAvailability_r17__Type RB_SetGroup_r17__resourceAvailability_r17__cond := seq_of_format RB_SetGroup_r17__resourceAvailability_r17__seq_of__Format 1 maxNrofResourceAvailabilityPerCombination_r16 RB_SetGroup_r17__resourceAvailability_r17__helper1 RB_SetGroup_r17__resourceAvailability_r17__helper2.

Opaque RB_SetGroup_r17__resourceAvailability_r17__cond RB_SetGroup_r17__resourceAvailability_r17__Format.

Definition RB_SetGroup_r17__rb_Sets_r17__seq_of__Format : T_Format Z RB_SetGroup_r17__rb_Sets_r17__seq_of__cond :=
 ranged_int_format (0) (7) RB_SetGroup_r17__rb_Sets_r17__seq_of__helper1 RB_SetGroup_r17__rb_Sets_r17__seq_of__helper2.

Opaque RB_SetGroup_r17__rb_Sets_r17__seq_of__cond RB_SetGroup_r17__rb_Sets_r17__seq_of__Format.

Definition RB_SetGroup_r17__rb_Sets_r17__Format : T_Format RB_SetGroup_r17__rb_Sets_r17__Type RB_SetGroup_r17__rb_Sets_r17__cond := seq_of_format RB_SetGroup_r17__rb_Sets_r17__seq_of__Format 1 maxNrofRB_Sets_r17 RB_SetGroup_r17__rb_Sets_r17__helper1 RB_SetGroup_r17__rb_Sets_r17__helper2.

Opaque RB_SetGroup_r17__rb_Sets_r17__cond RB_SetGroup_r17__rb_Sets_r17__Format.


Definition RB_SetGroup_r17__Format_Type := Eval cbn in seq_format_prod RB_SetGroup_r17__list.
Definition RB_SetGroup_r17__Format_list : RB_SetGroup_r17__Format_Type :=
  (RB_SetGroup_r17__resourceAvailability_r17__Format, (RB_SetGroup_r17__rb_Sets_r17__Format, unit_format)).
Definition RB_SetGroup_r17__list__Format := (*Eval compute in *) seq_format RB_SetGroup_r17__list RB_SetGroup_r17__Format_list.
Definition RB_SetGroup_r17__F1 z :=
  (RB_SetGroup_r17__resourceAvailability_r17 z, (RB_SetGroup_r17__rb_Sets_r17 z, tt)).
Definition RB_SetGroup_r17__F2 (y : seq_type RB_SetGroup_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RB_SetGroup_r17__Type i0 i1
  end.
Lemma RB_SetGroup_r17__F1F2_cond (z : RB_SetGroup_r17__Type)
  : RB_SetGroup_r17__cond z ->
  (seq_cond RB_SetGroup_r17__list (RB_SetGroup_r17__F1 z)).
intro H. unfold RB_SetGroup_r17__cond in H. simpl. auto. Qed.
Lemma RB_SetGroup_r17__F1F2_cond2 (z : RB_SetGroup_r17__Type)
 : RB_SetGroup_r17__F2 (RB_SetGroup_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RB_SetGroup_r17__F2F1_cond (y : seq_type RB_SetGroup_r17__list)
  : seq_cond RB_SetGroup_r17__list y ->
 (RB_SetGroup_r17__cond (RB_SetGroup_r17__F2 y)) /\  RB_SetGroup_r17__F1 (RB_SetGroup_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RB_SetGroup_r17__cond. simpl in *. auto.
 - simpl. unfold RB_SetGroup_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RB_SetGroup_r17__Format : T_Format RB_SetGroup_r17__Type RB_SetGroup_r17__cond :=
        proj2_format  RB_SetGroup_r17__cond RB_SetGroup_r17__list__Format
    RB_SetGroup_r17__F1 RB_SetGroup_r17__F2 RB_SetGroup_r17__F1F2_cond  RB_SetGroup_r17__F1F2_cond2 RB_SetGroup_r17__F2F1_cond.
Opaque RB_SetGroup_r17__cond RB_SetGroup_r17__Format.

