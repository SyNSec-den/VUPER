Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__Type := Z.
Definition UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__cond := (fun z => (0 <= z <= 3)%Z).
Record UL_GapFR2_Preference_r17__Type : Set :=
  make__UL_GapFR2_Preference_r17__Type {
    UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17 : option Z ;
}.
Definition UL_GapFR2_Preference_r17__list := (
 Opt Z UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__cond ::
 nil).
Definition UL_GapFR2_Preference_r17__cond z := 
  opt_cond UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__cond (UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17 z) /\
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
Definition UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__Format : T_Format Z UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__cond :=
 ranged_int_format (0) (3) UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__helper1 UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__helper2.

Opaque UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__cond UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__Format.


Definition UL_GapFR2_Preference_r17__Format_Type := Eval cbn in seq_format_prod UL_GapFR2_Preference_r17__list.
Definition UL_GapFR2_Preference_r17__Format_list : UL_GapFR2_Preference_r17__Format_Type :=
  (UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17__Format, unit_format).
Definition UL_GapFR2_Preference_r17__list__Format := (*Eval compute in *) seq_format UL_GapFR2_Preference_r17__list UL_GapFR2_Preference_r17__Format_list.
Definition UL_GapFR2_Preference_r17__F1 z :=
  (UL_GapFR2_Preference_r17__ul_GapFR2_PatternPreference_r17 z, tt).
Definition UL_GapFR2_Preference_r17__F2 (y : seq_type UL_GapFR2_Preference_r17__list) :=
  match y with
  | (i0, _)=>
    make__UL_GapFR2_Preference_r17__Type i0
  end.
Lemma UL_GapFR2_Preference_r17__F1F2_cond (z : UL_GapFR2_Preference_r17__Type)
  : UL_GapFR2_Preference_r17__cond z ->
  (seq_cond UL_GapFR2_Preference_r17__list (UL_GapFR2_Preference_r17__F1 z)).
intro H. unfold UL_GapFR2_Preference_r17__cond in H. simpl. auto. Qed.
Lemma UL_GapFR2_Preference_r17__F1F2_cond2 (z : UL_GapFR2_Preference_r17__Type)
 : UL_GapFR2_Preference_r17__F2 (UL_GapFR2_Preference_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UL_GapFR2_Preference_r17__F2F1_cond (y : seq_type UL_GapFR2_Preference_r17__list)
  : seq_cond UL_GapFR2_Preference_r17__list y ->
 (UL_GapFR2_Preference_r17__cond (UL_GapFR2_Preference_r17__F2 y)) /\  UL_GapFR2_Preference_r17__F1 (UL_GapFR2_Preference_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UL_GapFR2_Preference_r17__cond. simpl in *. auto.
 - simpl. unfold UL_GapFR2_Preference_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UL_GapFR2_Preference_r17__Format : T_Format UL_GapFR2_Preference_r17__Type UL_GapFR2_Preference_r17__cond :=
        proj2_format  UL_GapFR2_Preference_r17__cond UL_GapFR2_Preference_r17__list__Format
    UL_GapFR2_Preference_r17__F1 UL_GapFR2_Preference_r17__F2 UL_GapFR2_Preference_r17__F1F2_cond  UL_GapFR2_Preference_r17__F1F2_cond2 UL_GapFR2_Preference_r17__F2F1_cond.
Opaque UL_GapFR2_Preference_r17__cond UL_GapFR2_Preference_r17__Format.

