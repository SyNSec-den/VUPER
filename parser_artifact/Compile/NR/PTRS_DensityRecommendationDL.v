Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PTRS_DensityRecommendationDL__frequencyDensity1__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationDL__frequencyDensity1__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationDL__frequencyDensity1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationDL__frequencyDensity1__Type := Z.
Definition PTRS_DensityRecommendationDL__frequencyDensity1__cond := (fun z => (1 <= z <= 276)%Z).
Lemma PTRS_DensityRecommendationDL__frequencyDensity2__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationDL__frequencyDensity2__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationDL__frequencyDensity2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationDL__frequencyDensity2__Type := Z.
Definition PTRS_DensityRecommendationDL__frequencyDensity2__cond := (fun z => (1 <= z <= 276)%Z).
Lemma PTRS_DensityRecommendationDL__timeDensity1__helper1 : (0 <= 29)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationDL__timeDensity1__helper2 : to_bit_sz (Z.to_nat (29 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (29 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationDL__timeDensity1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationDL__timeDensity1__Type := Z.
Definition PTRS_DensityRecommendationDL__timeDensity1__cond := (fun z => (0 <= z <= 29)%Z).
Lemma PTRS_DensityRecommendationDL__timeDensity2__helper1 : (0 <= 29)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationDL__timeDensity2__helper2 : to_bit_sz (Z.to_nat (29 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (29 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationDL__timeDensity2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationDL__timeDensity2__Type := Z.
Definition PTRS_DensityRecommendationDL__timeDensity2__cond := (fun z => (0 <= z <= 29)%Z).
Lemma PTRS_DensityRecommendationDL__timeDensity3__helper1 : (0 <= 29)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationDL__timeDensity3__helper2 : to_bit_sz (Z.to_nat (29 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (29 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationDL__timeDensity3__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationDL__timeDensity3__Type := Z.
Definition PTRS_DensityRecommendationDL__timeDensity3__cond := (fun z => (0 <= z <= 29)%Z).
Record PTRS_DensityRecommendationDL__Type : Set :=
  make__PTRS_DensityRecommendationDL__Type {
    PTRS_DensityRecommendationDL__frequencyDensity1 : Z ;
    PTRS_DensityRecommendationDL__frequencyDensity2 : Z ;
    PTRS_DensityRecommendationDL__timeDensity1 : Z ;
    PTRS_DensityRecommendationDL__timeDensity2 : Z ;
    PTRS_DensityRecommendationDL__timeDensity3 : Z ;
}.
Definition PTRS_DensityRecommendationDL__list := (
 Nor Z PTRS_DensityRecommendationDL__frequencyDensity1__cond ::
 Nor Z PTRS_DensityRecommendationDL__frequencyDensity2__cond ::
 Nor Z PTRS_DensityRecommendationDL__timeDensity1__cond ::
 Nor Z PTRS_DensityRecommendationDL__timeDensity2__cond ::
 Nor Z PTRS_DensityRecommendationDL__timeDensity3__cond ::
 nil).
Definition PTRS_DensityRecommendationDL__cond z := 
  PTRS_DensityRecommendationDL__frequencyDensity1__cond (PTRS_DensityRecommendationDL__frequencyDensity1 z) /\
  PTRS_DensityRecommendationDL__frequencyDensity2__cond (PTRS_DensityRecommendationDL__frequencyDensity2 z) /\
  PTRS_DensityRecommendationDL__timeDensity1__cond (PTRS_DensityRecommendationDL__timeDensity1 z) /\
  PTRS_DensityRecommendationDL__timeDensity2__cond (PTRS_DensityRecommendationDL__timeDensity2 z) /\
  PTRS_DensityRecommendationDL__timeDensity3__cond (PTRS_DensityRecommendationDL__timeDensity3 z) /\
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
Definition PTRS_DensityRecommendationDL__frequencyDensity1__Format : T_Format Z PTRS_DensityRecommendationDL__frequencyDensity1__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationDL__frequencyDensity1__helper1 PTRS_DensityRecommendationDL__frequencyDensity1__helper2.

Opaque PTRS_DensityRecommendationDL__frequencyDensity1__cond PTRS_DensityRecommendationDL__frequencyDensity1__Format.

Definition PTRS_DensityRecommendationDL__frequencyDensity2__Format : T_Format Z PTRS_DensityRecommendationDL__frequencyDensity2__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationDL__frequencyDensity2__helper1 PTRS_DensityRecommendationDL__frequencyDensity2__helper2.

Opaque PTRS_DensityRecommendationDL__frequencyDensity2__cond PTRS_DensityRecommendationDL__frequencyDensity2__Format.

Definition PTRS_DensityRecommendationDL__timeDensity1__Format : T_Format Z PTRS_DensityRecommendationDL__timeDensity1__cond :=
 ranged_int_format (0) (29) PTRS_DensityRecommendationDL__timeDensity1__helper1 PTRS_DensityRecommendationDL__timeDensity1__helper2.

Opaque PTRS_DensityRecommendationDL__timeDensity1__cond PTRS_DensityRecommendationDL__timeDensity1__Format.

Definition PTRS_DensityRecommendationDL__timeDensity2__Format : T_Format Z PTRS_DensityRecommendationDL__timeDensity2__cond :=
 ranged_int_format (0) (29) PTRS_DensityRecommendationDL__timeDensity2__helper1 PTRS_DensityRecommendationDL__timeDensity2__helper2.

Opaque PTRS_DensityRecommendationDL__timeDensity2__cond PTRS_DensityRecommendationDL__timeDensity2__Format.

Definition PTRS_DensityRecommendationDL__timeDensity3__Format : T_Format Z PTRS_DensityRecommendationDL__timeDensity3__cond :=
 ranged_int_format (0) (29) PTRS_DensityRecommendationDL__timeDensity3__helper1 PTRS_DensityRecommendationDL__timeDensity3__helper2.

Opaque PTRS_DensityRecommendationDL__timeDensity3__cond PTRS_DensityRecommendationDL__timeDensity3__Format.


Definition PTRS_DensityRecommendationDL__Format_Type := Eval cbn in seq_format_prod PTRS_DensityRecommendationDL__list.
Definition PTRS_DensityRecommendationDL__Format_list : PTRS_DensityRecommendationDL__Format_Type :=
  (PTRS_DensityRecommendationDL__frequencyDensity1__Format, (PTRS_DensityRecommendationDL__frequencyDensity2__Format, (PTRS_DensityRecommendationDL__timeDensity1__Format, (PTRS_DensityRecommendationDL__timeDensity2__Format, (PTRS_DensityRecommendationDL__timeDensity3__Format, unit_format))))).
Definition PTRS_DensityRecommendationDL__list__Format := (*Eval compute in *) seq_format PTRS_DensityRecommendationDL__list PTRS_DensityRecommendationDL__Format_list.
Definition PTRS_DensityRecommendationDL__F1 z :=
  (PTRS_DensityRecommendationDL__frequencyDensity1 z, (PTRS_DensityRecommendationDL__frequencyDensity2 z, (PTRS_DensityRecommendationDL__timeDensity1 z, (PTRS_DensityRecommendationDL__timeDensity2 z, (PTRS_DensityRecommendationDL__timeDensity3 z, tt))))).
Definition PTRS_DensityRecommendationDL__F2 (y : seq_type PTRS_DensityRecommendationDL__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__PTRS_DensityRecommendationDL__Type i0 i1 i2 i3 i4
  end.
Lemma PTRS_DensityRecommendationDL__F1F2_cond (z : PTRS_DensityRecommendationDL__Type)
  : PTRS_DensityRecommendationDL__cond z ->
  (seq_cond PTRS_DensityRecommendationDL__list (PTRS_DensityRecommendationDL__F1 z)).
intro H. unfold PTRS_DensityRecommendationDL__cond in H. simpl. auto. Qed.
Lemma PTRS_DensityRecommendationDL__F1F2_cond2 (z : PTRS_DensityRecommendationDL__Type)
 : PTRS_DensityRecommendationDL__F2 (PTRS_DensityRecommendationDL__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PTRS_DensityRecommendationDL__F2F1_cond (y : seq_type PTRS_DensityRecommendationDL__list)
  : seq_cond PTRS_DensityRecommendationDL__list y ->
 (PTRS_DensityRecommendationDL__cond (PTRS_DensityRecommendationDL__F2 y)) /\  PTRS_DensityRecommendationDL__F1 (PTRS_DensityRecommendationDL__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PTRS_DensityRecommendationDL__cond. simpl in *. auto.
 - simpl. unfold PTRS_DensityRecommendationDL__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PTRS_DensityRecommendationDL__Format : T_Format PTRS_DensityRecommendationDL__Type PTRS_DensityRecommendationDL__cond :=
        proj2_format  PTRS_DensityRecommendationDL__cond PTRS_DensityRecommendationDL__list__Format
    PTRS_DensityRecommendationDL__F1 PTRS_DensityRecommendationDL__F2 PTRS_DensityRecommendationDL__F1F2_cond  PTRS_DensityRecommendationDL__F1F2_cond2 PTRS_DensityRecommendationDL__F2F1_cond.
Opaque PTRS_DensityRecommendationDL__cond PTRS_DensityRecommendationDL__Format.

