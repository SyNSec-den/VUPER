Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PTRS_DensityRecommendationUL__frequencyDensity1__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__frequencyDensity1__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__frequencyDensity1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__frequencyDensity1__Type := Z.
Definition PTRS_DensityRecommendationUL__frequencyDensity1__cond := (fun z => (1 <= z <= 276)%Z).
Lemma PTRS_DensityRecommendationUL__frequencyDensity2__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__frequencyDensity2__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__frequencyDensity2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__frequencyDensity2__Type := Z.
Definition PTRS_DensityRecommendationUL__frequencyDensity2__cond := (fun z => (1 <= z <= 276)%Z).
Lemma PTRS_DensityRecommendationUL__timeDensity1__helper1 : (0 <= 29)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__timeDensity1__helper2 : to_bit_sz (Z.to_nat (29 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (29 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__timeDensity1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__timeDensity1__Type := Z.
Definition PTRS_DensityRecommendationUL__timeDensity1__cond := (fun z => (0 <= z <= 29)%Z).
Lemma PTRS_DensityRecommendationUL__timeDensity2__helper1 : (0 <= 29)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__timeDensity2__helper2 : to_bit_sz (Z.to_nat (29 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (29 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__timeDensity2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__timeDensity2__Type := Z.
Definition PTRS_DensityRecommendationUL__timeDensity2__cond := (fun z => (0 <= z <= 29)%Z).
Lemma PTRS_DensityRecommendationUL__timeDensity3__helper1 : (0 <= 29)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__timeDensity3__helper2 : to_bit_sz (Z.to_nat (29 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (29 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__timeDensity3__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__timeDensity3__Type := Z.
Definition PTRS_DensityRecommendationUL__timeDensity3__cond := (fun z => (0 <= z <= 29)%Z).
Lemma PTRS_DensityRecommendationUL__sampleDensity1__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__sampleDensity1__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__sampleDensity1__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__sampleDensity1__Type := Z.
Definition PTRS_DensityRecommendationUL__sampleDensity1__cond := (fun z => (1 <= z <= 276)%Z).
Lemma PTRS_DensityRecommendationUL__sampleDensity2__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__sampleDensity2__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__sampleDensity2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__sampleDensity2__Type := Z.
Definition PTRS_DensityRecommendationUL__sampleDensity2__cond := (fun z => (1 <= z <= 276)%Z).
Lemma PTRS_DensityRecommendationUL__sampleDensity3__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__sampleDensity3__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__sampleDensity3__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__sampleDensity3__Type := Z.
Definition PTRS_DensityRecommendationUL__sampleDensity3__cond := (fun z => (1 <= z <= 276)%Z).
Lemma PTRS_DensityRecommendationUL__sampleDensity4__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__sampleDensity4__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__sampleDensity4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__sampleDensity4__Type := Z.
Definition PTRS_DensityRecommendationUL__sampleDensity4__cond := (fun z => (1 <= z <= 276)%Z).
Lemma PTRS_DensityRecommendationUL__sampleDensity5__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DensityRecommendationUL__sampleDensity5__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DensityRecommendationUL__sampleDensity5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DensityRecommendationUL__sampleDensity5__Type := Z.
Definition PTRS_DensityRecommendationUL__sampleDensity5__cond := (fun z => (1 <= z <= 276)%Z).
Record PTRS_DensityRecommendationUL__Type : Set :=
  make__PTRS_DensityRecommendationUL__Type {
    PTRS_DensityRecommendationUL__frequencyDensity1 : Z ;
    PTRS_DensityRecommendationUL__frequencyDensity2 : Z ;
    PTRS_DensityRecommendationUL__timeDensity1 : Z ;
    PTRS_DensityRecommendationUL__timeDensity2 : Z ;
    PTRS_DensityRecommendationUL__timeDensity3 : Z ;
    PTRS_DensityRecommendationUL__sampleDensity1 : Z ;
    PTRS_DensityRecommendationUL__sampleDensity2 : Z ;
    PTRS_DensityRecommendationUL__sampleDensity3 : Z ;
    PTRS_DensityRecommendationUL__sampleDensity4 : Z ;
    PTRS_DensityRecommendationUL__sampleDensity5 : Z ;
}.
Definition PTRS_DensityRecommendationUL__list := (
 Nor Z PTRS_DensityRecommendationUL__frequencyDensity1__cond ::
 Nor Z PTRS_DensityRecommendationUL__frequencyDensity2__cond ::
 Nor Z PTRS_DensityRecommendationUL__timeDensity1__cond ::
 Nor Z PTRS_DensityRecommendationUL__timeDensity2__cond ::
 Nor Z PTRS_DensityRecommendationUL__timeDensity3__cond ::
 Nor Z PTRS_DensityRecommendationUL__sampleDensity1__cond ::
 Nor Z PTRS_DensityRecommendationUL__sampleDensity2__cond ::
 Nor Z PTRS_DensityRecommendationUL__sampleDensity3__cond ::
 Nor Z PTRS_DensityRecommendationUL__sampleDensity4__cond ::
 Nor Z PTRS_DensityRecommendationUL__sampleDensity5__cond ::
 nil).
Definition PTRS_DensityRecommendationUL__cond z := 
  PTRS_DensityRecommendationUL__frequencyDensity1__cond (PTRS_DensityRecommendationUL__frequencyDensity1 z) /\
  PTRS_DensityRecommendationUL__frequencyDensity2__cond (PTRS_DensityRecommendationUL__frequencyDensity2 z) /\
  PTRS_DensityRecommendationUL__timeDensity1__cond (PTRS_DensityRecommendationUL__timeDensity1 z) /\
  PTRS_DensityRecommendationUL__timeDensity2__cond (PTRS_DensityRecommendationUL__timeDensity2 z) /\
  PTRS_DensityRecommendationUL__timeDensity3__cond (PTRS_DensityRecommendationUL__timeDensity3 z) /\
  PTRS_DensityRecommendationUL__sampleDensity1__cond (PTRS_DensityRecommendationUL__sampleDensity1 z) /\
  PTRS_DensityRecommendationUL__sampleDensity2__cond (PTRS_DensityRecommendationUL__sampleDensity2 z) /\
  PTRS_DensityRecommendationUL__sampleDensity3__cond (PTRS_DensityRecommendationUL__sampleDensity3 z) /\
  PTRS_DensityRecommendationUL__sampleDensity4__cond (PTRS_DensityRecommendationUL__sampleDensity4 z) /\
  PTRS_DensityRecommendationUL__sampleDensity5__cond (PTRS_DensityRecommendationUL__sampleDensity5 z) /\
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
Definition PTRS_DensityRecommendationUL__frequencyDensity1__Format : T_Format Z PTRS_DensityRecommendationUL__frequencyDensity1__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationUL__frequencyDensity1__helper1 PTRS_DensityRecommendationUL__frequencyDensity1__helper2.

Opaque PTRS_DensityRecommendationUL__frequencyDensity1__cond PTRS_DensityRecommendationUL__frequencyDensity1__Format.

Definition PTRS_DensityRecommendationUL__frequencyDensity2__Format : T_Format Z PTRS_DensityRecommendationUL__frequencyDensity2__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationUL__frequencyDensity2__helper1 PTRS_DensityRecommendationUL__frequencyDensity2__helper2.

Opaque PTRS_DensityRecommendationUL__frequencyDensity2__cond PTRS_DensityRecommendationUL__frequencyDensity2__Format.

Definition PTRS_DensityRecommendationUL__timeDensity1__Format : T_Format Z PTRS_DensityRecommendationUL__timeDensity1__cond :=
 ranged_int_format (0) (29) PTRS_DensityRecommendationUL__timeDensity1__helper1 PTRS_DensityRecommendationUL__timeDensity1__helper2.

Opaque PTRS_DensityRecommendationUL__timeDensity1__cond PTRS_DensityRecommendationUL__timeDensity1__Format.

Definition PTRS_DensityRecommendationUL__timeDensity2__Format : T_Format Z PTRS_DensityRecommendationUL__timeDensity2__cond :=
 ranged_int_format (0) (29) PTRS_DensityRecommendationUL__timeDensity2__helper1 PTRS_DensityRecommendationUL__timeDensity2__helper2.

Opaque PTRS_DensityRecommendationUL__timeDensity2__cond PTRS_DensityRecommendationUL__timeDensity2__Format.

Definition PTRS_DensityRecommendationUL__timeDensity3__Format : T_Format Z PTRS_DensityRecommendationUL__timeDensity3__cond :=
 ranged_int_format (0) (29) PTRS_DensityRecommendationUL__timeDensity3__helper1 PTRS_DensityRecommendationUL__timeDensity3__helper2.

Opaque PTRS_DensityRecommendationUL__timeDensity3__cond PTRS_DensityRecommendationUL__timeDensity3__Format.

Definition PTRS_DensityRecommendationUL__sampleDensity1__Format : T_Format Z PTRS_DensityRecommendationUL__sampleDensity1__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationUL__sampleDensity1__helper1 PTRS_DensityRecommendationUL__sampleDensity1__helper2.

Opaque PTRS_DensityRecommendationUL__sampleDensity1__cond PTRS_DensityRecommendationUL__sampleDensity1__Format.

Definition PTRS_DensityRecommendationUL__sampleDensity2__Format : T_Format Z PTRS_DensityRecommendationUL__sampleDensity2__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationUL__sampleDensity2__helper1 PTRS_DensityRecommendationUL__sampleDensity2__helper2.

Opaque PTRS_DensityRecommendationUL__sampleDensity2__cond PTRS_DensityRecommendationUL__sampleDensity2__Format.

Definition PTRS_DensityRecommendationUL__sampleDensity3__Format : T_Format Z PTRS_DensityRecommendationUL__sampleDensity3__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationUL__sampleDensity3__helper1 PTRS_DensityRecommendationUL__sampleDensity3__helper2.

Opaque PTRS_DensityRecommendationUL__sampleDensity3__cond PTRS_DensityRecommendationUL__sampleDensity3__Format.

Definition PTRS_DensityRecommendationUL__sampleDensity4__Format : T_Format Z PTRS_DensityRecommendationUL__sampleDensity4__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationUL__sampleDensity4__helper1 PTRS_DensityRecommendationUL__sampleDensity4__helper2.

Opaque PTRS_DensityRecommendationUL__sampleDensity4__cond PTRS_DensityRecommendationUL__sampleDensity4__Format.

Definition PTRS_DensityRecommendationUL__sampleDensity5__Format : T_Format Z PTRS_DensityRecommendationUL__sampleDensity5__cond :=
 ranged_int_format (1) (276) PTRS_DensityRecommendationUL__sampleDensity5__helper1 PTRS_DensityRecommendationUL__sampleDensity5__helper2.

Opaque PTRS_DensityRecommendationUL__sampleDensity5__cond PTRS_DensityRecommendationUL__sampleDensity5__Format.


Definition PTRS_DensityRecommendationUL__Format_Type := Eval cbn in seq_format_prod PTRS_DensityRecommendationUL__list.
Definition PTRS_DensityRecommendationUL__Format_list : PTRS_DensityRecommendationUL__Format_Type :=
  (PTRS_DensityRecommendationUL__frequencyDensity1__Format, (PTRS_DensityRecommendationUL__frequencyDensity2__Format, (PTRS_DensityRecommendationUL__timeDensity1__Format, (PTRS_DensityRecommendationUL__timeDensity2__Format, (PTRS_DensityRecommendationUL__timeDensity3__Format, (PTRS_DensityRecommendationUL__sampleDensity1__Format, (PTRS_DensityRecommendationUL__sampleDensity2__Format, (PTRS_DensityRecommendationUL__sampleDensity3__Format, (PTRS_DensityRecommendationUL__sampleDensity4__Format, (PTRS_DensityRecommendationUL__sampleDensity5__Format, unit_format)))))))))).
Definition PTRS_DensityRecommendationUL__list__Format := (*Eval compute in *) seq_format PTRS_DensityRecommendationUL__list PTRS_DensityRecommendationUL__Format_list.
Definition PTRS_DensityRecommendationUL__F1 z :=
  (PTRS_DensityRecommendationUL__frequencyDensity1 z, (PTRS_DensityRecommendationUL__frequencyDensity2 z, (PTRS_DensityRecommendationUL__timeDensity1 z, (PTRS_DensityRecommendationUL__timeDensity2 z, (PTRS_DensityRecommendationUL__timeDensity3 z, (PTRS_DensityRecommendationUL__sampleDensity1 z, (PTRS_DensityRecommendationUL__sampleDensity2 z, (PTRS_DensityRecommendationUL__sampleDensity3 z, (PTRS_DensityRecommendationUL__sampleDensity4 z, (PTRS_DensityRecommendationUL__sampleDensity5 z, tt)))))))))).
Definition PTRS_DensityRecommendationUL__F2 (y : seq_type PTRS_DensityRecommendationUL__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__PTRS_DensityRecommendationUL__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma PTRS_DensityRecommendationUL__F1F2_cond (z : PTRS_DensityRecommendationUL__Type)
  : PTRS_DensityRecommendationUL__cond z ->
  (seq_cond PTRS_DensityRecommendationUL__list (PTRS_DensityRecommendationUL__F1 z)).
intro H. unfold PTRS_DensityRecommendationUL__cond in H. simpl. auto. Qed.
Lemma PTRS_DensityRecommendationUL__F1F2_cond2 (z : PTRS_DensityRecommendationUL__Type)
 : PTRS_DensityRecommendationUL__F2 (PTRS_DensityRecommendationUL__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PTRS_DensityRecommendationUL__F2F1_cond (y : seq_type PTRS_DensityRecommendationUL__list)
  : seq_cond PTRS_DensityRecommendationUL__list y ->
 (PTRS_DensityRecommendationUL__cond (PTRS_DensityRecommendationUL__F2 y)) /\  PTRS_DensityRecommendationUL__F1 (PTRS_DensityRecommendationUL__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PTRS_DensityRecommendationUL__cond. simpl in *. auto.
 - simpl. unfold PTRS_DensityRecommendationUL__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PTRS_DensityRecommendationUL__Format : T_Format PTRS_DensityRecommendationUL__Type PTRS_DensityRecommendationUL__cond :=
        proj2_format  PTRS_DensityRecommendationUL__cond PTRS_DensityRecommendationUL__list__Format
    PTRS_DensityRecommendationUL__F1 PTRS_DensityRecommendationUL__F2 PTRS_DensityRecommendationUL__F1F2_cond  PTRS_DensityRecommendationUL__F1F2_cond2 PTRS_DensityRecommendationUL__F2F1_cond.
Opaque PTRS_DensityRecommendationUL__cond PTRS_DensityRecommendationUL__Format.

