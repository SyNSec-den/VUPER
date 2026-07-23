Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma Orbital_r17__semiMajorAxis_r17__helper1 : (0 <= 8589934591)%Z.  lia. Qed.
Lemma Orbital_r17__semiMajorAxis_r17__helper2 : to_bit_sz (Z.to_nat (8589934591 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8589934591 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply Orbital_r17__semiMajorAxis_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Orbital_r17__semiMajorAxis_r17__Type := Z.
Definition Orbital_r17__semiMajorAxis_r17__cond := (fun z => (0 <= z <= 8589934591)%Z).
Lemma Orbital_r17__eccentricity_r17__helper1 : (0 <= 1048575)%Z.  lia. Qed.
Lemma Orbital_r17__eccentricity_r17__helper2 : to_bit_sz (Z.to_nat (1048575 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1048575 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply Orbital_r17__eccentricity_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Orbital_r17__eccentricity_r17__Type := Z.
Definition Orbital_r17__eccentricity_r17__cond := (fun z => (0 <= z <= 1048575)%Z).
Lemma Orbital_r17__periapsis_r17__helper1 : (0 <= 268435455)%Z.  lia. Qed.
Lemma Orbital_r17__periapsis_r17__helper2 : to_bit_sz (Z.to_nat (268435455 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (268435455 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply Orbital_r17__periapsis_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Orbital_r17__periapsis_r17__Type := Z.
Definition Orbital_r17__periapsis_r17__cond := (fun z => (0 <= z <= 268435455)%Z).
Lemma Orbital_r17__longitude_r17__helper1 : (0 <= 268435455)%Z.  lia. Qed.
Lemma Orbital_r17__longitude_r17__helper2 : to_bit_sz (Z.to_nat (268435455 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (268435455 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply Orbital_r17__longitude_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Orbital_r17__longitude_r17__Type := Z.
Definition Orbital_r17__longitude_r17__cond := (fun z => (0 <= z <= 268435455)%Z).
Lemma Orbital_r17__inclination_r17__helper1 : (-67108864 <= 67108863)%Z.  lia. Qed.
Lemma Orbital_r17__inclination_r17__helper2 : to_bit_sz (Z.to_nat (67108863 - -67108864)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (67108863 - -67108864))%Z). { apply Zorder.Zle_minus_le_0. apply Orbital_r17__inclination_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Orbital_r17__inclination_r17__Type := Z.
Definition Orbital_r17__inclination_r17__cond := (fun z => (-67108864 <= z <= 67108863)%Z).
Lemma Orbital_r17__meanAnomaly_r17__helper1 : (0 <= 268435455)%Z.  lia. Qed.
Lemma Orbital_r17__meanAnomaly_r17__helper2 : to_bit_sz (Z.to_nat (268435455 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (268435455 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply Orbital_r17__meanAnomaly_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition Orbital_r17__meanAnomaly_r17__Type := Z.
Definition Orbital_r17__meanAnomaly_r17__cond := (fun z => (0 <= z <= 268435455)%Z).
Record Orbital_r17__Type : Set :=
  make__Orbital_r17__Type {
    Orbital_r17__semiMajorAxis_r17 : Z ;
    Orbital_r17__eccentricity_r17 : Z ;
    Orbital_r17__periapsis_r17 : Z ;
    Orbital_r17__longitude_r17 : Z ;
    Orbital_r17__inclination_r17 : Z ;
    Orbital_r17__meanAnomaly_r17 : Z ;
}.
Definition Orbital_r17__list := (
 Nor Z Orbital_r17__semiMajorAxis_r17__cond ::
 Nor Z Orbital_r17__eccentricity_r17__cond ::
 Nor Z Orbital_r17__periapsis_r17__cond ::
 Nor Z Orbital_r17__longitude_r17__cond ::
 Nor Z Orbital_r17__inclination_r17__cond ::
 Nor Z Orbital_r17__meanAnomaly_r17__cond ::
 nil).
Definition Orbital_r17__cond z := 
  Orbital_r17__semiMajorAxis_r17__cond (Orbital_r17__semiMajorAxis_r17 z) /\
  Orbital_r17__eccentricity_r17__cond (Orbital_r17__eccentricity_r17 z) /\
  Orbital_r17__periapsis_r17__cond (Orbital_r17__periapsis_r17 z) /\
  Orbital_r17__longitude_r17__cond (Orbital_r17__longitude_r17 z) /\
  Orbital_r17__inclination_r17__cond (Orbital_r17__inclination_r17 z) /\
  Orbital_r17__meanAnomaly_r17__cond (Orbital_r17__meanAnomaly_r17 z) /\
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
Definition Orbital_r17__semiMajorAxis_r17__Format : T_Format Z Orbital_r17__semiMajorAxis_r17__cond :=
 ranged_int_format (0) (8589934591) Orbital_r17__semiMajorAxis_r17__helper1 Orbital_r17__semiMajorAxis_r17__helper2.

Opaque Orbital_r17__semiMajorAxis_r17__cond Orbital_r17__semiMajorAxis_r17__Format.

Definition Orbital_r17__eccentricity_r17__Format : T_Format Z Orbital_r17__eccentricity_r17__cond :=
 ranged_int_format (0) (1048575) Orbital_r17__eccentricity_r17__helper1 Orbital_r17__eccentricity_r17__helper2.

Opaque Orbital_r17__eccentricity_r17__cond Orbital_r17__eccentricity_r17__Format.

Definition Orbital_r17__periapsis_r17__Format : T_Format Z Orbital_r17__periapsis_r17__cond :=
 ranged_int_format (0) (268435455) Orbital_r17__periapsis_r17__helper1 Orbital_r17__periapsis_r17__helper2.

Opaque Orbital_r17__periapsis_r17__cond Orbital_r17__periapsis_r17__Format.

Definition Orbital_r17__longitude_r17__Format : T_Format Z Orbital_r17__longitude_r17__cond :=
 ranged_int_format (0) (268435455) Orbital_r17__longitude_r17__helper1 Orbital_r17__longitude_r17__helper2.

Opaque Orbital_r17__longitude_r17__cond Orbital_r17__longitude_r17__Format.

Definition Orbital_r17__inclination_r17__Format : T_Format Z Orbital_r17__inclination_r17__cond :=
 ranged_int_format (-67108864) (67108863) Orbital_r17__inclination_r17__helper1 Orbital_r17__inclination_r17__helper2.

Opaque Orbital_r17__inclination_r17__cond Orbital_r17__inclination_r17__Format.

Definition Orbital_r17__meanAnomaly_r17__Format : T_Format Z Orbital_r17__meanAnomaly_r17__cond :=
 ranged_int_format (0) (268435455) Orbital_r17__meanAnomaly_r17__helper1 Orbital_r17__meanAnomaly_r17__helper2.

Opaque Orbital_r17__meanAnomaly_r17__cond Orbital_r17__meanAnomaly_r17__Format.


Definition Orbital_r17__Format_Type := Eval cbn in seq_format_prod Orbital_r17__list.
Definition Orbital_r17__Format_list : Orbital_r17__Format_Type :=
  (Orbital_r17__semiMajorAxis_r17__Format, (Orbital_r17__eccentricity_r17__Format, (Orbital_r17__periapsis_r17__Format, (Orbital_r17__longitude_r17__Format, (Orbital_r17__inclination_r17__Format, (Orbital_r17__meanAnomaly_r17__Format, unit_format)))))).
Definition Orbital_r17__list__Format := (*Eval compute in *) seq_format Orbital_r17__list Orbital_r17__Format_list.
Definition Orbital_r17__F1 z :=
  (Orbital_r17__semiMajorAxis_r17 z, (Orbital_r17__eccentricity_r17 z, (Orbital_r17__periapsis_r17 z, (Orbital_r17__longitude_r17 z, (Orbital_r17__inclination_r17 z, (Orbital_r17__meanAnomaly_r17 z, tt)))))).
Definition Orbital_r17__F2 (y : seq_type Orbital_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__Orbital_r17__Type i0 i1 i2 i3 i4 i5
  end.
Lemma Orbital_r17__F1F2_cond (z : Orbital_r17__Type)
  : Orbital_r17__cond z ->
  (seq_cond Orbital_r17__list (Orbital_r17__F1 z)).
intro H. unfold Orbital_r17__cond in H. simpl. auto. Qed.
Lemma Orbital_r17__F1F2_cond2 (z : Orbital_r17__Type)
 : Orbital_r17__F2 (Orbital_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Orbital_r17__F2F1_cond (y : seq_type Orbital_r17__list)
  : seq_cond Orbital_r17__list y ->
 (Orbital_r17__cond (Orbital_r17__F2 y)) /\  Orbital_r17__F1 (Orbital_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Orbital_r17__cond. simpl in *. auto.
 - simpl. unfold Orbital_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Orbital_r17__Format : T_Format Orbital_r17__Type Orbital_r17__cond :=
        proj2_format  Orbital_r17__cond Orbital_r17__list__Format
    Orbital_r17__F1 Orbital_r17__F2 Orbital_r17__F1F2_cond  Orbital_r17__F1F2_cond2 Orbital_r17__F2F1_cond.
Opaque Orbital_r17__cond Orbital_r17__Format.

