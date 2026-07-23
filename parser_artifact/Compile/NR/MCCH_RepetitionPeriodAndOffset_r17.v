Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__cond := (fun z : Z => z = 0)%Z.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__cond := (fun z => (0 <= z <= 1)%Z).
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__cond := (fun z => (0 <= z <= 3)%Z).
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__cond := (fun z => (0 <= z <= 7)%Z).
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__cond := (fun z => (0 <= z <= 15)%Z).
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__cond := (fun z => (0 <= z <= 31)%Z).
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__cond := (fun z => (0 <= z <= 63)%Z).
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__cond := (fun z => (0 <= z <= 127)%Z).
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__Type := Z.
Definition MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__cond := (fun z => (0 <= z <= 255)%Z).

Inductive MCCH_RepetitionPeriodAndOffset_r17__Type : Set :=
  | MCCH_RepetitionPeriodAndOffset_r17__rf1_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
  | MCCH_RepetitionPeriodAndOffset_r17__rf2_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
  | MCCH_RepetitionPeriodAndOffset_r17__rf4_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
  | MCCH_RepetitionPeriodAndOffset_r17__rf8_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
  | MCCH_RepetitionPeriodAndOffset_r17__rf16_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
  | MCCH_RepetitionPeriodAndOffset_r17__rf32_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
  | MCCH_RepetitionPeriodAndOffset_r17__rf64_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
  | MCCH_RepetitionPeriodAndOffset_r17__rf128_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
  | MCCH_RepetitionPeriodAndOffset_r17__rf256_r17 : Z -> MCCH_RepetitionPeriodAndOffset_r17__Type
.
Definition MCCH_RepetitionPeriodAndOffset_r17__list : list typ := (
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__cond ::
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__cond ::
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__cond ::
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__cond ::
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__cond ::
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__cond ::
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__cond ::
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__cond ::
typ_cons Z MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__cond ::
 nil).
Definition MCCH_RepetitionPeriodAndOffset_r17__cond (c : MCCH_RepetitionPeriodAndOffset_r17__Type) := 
  match c with
  | MCCH_RepetitionPeriodAndOffset_r17__rf1_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__cond t 
  | MCCH_RepetitionPeriodAndOffset_r17__rf2_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__cond t 
  | MCCH_RepetitionPeriodAndOffset_r17__rf4_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__cond t 
  | MCCH_RepetitionPeriodAndOffset_r17__rf8_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__cond t 
  | MCCH_RepetitionPeriodAndOffset_r17__rf16_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__cond t 
  | MCCH_RepetitionPeriodAndOffset_r17__rf32_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__cond t 
  | MCCH_RepetitionPeriodAndOffset_r17__rf64_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__cond t 
  | MCCH_RepetitionPeriodAndOffset_r17__rf128_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__cond t 
  | MCCH_RepetitionPeriodAndOffset_r17__rf256_r17 t => MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__cond t 
  end.

Lemma MCCH_RepetitionPeriodAndOffset_r17__len_helper1 : to_bit_sz (length MCCH_RepetitionPeriodAndOffset_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MCCH_RepetitionPeriodAndOffset_r17__len_helper2 : 2 <= length2 MCCH_RepetitionPeriodAndOffset_r17__list.
 simpl. lia. Qed.

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
Definition MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__cond := fixed_int_format 0. Opaque MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__Format.

Definition MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__cond :=
 ranged_int_format (0) (1) MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__helper1 MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__helper2.

Opaque MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__Format.

Definition MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__cond :=
 ranged_int_format (0) (3) MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__helper1 MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__helper2.

Opaque MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__Format.

Definition MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__cond :=
 ranged_int_format (0) (7) MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__helper1 MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__helper2.

Opaque MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__Format.

Definition MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__cond :=
 ranged_int_format (0) (15) MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__helper1 MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__helper2.

Opaque MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__Format.

Definition MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__cond :=
 ranged_int_format (0) (31) MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__helper1 MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__helper2.

Opaque MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__Format.

Definition MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__cond :=
 ranged_int_format (0) (63) MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__helper1 MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__helper2.

Opaque MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__Format.

Definition MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__cond :=
 ranged_int_format (0) (127) MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__helper1 MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__helper2.

Opaque MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__Format.

Definition MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__Format : T_Format Z MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__cond :=
 ranged_int_format (0) (255) MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__helper1 MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__helper2.

Opaque MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__cond MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__Format.


Definition MCCH_RepetitionPeriodAndOffset_r17__Format_Type := Eval cbn in get_formats MCCH_RepetitionPeriodAndOffset_r17__list.
Definition MCCH_RepetitionPeriodAndOffset_r17__Format_list : MCCH_RepetitionPeriodAndOffset_r17__Format_Type :=
  (MCCH_RepetitionPeriodAndOffset_r17__rf1_r17__Format, (MCCH_RepetitionPeriodAndOffset_r17__rf2_r17__Format, (MCCH_RepetitionPeriodAndOffset_r17__rf4_r17__Format, (MCCH_RepetitionPeriodAndOffset_r17__rf8_r17__Format, (MCCH_RepetitionPeriodAndOffset_r17__rf16_r17__Format, (MCCH_RepetitionPeriodAndOffset_r17__rf32_r17__Format, (MCCH_RepetitionPeriodAndOffset_r17__rf64_r17__Format, (MCCH_RepetitionPeriodAndOffset_r17__rf128_r17__Format, (MCCH_RepetitionPeriodAndOffset_r17__rf256_r17__Format, unit__Format))))))))).
Definition MCCH_RepetitionPeriodAndOffset_r17__list__Format := Eval compute in choice_format MCCH_RepetitionPeriodAndOffset_r17__list MCCH_RepetitionPeriodAndOffset_r17__len_helper1 MCCH_RepetitionPeriodAndOffset_r17__len_helper2  MCCH_RepetitionPeriodAndOffset_r17__Format_list.
Definition MCCH_RepetitionPeriodAndOffset_r17__F1 (z : MCCH_RepetitionPeriodAndOffset_r17__Type) : (choice MCCH_RepetitionPeriodAndOffset_r17__list) :=
  match z with
   | MCCH_RepetitionPeriodAndOffset_r17__rf1_r17 t => existT _ 0 t
  | MCCH_RepetitionPeriodAndOffset_r17__rf2_r17 t => existT _ 1 t
  | MCCH_RepetitionPeriodAndOffset_r17__rf4_r17 t => existT _ 2 t
  | MCCH_RepetitionPeriodAndOffset_r17__rf8_r17 t => existT _ 3 t
  | MCCH_RepetitionPeriodAndOffset_r17__rf16_r17 t => existT _ 4 t
  | MCCH_RepetitionPeriodAndOffset_r17__rf32_r17 t => existT _ 5 t
  | MCCH_RepetitionPeriodAndOffset_r17__rf64_r17 t => existT _ 6 t
  | MCCH_RepetitionPeriodAndOffset_r17__rf128_r17 t => existT _ 7 t
  | MCCH_RepetitionPeriodAndOffset_r17__rf256_r17 t => existT _ 8 t
  end.
Definition MCCH_RepetitionPeriodAndOffset_r17__g := (fun n => typ_set (get_nth_typ MCCH_RepetitionPeriodAndOffset_r17__list n)).
Definition MCCH_RepetitionPeriodAndOffset_r17__F2 (y : choice MCCH_RepetitionPeriodAndOffset_r17__list) : MCCH_RepetitionPeriodAndOffset_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MCCH_RepetitionPeriodAndOffset_r17__g n -> MCCH_RepetitionPeriodAndOffset_r17__Type) with
    | 0 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf1_r17 t 
    | 1 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf2_r17 t 
    | 2 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf4_r17 t 
    | 3 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf8_r17 t 
    | 4 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf16_r17 t 
    | 5 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf32_r17 t 
    | 6 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf64_r17 t 
    | 7 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf128_r17 t 
    | 8 => fun (t : Z) => MCCH_RepetitionPeriodAndOffset_r17__rf256_r17 t 
 | (S (S (S (S (S (S (S (S (S n0))))))))) => (fun (x' : nat) (t'' : MCCH_RepetitionPeriodAndOffset_r17__g (S (S (S (S (S (S (S (S (S x')))))))))) =>let t' :=
           eq_rect (get_nth_typ MCCH_RepetitionPeriodAndOffset_r17__list (S (S (S (S (S (S (S (S (S x'))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MCCH_RepetitionPeriodAndOffset_r17__list (S (S (S (S (S (S (S (S (S x')))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))) in match t' return MCCH_RepetitionPeriodAndOffset_r17__Type with end) n0
           end t0).

Lemma MCCH_RepetitionPeriodAndOffset_r17__helper2 :  forall (y : MCCH_RepetitionPeriodAndOffset_r17__Type), MCCH_RepetitionPeriodAndOffset_r17__cond y -> choice_cond MCCH_RepetitionPeriodAndOffset_r17__list (MCCH_RepetitionPeriodAndOffset_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MCCH_RepetitionPeriodAndOffset_r17__helper3 :  forall (y : MCCH_RepetitionPeriodAndOffset_r17__Type), MCCH_RepetitionPeriodAndOffset_r17__F2 (MCCH_RepetitionPeriodAndOffset_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MCCH_RepetitionPeriodAndOffset_r17__helper4 : (forall b : choice MCCH_RepetitionPeriodAndOffset_r17__list, choice_cond MCCH_RepetitionPeriodAndOffset_r17__list b -> MCCH_RepetitionPeriodAndOffset_r17__cond (MCCH_RepetitionPeriodAndOffset_r17__F2 b) /\ MCCH_RepetitionPeriodAndOffset_r17__F1 (MCCH_RepetitionPeriodAndOffset_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MCCH_RepetitionPeriodAndOffset_r17__F1 MCCH_RepetitionPeriodAndOffset_r17__F2.
Definition MCCH_RepetitionPeriodAndOffset_r17__Format : T_Format MCCH_RepetitionPeriodAndOffset_r17__Type MCCH_RepetitionPeriodAndOffset_r17__cond :=
  (* Eval compute in *) proj2_format MCCH_RepetitionPeriodAndOffset_r17__cond MCCH_RepetitionPeriodAndOffset_r17__list__Format MCCH_RepetitionPeriodAndOffset_r17__F1 MCCH_RepetitionPeriodAndOffset_r17__F2 MCCH_RepetitionPeriodAndOffset_r17__helper2 MCCH_RepetitionPeriodAndOffset_r17__helper3 MCCH_RepetitionPeriodAndOffset_r17__helper4.
Opaque MCCH_RepetitionPeriodAndOffset_r17__cond MCCH_RepetitionPeriodAndOffset_r17__Format.

