Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma RSSI_PeriodicityAndOffset_r16__root__sl10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma RSSI_PeriodicityAndOffset_r16__root__sl10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_PeriodicityAndOffset_r16__root__sl10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_PeriodicityAndOffset_r16__root__sl10__Type := Z.
Definition RSSI_PeriodicityAndOffset_r16__root__sl10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma RSSI_PeriodicityAndOffset_r16__root__sl20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma RSSI_PeriodicityAndOffset_r16__root__sl20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_PeriodicityAndOffset_r16__root__sl20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_PeriodicityAndOffset_r16__root__sl20__Type := Z.
Definition RSSI_PeriodicityAndOffset_r16__root__sl20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma RSSI_PeriodicityAndOffset_r16__root__sl40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma RSSI_PeriodicityAndOffset_r16__root__sl40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_PeriodicityAndOffset_r16__root__sl40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_PeriodicityAndOffset_r16__root__sl40__Type := Z.
Definition RSSI_PeriodicityAndOffset_r16__root__sl40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma RSSI_PeriodicityAndOffset_r16__root__sl80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma RSSI_PeriodicityAndOffset_r16__root__sl80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_PeriodicityAndOffset_r16__root__sl80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_PeriodicityAndOffset_r16__root__sl80__Type := Z.
Definition RSSI_PeriodicityAndOffset_r16__root__sl80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma RSSI_PeriodicityAndOffset_r16__root__sl160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma RSSI_PeriodicityAndOffset_r16__root__sl160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_PeriodicityAndOffset_r16__root__sl160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_PeriodicityAndOffset_r16__root__sl160__Type := Z.
Definition RSSI_PeriodicityAndOffset_r16__root__sl160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma RSSI_PeriodicityAndOffset_r16__root__sl320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma RSSI_PeriodicityAndOffset_r16__root__sl320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_PeriodicityAndOffset_r16__root__sl320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_PeriodicityAndOffset_r16__root__sl320__Type := Z.
Definition RSSI_PeriodicityAndOffset_r16__root__sl320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma RSSI_PeriodicityAndOffset_r16__root__s1640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma RSSI_PeriodicityAndOffset_r16__root__s1640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RSSI_PeriodicityAndOffset_r16__root__s1640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RSSI_PeriodicityAndOffset_r16__root__s1640__Type := Z.
Definition RSSI_PeriodicityAndOffset_r16__root__s1640__cond := (fun z => (0 <= z <= 639)%Z).

Inductive RSSI_PeriodicityAndOffset_r16__root__Type : Set :=
  | RSSI_PeriodicityAndOffset_r16__root__sl10 : Z -> RSSI_PeriodicityAndOffset_r16__root__Type
  | RSSI_PeriodicityAndOffset_r16__root__sl20 : Z -> RSSI_PeriodicityAndOffset_r16__root__Type
  | RSSI_PeriodicityAndOffset_r16__root__sl40 : Z -> RSSI_PeriodicityAndOffset_r16__root__Type
  | RSSI_PeriodicityAndOffset_r16__root__sl80 : Z -> RSSI_PeriodicityAndOffset_r16__root__Type
  | RSSI_PeriodicityAndOffset_r16__root__sl160 : Z -> RSSI_PeriodicityAndOffset_r16__root__Type
  | RSSI_PeriodicityAndOffset_r16__root__sl320 : Z -> RSSI_PeriodicityAndOffset_r16__root__Type
  | RSSI_PeriodicityAndOffset_r16__root__s1640 : Z -> RSSI_PeriodicityAndOffset_r16__root__Type
.
Definition RSSI_PeriodicityAndOffset_r16__root__list : list typ := (
typ_cons Z RSSI_PeriodicityAndOffset_r16__root__sl10__cond ::
typ_cons Z RSSI_PeriodicityAndOffset_r16__root__sl20__cond ::
typ_cons Z RSSI_PeriodicityAndOffset_r16__root__sl40__cond ::
typ_cons Z RSSI_PeriodicityAndOffset_r16__root__sl80__cond ::
typ_cons Z RSSI_PeriodicityAndOffset_r16__root__sl160__cond ::
typ_cons Z RSSI_PeriodicityAndOffset_r16__root__sl320__cond ::
typ_cons Z RSSI_PeriodicityAndOffset_r16__root__s1640__cond ::
 nil).
Definition RSSI_PeriodicityAndOffset_r16__root__cond (c : RSSI_PeriodicityAndOffset_r16__root__Type) := 
  match c with
  | RSSI_PeriodicityAndOffset_r16__root__sl10 t => RSSI_PeriodicityAndOffset_r16__root__sl10__cond t 
  | RSSI_PeriodicityAndOffset_r16__root__sl20 t => RSSI_PeriodicityAndOffset_r16__root__sl20__cond t 
  | RSSI_PeriodicityAndOffset_r16__root__sl40 t => RSSI_PeriodicityAndOffset_r16__root__sl40__cond t 
  | RSSI_PeriodicityAndOffset_r16__root__sl80 t => RSSI_PeriodicityAndOffset_r16__root__sl80__cond t 
  | RSSI_PeriodicityAndOffset_r16__root__sl160 t => RSSI_PeriodicityAndOffset_r16__root__sl160__cond t 
  | RSSI_PeriodicityAndOffset_r16__root__sl320 t => RSSI_PeriodicityAndOffset_r16__root__sl320__cond t 
  | RSSI_PeriodicityAndOffset_r16__root__s1640 t => RSSI_PeriodicityAndOffset_r16__root__s1640__cond t 
  end.

Lemma RSSI_PeriodicityAndOffset_r16__root__len_helper1 : to_bit_sz (length RSSI_PeriodicityAndOffset_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RSSI_PeriodicityAndOffset_r16__root__len_helper2 : 2 <= length2 RSSI_PeriodicityAndOffset_r16__root__list.
 simpl. lia. Qed.

Definition RSSI_PeriodicityAndOffset_r16__ext__Type : Set := Empty_set.
Definition RSSI_PeriodicityAndOffset_r16__ext__cond (c : RSSI_PeriodicityAndOffset_r16__ext__Type) := True.
Definition RSSI_PeriodicityAndOffset_r16__Type : Set := RSSI_PeriodicityAndOffset_r16__root__Type + RSSI_PeriodicityAndOffset_r16__ext__Type.
Definition RSSI_PeriodicityAndOffset_r16__cond :=
  sum_cond RSSI_PeriodicityAndOffset_r16__root__cond RSSI_PeriodicityAndOffset_r16__ext__cond.

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
Definition RSSI_PeriodicityAndOffset_r16__root__sl10__Format : T_Format Z RSSI_PeriodicityAndOffset_r16__root__sl10__cond :=
 ranged_int_format (0) (9) RSSI_PeriodicityAndOffset_r16__root__sl10__helper1 RSSI_PeriodicityAndOffset_r16__root__sl10__helper2.

Opaque RSSI_PeriodicityAndOffset_r16__root__sl10__cond RSSI_PeriodicityAndOffset_r16__root__sl10__Format.

Definition RSSI_PeriodicityAndOffset_r16__root__sl20__Format : T_Format Z RSSI_PeriodicityAndOffset_r16__root__sl20__cond :=
 ranged_int_format (0) (19) RSSI_PeriodicityAndOffset_r16__root__sl20__helper1 RSSI_PeriodicityAndOffset_r16__root__sl20__helper2.

Opaque RSSI_PeriodicityAndOffset_r16__root__sl20__cond RSSI_PeriodicityAndOffset_r16__root__sl20__Format.

Definition RSSI_PeriodicityAndOffset_r16__root__sl40__Format : T_Format Z RSSI_PeriodicityAndOffset_r16__root__sl40__cond :=
 ranged_int_format (0) (39) RSSI_PeriodicityAndOffset_r16__root__sl40__helper1 RSSI_PeriodicityAndOffset_r16__root__sl40__helper2.

Opaque RSSI_PeriodicityAndOffset_r16__root__sl40__cond RSSI_PeriodicityAndOffset_r16__root__sl40__Format.

Definition RSSI_PeriodicityAndOffset_r16__root__sl80__Format : T_Format Z RSSI_PeriodicityAndOffset_r16__root__sl80__cond :=
 ranged_int_format (0) (79) RSSI_PeriodicityAndOffset_r16__root__sl80__helper1 RSSI_PeriodicityAndOffset_r16__root__sl80__helper2.

Opaque RSSI_PeriodicityAndOffset_r16__root__sl80__cond RSSI_PeriodicityAndOffset_r16__root__sl80__Format.

Definition RSSI_PeriodicityAndOffset_r16__root__sl160__Format : T_Format Z RSSI_PeriodicityAndOffset_r16__root__sl160__cond :=
 ranged_int_format (0) (159) RSSI_PeriodicityAndOffset_r16__root__sl160__helper1 RSSI_PeriodicityAndOffset_r16__root__sl160__helper2.

Opaque RSSI_PeriodicityAndOffset_r16__root__sl160__cond RSSI_PeriodicityAndOffset_r16__root__sl160__Format.

Definition RSSI_PeriodicityAndOffset_r16__root__sl320__Format : T_Format Z RSSI_PeriodicityAndOffset_r16__root__sl320__cond :=
 ranged_int_format (0) (319) RSSI_PeriodicityAndOffset_r16__root__sl320__helper1 RSSI_PeriodicityAndOffset_r16__root__sl320__helper2.

Opaque RSSI_PeriodicityAndOffset_r16__root__sl320__cond RSSI_PeriodicityAndOffset_r16__root__sl320__Format.

Definition RSSI_PeriodicityAndOffset_r16__root__s1640__Format : T_Format Z RSSI_PeriodicityAndOffset_r16__root__s1640__cond :=
 ranged_int_format (0) (639) RSSI_PeriodicityAndOffset_r16__root__s1640__helper1 RSSI_PeriodicityAndOffset_r16__root__s1640__helper2.

Opaque RSSI_PeriodicityAndOffset_r16__root__s1640__cond RSSI_PeriodicityAndOffset_r16__root__s1640__Format.


Definition RSSI_PeriodicityAndOffset_r16__root__Format_Type := Eval cbn in get_formats RSSI_PeriodicityAndOffset_r16__root__list.
Definition RSSI_PeriodicityAndOffset_r16__root__Format_list : RSSI_PeriodicityAndOffset_r16__root__Format_Type :=
  (RSSI_PeriodicityAndOffset_r16__root__sl10__Format, (RSSI_PeriodicityAndOffset_r16__root__sl20__Format, (RSSI_PeriodicityAndOffset_r16__root__sl40__Format, (RSSI_PeriodicityAndOffset_r16__root__sl80__Format, (RSSI_PeriodicityAndOffset_r16__root__sl160__Format, (RSSI_PeriodicityAndOffset_r16__root__sl320__Format, (RSSI_PeriodicityAndOffset_r16__root__s1640__Format, unit__Format))))))).
Definition RSSI_PeriodicityAndOffset_r16__root__list__Format := Eval compute in choice_format RSSI_PeriodicityAndOffset_r16__root__list RSSI_PeriodicityAndOffset_r16__root__len_helper1 RSSI_PeriodicityAndOffset_r16__root__len_helper2  RSSI_PeriodicityAndOffset_r16__root__Format_list.
Definition RSSI_PeriodicityAndOffset_r16__root__F1 (z : RSSI_PeriodicityAndOffset_r16__root__Type) : (choice RSSI_PeriodicityAndOffset_r16__root__list) :=
  match z with
   | RSSI_PeriodicityAndOffset_r16__root__sl10 t => existT _ 0 t
  | RSSI_PeriodicityAndOffset_r16__root__sl20 t => existT _ 1 t
  | RSSI_PeriodicityAndOffset_r16__root__sl40 t => existT _ 2 t
  | RSSI_PeriodicityAndOffset_r16__root__sl80 t => existT _ 3 t
  | RSSI_PeriodicityAndOffset_r16__root__sl160 t => existT _ 4 t
  | RSSI_PeriodicityAndOffset_r16__root__sl320 t => existT _ 5 t
  | RSSI_PeriodicityAndOffset_r16__root__s1640 t => existT _ 6 t
  end.
Definition RSSI_PeriodicityAndOffset_r16__root__g := (fun n => typ_set (get_nth_typ RSSI_PeriodicityAndOffset_r16__root__list n)).
Definition RSSI_PeriodicityAndOffset_r16__root__F2 (y : choice RSSI_PeriodicityAndOffset_r16__root__list) : RSSI_PeriodicityAndOffset_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RSSI_PeriodicityAndOffset_r16__root__g n -> RSSI_PeriodicityAndOffset_r16__root__Type) with
    | 0 => fun (t : Z) => RSSI_PeriodicityAndOffset_r16__root__sl10 t 
    | 1 => fun (t : Z) => RSSI_PeriodicityAndOffset_r16__root__sl20 t 
    | 2 => fun (t : Z) => RSSI_PeriodicityAndOffset_r16__root__sl40 t 
    | 3 => fun (t : Z) => RSSI_PeriodicityAndOffset_r16__root__sl80 t 
    | 4 => fun (t : Z) => RSSI_PeriodicityAndOffset_r16__root__sl160 t 
    | 5 => fun (t : Z) => RSSI_PeriodicityAndOffset_r16__root__sl320 t 
    | 6 => fun (t : Z) => RSSI_PeriodicityAndOffset_r16__root__s1640 t 
 | (S (S (S (S (S (S (S n0))))))) => (fun (x' : nat) (t'' : RSSI_PeriodicityAndOffset_r16__root__g (S (S (S (S (S (S (S x')))))))) =>let t' :=
           eq_rect (get_nth_typ RSSI_PeriodicityAndOffset_r16__root__list (S (S (S (S (S (S (S x'))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RSSI_PeriodicityAndOffset_r16__root__list (S (S (S (S (S (S (S x')))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))) in match t' return RSSI_PeriodicityAndOffset_r16__root__Type with end) n0
           end t0).

Lemma RSSI_PeriodicityAndOffset_r16__root__helper2 :  forall (y : RSSI_PeriodicityAndOffset_r16__root__Type), RSSI_PeriodicityAndOffset_r16__root__cond y -> choice_cond RSSI_PeriodicityAndOffset_r16__root__list (RSSI_PeriodicityAndOffset_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RSSI_PeriodicityAndOffset_r16__root__helper3 :  forall (y : RSSI_PeriodicityAndOffset_r16__root__Type), RSSI_PeriodicityAndOffset_r16__root__F2 (RSSI_PeriodicityAndOffset_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RSSI_PeriodicityAndOffset_r16__root__helper4 : (forall b : choice RSSI_PeriodicityAndOffset_r16__root__list, choice_cond RSSI_PeriodicityAndOffset_r16__root__list b -> RSSI_PeriodicityAndOffset_r16__root__cond (RSSI_PeriodicityAndOffset_r16__root__F2 b) /\ RSSI_PeriodicityAndOffset_r16__root__F1 (RSSI_PeriodicityAndOffset_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RSSI_PeriodicityAndOffset_r16__root__F1 RSSI_PeriodicityAndOffset_r16__root__F2.
Definition RSSI_PeriodicityAndOffset_r16__root__Format : T_Format RSSI_PeriodicityAndOffset_r16__root__Type RSSI_PeriodicityAndOffset_r16__root__cond :=
  (* Eval compute in *) proj2_format RSSI_PeriodicityAndOffset_r16__root__cond RSSI_PeriodicityAndOffset_r16__root__list__Format RSSI_PeriodicityAndOffset_r16__root__F1 RSSI_PeriodicityAndOffset_r16__root__F2 RSSI_PeriodicityAndOffset_r16__root__helper2 RSSI_PeriodicityAndOffset_r16__root__helper3 RSSI_PeriodicityAndOffset_r16__root__helper4.
Opaque RSSI_PeriodicityAndOffset_r16__root__cond RSSI_PeriodicityAndOffset_r16__root__Format.

Definition RSSI_PeriodicityAndOffset_r16__ext__Format : T_Format RSSI_PeriodicityAndOffset_r16__ext__Type RSSI_PeriodicityAndOffset_r16__ext__cond := empty_format.
Opaque RSSI_PeriodicityAndOffset_r16__ext__cond RSSI_PeriodicityAndOffset_r16__ext__Format.

Definition RSSI_PeriodicityAndOffset_r16__Format : T_Format RSSI_PeriodicityAndOffset_r16__Type RSSI_PeriodicityAndOffset_r16__cond := sum_format RSSI_PeriodicityAndOffset_r16__root__Format RSSI_PeriodicityAndOffset_r16__ext__Format.
Opaque RSSI_PeriodicityAndOffset_r16__cond RSSI_PeriodicityAndOffset_r16__Format.

