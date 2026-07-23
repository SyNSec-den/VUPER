Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MTCH_SSB_MappingWindowCycleOffset_r17__ms10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms10__Type := Z.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MTCH_SSB_MappingWindowCycleOffset_r17__ms20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms20__Type := Z.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MTCH_SSB_MappingWindowCycleOffset_r17__ms32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms32__Type := Z.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MTCH_SSB_MappingWindowCycleOffset_r17__ms64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms64__Type := Z.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms128__helper1 : (0 <= 127)%Z.  lia. Qed.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms128__helper2 : to_bit_sz (Z.to_nat (127 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (127 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MTCH_SSB_MappingWindowCycleOffset_r17__ms128__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms128__Type := Z.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms128__cond := (fun z => (0 <= z <= 127)%Z).
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms256__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__ms256__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MTCH_SSB_MappingWindowCycleOffset_r17__ms256__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms256__Type := Z.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms256__cond := (fun z => (0 <= z <= 255)%Z).

Inductive MTCH_SSB_MappingWindowCycleOffset_r17__Type : Set :=
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms10 : Z -> MTCH_SSB_MappingWindowCycleOffset_r17__Type
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms20 : Z -> MTCH_SSB_MappingWindowCycleOffset_r17__Type
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms32 : Z -> MTCH_SSB_MappingWindowCycleOffset_r17__Type
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms64 : Z -> MTCH_SSB_MappingWindowCycleOffset_r17__Type
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms128 : Z -> MTCH_SSB_MappingWindowCycleOffset_r17__Type
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms256 : Z -> MTCH_SSB_MappingWindowCycleOffset_r17__Type
.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__list : list typ := (
typ_cons Z MTCH_SSB_MappingWindowCycleOffset_r17__ms10__cond ::
typ_cons Z MTCH_SSB_MappingWindowCycleOffset_r17__ms20__cond ::
typ_cons Z MTCH_SSB_MappingWindowCycleOffset_r17__ms32__cond ::
typ_cons Z MTCH_SSB_MappingWindowCycleOffset_r17__ms64__cond ::
typ_cons Z MTCH_SSB_MappingWindowCycleOffset_r17__ms128__cond ::
typ_cons Z MTCH_SSB_MappingWindowCycleOffset_r17__ms256__cond ::
 nil).
Definition MTCH_SSB_MappingWindowCycleOffset_r17__cond (c : MTCH_SSB_MappingWindowCycleOffset_r17__Type) := 
  match c with
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms10 t => MTCH_SSB_MappingWindowCycleOffset_r17__ms10__cond t 
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms20 t => MTCH_SSB_MappingWindowCycleOffset_r17__ms20__cond t 
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms32 t => MTCH_SSB_MappingWindowCycleOffset_r17__ms32__cond t 
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms64 t => MTCH_SSB_MappingWindowCycleOffset_r17__ms64__cond t 
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms128 t => MTCH_SSB_MappingWindowCycleOffset_r17__ms128__cond t 
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms256 t => MTCH_SSB_MappingWindowCycleOffset_r17__ms256__cond t 
  end.

Lemma MTCH_SSB_MappingWindowCycleOffset_r17__len_helper1 : to_bit_sz (length MTCH_SSB_MappingWindowCycleOffset_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__len_helper2 : 2 <= length2 MTCH_SSB_MappingWindowCycleOffset_r17__list.
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
Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms10__Format : T_Format Z MTCH_SSB_MappingWindowCycleOffset_r17__ms10__cond :=
 ranged_int_format (0) (9) MTCH_SSB_MappingWindowCycleOffset_r17__ms10__helper1 MTCH_SSB_MappingWindowCycleOffset_r17__ms10__helper2.

Opaque MTCH_SSB_MappingWindowCycleOffset_r17__ms10__cond MTCH_SSB_MappingWindowCycleOffset_r17__ms10__Format.

Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms20__Format : T_Format Z MTCH_SSB_MappingWindowCycleOffset_r17__ms20__cond :=
 ranged_int_format (0) (19) MTCH_SSB_MappingWindowCycleOffset_r17__ms20__helper1 MTCH_SSB_MappingWindowCycleOffset_r17__ms20__helper2.

Opaque MTCH_SSB_MappingWindowCycleOffset_r17__ms20__cond MTCH_SSB_MappingWindowCycleOffset_r17__ms20__Format.

Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms32__Format : T_Format Z MTCH_SSB_MappingWindowCycleOffset_r17__ms32__cond :=
 ranged_int_format (0) (31) MTCH_SSB_MappingWindowCycleOffset_r17__ms32__helper1 MTCH_SSB_MappingWindowCycleOffset_r17__ms32__helper2.

Opaque MTCH_SSB_MappingWindowCycleOffset_r17__ms32__cond MTCH_SSB_MappingWindowCycleOffset_r17__ms32__Format.

Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms64__Format : T_Format Z MTCH_SSB_MappingWindowCycleOffset_r17__ms64__cond :=
 ranged_int_format (0) (63) MTCH_SSB_MappingWindowCycleOffset_r17__ms64__helper1 MTCH_SSB_MappingWindowCycleOffset_r17__ms64__helper2.

Opaque MTCH_SSB_MappingWindowCycleOffset_r17__ms64__cond MTCH_SSB_MappingWindowCycleOffset_r17__ms64__Format.

Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms128__Format : T_Format Z MTCH_SSB_MappingWindowCycleOffset_r17__ms128__cond :=
 ranged_int_format (0) (127) MTCH_SSB_MappingWindowCycleOffset_r17__ms128__helper1 MTCH_SSB_MappingWindowCycleOffset_r17__ms128__helper2.

Opaque MTCH_SSB_MappingWindowCycleOffset_r17__ms128__cond MTCH_SSB_MappingWindowCycleOffset_r17__ms128__Format.

Definition MTCH_SSB_MappingWindowCycleOffset_r17__ms256__Format : T_Format Z MTCH_SSB_MappingWindowCycleOffset_r17__ms256__cond :=
 ranged_int_format (0) (255) MTCH_SSB_MappingWindowCycleOffset_r17__ms256__helper1 MTCH_SSB_MappingWindowCycleOffset_r17__ms256__helper2.

Opaque MTCH_SSB_MappingWindowCycleOffset_r17__ms256__cond MTCH_SSB_MappingWindowCycleOffset_r17__ms256__Format.


Definition MTCH_SSB_MappingWindowCycleOffset_r17__Format_Type := Eval cbn in get_formats MTCH_SSB_MappingWindowCycleOffset_r17__list.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__Format_list : MTCH_SSB_MappingWindowCycleOffset_r17__Format_Type :=
  (MTCH_SSB_MappingWindowCycleOffset_r17__ms10__Format, (MTCH_SSB_MappingWindowCycleOffset_r17__ms20__Format, (MTCH_SSB_MappingWindowCycleOffset_r17__ms32__Format, (MTCH_SSB_MappingWindowCycleOffset_r17__ms64__Format, (MTCH_SSB_MappingWindowCycleOffset_r17__ms128__Format, (MTCH_SSB_MappingWindowCycleOffset_r17__ms256__Format, unit__Format)))))).
Definition MTCH_SSB_MappingWindowCycleOffset_r17__list__Format := Eval compute in choice_format MTCH_SSB_MappingWindowCycleOffset_r17__list MTCH_SSB_MappingWindowCycleOffset_r17__len_helper1 MTCH_SSB_MappingWindowCycleOffset_r17__len_helper2  MTCH_SSB_MappingWindowCycleOffset_r17__Format_list.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__F1 (z : MTCH_SSB_MappingWindowCycleOffset_r17__Type) : (choice MTCH_SSB_MappingWindowCycleOffset_r17__list) :=
  match z with
   | MTCH_SSB_MappingWindowCycleOffset_r17__ms10 t => existT _ 0 t
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms20 t => existT _ 1 t
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms32 t => existT _ 2 t
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms64 t => existT _ 3 t
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms128 t => existT _ 4 t
  | MTCH_SSB_MappingWindowCycleOffset_r17__ms256 t => existT _ 5 t
  end.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__g := (fun n => typ_set (get_nth_typ MTCH_SSB_MappingWindowCycleOffset_r17__list n)).
Definition MTCH_SSB_MappingWindowCycleOffset_r17__F2 (y : choice MTCH_SSB_MappingWindowCycleOffset_r17__list) : MTCH_SSB_MappingWindowCycleOffset_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MTCH_SSB_MappingWindowCycleOffset_r17__g n -> MTCH_SSB_MappingWindowCycleOffset_r17__Type) with
    | 0 => fun (t : Z) => MTCH_SSB_MappingWindowCycleOffset_r17__ms10 t 
    | 1 => fun (t : Z) => MTCH_SSB_MappingWindowCycleOffset_r17__ms20 t 
    | 2 => fun (t : Z) => MTCH_SSB_MappingWindowCycleOffset_r17__ms32 t 
    | 3 => fun (t : Z) => MTCH_SSB_MappingWindowCycleOffset_r17__ms64 t 
    | 4 => fun (t : Z) => MTCH_SSB_MappingWindowCycleOffset_r17__ms128 t 
    | 5 => fun (t : Z) => MTCH_SSB_MappingWindowCycleOffset_r17__ms256 t 
 | (S (S (S (S (S (S n0)))))) => (fun (x' : nat) (t'' : MTCH_SSB_MappingWindowCycleOffset_r17__g (S (S (S (S (S (S x'))))))) =>let t' :=
           eq_rect (get_nth_typ MTCH_SSB_MappingWindowCycleOffset_r17__list (S (S (S (S (S (S x')))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MTCH_SSB_MappingWindowCycleOffset_r17__list (S (S (S (S (S (S x'))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))) in match t' return MTCH_SSB_MappingWindowCycleOffset_r17__Type with end) n0
           end t0).

Lemma MTCH_SSB_MappingWindowCycleOffset_r17__helper2 :  forall (y : MTCH_SSB_MappingWindowCycleOffset_r17__Type), MTCH_SSB_MappingWindowCycleOffset_r17__cond y -> choice_cond MTCH_SSB_MappingWindowCycleOffset_r17__list (MTCH_SSB_MappingWindowCycleOffset_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MTCH_SSB_MappingWindowCycleOffset_r17__helper3 :  forall (y : MTCH_SSB_MappingWindowCycleOffset_r17__Type), MTCH_SSB_MappingWindowCycleOffset_r17__F2 (MTCH_SSB_MappingWindowCycleOffset_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MTCH_SSB_MappingWindowCycleOffset_r17__helper4 : (forall b : choice MTCH_SSB_MappingWindowCycleOffset_r17__list, choice_cond MTCH_SSB_MappingWindowCycleOffset_r17__list b -> MTCH_SSB_MappingWindowCycleOffset_r17__cond (MTCH_SSB_MappingWindowCycleOffset_r17__F2 b) /\ MTCH_SSB_MappingWindowCycleOffset_r17__F1 (MTCH_SSB_MappingWindowCycleOffset_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MTCH_SSB_MappingWindowCycleOffset_r17__F1 MTCH_SSB_MappingWindowCycleOffset_r17__F2.
Definition MTCH_SSB_MappingWindowCycleOffset_r17__Format : T_Format MTCH_SSB_MappingWindowCycleOffset_r17__Type MTCH_SSB_MappingWindowCycleOffset_r17__cond :=
  (* Eval compute in *) proj2_format MTCH_SSB_MappingWindowCycleOffset_r17__cond MTCH_SSB_MappingWindowCycleOffset_r17__list__Format MTCH_SSB_MappingWindowCycleOffset_r17__F1 MTCH_SSB_MappingWindowCycleOffset_r17__F2 MTCH_SSB_MappingWindowCycleOffset_r17__helper2 MTCH_SSB_MappingWindowCycleOffset_r17__helper3 MTCH_SSB_MappingWindowCycleOffset_r17__helper4.
Opaque MTCH_SSB_MappingWindowCycleOffset_r17__cond MTCH_SSB_MappingWindowCycleOffset_r17__Format.

