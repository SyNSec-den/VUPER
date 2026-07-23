Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BetaOffsetsCrossPri_r17.

Opaque BetaOffsetsCrossPri_r17__cond BetaOffsetsCrossPri_r17__Format.

Definition BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Type := list BetaOffsetsCrossPri_r17__Type.

Lemma BetaOffsetsCrossPriSelCG_r17__dynamic_r17__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma BetaOffsetsCrossPriSelCG_r17__dynamic_r17__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BetaOffsetsCrossPriSelCG_r17__dynamic_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BetaOffsetsCrossPriSelCG_r17__dynamic_r17__cond (z : BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and BetaOffsetsCrossPri_r17__cond z) .

Require Import NR.BetaOffsetsCrossPri_r17.

Opaque BetaOffsetsCrossPri_r17__cond BetaOffsetsCrossPri_r17__Format.


Inductive BetaOffsetsCrossPriSelCG_r17__Type : Set :=
  | BetaOffsetsCrossPriSelCG_r17__dynamic_r17 : BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Type -> BetaOffsetsCrossPriSelCG_r17__Type
  | BetaOffsetsCrossPriSelCG_r17__semiStatic_r17 : BetaOffsetsCrossPri_r17__Type -> BetaOffsetsCrossPriSelCG_r17__Type
.
Definition BetaOffsetsCrossPriSelCG_r17__list : list typ := (
typ_cons BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Type BetaOffsetsCrossPriSelCG_r17__dynamic_r17__cond ::
typ_cons BetaOffsetsCrossPri_r17__Type BetaOffsetsCrossPri_r17__cond ::
 nil).
Definition BetaOffsetsCrossPriSelCG_r17__cond (c : BetaOffsetsCrossPriSelCG_r17__Type) := 
  match c with
  | BetaOffsetsCrossPriSelCG_r17__dynamic_r17 t => BetaOffsetsCrossPriSelCG_r17__dynamic_r17__cond t 
  | BetaOffsetsCrossPriSelCG_r17__semiStatic_r17 t => BetaOffsetsCrossPri_r17__cond t 
  end.

Lemma BetaOffsetsCrossPriSelCG_r17__len_helper1 : to_bit_sz (length BetaOffsetsCrossPriSelCG_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BetaOffsetsCrossPriSelCG_r17__len_helper2 : 2 <= length2 BetaOffsetsCrossPriSelCG_r17__list.
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
Definition BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Format : T_Format BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Type BetaOffsetsCrossPriSelCG_r17__dynamic_r17__cond := seq_of_format BetaOffsetsCrossPri_r17__Format 1 4 BetaOffsetsCrossPriSelCG_r17__dynamic_r17__helper1 BetaOffsetsCrossPriSelCG_r17__dynamic_r17__helper2.

Opaque BetaOffsetsCrossPriSelCG_r17__dynamic_r17__cond BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Format.


Definition BetaOffsetsCrossPriSelCG_r17__Format_Type := Eval cbn in get_formats BetaOffsetsCrossPriSelCG_r17__list.
Definition BetaOffsetsCrossPriSelCG_r17__Format_list : BetaOffsetsCrossPriSelCG_r17__Format_Type :=
  (BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Format, (BetaOffsetsCrossPri_r17__Format, unit__Format)).
Definition BetaOffsetsCrossPriSelCG_r17__list__Format := Eval compute in choice_format BetaOffsetsCrossPriSelCG_r17__list BetaOffsetsCrossPriSelCG_r17__len_helper1 BetaOffsetsCrossPriSelCG_r17__len_helper2  BetaOffsetsCrossPriSelCG_r17__Format_list.
Definition BetaOffsetsCrossPriSelCG_r17__F1 (z : BetaOffsetsCrossPriSelCG_r17__Type) : (choice BetaOffsetsCrossPriSelCG_r17__list) :=
  match z with
   | BetaOffsetsCrossPriSelCG_r17__dynamic_r17 t => existT _ 0 t
  | BetaOffsetsCrossPriSelCG_r17__semiStatic_r17 t => existT _ 1 t
  end.
Definition BetaOffsetsCrossPriSelCG_r17__g := (fun n => typ_set (get_nth_typ BetaOffsetsCrossPriSelCG_r17__list n)).
Definition BetaOffsetsCrossPriSelCG_r17__F2 (y : choice BetaOffsetsCrossPriSelCG_r17__list) : BetaOffsetsCrossPriSelCG_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BetaOffsetsCrossPriSelCG_r17__g n -> BetaOffsetsCrossPriSelCG_r17__Type) with
    | 0 => fun (t : BetaOffsetsCrossPriSelCG_r17__dynamic_r17__Type) => BetaOffsetsCrossPriSelCG_r17__dynamic_r17 t 
    | 1 => fun (t : BetaOffsetsCrossPri_r17__Type) => BetaOffsetsCrossPriSelCG_r17__semiStatic_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BetaOffsetsCrossPriSelCG_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BetaOffsetsCrossPriSelCG_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BetaOffsetsCrossPriSelCG_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BetaOffsetsCrossPriSelCG_r17__Type with end) n0
           end t0).

Lemma BetaOffsetsCrossPriSelCG_r17__helper2 :  forall (y : BetaOffsetsCrossPriSelCG_r17__Type), BetaOffsetsCrossPriSelCG_r17__cond y -> choice_cond BetaOffsetsCrossPriSelCG_r17__list (BetaOffsetsCrossPriSelCG_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BetaOffsetsCrossPriSelCG_r17__helper3 :  forall (y : BetaOffsetsCrossPriSelCG_r17__Type), BetaOffsetsCrossPriSelCG_r17__F2 (BetaOffsetsCrossPriSelCG_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BetaOffsetsCrossPriSelCG_r17__helper4 : (forall b : choice BetaOffsetsCrossPriSelCG_r17__list, choice_cond BetaOffsetsCrossPriSelCG_r17__list b -> BetaOffsetsCrossPriSelCG_r17__cond (BetaOffsetsCrossPriSelCG_r17__F2 b) /\ BetaOffsetsCrossPriSelCG_r17__F1 (BetaOffsetsCrossPriSelCG_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BetaOffsetsCrossPriSelCG_r17__F1 BetaOffsetsCrossPriSelCG_r17__F2.
Definition BetaOffsetsCrossPriSelCG_r17__Format : T_Format BetaOffsetsCrossPriSelCG_r17__Type BetaOffsetsCrossPriSelCG_r17__cond :=
  (* Eval compute in *) proj2_format BetaOffsetsCrossPriSelCG_r17__cond BetaOffsetsCrossPriSelCG_r17__list__Format BetaOffsetsCrossPriSelCG_r17__F1 BetaOffsetsCrossPriSelCG_r17__F2 BetaOffsetsCrossPriSelCG_r17__helper2 BetaOffsetsCrossPriSelCG_r17__helper3 BetaOffsetsCrossPriSelCG_r17__helper4.
Opaque BetaOffsetsCrossPriSelCG_r17__cond BetaOffsetsCrossPriSelCG_r17__Format.

