Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BetaOffsetsCrossPri_r17.

Opaque BetaOffsetsCrossPri_r17__cond BetaOffsetsCrossPri_r17__Format.

Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Type := list BetaOffsetsCrossPri_r17__Type.

Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__cond (z : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Type) := (list_and BetaOffsetsCrossPri_r17__cond z) /\ (length z = Z.to_nat 2).

Require Import NR.BetaOffsetsCrossPri_r17.

Opaque BetaOffsetsCrossPri_r17__cond BetaOffsetsCrossPri_r17__Format.

Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Type := list BetaOffsetsCrossPri_r17__Type.

Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__cond (z : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Type) := (list_and BetaOffsetsCrossPri_r17__cond z) /\ (length z = Z.to_nat 4).


Inductive BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type : Set :=
  | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17 : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Type -> BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type
  | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17 : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Type -> BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type
.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list : list typ := (
typ_cons BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Type BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__cond ::
typ_cons BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Type BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__cond ::
 nil).
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__cond (c : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type) := 
  match c with
  | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17 t => BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__cond t 
  | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17 t => BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__cond t 
  end.

Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__len_helper1 : to_bit_sz (length BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__len_helper2 : 2 <= length2 BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list.
 simpl. lia. Qed.
Require Import NR.BetaOffsetsCrossPri_r17.

Opaque BetaOffsetsCrossPri_r17__cond BetaOffsetsCrossPri_r17__Format.


Inductive BetaOffsetsCrossPriSelDCI_0_2_r17__Type : Set :=
  | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17 : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type -> BetaOffsetsCrossPriSelDCI_0_2_r17__Type
  | BetaOffsetsCrossPriSelDCI_0_2_r17__semiStaticDCI_0_2_r17 : BetaOffsetsCrossPri_r17__Type -> BetaOffsetsCrossPriSelDCI_0_2_r17__Type
.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__list : list typ := (
typ_cons BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__cond ::
typ_cons BetaOffsetsCrossPri_r17__Type BetaOffsetsCrossPri_r17__cond ::
 nil).
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__cond (c : BetaOffsetsCrossPriSelDCI_0_2_r17__Type) := 
  match c with
  | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17 t => BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__cond t 
  | BetaOffsetsCrossPriSelDCI_0_2_r17__semiStaticDCI_0_2_r17 t => BetaOffsetsCrossPri_r17__cond t 
  end.

Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__len_helper1 : to_bit_sz (length BetaOffsetsCrossPriSelDCI_0_2_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__len_helper2 : 2 <= length2 BetaOffsetsCrossPriSelDCI_0_2_r17__list.
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
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Format : T_Format BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Type BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__cond := seq_of_fixed_format BetaOffsetsCrossPri_r17__Format 2.

Opaque BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__cond BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Format.

Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Format : T_Format BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Type BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__cond := seq_of_fixed_format BetaOffsetsCrossPri_r17__Format 4.

Opaque BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__cond BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Format.


Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Format_Type := Eval cbn in get_formats BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Format_list : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Format_Type :=
  (BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Format, (BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Format, unit__Format)).
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list__Format := Eval compute in choice_format BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__len_helper1 BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__len_helper2  BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Format_list.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F1 (z : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type) : (choice BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list) :=
  match z with
   | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17 t => existT _ 0 t
  | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17 t => existT _ 1 t
  end.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__g := (fun n => typ_set (get_nth_typ BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list n)).
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F2 (y : choice BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list) : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__g n -> BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type) with
    | 0 => fun (t : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17__Type) => BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__oneBit_r17 t 
    | 1 => fun (t : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17__Type) => BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__twoBits_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type with end) n0
           end t0).

Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__helper2 :  forall (y : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type), BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__cond y -> choice_cond BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list (BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__helper3 :  forall (y : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type), BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F2 (BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__helper4 : (forall b : choice BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list, choice_cond BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list b -> BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__cond (BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F2 b) /\ BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F1 (BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F1 BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F2.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Format : T_Format BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__cond :=
  (* Eval compute in *) proj2_format BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__cond BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__list__Format BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F1 BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__F2 BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__helper2 BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__helper3 BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__helper4.
Opaque BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__cond BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Format.


Definition BetaOffsetsCrossPriSelDCI_0_2_r17__Format_Type := Eval cbn in get_formats BetaOffsetsCrossPriSelDCI_0_2_r17__list.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__Format_list : BetaOffsetsCrossPriSelDCI_0_2_r17__Format_Type :=
  (BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Format, (BetaOffsetsCrossPri_r17__Format, unit__Format)).
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__list__Format := Eval compute in choice_format BetaOffsetsCrossPriSelDCI_0_2_r17__list BetaOffsetsCrossPriSelDCI_0_2_r17__len_helper1 BetaOffsetsCrossPriSelDCI_0_2_r17__len_helper2  BetaOffsetsCrossPriSelDCI_0_2_r17__Format_list.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__F1 (z : BetaOffsetsCrossPriSelDCI_0_2_r17__Type) : (choice BetaOffsetsCrossPriSelDCI_0_2_r17__list) :=
  match z with
   | BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17 t => existT _ 0 t
  | BetaOffsetsCrossPriSelDCI_0_2_r17__semiStaticDCI_0_2_r17 t => existT _ 1 t
  end.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__g := (fun n => typ_set (get_nth_typ BetaOffsetsCrossPriSelDCI_0_2_r17__list n)).
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__F2 (y : choice BetaOffsetsCrossPriSelDCI_0_2_r17__list) : BetaOffsetsCrossPriSelDCI_0_2_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BetaOffsetsCrossPriSelDCI_0_2_r17__g n -> BetaOffsetsCrossPriSelDCI_0_2_r17__Type) with
    | 0 => fun (t : BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17__Type) => BetaOffsetsCrossPriSelDCI_0_2_r17__dynamicDCI_0_2_r17 t 
    | 1 => fun (t : BetaOffsetsCrossPri_r17__Type) => BetaOffsetsCrossPriSelDCI_0_2_r17__semiStaticDCI_0_2_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BetaOffsetsCrossPriSelDCI_0_2_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BetaOffsetsCrossPriSelDCI_0_2_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BetaOffsetsCrossPriSelDCI_0_2_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BetaOffsetsCrossPriSelDCI_0_2_r17__Type with end) n0
           end t0).

Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__helper2 :  forall (y : BetaOffsetsCrossPriSelDCI_0_2_r17__Type), BetaOffsetsCrossPriSelDCI_0_2_r17__cond y -> choice_cond BetaOffsetsCrossPriSelDCI_0_2_r17__list (BetaOffsetsCrossPriSelDCI_0_2_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__helper3 :  forall (y : BetaOffsetsCrossPriSelDCI_0_2_r17__Type), BetaOffsetsCrossPriSelDCI_0_2_r17__F2 (BetaOffsetsCrossPriSelDCI_0_2_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BetaOffsetsCrossPriSelDCI_0_2_r17__helper4 : (forall b : choice BetaOffsetsCrossPriSelDCI_0_2_r17__list, choice_cond BetaOffsetsCrossPriSelDCI_0_2_r17__list b -> BetaOffsetsCrossPriSelDCI_0_2_r17__cond (BetaOffsetsCrossPriSelDCI_0_2_r17__F2 b) /\ BetaOffsetsCrossPriSelDCI_0_2_r17__F1 (BetaOffsetsCrossPriSelDCI_0_2_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BetaOffsetsCrossPriSelDCI_0_2_r17__F1 BetaOffsetsCrossPriSelDCI_0_2_r17__F2.
Definition BetaOffsetsCrossPriSelDCI_0_2_r17__Format : T_Format BetaOffsetsCrossPriSelDCI_0_2_r17__Type BetaOffsetsCrossPriSelDCI_0_2_r17__cond :=
  (* Eval compute in *) proj2_format BetaOffsetsCrossPriSelDCI_0_2_r17__cond BetaOffsetsCrossPriSelDCI_0_2_r17__list__Format BetaOffsetsCrossPriSelDCI_0_2_r17__F1 BetaOffsetsCrossPriSelDCI_0_2_r17__F2 BetaOffsetsCrossPriSelDCI_0_2_r17__helper2 BetaOffsetsCrossPriSelDCI_0_2_r17__helper3 BetaOffsetsCrossPriSelDCI_0_2_r17__helper4.
Opaque BetaOffsetsCrossPriSelDCI_0_2_r17__cond BetaOffsetsCrossPriSelDCI_0_2_r17__Format.

