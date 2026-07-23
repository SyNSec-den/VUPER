Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Lemma PLMN_Identity_EUTRA_5GC__plmn_index__helper1 : (1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma PLMN_Identity_EUTRA_5GC__plmn_index__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PLMN_Identity_EUTRA_5GC__plmn_index__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PLMN_Identity_EUTRA_5GC__plmn_index__Type := Z.
Definition PLMN_Identity_EUTRA_5GC__plmn_index__cond := (fun z => (1 <= z <= maxPLMN)%Z).

Inductive PLMN_Identity_EUTRA_5GC__Type : Set :=
  | PLMN_Identity_EUTRA_5GC__plmn_Identity_EUTRA_5GC : PLMN_Identity__Type -> PLMN_Identity_EUTRA_5GC__Type
  | PLMN_Identity_EUTRA_5GC__plmn_index : Z -> PLMN_Identity_EUTRA_5GC__Type
.
Definition PLMN_Identity_EUTRA_5GC__list : list typ := (
typ_cons PLMN_Identity__Type PLMN_Identity__cond ::
typ_cons Z PLMN_Identity_EUTRA_5GC__plmn_index__cond ::
 nil).
Definition PLMN_Identity_EUTRA_5GC__cond (c : PLMN_Identity_EUTRA_5GC__Type) := 
  match c with
  | PLMN_Identity_EUTRA_5GC__plmn_Identity_EUTRA_5GC t => PLMN_Identity__cond t 
  | PLMN_Identity_EUTRA_5GC__plmn_index t => PLMN_Identity_EUTRA_5GC__plmn_index__cond t 
  end.

Lemma PLMN_Identity_EUTRA_5GC__len_helper1 : to_bit_sz (length PLMN_Identity_EUTRA_5GC__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PLMN_Identity_EUTRA_5GC__len_helper2 : 2 <= length2 PLMN_Identity_EUTRA_5GC__list.
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
Definition PLMN_Identity_EUTRA_5GC__plmn_index__Format : T_Format Z PLMN_Identity_EUTRA_5GC__plmn_index__cond :=
 ranged_int_format (1) (maxPLMN) PLMN_Identity_EUTRA_5GC__plmn_index__helper1 PLMN_Identity_EUTRA_5GC__plmn_index__helper2.

Opaque PLMN_Identity_EUTRA_5GC__plmn_index__cond PLMN_Identity_EUTRA_5GC__plmn_index__Format.


Definition PLMN_Identity_EUTRA_5GC__Format_Type := Eval cbn in get_formats PLMN_Identity_EUTRA_5GC__list.
Definition PLMN_Identity_EUTRA_5GC__Format_list : PLMN_Identity_EUTRA_5GC__Format_Type :=
  (PLMN_Identity__Format, (PLMN_Identity_EUTRA_5GC__plmn_index__Format, unit__Format)).
Definition PLMN_Identity_EUTRA_5GC__list__Format := Eval compute in choice_format PLMN_Identity_EUTRA_5GC__list PLMN_Identity_EUTRA_5GC__len_helper1 PLMN_Identity_EUTRA_5GC__len_helper2  PLMN_Identity_EUTRA_5GC__Format_list.
Definition PLMN_Identity_EUTRA_5GC__F1 (z : PLMN_Identity_EUTRA_5GC__Type) : (choice PLMN_Identity_EUTRA_5GC__list) :=
  match z with
   | PLMN_Identity_EUTRA_5GC__plmn_Identity_EUTRA_5GC t => existT _ 0 t
  | PLMN_Identity_EUTRA_5GC__plmn_index t => existT _ 1 t
  end.
Definition PLMN_Identity_EUTRA_5GC__g := (fun n => typ_set (get_nth_typ PLMN_Identity_EUTRA_5GC__list n)).
Definition PLMN_Identity_EUTRA_5GC__F2 (y : choice PLMN_Identity_EUTRA_5GC__list) : PLMN_Identity_EUTRA_5GC__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PLMN_Identity_EUTRA_5GC__g n -> PLMN_Identity_EUTRA_5GC__Type) with
    | 0 => fun (t : PLMN_Identity__Type) => PLMN_Identity_EUTRA_5GC__plmn_Identity_EUTRA_5GC t 
    | 1 => fun (t : Z) => PLMN_Identity_EUTRA_5GC__plmn_index t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PLMN_Identity_EUTRA_5GC__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PLMN_Identity_EUTRA_5GC__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PLMN_Identity_EUTRA_5GC__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PLMN_Identity_EUTRA_5GC__Type with end) n0
           end t0).

Lemma PLMN_Identity_EUTRA_5GC__helper2 :  forall (y : PLMN_Identity_EUTRA_5GC__Type), PLMN_Identity_EUTRA_5GC__cond y -> choice_cond PLMN_Identity_EUTRA_5GC__list (PLMN_Identity_EUTRA_5GC__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PLMN_Identity_EUTRA_5GC__helper3 :  forall (y : PLMN_Identity_EUTRA_5GC__Type), PLMN_Identity_EUTRA_5GC__F2 (PLMN_Identity_EUTRA_5GC__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PLMN_Identity_EUTRA_5GC__helper4 : (forall b : choice PLMN_Identity_EUTRA_5GC__list, choice_cond PLMN_Identity_EUTRA_5GC__list b -> PLMN_Identity_EUTRA_5GC__cond (PLMN_Identity_EUTRA_5GC__F2 b) /\ PLMN_Identity_EUTRA_5GC__F1 (PLMN_Identity_EUTRA_5GC__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PLMN_Identity_EUTRA_5GC__F1 PLMN_Identity_EUTRA_5GC__F2.
Definition PLMN_Identity_EUTRA_5GC__Format : T_Format PLMN_Identity_EUTRA_5GC__Type PLMN_Identity_EUTRA_5GC__cond :=
  (* Eval compute in *) proj2_format PLMN_Identity_EUTRA_5GC__cond PLMN_Identity_EUTRA_5GC__list__Format PLMN_Identity_EUTRA_5GC__F1 PLMN_Identity_EUTRA_5GC__F2 PLMN_Identity_EUTRA_5GC__helper2 PLMN_Identity_EUTRA_5GC__helper3 PLMN_Identity_EUTRA_5GC__helper4.
Opaque PLMN_Identity_EUTRA_5GC__cond PLMN_Identity_EUTRA_5GC__Format.

