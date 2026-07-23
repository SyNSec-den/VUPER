Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RateMatchPatternId.

Opaque RateMatchPatternId__cond RateMatchPatternId__Format.

Require Import NR.RateMatchPatternId.

Opaque RateMatchPatternId__cond RateMatchPatternId__Format.


Inductive RateMatchPatternGroup__seq_of__Type : Set :=
  | RateMatchPatternGroup__seq_of__cellLevel : RateMatchPatternId__Type -> RateMatchPatternGroup__seq_of__Type
  | RateMatchPatternGroup__seq_of__bwpLevel : RateMatchPatternId__Type -> RateMatchPatternGroup__seq_of__Type
.
Definition RateMatchPatternGroup__seq_of__list : list typ := (
typ_cons RateMatchPatternId__Type RateMatchPatternId__cond ::
typ_cons RateMatchPatternId__Type RateMatchPatternId__cond ::
 nil).
Definition RateMatchPatternGroup__seq_of__cond (c : RateMatchPatternGroup__seq_of__Type) := 
  match c with
  | RateMatchPatternGroup__seq_of__cellLevel t => RateMatchPatternId__cond t 
  | RateMatchPatternGroup__seq_of__bwpLevel t => RateMatchPatternId__cond t 
  end.

Lemma RateMatchPatternGroup__seq_of__len_helper1 : to_bit_sz (length RateMatchPatternGroup__seq_of__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RateMatchPatternGroup__seq_of__len_helper2 : 2 <= length2 RateMatchPatternGroup__seq_of__list.
 simpl. lia. Qed.
Definition RateMatchPatternGroup__Type := list RateMatchPatternGroup__seq_of__Type.

Lemma RateMatchPatternGroup__helper1 : (0 <= 1 <= maxNrofRateMatchPatternsPerGroup)%Z. unfold maxNrofRateMatchPatternsPerGroup.
 lia. Qed.
Lemma RateMatchPatternGroup__helper2 : to_bit_sz (Z.to_nat (maxNrofRateMatchPatternsPerGroup - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofRateMatchPatternsPerGroup - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RateMatchPatternGroup__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RateMatchPatternGroup__cond (z : RateMatchPatternGroup__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofRateMatchPatternsPerGroup)%Z /\ (list_and RateMatchPatternGroup__seq_of__cond z) .


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

Definition RateMatchPatternGroup__seq_of__Format_Type := Eval cbn in get_formats RateMatchPatternGroup__seq_of__list.
Definition RateMatchPatternGroup__seq_of__Format_list : RateMatchPatternGroup__seq_of__Format_Type :=
  (RateMatchPatternId__Format, (RateMatchPatternId__Format, unit__Format)).
Definition RateMatchPatternGroup__seq_of__list__Format := Eval compute in choice_format RateMatchPatternGroup__seq_of__list RateMatchPatternGroup__seq_of__len_helper1 RateMatchPatternGroup__seq_of__len_helper2  RateMatchPatternGroup__seq_of__Format_list.
Definition RateMatchPatternGroup__seq_of__F1 (z : RateMatchPatternGroup__seq_of__Type) : (choice RateMatchPatternGroup__seq_of__list) :=
  match z with
   | RateMatchPatternGroup__seq_of__cellLevel t => existT _ 0 t
  | RateMatchPatternGroup__seq_of__bwpLevel t => existT _ 1 t
  end.
Definition RateMatchPatternGroup__seq_of__g := (fun n => typ_set (get_nth_typ RateMatchPatternGroup__seq_of__list n)).
Definition RateMatchPatternGroup__seq_of__F2 (y : choice RateMatchPatternGroup__seq_of__list) : RateMatchPatternGroup__seq_of__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RateMatchPatternGroup__seq_of__g n -> RateMatchPatternGroup__seq_of__Type) with
    | 0 => fun (t : RateMatchPatternId__Type) => RateMatchPatternGroup__seq_of__cellLevel t 
    | 1 => fun (t : RateMatchPatternId__Type) => RateMatchPatternGroup__seq_of__bwpLevel t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RateMatchPatternGroup__seq_of__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RateMatchPatternGroup__seq_of__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RateMatchPatternGroup__seq_of__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RateMatchPatternGroup__seq_of__Type with end) n0
           end t0).

Lemma RateMatchPatternGroup__seq_of__helper2 :  forall (y : RateMatchPatternGroup__seq_of__Type), RateMatchPatternGroup__seq_of__cond y -> choice_cond RateMatchPatternGroup__seq_of__list (RateMatchPatternGroup__seq_of__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RateMatchPatternGroup__seq_of__helper3 :  forall (y : RateMatchPatternGroup__seq_of__Type), RateMatchPatternGroup__seq_of__F2 (RateMatchPatternGroup__seq_of__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RateMatchPatternGroup__seq_of__helper4 : (forall b : choice RateMatchPatternGroup__seq_of__list, choice_cond RateMatchPatternGroup__seq_of__list b -> RateMatchPatternGroup__seq_of__cond (RateMatchPatternGroup__seq_of__F2 b) /\ RateMatchPatternGroup__seq_of__F1 (RateMatchPatternGroup__seq_of__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RateMatchPatternGroup__seq_of__F1 RateMatchPatternGroup__seq_of__F2.
Definition RateMatchPatternGroup__seq_of__Format : T_Format RateMatchPatternGroup__seq_of__Type RateMatchPatternGroup__seq_of__cond :=
  (* Eval compute in *) proj2_format RateMatchPatternGroup__seq_of__cond RateMatchPatternGroup__seq_of__list__Format RateMatchPatternGroup__seq_of__F1 RateMatchPatternGroup__seq_of__F2 RateMatchPatternGroup__seq_of__helper2 RateMatchPatternGroup__seq_of__helper3 RateMatchPatternGroup__seq_of__helper4.
Opaque RateMatchPatternGroup__seq_of__cond RateMatchPatternGroup__seq_of__Format.

Definition RateMatchPatternGroup__Format : T_Format RateMatchPatternGroup__Type RateMatchPatternGroup__cond := seq_of_format RateMatchPatternGroup__seq_of__Format 1 maxNrofRateMatchPatternsPerGroup RateMatchPatternGroup__helper1 RateMatchPatternGroup__helper2.

Opaque RateMatchPatternGroup__cond RateMatchPatternGroup__Format.

