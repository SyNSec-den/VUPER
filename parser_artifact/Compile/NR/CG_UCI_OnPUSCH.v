Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BetaOffsets.

Opaque BetaOffsets__cond BetaOffsets__Format.

Definition CG_UCI_OnPUSCH__dynamic__Type := list BetaOffsets__Type.

Lemma CG_UCI_OnPUSCH__dynamic__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma CG_UCI_OnPUSCH__dynamic__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CG_UCI_OnPUSCH__dynamic__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CG_UCI_OnPUSCH__dynamic__cond (z : CG_UCI_OnPUSCH__dynamic__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and BetaOffsets__cond z) .

Require Import NR.BetaOffsets.

Opaque BetaOffsets__cond BetaOffsets__Format.


Inductive CG_UCI_OnPUSCH__Type : Set :=
  | CG_UCI_OnPUSCH__dynamic : CG_UCI_OnPUSCH__dynamic__Type -> CG_UCI_OnPUSCH__Type
  | CG_UCI_OnPUSCH__semiStatic : BetaOffsets__Type -> CG_UCI_OnPUSCH__Type
.
Definition CG_UCI_OnPUSCH__list : list typ := (
typ_cons CG_UCI_OnPUSCH__dynamic__Type CG_UCI_OnPUSCH__dynamic__cond ::
typ_cons BetaOffsets__Type BetaOffsets__cond ::
 nil).
Definition CG_UCI_OnPUSCH__cond (c : CG_UCI_OnPUSCH__Type) := 
  match c with
  | CG_UCI_OnPUSCH__dynamic t => CG_UCI_OnPUSCH__dynamic__cond t 
  | CG_UCI_OnPUSCH__semiStatic t => BetaOffsets__cond t 
  end.

Lemma CG_UCI_OnPUSCH__len_helper1 : to_bit_sz (length CG_UCI_OnPUSCH__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CG_UCI_OnPUSCH__len_helper2 : 2 <= length2 CG_UCI_OnPUSCH__list.
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
Definition CG_UCI_OnPUSCH__dynamic__Format : T_Format CG_UCI_OnPUSCH__dynamic__Type CG_UCI_OnPUSCH__dynamic__cond := seq_of_format BetaOffsets__Format 1 4 CG_UCI_OnPUSCH__dynamic__helper1 CG_UCI_OnPUSCH__dynamic__helper2.

Opaque CG_UCI_OnPUSCH__dynamic__cond CG_UCI_OnPUSCH__dynamic__Format.


Definition CG_UCI_OnPUSCH__Format_Type := Eval cbn in get_formats CG_UCI_OnPUSCH__list.
Definition CG_UCI_OnPUSCH__Format_list : CG_UCI_OnPUSCH__Format_Type :=
  (CG_UCI_OnPUSCH__dynamic__Format, (BetaOffsets__Format, unit__Format)).
Definition CG_UCI_OnPUSCH__list__Format := Eval compute in choice_format CG_UCI_OnPUSCH__list CG_UCI_OnPUSCH__len_helper1 CG_UCI_OnPUSCH__len_helper2  CG_UCI_OnPUSCH__Format_list.
Definition CG_UCI_OnPUSCH__F1 (z : CG_UCI_OnPUSCH__Type) : (choice CG_UCI_OnPUSCH__list) :=
  match z with
   | CG_UCI_OnPUSCH__dynamic t => existT _ 0 t
  | CG_UCI_OnPUSCH__semiStatic t => existT _ 1 t
  end.
Definition CG_UCI_OnPUSCH__g := (fun n => typ_set (get_nth_typ CG_UCI_OnPUSCH__list n)).
Definition CG_UCI_OnPUSCH__F2 (y : choice CG_UCI_OnPUSCH__list) : CG_UCI_OnPUSCH__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CG_UCI_OnPUSCH__g n -> CG_UCI_OnPUSCH__Type) with
    | 0 => fun (t : CG_UCI_OnPUSCH__dynamic__Type) => CG_UCI_OnPUSCH__dynamic t 
    | 1 => fun (t : BetaOffsets__Type) => CG_UCI_OnPUSCH__semiStatic t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CG_UCI_OnPUSCH__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CG_UCI_OnPUSCH__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CG_UCI_OnPUSCH__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CG_UCI_OnPUSCH__Type with end) n0
           end t0).

Lemma CG_UCI_OnPUSCH__helper2 :  forall (y : CG_UCI_OnPUSCH__Type), CG_UCI_OnPUSCH__cond y -> choice_cond CG_UCI_OnPUSCH__list (CG_UCI_OnPUSCH__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CG_UCI_OnPUSCH__helper3 :  forall (y : CG_UCI_OnPUSCH__Type), CG_UCI_OnPUSCH__F2 (CG_UCI_OnPUSCH__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CG_UCI_OnPUSCH__helper4 : (forall b : choice CG_UCI_OnPUSCH__list, choice_cond CG_UCI_OnPUSCH__list b -> CG_UCI_OnPUSCH__cond (CG_UCI_OnPUSCH__F2 b) /\ CG_UCI_OnPUSCH__F1 (CG_UCI_OnPUSCH__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CG_UCI_OnPUSCH__F1 CG_UCI_OnPUSCH__F2.
Definition CG_UCI_OnPUSCH__Format : T_Format CG_UCI_OnPUSCH__Type CG_UCI_OnPUSCH__cond :=
  (* Eval compute in *) proj2_format CG_UCI_OnPUSCH__cond CG_UCI_OnPUSCH__list__Format CG_UCI_OnPUSCH__F1 CG_UCI_OnPUSCH__F2 CG_UCI_OnPUSCH__helper2 CG_UCI_OnPUSCH__helper3 CG_UCI_OnPUSCH__helper4.
Opaque CG_UCI_OnPUSCH__cond CG_UCI_OnPUSCH__Format.

