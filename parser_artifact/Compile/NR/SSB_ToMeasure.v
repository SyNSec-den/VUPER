Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition SSB_ToMeasure__shortBitmap__Type := bit_string_fixed.
Definition SSB_ToMeasure__shortBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition SSB_ToMeasure__mediumBitmap__Type := bit_string_fixed.
Definition SSB_ToMeasure__mediumBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition SSB_ToMeasure__longBitmap__Type := bit_string_fixed.
Definition SSB_ToMeasure__longBitmap__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 64 /\ bit_string_len_prop (fst z) (snd z)).

Inductive SSB_ToMeasure__Type : Set :=
  | SSB_ToMeasure__shortBitmap : SSB_ToMeasure__shortBitmap__Type -> SSB_ToMeasure__Type
  | SSB_ToMeasure__mediumBitmap : SSB_ToMeasure__mediumBitmap__Type -> SSB_ToMeasure__Type
  | SSB_ToMeasure__longBitmap : SSB_ToMeasure__longBitmap__Type -> SSB_ToMeasure__Type
.
Definition SSB_ToMeasure__list : list typ := (
typ_cons SSB_ToMeasure__shortBitmap__Type SSB_ToMeasure__shortBitmap__cond ::
typ_cons SSB_ToMeasure__mediumBitmap__Type SSB_ToMeasure__mediumBitmap__cond ::
typ_cons SSB_ToMeasure__longBitmap__Type SSB_ToMeasure__longBitmap__cond ::
 nil).
Definition SSB_ToMeasure__cond (c : SSB_ToMeasure__Type) := 
  match c with
  | SSB_ToMeasure__shortBitmap t => SSB_ToMeasure__shortBitmap__cond t 
  | SSB_ToMeasure__mediumBitmap t => SSB_ToMeasure__mediumBitmap__cond t 
  | SSB_ToMeasure__longBitmap t => SSB_ToMeasure__longBitmap__cond t 
  end.

Lemma SSB_ToMeasure__len_helper1 : to_bit_sz (length SSB_ToMeasure__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SSB_ToMeasure__len_helper2 : 2 <= length2 SSB_ToMeasure__list.
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
Definition SSB_ToMeasure__shortBitmap__Format : T_Format SSB_ToMeasure__shortBitmap__Type SSB_ToMeasure__shortBitmap__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque SSB_ToMeasure__shortBitmap__cond SSB_ToMeasure__shortBitmap__Format.

Definition SSB_ToMeasure__mediumBitmap__Format : T_Format SSB_ToMeasure__mediumBitmap__Type SSB_ToMeasure__mediumBitmap__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque SSB_ToMeasure__mediumBitmap__cond SSB_ToMeasure__mediumBitmap__Format.

Definition SSB_ToMeasure__longBitmap__Format : T_Format SSB_ToMeasure__longBitmap__Type SSB_ToMeasure__longBitmap__cond := (* Eval compute in *) bit_string_fixed_format 64.
Opaque SSB_ToMeasure__longBitmap__cond SSB_ToMeasure__longBitmap__Format.


Definition SSB_ToMeasure__Format_Type := Eval cbn in get_formats SSB_ToMeasure__list.
Definition SSB_ToMeasure__Format_list : SSB_ToMeasure__Format_Type :=
  (SSB_ToMeasure__shortBitmap__Format, (SSB_ToMeasure__mediumBitmap__Format, (SSB_ToMeasure__longBitmap__Format, unit__Format))).
Definition SSB_ToMeasure__list__Format := Eval compute in choice_format SSB_ToMeasure__list SSB_ToMeasure__len_helper1 SSB_ToMeasure__len_helper2  SSB_ToMeasure__Format_list.
Definition SSB_ToMeasure__F1 (z : SSB_ToMeasure__Type) : (choice SSB_ToMeasure__list) :=
  match z with
   | SSB_ToMeasure__shortBitmap t => existT _ 0 t
  | SSB_ToMeasure__mediumBitmap t => existT _ 1 t
  | SSB_ToMeasure__longBitmap t => existT _ 2 t
  end.
Definition SSB_ToMeasure__g := (fun n => typ_set (get_nth_typ SSB_ToMeasure__list n)).
Definition SSB_ToMeasure__F2 (y : choice SSB_ToMeasure__list) : SSB_ToMeasure__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SSB_ToMeasure__g n -> SSB_ToMeasure__Type) with
    | 0 => fun (t : SSB_ToMeasure__shortBitmap__Type) => SSB_ToMeasure__shortBitmap t 
    | 1 => fun (t : SSB_ToMeasure__mediumBitmap__Type) => SSB_ToMeasure__mediumBitmap t 
    | 2 => fun (t : SSB_ToMeasure__longBitmap__Type) => SSB_ToMeasure__longBitmap t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SSB_ToMeasure__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SSB_ToMeasure__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SSB_ToMeasure__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SSB_ToMeasure__Type with end) n0
           end t0).

Lemma SSB_ToMeasure__helper2 :  forall (y : SSB_ToMeasure__Type), SSB_ToMeasure__cond y -> choice_cond SSB_ToMeasure__list (SSB_ToMeasure__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SSB_ToMeasure__helper3 :  forall (y : SSB_ToMeasure__Type), SSB_ToMeasure__F2 (SSB_ToMeasure__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SSB_ToMeasure__helper4 : (forall b : choice SSB_ToMeasure__list, choice_cond SSB_ToMeasure__list b -> SSB_ToMeasure__cond (SSB_ToMeasure__F2 b) /\ SSB_ToMeasure__F1 (SSB_ToMeasure__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SSB_ToMeasure__F1 SSB_ToMeasure__F2.
Definition SSB_ToMeasure__Format : T_Format SSB_ToMeasure__Type SSB_ToMeasure__cond :=
  (* Eval compute in *) proj2_format SSB_ToMeasure__cond SSB_ToMeasure__list__Format SSB_ToMeasure__F1 SSB_ToMeasure__F2 SSB_ToMeasure__helper2 SSB_ToMeasure__helper3 SSB_ToMeasure__helper4.
Opaque SSB_ToMeasure__cond SSB_ToMeasure__Format.

