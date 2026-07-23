Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition S_NSSAI__sst__Type := bit_string_fixed.
Definition S_NSSAI__sst__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition S_NSSAI__sst_SD__Type := bit_string_fixed.
Definition S_NSSAI__sst_SD__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 32 /\ bit_string_len_prop (fst z) (snd z)).

Inductive S_NSSAI__Type : Set :=
  | S_NSSAI__sst : S_NSSAI__sst__Type -> S_NSSAI__Type
  | S_NSSAI__sst_SD : S_NSSAI__sst_SD__Type -> S_NSSAI__Type
.
Definition S_NSSAI__list : list typ := (
typ_cons S_NSSAI__sst__Type S_NSSAI__sst__cond ::
typ_cons S_NSSAI__sst_SD__Type S_NSSAI__sst_SD__cond ::
 nil).
Definition S_NSSAI__cond (c : S_NSSAI__Type) := 
  match c with
  | S_NSSAI__sst t => S_NSSAI__sst__cond t 
  | S_NSSAI__sst_SD t => S_NSSAI__sst_SD__cond t 
  end.

Lemma S_NSSAI__len_helper1 : to_bit_sz (length S_NSSAI__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma S_NSSAI__len_helper2 : 2 <= length2 S_NSSAI__list.
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
Definition S_NSSAI__sst__Format : T_Format S_NSSAI__sst__Type S_NSSAI__sst__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque S_NSSAI__sst__cond S_NSSAI__sst__Format.

Definition S_NSSAI__sst_SD__Format : T_Format S_NSSAI__sst_SD__Type S_NSSAI__sst_SD__cond := (* Eval compute in *) bit_string_fixed_format 32.
Opaque S_NSSAI__sst_SD__cond S_NSSAI__sst_SD__Format.


Definition S_NSSAI__Format_Type := Eval cbn in get_formats S_NSSAI__list.
Definition S_NSSAI__Format_list : S_NSSAI__Format_Type :=
  (S_NSSAI__sst__Format, (S_NSSAI__sst_SD__Format, unit__Format)).
Definition S_NSSAI__list__Format := Eval compute in choice_format S_NSSAI__list S_NSSAI__len_helper1 S_NSSAI__len_helper2  S_NSSAI__Format_list.
Definition S_NSSAI__F1 (z : S_NSSAI__Type) : (choice S_NSSAI__list) :=
  match z with
   | S_NSSAI__sst t => existT _ 0 t
  | S_NSSAI__sst_SD t => existT _ 1 t
  end.
Definition S_NSSAI__g := (fun n => typ_set (get_nth_typ S_NSSAI__list n)).
Definition S_NSSAI__F2 (y : choice S_NSSAI__list) : S_NSSAI__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (S_NSSAI__g n -> S_NSSAI__Type) with
    | 0 => fun (t : S_NSSAI__sst__Type) => S_NSSAI__sst t 
    | 1 => fun (t : S_NSSAI__sst_SD__Type) => S_NSSAI__sst_SD t 
 | (S (S n0)) => (fun (x' : nat) (t'' : S_NSSAI__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ S_NSSAI__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len S_NSSAI__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return S_NSSAI__Type with end) n0
           end t0).

Lemma S_NSSAI__helper2 :  forall (y : S_NSSAI__Type), S_NSSAI__cond y -> choice_cond S_NSSAI__list (S_NSSAI__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma S_NSSAI__helper3 :  forall (y : S_NSSAI__Type), S_NSSAI__F2 (S_NSSAI__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma S_NSSAI__helper4 : (forall b : choice S_NSSAI__list, choice_cond S_NSSAI__list b -> S_NSSAI__cond (S_NSSAI__F2 b) /\ S_NSSAI__F1 (S_NSSAI__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length S_NSSAI__F1 S_NSSAI__F2.
Definition S_NSSAI__Format : T_Format S_NSSAI__Type S_NSSAI__cond :=
  (* Eval compute in *) proj2_format S_NSSAI__cond S_NSSAI__list__Format S_NSSAI__F1 S_NSSAI__F2 S_NSSAI__helper2 S_NSSAI__helper3 S_NSSAI__helper4.
Opaque S_NSSAI__cond S_NSSAI__Format.

