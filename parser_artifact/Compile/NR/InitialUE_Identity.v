Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition InitialUE_Identity__ng_5G_S_TMSI_Part1__Type := bit_string_fixed.
Definition InitialUE_Identity__ng_5G_S_TMSI_Part1__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 39 /\ bit_string_len_prop (fst z) (snd z)).
Definition InitialUE_Identity__randomValue__Type := bit_string_fixed.
Definition InitialUE_Identity__randomValue__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 39 /\ bit_string_len_prop (fst z) (snd z)).

Inductive InitialUE_Identity__Type : Set :=
  | InitialUE_Identity__ng_5G_S_TMSI_Part1 : InitialUE_Identity__ng_5G_S_TMSI_Part1__Type -> InitialUE_Identity__Type
  | InitialUE_Identity__randomValue : InitialUE_Identity__randomValue__Type -> InitialUE_Identity__Type
.
Definition InitialUE_Identity__list : list typ := (
typ_cons InitialUE_Identity__ng_5G_S_TMSI_Part1__Type InitialUE_Identity__ng_5G_S_TMSI_Part1__cond ::
typ_cons InitialUE_Identity__randomValue__Type InitialUE_Identity__randomValue__cond ::
 nil).
Definition InitialUE_Identity__cond (c : InitialUE_Identity__Type) := 
  match c with
  | InitialUE_Identity__ng_5G_S_TMSI_Part1 t => InitialUE_Identity__ng_5G_S_TMSI_Part1__cond t 
  | InitialUE_Identity__randomValue t => InitialUE_Identity__randomValue__cond t 
  end.

Lemma InitialUE_Identity__len_helper1 : to_bit_sz (length InitialUE_Identity__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma InitialUE_Identity__len_helper2 : 2 <= length2 InitialUE_Identity__list.
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
Definition InitialUE_Identity__ng_5G_S_TMSI_Part1__Format : T_Format InitialUE_Identity__ng_5G_S_TMSI_Part1__Type InitialUE_Identity__ng_5G_S_TMSI_Part1__cond := (* Eval compute in *) bit_string_fixed_format 39.
Opaque InitialUE_Identity__ng_5G_S_TMSI_Part1__cond InitialUE_Identity__ng_5G_S_TMSI_Part1__Format.

Definition InitialUE_Identity__randomValue__Format : T_Format InitialUE_Identity__randomValue__Type InitialUE_Identity__randomValue__cond := (* Eval compute in *) bit_string_fixed_format 39.
Opaque InitialUE_Identity__randomValue__cond InitialUE_Identity__randomValue__Format.


Definition InitialUE_Identity__Format_Type := Eval cbn in get_formats InitialUE_Identity__list.
Definition InitialUE_Identity__Format_list : InitialUE_Identity__Format_Type :=
  (InitialUE_Identity__ng_5G_S_TMSI_Part1__Format, (InitialUE_Identity__randomValue__Format, unit__Format)).
Definition InitialUE_Identity__list__Format := Eval compute in choice_format InitialUE_Identity__list InitialUE_Identity__len_helper1 InitialUE_Identity__len_helper2  InitialUE_Identity__Format_list.
Definition InitialUE_Identity__F1 (z : InitialUE_Identity__Type) : (choice InitialUE_Identity__list) :=
  match z with
   | InitialUE_Identity__ng_5G_S_TMSI_Part1 t => existT _ 0 t
  | InitialUE_Identity__randomValue t => existT _ 1 t
  end.
Definition InitialUE_Identity__g := (fun n => typ_set (get_nth_typ InitialUE_Identity__list n)).
Definition InitialUE_Identity__F2 (y : choice InitialUE_Identity__list) : InitialUE_Identity__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (InitialUE_Identity__g n -> InitialUE_Identity__Type) with
    | 0 => fun (t : InitialUE_Identity__ng_5G_S_TMSI_Part1__Type) => InitialUE_Identity__ng_5G_S_TMSI_Part1 t 
    | 1 => fun (t : InitialUE_Identity__randomValue__Type) => InitialUE_Identity__randomValue t 
 | (S (S n0)) => (fun (x' : nat) (t'' : InitialUE_Identity__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ InitialUE_Identity__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len InitialUE_Identity__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return InitialUE_Identity__Type with end) n0
           end t0).

Lemma InitialUE_Identity__helper2 :  forall (y : InitialUE_Identity__Type), InitialUE_Identity__cond y -> choice_cond InitialUE_Identity__list (InitialUE_Identity__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma InitialUE_Identity__helper3 :  forall (y : InitialUE_Identity__Type), InitialUE_Identity__F2 (InitialUE_Identity__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma InitialUE_Identity__helper4 : (forall b : choice InitialUE_Identity__list, choice_cond InitialUE_Identity__list b -> InitialUE_Identity__cond (InitialUE_Identity__F2 b) /\ InitialUE_Identity__F1 (InitialUE_Identity__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length InitialUE_Identity__F1 InitialUE_Identity__F2.
Definition InitialUE_Identity__Format : T_Format InitialUE_Identity__Type InitialUE_Identity__cond :=
  (* Eval compute in *) proj2_format InitialUE_Identity__cond InitialUE_Identity__list__Format InitialUE_Identity__F1 InitialUE_Identity__F2 InitialUE_Identity__helper2 InitialUE_Identity__helper3 InitialUE_Identity__helper4.
Opaque InitialUE_Identity__cond InitialUE_Identity__Format.

