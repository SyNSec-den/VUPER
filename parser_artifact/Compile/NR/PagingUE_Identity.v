Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NG_5G_S_TMSI.

Opaque NG_5G_S_TMSI__cond NG_5G_S_TMSI__Format.

Require Import NR.I_RNTI_Value.

Opaque I_RNTI_Value__cond I_RNTI_Value__Format.


Inductive PagingUE_Identity__root__Type : Set :=
  | PagingUE_Identity__root__ng_5G_S_TMSI : NG_5G_S_TMSI__Type -> PagingUE_Identity__root__Type
  | PagingUE_Identity__root__fullI_RNTI : I_RNTI_Value__Type -> PagingUE_Identity__root__Type
.
Definition PagingUE_Identity__root__list : list typ := (
typ_cons NG_5G_S_TMSI__Type NG_5G_S_TMSI__cond ::
typ_cons I_RNTI_Value__Type I_RNTI_Value__cond ::
 nil).
Definition PagingUE_Identity__root__cond (c : PagingUE_Identity__root__Type) := 
  match c with
  | PagingUE_Identity__root__ng_5G_S_TMSI t => NG_5G_S_TMSI__cond t 
  | PagingUE_Identity__root__fullI_RNTI t => I_RNTI_Value__cond t 
  end.

Lemma PagingUE_Identity__root__len_helper1 : to_bit_sz (length PagingUE_Identity__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PagingUE_Identity__root__len_helper2 : 2 <= length2 PagingUE_Identity__root__list.
 simpl. lia. Qed.

Definition PagingUE_Identity__ext__Type : Set := Empty_set.
Definition PagingUE_Identity__ext__cond (c : PagingUE_Identity__ext__Type) := True.
Definition PagingUE_Identity__Type : Set := PagingUE_Identity__root__Type + PagingUE_Identity__ext__Type.
Definition PagingUE_Identity__cond :=
  sum_cond PagingUE_Identity__root__cond PagingUE_Identity__ext__cond.

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

Definition PagingUE_Identity__root__Format_Type := Eval cbn in get_formats PagingUE_Identity__root__list.
Definition PagingUE_Identity__root__Format_list : PagingUE_Identity__root__Format_Type :=
  (NG_5G_S_TMSI__Format, (I_RNTI_Value__Format, unit__Format)).
Definition PagingUE_Identity__root__list__Format := Eval compute in choice_format PagingUE_Identity__root__list PagingUE_Identity__root__len_helper1 PagingUE_Identity__root__len_helper2  PagingUE_Identity__root__Format_list.
Definition PagingUE_Identity__root__F1 (z : PagingUE_Identity__root__Type) : (choice PagingUE_Identity__root__list) :=
  match z with
   | PagingUE_Identity__root__ng_5G_S_TMSI t => existT _ 0 t
  | PagingUE_Identity__root__fullI_RNTI t => existT _ 1 t
  end.
Definition PagingUE_Identity__root__g := (fun n => typ_set (get_nth_typ PagingUE_Identity__root__list n)).
Definition PagingUE_Identity__root__F2 (y : choice PagingUE_Identity__root__list) : PagingUE_Identity__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PagingUE_Identity__root__g n -> PagingUE_Identity__root__Type) with
    | 0 => fun (t : NG_5G_S_TMSI__Type) => PagingUE_Identity__root__ng_5G_S_TMSI t 
    | 1 => fun (t : I_RNTI_Value__Type) => PagingUE_Identity__root__fullI_RNTI t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PagingUE_Identity__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PagingUE_Identity__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PagingUE_Identity__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PagingUE_Identity__root__Type with end) n0
           end t0).

Lemma PagingUE_Identity__root__helper2 :  forall (y : PagingUE_Identity__root__Type), PagingUE_Identity__root__cond y -> choice_cond PagingUE_Identity__root__list (PagingUE_Identity__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PagingUE_Identity__root__helper3 :  forall (y : PagingUE_Identity__root__Type), PagingUE_Identity__root__F2 (PagingUE_Identity__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PagingUE_Identity__root__helper4 : (forall b : choice PagingUE_Identity__root__list, choice_cond PagingUE_Identity__root__list b -> PagingUE_Identity__root__cond (PagingUE_Identity__root__F2 b) /\ PagingUE_Identity__root__F1 (PagingUE_Identity__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PagingUE_Identity__root__F1 PagingUE_Identity__root__F2.
Definition PagingUE_Identity__root__Format : T_Format PagingUE_Identity__root__Type PagingUE_Identity__root__cond :=
  (* Eval compute in *) proj2_format PagingUE_Identity__root__cond PagingUE_Identity__root__list__Format PagingUE_Identity__root__F1 PagingUE_Identity__root__F2 PagingUE_Identity__root__helper2 PagingUE_Identity__root__helper3 PagingUE_Identity__root__helper4.
Opaque PagingUE_Identity__root__cond PagingUE_Identity__root__Format.

Definition PagingUE_Identity__ext__Format : T_Format PagingUE_Identity__ext__Type PagingUE_Identity__ext__cond := empty_format.
Opaque PagingUE_Identity__ext__cond PagingUE_Identity__ext__Format.

Definition PagingUE_Identity__Format : T_Format PagingUE_Identity__Type PagingUE_Identity__cond := sum_format PagingUE_Identity__root__Format PagingUE_Identity__ext__Format.
Opaque PagingUE_Identity__cond PagingUE_Identity__Format.

