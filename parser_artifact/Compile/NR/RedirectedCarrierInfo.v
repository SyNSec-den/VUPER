Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CarrierInfoNR.

Opaque CarrierInfoNR__cond CarrierInfoNR__Format.

Require Import NR.RedirectedCarrierInfo_EUTRA.

Opaque RedirectedCarrierInfo_EUTRA__cond RedirectedCarrierInfo_EUTRA__Format.


Inductive RedirectedCarrierInfo__root__Type : Set :=
  | RedirectedCarrierInfo__root__nr : CarrierInfoNR__Type -> RedirectedCarrierInfo__root__Type
  | RedirectedCarrierInfo__root__eutra : RedirectedCarrierInfo_EUTRA__Type -> RedirectedCarrierInfo__root__Type
.
Definition RedirectedCarrierInfo__root__list : list typ := (
typ_cons CarrierInfoNR__Type CarrierInfoNR__cond ::
typ_cons RedirectedCarrierInfo_EUTRA__Type RedirectedCarrierInfo_EUTRA__cond ::
 nil).
Definition RedirectedCarrierInfo__root__cond (c : RedirectedCarrierInfo__root__Type) := 
  match c with
  | RedirectedCarrierInfo__root__nr t => CarrierInfoNR__cond t 
  | RedirectedCarrierInfo__root__eutra t => RedirectedCarrierInfo_EUTRA__cond t 
  end.

Lemma RedirectedCarrierInfo__root__len_helper1 : to_bit_sz (length RedirectedCarrierInfo__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RedirectedCarrierInfo__root__len_helper2 : 2 <= length2 RedirectedCarrierInfo__root__list.
 simpl. lia. Qed.

Definition RedirectedCarrierInfo__ext__Type : Set := Empty_set.
Definition RedirectedCarrierInfo__ext__cond (c : RedirectedCarrierInfo__ext__Type) := True.
Definition RedirectedCarrierInfo__Type : Set := RedirectedCarrierInfo__root__Type + RedirectedCarrierInfo__ext__Type.
Definition RedirectedCarrierInfo__cond :=
  sum_cond RedirectedCarrierInfo__root__cond RedirectedCarrierInfo__ext__cond.

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

Definition RedirectedCarrierInfo__root__Format_Type := Eval cbn in get_formats RedirectedCarrierInfo__root__list.
Definition RedirectedCarrierInfo__root__Format_list : RedirectedCarrierInfo__root__Format_Type :=
  (CarrierInfoNR__Format, (RedirectedCarrierInfo_EUTRA__Format, unit__Format)).
Definition RedirectedCarrierInfo__root__list__Format := Eval compute in choice_format RedirectedCarrierInfo__root__list RedirectedCarrierInfo__root__len_helper1 RedirectedCarrierInfo__root__len_helper2  RedirectedCarrierInfo__root__Format_list.
Definition RedirectedCarrierInfo__root__F1 (z : RedirectedCarrierInfo__root__Type) : (choice RedirectedCarrierInfo__root__list) :=
  match z with
   | RedirectedCarrierInfo__root__nr t => existT _ 0 t
  | RedirectedCarrierInfo__root__eutra t => existT _ 1 t
  end.
Definition RedirectedCarrierInfo__root__g := (fun n => typ_set (get_nth_typ RedirectedCarrierInfo__root__list n)).
Definition RedirectedCarrierInfo__root__F2 (y : choice RedirectedCarrierInfo__root__list) : RedirectedCarrierInfo__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RedirectedCarrierInfo__root__g n -> RedirectedCarrierInfo__root__Type) with
    | 0 => fun (t : CarrierInfoNR__Type) => RedirectedCarrierInfo__root__nr t 
    | 1 => fun (t : RedirectedCarrierInfo_EUTRA__Type) => RedirectedCarrierInfo__root__eutra t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RedirectedCarrierInfo__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RedirectedCarrierInfo__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RedirectedCarrierInfo__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RedirectedCarrierInfo__root__Type with end) n0
           end t0).

Lemma RedirectedCarrierInfo__root__helper2 :  forall (y : RedirectedCarrierInfo__root__Type), RedirectedCarrierInfo__root__cond y -> choice_cond RedirectedCarrierInfo__root__list (RedirectedCarrierInfo__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RedirectedCarrierInfo__root__helper3 :  forall (y : RedirectedCarrierInfo__root__Type), RedirectedCarrierInfo__root__F2 (RedirectedCarrierInfo__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RedirectedCarrierInfo__root__helper4 : (forall b : choice RedirectedCarrierInfo__root__list, choice_cond RedirectedCarrierInfo__root__list b -> RedirectedCarrierInfo__root__cond (RedirectedCarrierInfo__root__F2 b) /\ RedirectedCarrierInfo__root__F1 (RedirectedCarrierInfo__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RedirectedCarrierInfo__root__F1 RedirectedCarrierInfo__root__F2.
Definition RedirectedCarrierInfo__root__Format : T_Format RedirectedCarrierInfo__root__Type RedirectedCarrierInfo__root__cond :=
  (* Eval compute in *) proj2_format RedirectedCarrierInfo__root__cond RedirectedCarrierInfo__root__list__Format RedirectedCarrierInfo__root__F1 RedirectedCarrierInfo__root__F2 RedirectedCarrierInfo__root__helper2 RedirectedCarrierInfo__root__helper3 RedirectedCarrierInfo__root__helper4.
Opaque RedirectedCarrierInfo__root__cond RedirectedCarrierInfo__root__Format.

Definition RedirectedCarrierInfo__ext__Format : T_Format RedirectedCarrierInfo__ext__Type RedirectedCarrierInfo__ext__cond := empty_format.
Opaque RedirectedCarrierInfo__ext__cond RedirectedCarrierInfo__ext__Format.

Definition RedirectedCarrierInfo__Format : T_Format RedirectedCarrierInfo__Type RedirectedCarrierInfo__cond := sum_format RedirectedCarrierInfo__root__Format RedirectedCarrierInfo__ext__Format.
Opaque RedirectedCarrierInfo__cond RedirectedCarrierInfo__Format.

