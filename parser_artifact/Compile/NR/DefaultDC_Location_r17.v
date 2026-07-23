Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FrequencyComponent_r17.

Opaque FrequencyComponent_r17__cond FrequencyComponent_r17__Format.

Require Import NR.FrequencyComponent_r17.

Opaque FrequencyComponent_r17__cond FrequencyComponent_r17__Format.

Require Import NR.FrequencyComponent_r17.

Opaque FrequencyComponent_r17__cond FrequencyComponent_r17__Format.


Inductive DefaultDC_Location_r17__Type : Set :=
  | DefaultDC_Location_r17__ul : FrequencyComponent_r17__Type -> DefaultDC_Location_r17__Type
  | DefaultDC_Location_r17__dl : FrequencyComponent_r17__Type -> DefaultDC_Location_r17__Type
  | DefaultDC_Location_r17__ulAndDL : FrequencyComponent_r17__Type -> DefaultDC_Location_r17__Type
.
Definition DefaultDC_Location_r17__list : list typ := (
typ_cons FrequencyComponent_r17__Type FrequencyComponent_r17__cond ::
typ_cons FrequencyComponent_r17__Type FrequencyComponent_r17__cond ::
typ_cons FrequencyComponent_r17__Type FrequencyComponent_r17__cond ::
 nil).
Definition DefaultDC_Location_r17__cond (c : DefaultDC_Location_r17__Type) := 
  match c with
  | DefaultDC_Location_r17__ul t => FrequencyComponent_r17__cond t 
  | DefaultDC_Location_r17__dl t => FrequencyComponent_r17__cond t 
  | DefaultDC_Location_r17__ulAndDL t => FrequencyComponent_r17__cond t 
  end.

Lemma DefaultDC_Location_r17__len_helper1 : to_bit_sz (length DefaultDC_Location_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DefaultDC_Location_r17__len_helper2 : 2 <= length2 DefaultDC_Location_r17__list.
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

Definition DefaultDC_Location_r17__Format_Type := Eval cbn in get_formats DefaultDC_Location_r17__list.
Definition DefaultDC_Location_r17__Format_list : DefaultDC_Location_r17__Format_Type :=
  (FrequencyComponent_r17__Format, (FrequencyComponent_r17__Format, (FrequencyComponent_r17__Format, unit__Format))).
Definition DefaultDC_Location_r17__list__Format := Eval compute in choice_format DefaultDC_Location_r17__list DefaultDC_Location_r17__len_helper1 DefaultDC_Location_r17__len_helper2  DefaultDC_Location_r17__Format_list.
Definition DefaultDC_Location_r17__F1 (z : DefaultDC_Location_r17__Type) : (choice DefaultDC_Location_r17__list) :=
  match z with
   | DefaultDC_Location_r17__ul t => existT _ 0 t
  | DefaultDC_Location_r17__dl t => existT _ 1 t
  | DefaultDC_Location_r17__ulAndDL t => existT _ 2 t
  end.
Definition DefaultDC_Location_r17__g := (fun n => typ_set (get_nth_typ DefaultDC_Location_r17__list n)).
Definition DefaultDC_Location_r17__F2 (y : choice DefaultDC_Location_r17__list) : DefaultDC_Location_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DefaultDC_Location_r17__g n -> DefaultDC_Location_r17__Type) with
    | 0 => fun (t : FrequencyComponent_r17__Type) => DefaultDC_Location_r17__ul t 
    | 1 => fun (t : FrequencyComponent_r17__Type) => DefaultDC_Location_r17__dl t 
    | 2 => fun (t : FrequencyComponent_r17__Type) => DefaultDC_Location_r17__ulAndDL t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : DefaultDC_Location_r17__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ DefaultDC_Location_r17__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DefaultDC_Location_r17__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return DefaultDC_Location_r17__Type with end) n0
           end t0).

Lemma DefaultDC_Location_r17__helper2 :  forall (y : DefaultDC_Location_r17__Type), DefaultDC_Location_r17__cond y -> choice_cond DefaultDC_Location_r17__list (DefaultDC_Location_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DefaultDC_Location_r17__helper3 :  forall (y : DefaultDC_Location_r17__Type), DefaultDC_Location_r17__F2 (DefaultDC_Location_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DefaultDC_Location_r17__helper4 : (forall b : choice DefaultDC_Location_r17__list, choice_cond DefaultDC_Location_r17__list b -> DefaultDC_Location_r17__cond (DefaultDC_Location_r17__F2 b) /\ DefaultDC_Location_r17__F1 (DefaultDC_Location_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DefaultDC_Location_r17__F1 DefaultDC_Location_r17__F2.
Definition DefaultDC_Location_r17__Format : T_Format DefaultDC_Location_r17__Type DefaultDC_Location_r17__cond :=
  (* Eval compute in *) proj2_format DefaultDC_Location_r17__cond DefaultDC_Location_r17__list__Format DefaultDC_Location_r17__F1 DefaultDC_Location_r17__F2 DefaultDC_Location_r17__helper2 DefaultDC_Location_r17__helper3 DefaultDC_Location_r17__helper4.
Opaque DefaultDC_Location_r17__cond DefaultDC_Location_r17__Format.

