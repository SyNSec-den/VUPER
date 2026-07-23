Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition InvalidSymbolPattern_r16__symbols_r16__oneSlot__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__symbols_r16__oneSlot__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 14 /\ bit_string_len_prop (fst z) (snd z)).
Definition InvalidSymbolPattern_r16__symbols_r16__twoSlots__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__symbols_r16__twoSlots__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 28 /\ bit_string_len_prop (fst z) (snd z)).

Inductive InvalidSymbolPattern_r16__symbols_r16__Type : Set :=
  | InvalidSymbolPattern_r16__symbols_r16__oneSlot : InvalidSymbolPattern_r16__symbols_r16__oneSlot__Type -> InvalidSymbolPattern_r16__symbols_r16__Type
  | InvalidSymbolPattern_r16__symbols_r16__twoSlots : InvalidSymbolPattern_r16__symbols_r16__twoSlots__Type -> InvalidSymbolPattern_r16__symbols_r16__Type
.
Definition InvalidSymbolPattern_r16__symbols_r16__list : list typ := (
typ_cons InvalidSymbolPattern_r16__symbols_r16__oneSlot__Type InvalidSymbolPattern_r16__symbols_r16__oneSlot__cond ::
typ_cons InvalidSymbolPattern_r16__symbols_r16__twoSlots__Type InvalidSymbolPattern_r16__symbols_r16__twoSlots__cond ::
 nil).
Definition InvalidSymbolPattern_r16__symbols_r16__cond (c : InvalidSymbolPattern_r16__symbols_r16__Type) := 
  match c with
  | InvalidSymbolPattern_r16__symbols_r16__oneSlot t => InvalidSymbolPattern_r16__symbols_r16__oneSlot__cond t 
  | InvalidSymbolPattern_r16__symbols_r16__twoSlots t => InvalidSymbolPattern_r16__symbols_r16__twoSlots__cond t 
  end.

Lemma InvalidSymbolPattern_r16__symbols_r16__len_helper1 : to_bit_sz (length InvalidSymbolPattern_r16__symbols_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma InvalidSymbolPattern_r16__symbols_r16__len_helper2 : 2 <= length2 InvalidSymbolPattern_r16__symbols_r16__list.
 simpl. lia. Qed.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 2 /\ bit_string_len_prop (fst z) (snd z)).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 5 /\ bit_string_len_prop (fst z) (snd z)).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 20 /\ bit_string_len_prop (fst z) (snd z)).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__Type := bit_string_fixed.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 40 /\ bit_string_len_prop (fst z) (snd z)).

Inductive InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type : Set :=
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2 : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__Type -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4 : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__Type -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5 : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__Type -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8 : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__Type -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10 : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__Type -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20 : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__Type -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40 : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__Type -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type
.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__list : list typ := (
typ_cons InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__cond ::
typ_cons InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__cond ::
typ_cons InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__cond ::
typ_cons InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__cond ::
typ_cons InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__cond ::
typ_cons InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__cond ::
typ_cons InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__cond ::
 nil).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__cond (c : InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type) := 
  match c with
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2 t => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__cond t 
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4 t => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__cond t 
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5 t => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__cond t 
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8 t => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__cond t 
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10 t => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__cond t 
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20 t => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__cond t 
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40 t => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__cond t 
  end.

Lemma InvalidSymbolPattern_r16__periodicityAndPattern_r16__len_helper1 : to_bit_sz (length InvalidSymbolPattern_r16__periodicityAndPattern_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma InvalidSymbolPattern_r16__periodicityAndPattern_r16__len_helper2 : 2 <= length2 InvalidSymbolPattern_r16__periodicityAndPattern_r16__list.
 simpl. lia. Qed.
Record InvalidSymbolPattern_r16__Type : Set :=
  make__InvalidSymbolPattern_r16__Type {
    InvalidSymbolPattern_r16__symbols_r16 : InvalidSymbolPattern_r16__symbols_r16__Type ;
    InvalidSymbolPattern_r16__periodicityAndPattern_r16 : option InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type ;
}.
Definition InvalidSymbolPattern_r16__root_list : list seq_elem := (
 Nor InvalidSymbolPattern_r16__symbols_r16__Type InvalidSymbolPattern_r16__symbols_r16__cond ::
 Opt InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__cond ::
 nil).
Definition InvalidSymbolPattern_r16__ext_list : list typ := (
  nil).
Definition InvalidSymbolPattern_r16__cond (z : InvalidSymbolPattern_r16__Type) := 
(  InvalidSymbolPattern_r16__symbols_r16__cond (InvalidSymbolPattern_r16__symbols_r16 z) /\
  opt_cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__cond (InvalidSymbolPattern_r16__periodicityAndPattern_r16 z) /\
  True) /\ 
(  True).


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
Definition InvalidSymbolPattern_r16__symbols_r16__oneSlot__Format : T_Format InvalidSymbolPattern_r16__symbols_r16__oneSlot__Type InvalidSymbolPattern_r16__symbols_r16__oneSlot__cond := (* Eval compute in *) bit_string_fixed_format 14.
Opaque InvalidSymbolPattern_r16__symbols_r16__oneSlot__cond InvalidSymbolPattern_r16__symbols_r16__oneSlot__Format.

Definition InvalidSymbolPattern_r16__symbols_r16__twoSlots__Format : T_Format InvalidSymbolPattern_r16__symbols_r16__twoSlots__Type InvalidSymbolPattern_r16__symbols_r16__twoSlots__cond := (* Eval compute in *) bit_string_fixed_format 28.
Opaque InvalidSymbolPattern_r16__symbols_r16__twoSlots__cond InvalidSymbolPattern_r16__symbols_r16__twoSlots__Format.


Definition InvalidSymbolPattern_r16__symbols_r16__Format_Type := Eval cbn in get_formats InvalidSymbolPattern_r16__symbols_r16__list.
Definition InvalidSymbolPattern_r16__symbols_r16__Format_list : InvalidSymbolPattern_r16__symbols_r16__Format_Type :=
  (InvalidSymbolPattern_r16__symbols_r16__oneSlot__Format, (InvalidSymbolPattern_r16__symbols_r16__twoSlots__Format, unit__Format)).
Definition InvalidSymbolPattern_r16__symbols_r16__list__Format := Eval compute in choice_format InvalidSymbolPattern_r16__symbols_r16__list InvalidSymbolPattern_r16__symbols_r16__len_helper1 InvalidSymbolPattern_r16__symbols_r16__len_helper2  InvalidSymbolPattern_r16__symbols_r16__Format_list.
Definition InvalidSymbolPattern_r16__symbols_r16__F1 (z : InvalidSymbolPattern_r16__symbols_r16__Type) : (choice InvalidSymbolPattern_r16__symbols_r16__list) :=
  match z with
   | InvalidSymbolPattern_r16__symbols_r16__oneSlot t => existT _ 0 t
  | InvalidSymbolPattern_r16__symbols_r16__twoSlots t => existT _ 1 t
  end.
Definition InvalidSymbolPattern_r16__symbols_r16__g := (fun n => typ_set (get_nth_typ InvalidSymbolPattern_r16__symbols_r16__list n)).
Definition InvalidSymbolPattern_r16__symbols_r16__F2 (y : choice InvalidSymbolPattern_r16__symbols_r16__list) : InvalidSymbolPattern_r16__symbols_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (InvalidSymbolPattern_r16__symbols_r16__g n -> InvalidSymbolPattern_r16__symbols_r16__Type) with
    | 0 => fun (t : InvalidSymbolPattern_r16__symbols_r16__oneSlot__Type) => InvalidSymbolPattern_r16__symbols_r16__oneSlot t 
    | 1 => fun (t : InvalidSymbolPattern_r16__symbols_r16__twoSlots__Type) => InvalidSymbolPattern_r16__symbols_r16__twoSlots t 
 | (S (S n0)) => (fun (x' : nat) (t'' : InvalidSymbolPattern_r16__symbols_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ InvalidSymbolPattern_r16__symbols_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len InvalidSymbolPattern_r16__symbols_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return InvalidSymbolPattern_r16__symbols_r16__Type with end) n0
           end t0).

Lemma InvalidSymbolPattern_r16__symbols_r16__helper2 :  forall (y : InvalidSymbolPattern_r16__symbols_r16__Type), InvalidSymbolPattern_r16__symbols_r16__cond y -> choice_cond InvalidSymbolPattern_r16__symbols_r16__list (InvalidSymbolPattern_r16__symbols_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma InvalidSymbolPattern_r16__symbols_r16__helper3 :  forall (y : InvalidSymbolPattern_r16__symbols_r16__Type), InvalidSymbolPattern_r16__symbols_r16__F2 (InvalidSymbolPattern_r16__symbols_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma InvalidSymbolPattern_r16__symbols_r16__helper4 : (forall b : choice InvalidSymbolPattern_r16__symbols_r16__list, choice_cond InvalidSymbolPattern_r16__symbols_r16__list b -> InvalidSymbolPattern_r16__symbols_r16__cond (InvalidSymbolPattern_r16__symbols_r16__F2 b) /\ InvalidSymbolPattern_r16__symbols_r16__F1 (InvalidSymbolPattern_r16__symbols_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length InvalidSymbolPattern_r16__symbols_r16__F1 InvalidSymbolPattern_r16__symbols_r16__F2.
Definition InvalidSymbolPattern_r16__symbols_r16__Format : T_Format InvalidSymbolPattern_r16__symbols_r16__Type InvalidSymbolPattern_r16__symbols_r16__cond :=
  (* Eval compute in *) proj2_format InvalidSymbolPattern_r16__symbols_r16__cond InvalidSymbolPattern_r16__symbols_r16__list__Format InvalidSymbolPattern_r16__symbols_r16__F1 InvalidSymbolPattern_r16__symbols_r16__F2 InvalidSymbolPattern_r16__symbols_r16__helper2 InvalidSymbolPattern_r16__symbols_r16__helper3 InvalidSymbolPattern_r16__symbols_r16__helper4.
Opaque InvalidSymbolPattern_r16__symbols_r16__cond InvalidSymbolPattern_r16__symbols_r16__Format.

Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__Format : T_Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__cond := (* Eval compute in *) bit_string_fixed_format 2.
Opaque InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__Format.

Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__Format : T_Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__Format.

Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__Format : T_Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__cond := (* Eval compute in *) bit_string_fixed_format 5.
Opaque InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__Format.

Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__Format : T_Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__Format.

Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__Format : T_Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__Format.

Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__Format : T_Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__cond := (* Eval compute in *) bit_string_fixed_format 20.
Opaque InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__Format.

Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__Format : T_Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__cond := (* Eval compute in *) bit_string_fixed_format 40.
Opaque InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__Format.


Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__Format_Type := Eval cbn in get_formats InvalidSymbolPattern_r16__periodicityAndPattern_r16__list.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__Format_list : InvalidSymbolPattern_r16__periodicityAndPattern_r16__Format_Type :=
  (InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__Format, (InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__Format, (InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__Format, (InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__Format, (InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__Format, (InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__Format, (InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__Format, unit__Format))))))).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__list__Format := Eval compute in choice_format InvalidSymbolPattern_r16__periodicityAndPattern_r16__list InvalidSymbolPattern_r16__periodicityAndPattern_r16__len_helper1 InvalidSymbolPattern_r16__periodicityAndPattern_r16__len_helper2  InvalidSymbolPattern_r16__periodicityAndPattern_r16__Format_list.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__F1 (z : InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type) : (choice InvalidSymbolPattern_r16__periodicityAndPattern_r16__list) :=
  match z with
   | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2 t => existT _ 0 t
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4 t => existT _ 1 t
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5 t => existT _ 2 t
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8 t => existT _ 3 t
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10 t => existT _ 4 t
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20 t => existT _ 5 t
  | InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40 t => existT _ 6 t
  end.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__g := (fun n => typ_set (get_nth_typ InvalidSymbolPattern_r16__periodicityAndPattern_r16__list n)).
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__F2 (y : choice InvalidSymbolPattern_r16__periodicityAndPattern_r16__list) : InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (InvalidSymbolPattern_r16__periodicityAndPattern_r16__g n -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type) with
    | 0 => fun (t : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2__Type) => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n2 t 
    | 1 => fun (t : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4__Type) => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n4 t 
    | 2 => fun (t : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5__Type) => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n5 t 
    | 3 => fun (t : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8__Type) => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n8 t 
    | 4 => fun (t : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10__Type) => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n10 t 
    | 5 => fun (t : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20__Type) => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n20 t 
    | 6 => fun (t : InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40__Type) => InvalidSymbolPattern_r16__periodicityAndPattern_r16__n40 t 
 | (S (S (S (S (S (S (S n0))))))) => (fun (x' : nat) (t'' : InvalidSymbolPattern_r16__periodicityAndPattern_r16__g (S (S (S (S (S (S (S x')))))))) =>let t' :=
           eq_rect (get_nth_typ InvalidSymbolPattern_r16__periodicityAndPattern_r16__list (S (S (S (S (S (S (S x'))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len InvalidSymbolPattern_r16__periodicityAndPattern_r16__list (S (S (S (S (S (S (S x')))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))) in match t' return InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type with end) n0
           end t0).

Lemma InvalidSymbolPattern_r16__periodicityAndPattern_r16__helper2 :  forall (y : InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type), InvalidSymbolPattern_r16__periodicityAndPattern_r16__cond y -> choice_cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__list (InvalidSymbolPattern_r16__periodicityAndPattern_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma InvalidSymbolPattern_r16__periodicityAndPattern_r16__helper3 :  forall (y : InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type), InvalidSymbolPattern_r16__periodicityAndPattern_r16__F2 (InvalidSymbolPattern_r16__periodicityAndPattern_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma InvalidSymbolPattern_r16__periodicityAndPattern_r16__helper4 : (forall b : choice InvalidSymbolPattern_r16__periodicityAndPattern_r16__list, choice_cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__list b -> InvalidSymbolPattern_r16__periodicityAndPattern_r16__cond (InvalidSymbolPattern_r16__periodicityAndPattern_r16__F2 b) /\ InvalidSymbolPattern_r16__periodicityAndPattern_r16__F1 (InvalidSymbolPattern_r16__periodicityAndPattern_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length InvalidSymbolPattern_r16__periodicityAndPattern_r16__F1 InvalidSymbolPattern_r16__periodicityAndPattern_r16__F2.
Definition InvalidSymbolPattern_r16__periodicityAndPattern_r16__Format : T_Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__Type InvalidSymbolPattern_r16__periodicityAndPattern_r16__cond :=
  (* Eval compute in *) proj2_format InvalidSymbolPattern_r16__periodicityAndPattern_r16__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__list__Format InvalidSymbolPattern_r16__periodicityAndPattern_r16__F1 InvalidSymbolPattern_r16__periodicityAndPattern_r16__F2 InvalidSymbolPattern_r16__periodicityAndPattern_r16__helper2 InvalidSymbolPattern_r16__periodicityAndPattern_r16__helper3 InvalidSymbolPattern_r16__periodicityAndPattern_r16__helper4.
Opaque InvalidSymbolPattern_r16__periodicityAndPattern_r16__cond InvalidSymbolPattern_r16__periodicityAndPattern_r16__Format.


Definition InvalidSymbolPattern_r16__root_Format_Type := Eval cbn in seq_format_prod InvalidSymbolPattern_r16__root_list.
Definition InvalidSymbolPattern_r16__root_Format_list : InvalidSymbolPattern_r16__root_Format_Type :=
  (InvalidSymbolPattern_r16__symbols_r16__Format, (InvalidSymbolPattern_r16__periodicityAndPattern_r16__Format, unit_format)).

Definition InvalidSymbolPattern_r16__ext_Format_Type := Eval cbn in get_formats InvalidSymbolPattern_r16__ext_list.
Definition InvalidSymbolPattern_r16__ext_Format_list : InvalidSymbolPattern_r16__ext_Format_Type :=
  unit__Format.

Definition InvalidSymbolPattern_r16__list_type : Set := (seq_type InvalidSymbolPattern_r16__root_list) * (seq_ext_type InvalidSymbolPattern_r16__ext_list).
Definition InvalidSymbolPattern_r16__list_cond (z : InvalidSymbolPattern_r16__list_type) : Prop :=
        (seq_cond InvalidSymbolPattern_r16__root_list (fst z)) /\ (seq_ext_cond InvalidSymbolPattern_r16__ext_list (snd z)).
Definition InvalidSymbolPattern_r16__list_format : T_Format InvalidSymbolPattern_r16__list_type InvalidSymbolPattern_r16__list_cond :=
 (* Eval compute in *) seq_ext_format InvalidSymbolPattern_r16__root_list InvalidSymbolPattern_r16__root_Format_list InvalidSymbolPattern_r16__ext_list InvalidSymbolPattern_r16__ext_Format_list.

Opaque InvalidSymbolPattern_r16__list_format.
Definition InvalidSymbolPattern_r16__F1 (z : InvalidSymbolPattern_r16__Type) : InvalidSymbolPattern_r16__list_type :=
  (((InvalidSymbolPattern_r16__symbols_r16 z, (InvalidSymbolPattern_r16__periodicityAndPattern_r16 z, tt))), (
tt)).
Definition InvalidSymbolPattern_r16__F2 (y : InvalidSymbolPattern_r16__list_type) : InvalidSymbolPattern_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__InvalidSymbolPattern_r16__Type j0 j1
  end.
Definition InvalidSymbolPattern_r16__helper1 : (forall a : InvalidSymbolPattern_r16__Type, InvalidSymbolPattern_r16__cond a -> InvalidSymbolPattern_r16__list_cond (InvalidSymbolPattern_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition InvalidSymbolPattern_r16__helper2 : (forall a : InvalidSymbolPattern_r16__Type, InvalidSymbolPattern_r16__F2 (InvalidSymbolPattern_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition InvalidSymbolPattern_r16__helper3 : (forall b : InvalidSymbolPattern_r16__list_type, InvalidSymbolPattern_r16__list_cond b -> InvalidSymbolPattern_r16__cond (InvalidSymbolPattern_r16__F2 b) /\ InvalidSymbolPattern_r16__F1 (InvalidSymbolPattern_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold InvalidSymbolPattern_r16__cond, InvalidSymbolPattern_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition InvalidSymbolPattern_r16__Format : T_Format InvalidSymbolPattern_r16__Type InvalidSymbolPattern_r16__cond :=
 proj2_format InvalidSymbolPattern_r16__cond InvalidSymbolPattern_r16__list_format  InvalidSymbolPattern_r16__F1 InvalidSymbolPattern_r16__F2 InvalidSymbolPattern_r16__helper1 InvalidSymbolPattern_r16__helper2 InvalidSymbolPattern_r16__helper3.

Opaque InvalidSymbolPattern_r16__cond InvalidSymbolPattern_r16__Format.

