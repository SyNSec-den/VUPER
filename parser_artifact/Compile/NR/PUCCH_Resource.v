Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PUCCH_ResourceId.

Opaque PUCCH_ResourceId__cond PUCCH_ResourceId__Format.

Require Import NR.PRB_Id.

Opaque PRB_Id__cond PRB_Id__Format.

Inductive PUCCH_Resource__intraSlotFrequencyHopping__Type : Set :=
 | PUCCH_Resource__intraSlotFrequencyHopping__enabled
.
Definition PUCCH_Resource__intraSlotFrequencyHopping__cond := (fun (_ : PUCCH_Resource__intraSlotFrequencyHopping__Type) => True).
Lemma PUCCH_Resource__intraSlotFrequencyHopping__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PUCCH_Resource__intraSlotFrequencyHopping__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PUCCH_Resource__intraSlotFrequencyHopping__nat__helper.

Definition PUCCH_Resource__intraSlotFrequencyHopping__F1 t :=
  match t with
  | PUCCH_Resource__intraSlotFrequencyHopping__enabled => 0
  end.
Definition PUCCH_Resource__intraSlotFrequencyHopping__F2 n :=
  match n with
  | 0 => PUCCH_Resource__intraSlotFrequencyHopping__enabled
  | _ => PUCCH_Resource__intraSlotFrequencyHopping__enabled
  end.
Lemma PUCCH_Resource__intraSlotFrequencyHopping__F1F2 : forall x : PUCCH_Resource__intraSlotFrequencyHopping__Type, (PUCCH_Resource__intraSlotFrequencyHopping__F1 x <= 0) /\ PUCCH_Resource__intraSlotFrequencyHopping__F2 (PUCCH_Resource__intraSlotFrequencyHopping__F1 x) = x. imp_solve. Qed.
Lemma PUCCH_Resource__intraSlotFrequencyHopping__F2F1 : forall (y : nat) (H : y <= 0), PUCCH_Resource__intraSlotFrequencyHopping__F1 (PUCCH_Resource__intraSlotFrequencyHopping__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PRB_Id.

Opaque PRB_Id__cond PRB_Id__Format.

Require Import NR.PUCCH_format0.

Opaque PUCCH_format0__cond PUCCH_format0__Format.

Require Import NR.PUCCH_format1.

Opaque PUCCH_format1__cond PUCCH_format1__Format.

Require Import NR.PUCCH_format2.

Opaque PUCCH_format2__cond PUCCH_format2__Format.

Require Import NR.PUCCH_format3.

Opaque PUCCH_format3__cond PUCCH_format3__Format.

Require Import NR.PUCCH_format4.

Opaque PUCCH_format4__cond PUCCH_format4__Format.


Inductive PUCCH_Resource__format__Type : Set :=
  | PUCCH_Resource__format__format0 : PUCCH_format0__Type -> PUCCH_Resource__format__Type
  | PUCCH_Resource__format__format1 : PUCCH_format1__Type -> PUCCH_Resource__format__Type
  | PUCCH_Resource__format__format2 : PUCCH_format2__Type -> PUCCH_Resource__format__Type
  | PUCCH_Resource__format__format3 : PUCCH_format3__Type -> PUCCH_Resource__format__Type
  | PUCCH_Resource__format__format4 : PUCCH_format4__Type -> PUCCH_Resource__format__Type
.
Definition PUCCH_Resource__format__list : list typ := (
typ_cons PUCCH_format0__Type PUCCH_format0__cond ::
typ_cons PUCCH_format1__Type PUCCH_format1__cond ::
typ_cons PUCCH_format2__Type PUCCH_format2__cond ::
typ_cons PUCCH_format3__Type PUCCH_format3__cond ::
typ_cons PUCCH_format4__Type PUCCH_format4__cond ::
 nil).
Definition PUCCH_Resource__format__cond (c : PUCCH_Resource__format__Type) := 
  match c with
  | PUCCH_Resource__format__format0 t => PUCCH_format0__cond t 
  | PUCCH_Resource__format__format1 t => PUCCH_format1__cond t 
  | PUCCH_Resource__format__format2 t => PUCCH_format2__cond t 
  | PUCCH_Resource__format__format3 t => PUCCH_format3__cond t 
  | PUCCH_Resource__format__format4 t => PUCCH_format4__cond t 
  end.

Lemma PUCCH_Resource__format__len_helper1 : to_bit_sz (length PUCCH_Resource__format__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PUCCH_Resource__format__len_helper2 : 2 <= length2 PUCCH_Resource__format__list.
 simpl. lia. Qed.
Record PUCCH_Resource__Type : Set :=
  make__PUCCH_Resource__Type {
    PUCCH_Resource__pucch_ResourceId : PUCCH_ResourceId__Type ;
    PUCCH_Resource__startingPRB : PRB_Id__Type ;
    PUCCH_Resource__intraSlotFrequencyHopping : option PUCCH_Resource__intraSlotFrequencyHopping__Type ;
    PUCCH_Resource__secondHopPRB : option PRB_Id__Type ;
    PUCCH_Resource__format : PUCCH_Resource__format__Type ;
}.
Definition PUCCH_Resource__list := (
 Nor PUCCH_ResourceId__Type PUCCH_ResourceId__cond ::
 Nor PRB_Id__Type PRB_Id__cond ::
 Opt PUCCH_Resource__intraSlotFrequencyHopping__Type PUCCH_Resource__intraSlotFrequencyHopping__cond ::
 Opt PRB_Id__Type PRB_Id__cond ::
 Nor PUCCH_Resource__format__Type PUCCH_Resource__format__cond ::
 nil).
Definition PUCCH_Resource__cond z := 
  PUCCH_ResourceId__cond (PUCCH_Resource__pucch_ResourceId z) /\
  PRB_Id__cond (PUCCH_Resource__startingPRB z) /\
  opt_cond PUCCH_Resource__intraSlotFrequencyHopping__cond (PUCCH_Resource__intraSlotFrequencyHopping z) /\
  opt_cond PRB_Id__cond (PUCCH_Resource__secondHopPRB z) /\
  PUCCH_Resource__format__cond (PUCCH_Resource__format z) /\
  True.


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
Definition PUCCH_Resource__intraSlotFrequencyHopping__Format : T_Format PUCCH_Resource__intraSlotFrequencyHopping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PUCCH_Resource__intraSlotFrequencyHopping__nat__Format PUCCH_Resource__intraSlotFrequencyHopping__F1 PUCCH_Resource__intraSlotFrequencyHopping__F2 PUCCH_Resource__intraSlotFrequencyHopping__F1F2 PUCCH_Resource__intraSlotFrequencyHopping__F2F1.

Opaque PUCCH_Resource__intraSlotFrequencyHopping__cond PUCCH_Resource__intraSlotFrequencyHopping__Format.


Definition PUCCH_Resource__format__Format_Type := Eval cbn in get_formats PUCCH_Resource__format__list.
Definition PUCCH_Resource__format__Format_list : PUCCH_Resource__format__Format_Type :=
  (PUCCH_format0__Format, (PUCCH_format1__Format, (PUCCH_format2__Format, (PUCCH_format3__Format, (PUCCH_format4__Format, unit__Format))))).
Definition PUCCH_Resource__format__list__Format := Eval compute in choice_format PUCCH_Resource__format__list PUCCH_Resource__format__len_helper1 PUCCH_Resource__format__len_helper2  PUCCH_Resource__format__Format_list.
Definition PUCCH_Resource__format__F1 (z : PUCCH_Resource__format__Type) : (choice PUCCH_Resource__format__list) :=
  match z with
   | PUCCH_Resource__format__format0 t => existT _ 0 t
  | PUCCH_Resource__format__format1 t => existT _ 1 t
  | PUCCH_Resource__format__format2 t => existT _ 2 t
  | PUCCH_Resource__format__format3 t => existT _ 3 t
  | PUCCH_Resource__format__format4 t => existT _ 4 t
  end.
Definition PUCCH_Resource__format__g := (fun n => typ_set (get_nth_typ PUCCH_Resource__format__list n)).
Definition PUCCH_Resource__format__F2 (y : choice PUCCH_Resource__format__list) : PUCCH_Resource__format__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PUCCH_Resource__format__g n -> PUCCH_Resource__format__Type) with
    | 0 => fun (t : PUCCH_format0__Type) => PUCCH_Resource__format__format0 t 
    | 1 => fun (t : PUCCH_format1__Type) => PUCCH_Resource__format__format1 t 
    | 2 => fun (t : PUCCH_format2__Type) => PUCCH_Resource__format__format2 t 
    | 3 => fun (t : PUCCH_format3__Type) => PUCCH_Resource__format__format3 t 
    | 4 => fun (t : PUCCH_format4__Type) => PUCCH_Resource__format__format4 t 
 | (S (S (S (S (S n0))))) => (fun (x' : nat) (t'' : PUCCH_Resource__format__g (S (S (S (S (S x')))))) =>let t' :=
           eq_rect (get_nth_typ PUCCH_Resource__format__list (S (S (S (S (S x'))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PUCCH_Resource__format__list (S (S (S (S (S x')))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))) in match t' return PUCCH_Resource__format__Type with end) n0
           end t0).

Lemma PUCCH_Resource__format__helper2 :  forall (y : PUCCH_Resource__format__Type), PUCCH_Resource__format__cond y -> choice_cond PUCCH_Resource__format__list (PUCCH_Resource__format__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PUCCH_Resource__format__helper3 :  forall (y : PUCCH_Resource__format__Type), PUCCH_Resource__format__F2 (PUCCH_Resource__format__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PUCCH_Resource__format__helper4 : (forall b : choice PUCCH_Resource__format__list, choice_cond PUCCH_Resource__format__list b -> PUCCH_Resource__format__cond (PUCCH_Resource__format__F2 b) /\ PUCCH_Resource__format__F1 (PUCCH_Resource__format__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PUCCH_Resource__format__F1 PUCCH_Resource__format__F2.
Definition PUCCH_Resource__format__Format : T_Format PUCCH_Resource__format__Type PUCCH_Resource__format__cond :=
  (* Eval compute in *) proj2_format PUCCH_Resource__format__cond PUCCH_Resource__format__list__Format PUCCH_Resource__format__F1 PUCCH_Resource__format__F2 PUCCH_Resource__format__helper2 PUCCH_Resource__format__helper3 PUCCH_Resource__format__helper4.
Opaque PUCCH_Resource__format__cond PUCCH_Resource__format__Format.


Definition PUCCH_Resource__Format_Type := Eval cbn in seq_format_prod PUCCH_Resource__list.
Definition PUCCH_Resource__Format_list : PUCCH_Resource__Format_Type :=
  (PUCCH_ResourceId__Format, (PRB_Id__Format, (PUCCH_Resource__intraSlotFrequencyHopping__Format, (PRB_Id__Format, (PUCCH_Resource__format__Format, unit_format))))).
Definition PUCCH_Resource__list__Format := (*Eval compute in *) seq_format PUCCH_Resource__list PUCCH_Resource__Format_list.
Definition PUCCH_Resource__F1 z :=
  (PUCCH_Resource__pucch_ResourceId z, (PUCCH_Resource__startingPRB z, (PUCCH_Resource__intraSlotFrequencyHopping z, (PUCCH_Resource__secondHopPRB z, (PUCCH_Resource__format z, tt))))).
Definition PUCCH_Resource__F2 (y : seq_type PUCCH_Resource__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__PUCCH_Resource__Type i0 i1 i2 i3 i4
  end.
Lemma PUCCH_Resource__F1F2_cond (z : PUCCH_Resource__Type)
  : PUCCH_Resource__cond z ->
  (seq_cond PUCCH_Resource__list (PUCCH_Resource__F1 z)).
intro H. unfold PUCCH_Resource__cond in H. simpl. auto. Qed.
Lemma PUCCH_Resource__F1F2_cond2 (z : PUCCH_Resource__Type)
 : PUCCH_Resource__F2 (PUCCH_Resource__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PUCCH_Resource__F2F1_cond (y : seq_type PUCCH_Resource__list)
  : seq_cond PUCCH_Resource__list y ->
 (PUCCH_Resource__cond (PUCCH_Resource__F2 y)) /\  PUCCH_Resource__F1 (PUCCH_Resource__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PUCCH_Resource__cond. simpl in *. auto.
 - simpl. unfold PUCCH_Resource__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PUCCH_Resource__Format : T_Format PUCCH_Resource__Type PUCCH_Resource__cond :=
        proj2_format  PUCCH_Resource__cond PUCCH_Resource__list__Format
    PUCCH_Resource__F1 PUCCH_Resource__F2 PUCCH_Resource__F1F2_cond  PUCCH_Resource__F1F2_cond2 PUCCH_Resource__F2F1_cond.
Opaque PUCCH_Resource__cond PUCCH_Resource__Format.

