Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Type : Set :=
 | MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__true
.
Definition MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__cond := (fun (_ : MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Type) => True).
Lemma MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__nat__helper.

Definition MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F1 t :=
  match t with
  | MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__true => 0
  end.
Definition MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F2 n :=
  match n with
  | 0 => MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__true
  | _ => MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__true
  end.
Lemma MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F1F2 : forall x : MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Type, (MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F1 x <= 0) /\ MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F2 (MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F1 x) = x. imp_solve. Qed.
Lemma MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F2F1 : forall (y : nat) (H : y <= 0), MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F1 (MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F2 y) = y. enum_solve H y. Qed.


Inductive MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type : Set :=
  | MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__nr_SCG : octet_string -> MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type
  | MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__eutra_SCG : octet_string -> MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type
.
Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list : list typ := (
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
typ_cons octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__cond (c : MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type) := 
  match c with
  | MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__nr_SCG t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  | MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__eutra_SCG t => (fun (b : octet_string) => length b < Nat.pow 2 14) t 
  end.

Lemma MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__len_helper1 : to_bit_sz (length MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__len_helper2 : 2 <= length2 MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list.
 simpl. lia. Qed.
Record MRDC_SecondaryCellGroupConfig__Type : Set :=
  make__MRDC_SecondaryCellGroupConfig__Type {
    MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd : option MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Type ;
    MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup : MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type ;
}.
Definition MRDC_SecondaryCellGroupConfig__list := (
 Opt MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Type MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__cond ::
 Nor MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__cond ::
 nil).
Definition MRDC_SecondaryCellGroupConfig__cond z := 
  opt_cond MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__cond (MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd z) /\
  MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__cond (MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup z) /\
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
Definition MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Format : T_Format MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__nat__Format MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F1 MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F2 MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F1F2 MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__F2F1.

Opaque MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__cond MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Format.


Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Format_Type := Eval cbn in get_formats MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list.
Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Format_list : MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Format_Type :=
  (octet_string_nc__Format, (octet_string_nc__Format, unit__Format)).
Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list__Format := Eval compute in choice_format MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__len_helper1 MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__len_helper2  MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Format_list.
Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F1 (z : MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type) : (choice MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list) :=
  match z with
   | MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__nr_SCG t => existT _ 0 t
  | MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__eutra_SCG t => existT _ 1 t
  end.
Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__g := (fun n => typ_set (get_nth_typ MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list n)).
Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F2 (y : choice MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list) : MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__g n -> MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type) with
    | 0 => fun (t : octet_string) => MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__nr_SCG t 
    | 1 => fun (t : octet_string) => MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__eutra_SCG t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type with end) n0
           end t0).

Lemma MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__helper2 :  forall (y : MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type), MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__cond y -> choice_cond MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list (MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__helper3 :  forall (y : MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type), MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F2 (MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__helper4 : (forall b : choice MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list, choice_cond MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list b -> MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__cond (MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F2 b) /\ MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F1 (MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F1 MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F2.
Definition MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Format : T_Format MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Type MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__cond :=
  (* Eval compute in *) proj2_format MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__cond MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__list__Format MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F1 MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__F2 MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__helper2 MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__helper3 MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__helper4.
Opaque MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__cond MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Format.


Definition MRDC_SecondaryCellGroupConfig__Format_Type := Eval cbn in seq_format_prod MRDC_SecondaryCellGroupConfig__list.
Definition MRDC_SecondaryCellGroupConfig__Format_list : MRDC_SecondaryCellGroupConfig__Format_Type :=
  (MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd__Format, (MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup__Format, unit_format)).
Definition MRDC_SecondaryCellGroupConfig__list__Format := (*Eval compute in *) seq_format MRDC_SecondaryCellGroupConfig__list MRDC_SecondaryCellGroupConfig__Format_list.
Definition MRDC_SecondaryCellGroupConfig__F1 z :=
  (MRDC_SecondaryCellGroupConfig__mrdc_ReleaseAndAdd z, (MRDC_SecondaryCellGroupConfig__mrdc_SecondaryCellGroup z, tt)).
Definition MRDC_SecondaryCellGroupConfig__F2 (y : seq_type MRDC_SecondaryCellGroupConfig__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MRDC_SecondaryCellGroupConfig__Type i0 i1
  end.
Lemma MRDC_SecondaryCellGroupConfig__F1F2_cond (z : MRDC_SecondaryCellGroupConfig__Type)
  : MRDC_SecondaryCellGroupConfig__cond z ->
  (seq_cond MRDC_SecondaryCellGroupConfig__list (MRDC_SecondaryCellGroupConfig__F1 z)).
intro H. unfold MRDC_SecondaryCellGroupConfig__cond in H. simpl. auto. Qed.
Lemma MRDC_SecondaryCellGroupConfig__F1F2_cond2 (z : MRDC_SecondaryCellGroupConfig__Type)
 : MRDC_SecondaryCellGroupConfig__F2 (MRDC_SecondaryCellGroupConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRDC_SecondaryCellGroupConfig__F2F1_cond (y : seq_type MRDC_SecondaryCellGroupConfig__list)
  : seq_cond MRDC_SecondaryCellGroupConfig__list y ->
 (MRDC_SecondaryCellGroupConfig__cond (MRDC_SecondaryCellGroupConfig__F2 y)) /\  MRDC_SecondaryCellGroupConfig__F1 (MRDC_SecondaryCellGroupConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRDC_SecondaryCellGroupConfig__cond. simpl in *. auto.
 - simpl. unfold MRDC_SecondaryCellGroupConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRDC_SecondaryCellGroupConfig__Format : T_Format MRDC_SecondaryCellGroupConfig__Type MRDC_SecondaryCellGroupConfig__cond :=
        proj2_format  MRDC_SecondaryCellGroupConfig__cond MRDC_SecondaryCellGroupConfig__list__Format
    MRDC_SecondaryCellGroupConfig__F1 MRDC_SecondaryCellGroupConfig__F2 MRDC_SecondaryCellGroupConfig__F1F2_cond  MRDC_SecondaryCellGroupConfig__F1F2_cond2 MRDC_SecondaryCellGroupConfig__F2F1_cond.
Opaque MRDC_SecondaryCellGroupConfig__cond MRDC_SecondaryCellGroupConfig__Format.

