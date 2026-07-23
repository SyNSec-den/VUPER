Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Type : Set :=
 | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0
 | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0dot4
 | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0dot8
 | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s1dot6
 | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s3
 | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s6
 | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s12
 | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s30
.
Definition OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__cond := (fun (_ : OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Type) => True).
Lemma OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__nat__helper.

Definition OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F1 t :=
  match t with
  | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0 => 0
  | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0dot4 => 1
  | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0dot8 => 2
  | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s1dot6 => 3
  | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s3 => 4
  | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s6 => 5
  | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s12 => 6
  | OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s30 => 7
  end.
Definition OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F2 n :=
  match n with
  | 0 => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0
  | 1 => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0dot4
  | 2 => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0dot8
  | 3 => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s1dot6
  | 4 => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s3
  | 5 => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s6
  | 6 => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s12
  | 7 => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s30
  | _ => OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__s0
  end.
Lemma OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F1F2 : forall x : OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Type, (OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F1 x <= 7) /\ OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F2 (OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F1 x) = x. imp_solve. Qed.
Lemma OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F2F1 : forall (y : nat) (H : y <= 7), OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F1 (OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F2 y) = y. enum_solve H y. Qed.

Record OtherConfig__delayBudgetReportingConfig__setup__Type : Set :=
  make__OtherConfig__delayBudgetReportingConfig__setup__Type {
    OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer : OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Type ;
}.
Definition OtherConfig__delayBudgetReportingConfig__setup__list := (
 Nor OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Type OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__cond ::
 nil).
Definition OtherConfig__delayBudgetReportingConfig__setup__cond z := 
  OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__cond (OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer z) /\
  True.


Inductive OtherConfig__delayBudgetReportingConfig__Type : Set :=
  | OtherConfig__delayBudgetReportingConfig__release : unit -> OtherConfig__delayBudgetReportingConfig__Type
  | OtherConfig__delayBudgetReportingConfig__setup : OtherConfig__delayBudgetReportingConfig__setup__Type -> OtherConfig__delayBudgetReportingConfig__Type
.
Definition OtherConfig__delayBudgetReportingConfig__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons OtherConfig__delayBudgetReportingConfig__setup__Type OtherConfig__delayBudgetReportingConfig__setup__cond ::
 nil).
Definition OtherConfig__delayBudgetReportingConfig__cond (c : OtherConfig__delayBudgetReportingConfig__Type) := 
  match c with
  | OtherConfig__delayBudgetReportingConfig__release t => (fun _ => True) t 
  | OtherConfig__delayBudgetReportingConfig__setup t => OtherConfig__delayBudgetReportingConfig__setup__cond t 
  end.

Lemma OtherConfig__delayBudgetReportingConfig__len_helper1 : to_bit_sz (length OtherConfig__delayBudgetReportingConfig__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma OtherConfig__delayBudgetReportingConfig__len_helper2 : 2 <= length2 OtherConfig__delayBudgetReportingConfig__list.
 simpl. lia. Qed.
Record OtherConfig__Type : Set :=
  make__OtherConfig__Type {
    OtherConfig__delayBudgetReportingConfig : option OtherConfig__delayBudgetReportingConfig__Type ;
}.
Definition OtherConfig__list := (
 Opt OtherConfig__delayBudgetReportingConfig__Type OtherConfig__delayBudgetReportingConfig__cond ::
 nil).
Definition OtherConfig__cond z := 
  opt_cond OtherConfig__delayBudgetReportingConfig__cond (OtherConfig__delayBudgetReportingConfig z) /\
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
Definition OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Format : T_Format OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Type (fun _ => True) :=
(* Eval compute in *) proj3_format OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__nat__Format OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F1 OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F2 OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F1F2 OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__F2F1.

Opaque OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__cond OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Format.


Definition OtherConfig__delayBudgetReportingConfig__setup__Format_Type := Eval cbn in seq_format_prod OtherConfig__delayBudgetReportingConfig__setup__list.
Definition OtherConfig__delayBudgetReportingConfig__setup__Format_list : OtherConfig__delayBudgetReportingConfig__setup__Format_Type :=
  (OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer__Format, unit_format).
Definition OtherConfig__delayBudgetReportingConfig__setup__list__Format := (*Eval compute in *) seq_format OtherConfig__delayBudgetReportingConfig__setup__list OtherConfig__delayBudgetReportingConfig__setup__Format_list.
Definition OtherConfig__delayBudgetReportingConfig__setup__F1 z :=
  (OtherConfig__delayBudgetReportingConfig__setup__delayBudgetReportingProhibitTimer z, tt).
Definition OtherConfig__delayBudgetReportingConfig__setup__F2 (y : seq_type OtherConfig__delayBudgetReportingConfig__setup__list) :=
  match y with
  | (i0, _)=>
    make__OtherConfig__delayBudgetReportingConfig__setup__Type i0
  end.
Lemma OtherConfig__delayBudgetReportingConfig__setup__F1F2_cond (z : OtherConfig__delayBudgetReportingConfig__setup__Type)
  : OtherConfig__delayBudgetReportingConfig__setup__cond z ->
  (seq_cond OtherConfig__delayBudgetReportingConfig__setup__list (OtherConfig__delayBudgetReportingConfig__setup__F1 z)).
intro H. unfold OtherConfig__delayBudgetReportingConfig__setup__cond in H. simpl. auto. Qed.
Lemma OtherConfig__delayBudgetReportingConfig__setup__F1F2_cond2 (z : OtherConfig__delayBudgetReportingConfig__setup__Type)
 : OtherConfig__delayBudgetReportingConfig__setup__F2 (OtherConfig__delayBudgetReportingConfig__setup__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OtherConfig__delayBudgetReportingConfig__setup__F2F1_cond (y : seq_type OtherConfig__delayBudgetReportingConfig__setup__list)
  : seq_cond OtherConfig__delayBudgetReportingConfig__setup__list y ->
 (OtherConfig__delayBudgetReportingConfig__setup__cond (OtherConfig__delayBudgetReportingConfig__setup__F2 y)) /\  OtherConfig__delayBudgetReportingConfig__setup__F1 (OtherConfig__delayBudgetReportingConfig__setup__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OtherConfig__delayBudgetReportingConfig__setup__cond. simpl in *. auto.
 - simpl. unfold OtherConfig__delayBudgetReportingConfig__setup__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OtherConfig__delayBudgetReportingConfig__setup__Format : T_Format OtherConfig__delayBudgetReportingConfig__setup__Type OtherConfig__delayBudgetReportingConfig__setup__cond :=
        proj2_format  OtherConfig__delayBudgetReportingConfig__setup__cond OtherConfig__delayBudgetReportingConfig__setup__list__Format
    OtherConfig__delayBudgetReportingConfig__setup__F1 OtherConfig__delayBudgetReportingConfig__setup__F2 OtherConfig__delayBudgetReportingConfig__setup__F1F2_cond  OtherConfig__delayBudgetReportingConfig__setup__F1F2_cond2 OtherConfig__delayBudgetReportingConfig__setup__F2F1_cond.
Opaque OtherConfig__delayBudgetReportingConfig__setup__cond OtherConfig__delayBudgetReportingConfig__setup__Format.


Definition OtherConfig__delayBudgetReportingConfig__Format_Type := Eval cbn in get_formats OtherConfig__delayBudgetReportingConfig__list.
Definition OtherConfig__delayBudgetReportingConfig__Format_list : OtherConfig__delayBudgetReportingConfig__Format_Type :=
  (unit__Format, (OtherConfig__delayBudgetReportingConfig__setup__Format, unit__Format)).
Definition OtherConfig__delayBudgetReportingConfig__list__Format := Eval compute in choice_format OtherConfig__delayBudgetReportingConfig__list OtherConfig__delayBudgetReportingConfig__len_helper1 OtherConfig__delayBudgetReportingConfig__len_helper2  OtherConfig__delayBudgetReportingConfig__Format_list.
Definition OtherConfig__delayBudgetReportingConfig__F1 (z : OtherConfig__delayBudgetReportingConfig__Type) : (choice OtherConfig__delayBudgetReportingConfig__list) :=
  match z with
   | OtherConfig__delayBudgetReportingConfig__release t => existT _ 0 t
  | OtherConfig__delayBudgetReportingConfig__setup t => existT _ 1 t
  end.
Definition OtherConfig__delayBudgetReportingConfig__g := (fun n => typ_set (get_nth_typ OtherConfig__delayBudgetReportingConfig__list n)).
Definition OtherConfig__delayBudgetReportingConfig__F2 (y : choice OtherConfig__delayBudgetReportingConfig__list) : OtherConfig__delayBudgetReportingConfig__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (OtherConfig__delayBudgetReportingConfig__g n -> OtherConfig__delayBudgetReportingConfig__Type) with
    | 0 => fun (t : unit) => OtherConfig__delayBudgetReportingConfig__release t 
    | 1 => fun (t : OtherConfig__delayBudgetReportingConfig__setup__Type) => OtherConfig__delayBudgetReportingConfig__setup t 
 | (S (S n0)) => (fun (x' : nat) (t'' : OtherConfig__delayBudgetReportingConfig__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ OtherConfig__delayBudgetReportingConfig__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len OtherConfig__delayBudgetReportingConfig__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return OtherConfig__delayBudgetReportingConfig__Type with end) n0
           end t0).

Lemma OtherConfig__delayBudgetReportingConfig__helper2 :  forall (y : OtherConfig__delayBudgetReportingConfig__Type), OtherConfig__delayBudgetReportingConfig__cond y -> choice_cond OtherConfig__delayBudgetReportingConfig__list (OtherConfig__delayBudgetReportingConfig__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma OtherConfig__delayBudgetReportingConfig__helper3 :  forall (y : OtherConfig__delayBudgetReportingConfig__Type), OtherConfig__delayBudgetReportingConfig__F2 (OtherConfig__delayBudgetReportingConfig__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma OtherConfig__delayBudgetReportingConfig__helper4 : (forall b : choice OtherConfig__delayBudgetReportingConfig__list, choice_cond OtherConfig__delayBudgetReportingConfig__list b -> OtherConfig__delayBudgetReportingConfig__cond (OtherConfig__delayBudgetReportingConfig__F2 b) /\ OtherConfig__delayBudgetReportingConfig__F1 (OtherConfig__delayBudgetReportingConfig__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length OtherConfig__delayBudgetReportingConfig__F1 OtherConfig__delayBudgetReportingConfig__F2.
Definition OtherConfig__delayBudgetReportingConfig__Format : T_Format OtherConfig__delayBudgetReportingConfig__Type OtherConfig__delayBudgetReportingConfig__cond :=
  (* Eval compute in *) proj2_format OtherConfig__delayBudgetReportingConfig__cond OtherConfig__delayBudgetReportingConfig__list__Format OtherConfig__delayBudgetReportingConfig__F1 OtherConfig__delayBudgetReportingConfig__F2 OtherConfig__delayBudgetReportingConfig__helper2 OtherConfig__delayBudgetReportingConfig__helper3 OtherConfig__delayBudgetReportingConfig__helper4.
Opaque OtherConfig__delayBudgetReportingConfig__cond OtherConfig__delayBudgetReportingConfig__Format.


Definition OtherConfig__Format_Type := Eval cbn in seq_format_prod OtherConfig__list.
Definition OtherConfig__Format_list : OtherConfig__Format_Type :=
  (OtherConfig__delayBudgetReportingConfig__Format, unit_format).
Definition OtherConfig__list__Format := (*Eval compute in *) seq_format OtherConfig__list OtherConfig__Format_list.
Definition OtherConfig__F1 z :=
  (OtherConfig__delayBudgetReportingConfig z, tt).
Definition OtherConfig__F2 (y : seq_type OtherConfig__list) :=
  match y with
  | (i0, _)=>
    make__OtherConfig__Type i0
  end.
Lemma OtherConfig__F1F2_cond (z : OtherConfig__Type)
  : OtherConfig__cond z ->
  (seq_cond OtherConfig__list (OtherConfig__F1 z)).
intro H. unfold OtherConfig__cond in H. simpl. auto. Qed.
Lemma OtherConfig__F1F2_cond2 (z : OtherConfig__Type)
 : OtherConfig__F2 (OtherConfig__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma OtherConfig__F2F1_cond (y : seq_type OtherConfig__list)
  : seq_cond OtherConfig__list y ->
 (OtherConfig__cond (OtherConfig__F2 y)) /\  OtherConfig__F1 (OtherConfig__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold OtherConfig__cond. simpl in *. auto.
 - simpl. unfold OtherConfig__F1. simpl. destruct_all_unit. auto.   Qed.
Definition OtherConfig__Format : T_Format OtherConfig__Type OtherConfig__cond :=
        proj2_format  OtherConfig__cond OtherConfig__list__Format
    OtherConfig__F1 OtherConfig__F2 OtherConfig__F1F2_cond  OtherConfig__F1F2_cond2 OtherConfig__F2F1_cond.
Opaque OtherConfig__cond OtherConfig__Format.

