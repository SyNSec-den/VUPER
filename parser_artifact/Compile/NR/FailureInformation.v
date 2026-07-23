Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FailureInformation_IEs.

Opaque FailureInformation_IEs__cond FailureInformation_IEs__Format.

Record FailureInformation__criticalExtensions__criticalExtensionsFuture__Type : Set := make__FailureInformation__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition FailureInformation__criticalExtensions__criticalExtensionsFuture__cond (z : FailureInformation__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive FailureInformation__criticalExtensions__Type : Set :=
  | FailureInformation__criticalExtensions__failureInformation : FailureInformation_IEs__Type -> FailureInformation__criticalExtensions__Type
  | FailureInformation__criticalExtensions__criticalExtensionsFuture : FailureInformation__criticalExtensions__criticalExtensionsFuture__Type -> FailureInformation__criticalExtensions__Type
.
Definition FailureInformation__criticalExtensions__list : list typ := (
typ_cons FailureInformation_IEs__Type FailureInformation_IEs__cond ::
typ_cons FailureInformation__criticalExtensions__criticalExtensionsFuture__Type FailureInformation__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition FailureInformation__criticalExtensions__cond (c : FailureInformation__criticalExtensions__Type) := 
  match c with
  | FailureInformation__criticalExtensions__failureInformation t => FailureInformation_IEs__cond t 
  | FailureInformation__criticalExtensions__criticalExtensionsFuture t => FailureInformation__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma FailureInformation__criticalExtensions__len_helper1 : to_bit_sz (length FailureInformation__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma FailureInformation__criticalExtensions__len_helper2 : 2 <= length2 FailureInformation__criticalExtensions__list.
 simpl. lia. Qed.
Record FailureInformation__Type : Set :=
  make__FailureInformation__Type {
    FailureInformation__criticalExtensions : FailureInformation__criticalExtensions__Type ;
}.
Definition FailureInformation__list := (
 Nor FailureInformation__criticalExtensions__Type FailureInformation__criticalExtensions__cond ::
 nil).
Definition FailureInformation__cond z := 
  FailureInformation__criticalExtensions__cond (FailureInformation__criticalExtensions z) /\
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
Definition FailureInformation__criticalExtensions__criticalExtensionsFuture__helper : forall a : FailureInformation__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__FailureInformation__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition FailureInformation__criticalExtensions__criticalExtensionsFuture__Format : T_Format FailureInformation__criticalExtensions__criticalExtensionsFuture__Type FailureInformation__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__FailureInformation__criticalExtensions__criticalExtensionsFuture__Type)
    FailureInformation__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque FailureInformation__criticalExtensions__criticalExtensionsFuture__cond FailureInformation__criticalExtensions__criticalExtensionsFuture__Format.


Definition FailureInformation__criticalExtensions__Format_Type := Eval cbn in get_formats FailureInformation__criticalExtensions__list.
Definition FailureInformation__criticalExtensions__Format_list : FailureInformation__criticalExtensions__Format_Type :=
  (FailureInformation_IEs__Format, (FailureInformation__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition FailureInformation__criticalExtensions__list__Format := Eval compute in choice_format FailureInformation__criticalExtensions__list FailureInformation__criticalExtensions__len_helper1 FailureInformation__criticalExtensions__len_helper2  FailureInformation__criticalExtensions__Format_list.
Definition FailureInformation__criticalExtensions__F1 (z : FailureInformation__criticalExtensions__Type) : (choice FailureInformation__criticalExtensions__list) :=
  match z with
   | FailureInformation__criticalExtensions__failureInformation t => existT _ 0 t
  | FailureInformation__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition FailureInformation__criticalExtensions__g := (fun n => typ_set (get_nth_typ FailureInformation__criticalExtensions__list n)).
Definition FailureInformation__criticalExtensions__F2 (y : choice FailureInformation__criticalExtensions__list) : FailureInformation__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (FailureInformation__criticalExtensions__g n -> FailureInformation__criticalExtensions__Type) with
    | 0 => fun (t : FailureInformation_IEs__Type) => FailureInformation__criticalExtensions__failureInformation t 
    | 1 => fun (t : FailureInformation__criticalExtensions__criticalExtensionsFuture__Type) => FailureInformation__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : FailureInformation__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ FailureInformation__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len FailureInformation__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return FailureInformation__criticalExtensions__Type with end) n0
           end t0).

Lemma FailureInformation__criticalExtensions__helper2 :  forall (y : FailureInformation__criticalExtensions__Type), FailureInformation__criticalExtensions__cond y -> choice_cond FailureInformation__criticalExtensions__list (FailureInformation__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma FailureInformation__criticalExtensions__helper3 :  forall (y : FailureInformation__criticalExtensions__Type), FailureInformation__criticalExtensions__F2 (FailureInformation__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma FailureInformation__criticalExtensions__helper4 : (forall b : choice FailureInformation__criticalExtensions__list, choice_cond FailureInformation__criticalExtensions__list b -> FailureInformation__criticalExtensions__cond (FailureInformation__criticalExtensions__F2 b) /\ FailureInformation__criticalExtensions__F1 (FailureInformation__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length FailureInformation__criticalExtensions__F1 FailureInformation__criticalExtensions__F2.
Definition FailureInformation__criticalExtensions__Format : T_Format FailureInformation__criticalExtensions__Type FailureInformation__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format FailureInformation__criticalExtensions__cond FailureInformation__criticalExtensions__list__Format FailureInformation__criticalExtensions__F1 FailureInformation__criticalExtensions__F2 FailureInformation__criticalExtensions__helper2 FailureInformation__criticalExtensions__helper3 FailureInformation__criticalExtensions__helper4.
Opaque FailureInformation__criticalExtensions__cond FailureInformation__criticalExtensions__Format.


Definition FailureInformation__Format_Type := Eval cbn in seq_format_prod FailureInformation__list.
Definition FailureInformation__Format_list : FailureInformation__Format_Type :=
  (FailureInformation__criticalExtensions__Format, unit_format).
Definition FailureInformation__list__Format := (*Eval compute in *) seq_format FailureInformation__list FailureInformation__Format_list.
Definition FailureInformation__F1 z :=
  (FailureInformation__criticalExtensions z, tt).
Definition FailureInformation__F2 (y : seq_type FailureInformation__list) :=
  match y with
  | (i0, _)=>
    make__FailureInformation__Type i0
  end.
Lemma FailureInformation__F1F2_cond (z : FailureInformation__Type)
  : FailureInformation__cond z ->
  (seq_cond FailureInformation__list (FailureInformation__F1 z)).
intro H. unfold FailureInformation__cond in H. simpl. auto. Qed.
Lemma FailureInformation__F1F2_cond2 (z : FailureInformation__Type)
 : FailureInformation__F2 (FailureInformation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma FailureInformation__F2F1_cond (y : seq_type FailureInformation__list)
  : seq_cond FailureInformation__list y ->
 (FailureInformation__cond (FailureInformation__F2 y)) /\  FailureInformation__F1 (FailureInformation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold FailureInformation__cond. simpl in *. auto.
 - simpl. unfold FailureInformation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition FailureInformation__Format : T_Format FailureInformation__Type FailureInformation__cond :=
        proj2_format  FailureInformation__cond FailureInformation__list__Format
    FailureInformation__F1 FailureInformation__F2 FailureInformation__F1F2_cond  FailureInformation__F1F2_cond2 FailureInformation__F2F1_cond.
Opaque FailureInformation__cond FailureInformation__Format.

