Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.SecurityModeFailure_IEs.

Opaque SecurityModeFailure_IEs__cond SecurityModeFailure_IEs__Format.

Record SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type : Set := make__SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__cond (z : SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive SecurityModeFailure__criticalExtensions__Type : Set :=
  | SecurityModeFailure__criticalExtensions__securityModeFailure : SecurityModeFailure_IEs__Type -> SecurityModeFailure__criticalExtensions__Type
  | SecurityModeFailure__criticalExtensions__criticalExtensionsFuture : SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type -> SecurityModeFailure__criticalExtensions__Type
.
Definition SecurityModeFailure__criticalExtensions__list : list typ := (
typ_cons SecurityModeFailure_IEs__Type SecurityModeFailure_IEs__cond ::
typ_cons SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition SecurityModeFailure__criticalExtensions__cond (c : SecurityModeFailure__criticalExtensions__Type) := 
  match c with
  | SecurityModeFailure__criticalExtensions__securityModeFailure t => SecurityModeFailure_IEs__cond t 
  | SecurityModeFailure__criticalExtensions__criticalExtensionsFuture t => SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma SecurityModeFailure__criticalExtensions__len_helper1 : to_bit_sz (length SecurityModeFailure__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SecurityModeFailure__criticalExtensions__len_helper2 : 2 <= length2 SecurityModeFailure__criticalExtensions__list.
 simpl. lia. Qed.
Record SecurityModeFailure__Type : Set :=
  make__SecurityModeFailure__Type {
    SecurityModeFailure__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    SecurityModeFailure__criticalExtensions : SecurityModeFailure__criticalExtensions__Type ;
}.
Definition SecurityModeFailure__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor SecurityModeFailure__criticalExtensions__Type SecurityModeFailure__criticalExtensions__cond ::
 nil).
Definition SecurityModeFailure__cond z := 
  RRC_TransactionIdentifier__cond (SecurityModeFailure__rrc_TransactionIdentifier z) /\
  SecurityModeFailure__criticalExtensions__cond (SecurityModeFailure__criticalExtensions z) /\
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
Definition SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__helper : forall a : SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Format : T_Format SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type)
    SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__cond SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Format.


Definition SecurityModeFailure__criticalExtensions__Format_Type := Eval cbn in get_formats SecurityModeFailure__criticalExtensions__list.
Definition SecurityModeFailure__criticalExtensions__Format_list : SecurityModeFailure__criticalExtensions__Format_Type :=
  (SecurityModeFailure_IEs__Format, (SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition SecurityModeFailure__criticalExtensions__list__Format := Eval compute in choice_format SecurityModeFailure__criticalExtensions__list SecurityModeFailure__criticalExtensions__len_helper1 SecurityModeFailure__criticalExtensions__len_helper2  SecurityModeFailure__criticalExtensions__Format_list.
Definition SecurityModeFailure__criticalExtensions__F1 (z : SecurityModeFailure__criticalExtensions__Type) : (choice SecurityModeFailure__criticalExtensions__list) :=
  match z with
   | SecurityModeFailure__criticalExtensions__securityModeFailure t => existT _ 0 t
  | SecurityModeFailure__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition SecurityModeFailure__criticalExtensions__g := (fun n => typ_set (get_nth_typ SecurityModeFailure__criticalExtensions__list n)).
Definition SecurityModeFailure__criticalExtensions__F2 (y : choice SecurityModeFailure__criticalExtensions__list) : SecurityModeFailure__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SecurityModeFailure__criticalExtensions__g n -> SecurityModeFailure__criticalExtensions__Type) with
    | 0 => fun (t : SecurityModeFailure_IEs__Type) => SecurityModeFailure__criticalExtensions__securityModeFailure t 
    | 1 => fun (t : SecurityModeFailure__criticalExtensions__criticalExtensionsFuture__Type) => SecurityModeFailure__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SecurityModeFailure__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SecurityModeFailure__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SecurityModeFailure__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SecurityModeFailure__criticalExtensions__Type with end) n0
           end t0).

Lemma SecurityModeFailure__criticalExtensions__helper2 :  forall (y : SecurityModeFailure__criticalExtensions__Type), SecurityModeFailure__criticalExtensions__cond y -> choice_cond SecurityModeFailure__criticalExtensions__list (SecurityModeFailure__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SecurityModeFailure__criticalExtensions__helper3 :  forall (y : SecurityModeFailure__criticalExtensions__Type), SecurityModeFailure__criticalExtensions__F2 (SecurityModeFailure__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SecurityModeFailure__criticalExtensions__helper4 : (forall b : choice SecurityModeFailure__criticalExtensions__list, choice_cond SecurityModeFailure__criticalExtensions__list b -> SecurityModeFailure__criticalExtensions__cond (SecurityModeFailure__criticalExtensions__F2 b) /\ SecurityModeFailure__criticalExtensions__F1 (SecurityModeFailure__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SecurityModeFailure__criticalExtensions__F1 SecurityModeFailure__criticalExtensions__F2.
Definition SecurityModeFailure__criticalExtensions__Format : T_Format SecurityModeFailure__criticalExtensions__Type SecurityModeFailure__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format SecurityModeFailure__criticalExtensions__cond SecurityModeFailure__criticalExtensions__list__Format SecurityModeFailure__criticalExtensions__F1 SecurityModeFailure__criticalExtensions__F2 SecurityModeFailure__criticalExtensions__helper2 SecurityModeFailure__criticalExtensions__helper3 SecurityModeFailure__criticalExtensions__helper4.
Opaque SecurityModeFailure__criticalExtensions__cond SecurityModeFailure__criticalExtensions__Format.


Definition SecurityModeFailure__Format_Type := Eval cbn in seq_format_prod SecurityModeFailure__list.
Definition SecurityModeFailure__Format_list : SecurityModeFailure__Format_Type :=
  (RRC_TransactionIdentifier__Format, (SecurityModeFailure__criticalExtensions__Format, unit_format)).
Definition SecurityModeFailure__list__Format := (*Eval compute in *) seq_format SecurityModeFailure__list SecurityModeFailure__Format_list.
Definition SecurityModeFailure__F1 z :=
  (SecurityModeFailure__rrc_TransactionIdentifier z, (SecurityModeFailure__criticalExtensions z, tt)).
Definition SecurityModeFailure__F2 (y : seq_type SecurityModeFailure__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SecurityModeFailure__Type i0 i1
  end.
Lemma SecurityModeFailure__F1F2_cond (z : SecurityModeFailure__Type)
  : SecurityModeFailure__cond z ->
  (seq_cond SecurityModeFailure__list (SecurityModeFailure__F1 z)).
intro H. unfold SecurityModeFailure__cond in H. simpl. auto. Qed.
Lemma SecurityModeFailure__F1F2_cond2 (z : SecurityModeFailure__Type)
 : SecurityModeFailure__F2 (SecurityModeFailure__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SecurityModeFailure__F2F1_cond (y : seq_type SecurityModeFailure__list)
  : seq_cond SecurityModeFailure__list y ->
 (SecurityModeFailure__cond (SecurityModeFailure__F2 y)) /\  SecurityModeFailure__F1 (SecurityModeFailure__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SecurityModeFailure__cond. simpl in *. auto.
 - simpl. unfold SecurityModeFailure__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SecurityModeFailure__Format : T_Format SecurityModeFailure__Type SecurityModeFailure__cond :=
        proj2_format  SecurityModeFailure__cond SecurityModeFailure__list__Format
    SecurityModeFailure__F1 SecurityModeFailure__F2 SecurityModeFailure__F1F2_cond  SecurityModeFailure__F1F2_cond2 SecurityModeFailure__F2F1_cond.
Opaque SecurityModeFailure__cond SecurityModeFailure__Format.

