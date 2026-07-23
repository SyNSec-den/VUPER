Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.SecurityModeComplete_IEs.

Opaque SecurityModeComplete_IEs__cond SecurityModeComplete_IEs__Format.

Record SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type : Set := make__SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__cond (z : SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive SecurityModeComplete__criticalExtensions__Type : Set :=
  | SecurityModeComplete__criticalExtensions__securityModeComplete : SecurityModeComplete_IEs__Type -> SecurityModeComplete__criticalExtensions__Type
  | SecurityModeComplete__criticalExtensions__criticalExtensionsFuture : SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type -> SecurityModeComplete__criticalExtensions__Type
.
Definition SecurityModeComplete__criticalExtensions__list : list typ := (
typ_cons SecurityModeComplete_IEs__Type SecurityModeComplete_IEs__cond ::
typ_cons SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition SecurityModeComplete__criticalExtensions__cond (c : SecurityModeComplete__criticalExtensions__Type) := 
  match c with
  | SecurityModeComplete__criticalExtensions__securityModeComplete t => SecurityModeComplete_IEs__cond t 
  | SecurityModeComplete__criticalExtensions__criticalExtensionsFuture t => SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma SecurityModeComplete__criticalExtensions__len_helper1 : to_bit_sz (length SecurityModeComplete__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SecurityModeComplete__criticalExtensions__len_helper2 : 2 <= length2 SecurityModeComplete__criticalExtensions__list.
 simpl. lia. Qed.
Record SecurityModeComplete__Type : Set :=
  make__SecurityModeComplete__Type {
    SecurityModeComplete__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    SecurityModeComplete__criticalExtensions : SecurityModeComplete__criticalExtensions__Type ;
}.
Definition SecurityModeComplete__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor SecurityModeComplete__criticalExtensions__Type SecurityModeComplete__criticalExtensions__cond ::
 nil).
Definition SecurityModeComplete__cond z := 
  RRC_TransactionIdentifier__cond (SecurityModeComplete__rrc_TransactionIdentifier z) /\
  SecurityModeComplete__criticalExtensions__cond (SecurityModeComplete__criticalExtensions z) /\
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
Definition SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__helper : forall a : SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Format : T_Format SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type)
    SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__cond SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Format.


Definition SecurityModeComplete__criticalExtensions__Format_Type := Eval cbn in get_formats SecurityModeComplete__criticalExtensions__list.
Definition SecurityModeComplete__criticalExtensions__Format_list : SecurityModeComplete__criticalExtensions__Format_Type :=
  (SecurityModeComplete_IEs__Format, (SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition SecurityModeComplete__criticalExtensions__list__Format := Eval compute in choice_format SecurityModeComplete__criticalExtensions__list SecurityModeComplete__criticalExtensions__len_helper1 SecurityModeComplete__criticalExtensions__len_helper2  SecurityModeComplete__criticalExtensions__Format_list.
Definition SecurityModeComplete__criticalExtensions__F1 (z : SecurityModeComplete__criticalExtensions__Type) : (choice SecurityModeComplete__criticalExtensions__list) :=
  match z with
   | SecurityModeComplete__criticalExtensions__securityModeComplete t => existT _ 0 t
  | SecurityModeComplete__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition SecurityModeComplete__criticalExtensions__g := (fun n => typ_set (get_nth_typ SecurityModeComplete__criticalExtensions__list n)).
Definition SecurityModeComplete__criticalExtensions__F2 (y : choice SecurityModeComplete__criticalExtensions__list) : SecurityModeComplete__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SecurityModeComplete__criticalExtensions__g n -> SecurityModeComplete__criticalExtensions__Type) with
    | 0 => fun (t : SecurityModeComplete_IEs__Type) => SecurityModeComplete__criticalExtensions__securityModeComplete t 
    | 1 => fun (t : SecurityModeComplete__criticalExtensions__criticalExtensionsFuture__Type) => SecurityModeComplete__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SecurityModeComplete__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SecurityModeComplete__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SecurityModeComplete__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SecurityModeComplete__criticalExtensions__Type with end) n0
           end t0).

Lemma SecurityModeComplete__criticalExtensions__helper2 :  forall (y : SecurityModeComplete__criticalExtensions__Type), SecurityModeComplete__criticalExtensions__cond y -> choice_cond SecurityModeComplete__criticalExtensions__list (SecurityModeComplete__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SecurityModeComplete__criticalExtensions__helper3 :  forall (y : SecurityModeComplete__criticalExtensions__Type), SecurityModeComplete__criticalExtensions__F2 (SecurityModeComplete__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SecurityModeComplete__criticalExtensions__helper4 : (forall b : choice SecurityModeComplete__criticalExtensions__list, choice_cond SecurityModeComplete__criticalExtensions__list b -> SecurityModeComplete__criticalExtensions__cond (SecurityModeComplete__criticalExtensions__F2 b) /\ SecurityModeComplete__criticalExtensions__F1 (SecurityModeComplete__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SecurityModeComplete__criticalExtensions__F1 SecurityModeComplete__criticalExtensions__F2.
Definition SecurityModeComplete__criticalExtensions__Format : T_Format SecurityModeComplete__criticalExtensions__Type SecurityModeComplete__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format SecurityModeComplete__criticalExtensions__cond SecurityModeComplete__criticalExtensions__list__Format SecurityModeComplete__criticalExtensions__F1 SecurityModeComplete__criticalExtensions__F2 SecurityModeComplete__criticalExtensions__helper2 SecurityModeComplete__criticalExtensions__helper3 SecurityModeComplete__criticalExtensions__helper4.
Opaque SecurityModeComplete__criticalExtensions__cond SecurityModeComplete__criticalExtensions__Format.


Definition SecurityModeComplete__Format_Type := Eval cbn in seq_format_prod SecurityModeComplete__list.
Definition SecurityModeComplete__Format_list : SecurityModeComplete__Format_Type :=
  (RRC_TransactionIdentifier__Format, (SecurityModeComplete__criticalExtensions__Format, unit_format)).
Definition SecurityModeComplete__list__Format := (*Eval compute in *) seq_format SecurityModeComplete__list SecurityModeComplete__Format_list.
Definition SecurityModeComplete__F1 z :=
  (SecurityModeComplete__rrc_TransactionIdentifier z, (SecurityModeComplete__criticalExtensions z, tt)).
Definition SecurityModeComplete__F2 (y : seq_type SecurityModeComplete__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SecurityModeComplete__Type i0 i1
  end.
Lemma SecurityModeComplete__F1F2_cond (z : SecurityModeComplete__Type)
  : SecurityModeComplete__cond z ->
  (seq_cond SecurityModeComplete__list (SecurityModeComplete__F1 z)).
intro H. unfold SecurityModeComplete__cond in H. simpl. auto. Qed.
Lemma SecurityModeComplete__F1F2_cond2 (z : SecurityModeComplete__Type)
 : SecurityModeComplete__F2 (SecurityModeComplete__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SecurityModeComplete__F2F1_cond (y : seq_type SecurityModeComplete__list)
  : seq_cond SecurityModeComplete__list y ->
 (SecurityModeComplete__cond (SecurityModeComplete__F2 y)) /\  SecurityModeComplete__F1 (SecurityModeComplete__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SecurityModeComplete__cond. simpl in *. auto.
 - simpl. unfold SecurityModeComplete__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SecurityModeComplete__Format : T_Format SecurityModeComplete__Type SecurityModeComplete__cond :=
        proj2_format  SecurityModeComplete__cond SecurityModeComplete__list__Format
    SecurityModeComplete__F1 SecurityModeComplete__F2 SecurityModeComplete__F1F2_cond  SecurityModeComplete__F1F2_cond2 SecurityModeComplete__F2F1_cond.
Opaque SecurityModeComplete__cond SecurityModeComplete__Format.

