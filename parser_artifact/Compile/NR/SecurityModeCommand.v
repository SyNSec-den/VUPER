Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.SecurityModeCommand_IEs.

Opaque SecurityModeCommand_IEs__cond SecurityModeCommand_IEs__Format.

Record SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type : Set := make__SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__cond (z : SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive SecurityModeCommand__criticalExtensions__Type : Set :=
  | SecurityModeCommand__criticalExtensions__securityModeCommand : SecurityModeCommand_IEs__Type -> SecurityModeCommand__criticalExtensions__Type
  | SecurityModeCommand__criticalExtensions__criticalExtensionsFuture : SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type -> SecurityModeCommand__criticalExtensions__Type
.
Definition SecurityModeCommand__criticalExtensions__list : list typ := (
typ_cons SecurityModeCommand_IEs__Type SecurityModeCommand_IEs__cond ::
typ_cons SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition SecurityModeCommand__criticalExtensions__cond (c : SecurityModeCommand__criticalExtensions__Type) := 
  match c with
  | SecurityModeCommand__criticalExtensions__securityModeCommand t => SecurityModeCommand_IEs__cond t 
  | SecurityModeCommand__criticalExtensions__criticalExtensionsFuture t => SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma SecurityModeCommand__criticalExtensions__len_helper1 : to_bit_sz (length SecurityModeCommand__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SecurityModeCommand__criticalExtensions__len_helper2 : 2 <= length2 SecurityModeCommand__criticalExtensions__list.
 simpl. lia. Qed.
Record SecurityModeCommand__Type : Set :=
  make__SecurityModeCommand__Type {
    SecurityModeCommand__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    SecurityModeCommand__criticalExtensions : SecurityModeCommand__criticalExtensions__Type ;
}.
Definition SecurityModeCommand__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor SecurityModeCommand__criticalExtensions__Type SecurityModeCommand__criticalExtensions__cond ::
 nil).
Definition SecurityModeCommand__cond z := 
  RRC_TransactionIdentifier__cond (SecurityModeCommand__rrc_TransactionIdentifier z) /\
  SecurityModeCommand__criticalExtensions__cond (SecurityModeCommand__criticalExtensions z) /\
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
Definition SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__helper : forall a : SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Format : T_Format SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type)
    SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__cond SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Format.


Definition SecurityModeCommand__criticalExtensions__Format_Type := Eval cbn in get_formats SecurityModeCommand__criticalExtensions__list.
Definition SecurityModeCommand__criticalExtensions__Format_list : SecurityModeCommand__criticalExtensions__Format_Type :=
  (SecurityModeCommand_IEs__Format, (SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition SecurityModeCommand__criticalExtensions__list__Format := Eval compute in choice_format SecurityModeCommand__criticalExtensions__list SecurityModeCommand__criticalExtensions__len_helper1 SecurityModeCommand__criticalExtensions__len_helper2  SecurityModeCommand__criticalExtensions__Format_list.
Definition SecurityModeCommand__criticalExtensions__F1 (z : SecurityModeCommand__criticalExtensions__Type) : (choice SecurityModeCommand__criticalExtensions__list) :=
  match z with
   | SecurityModeCommand__criticalExtensions__securityModeCommand t => existT _ 0 t
  | SecurityModeCommand__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition SecurityModeCommand__criticalExtensions__g := (fun n => typ_set (get_nth_typ SecurityModeCommand__criticalExtensions__list n)).
Definition SecurityModeCommand__criticalExtensions__F2 (y : choice SecurityModeCommand__criticalExtensions__list) : SecurityModeCommand__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SecurityModeCommand__criticalExtensions__g n -> SecurityModeCommand__criticalExtensions__Type) with
    | 0 => fun (t : SecurityModeCommand_IEs__Type) => SecurityModeCommand__criticalExtensions__securityModeCommand t 
    | 1 => fun (t : SecurityModeCommand__criticalExtensions__criticalExtensionsFuture__Type) => SecurityModeCommand__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SecurityModeCommand__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SecurityModeCommand__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SecurityModeCommand__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SecurityModeCommand__criticalExtensions__Type with end) n0
           end t0).

Lemma SecurityModeCommand__criticalExtensions__helper2 :  forall (y : SecurityModeCommand__criticalExtensions__Type), SecurityModeCommand__criticalExtensions__cond y -> choice_cond SecurityModeCommand__criticalExtensions__list (SecurityModeCommand__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SecurityModeCommand__criticalExtensions__helper3 :  forall (y : SecurityModeCommand__criticalExtensions__Type), SecurityModeCommand__criticalExtensions__F2 (SecurityModeCommand__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SecurityModeCommand__criticalExtensions__helper4 : (forall b : choice SecurityModeCommand__criticalExtensions__list, choice_cond SecurityModeCommand__criticalExtensions__list b -> SecurityModeCommand__criticalExtensions__cond (SecurityModeCommand__criticalExtensions__F2 b) /\ SecurityModeCommand__criticalExtensions__F1 (SecurityModeCommand__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SecurityModeCommand__criticalExtensions__F1 SecurityModeCommand__criticalExtensions__F2.
Definition SecurityModeCommand__criticalExtensions__Format : T_Format SecurityModeCommand__criticalExtensions__Type SecurityModeCommand__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format SecurityModeCommand__criticalExtensions__cond SecurityModeCommand__criticalExtensions__list__Format SecurityModeCommand__criticalExtensions__F1 SecurityModeCommand__criticalExtensions__F2 SecurityModeCommand__criticalExtensions__helper2 SecurityModeCommand__criticalExtensions__helper3 SecurityModeCommand__criticalExtensions__helper4.
Opaque SecurityModeCommand__criticalExtensions__cond SecurityModeCommand__criticalExtensions__Format.


Definition SecurityModeCommand__Format_Type := Eval cbn in seq_format_prod SecurityModeCommand__list.
Definition SecurityModeCommand__Format_list : SecurityModeCommand__Format_Type :=
  (RRC_TransactionIdentifier__Format, (SecurityModeCommand__criticalExtensions__Format, unit_format)).
Definition SecurityModeCommand__list__Format := (*Eval compute in *) seq_format SecurityModeCommand__list SecurityModeCommand__Format_list.
Definition SecurityModeCommand__F1 z :=
  (SecurityModeCommand__rrc_TransactionIdentifier z, (SecurityModeCommand__criticalExtensions z, tt)).
Definition SecurityModeCommand__F2 (y : seq_type SecurityModeCommand__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SecurityModeCommand__Type i0 i1
  end.
Lemma SecurityModeCommand__F1F2_cond (z : SecurityModeCommand__Type)
  : SecurityModeCommand__cond z ->
  (seq_cond SecurityModeCommand__list (SecurityModeCommand__F1 z)).
intro H. unfold SecurityModeCommand__cond in H. simpl. auto. Qed.
Lemma SecurityModeCommand__F1F2_cond2 (z : SecurityModeCommand__Type)
 : SecurityModeCommand__F2 (SecurityModeCommand__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SecurityModeCommand__F2F1_cond (y : seq_type SecurityModeCommand__list)
  : seq_cond SecurityModeCommand__list y ->
 (SecurityModeCommand__cond (SecurityModeCommand__F2 y)) /\  SecurityModeCommand__F1 (SecurityModeCommand__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SecurityModeCommand__cond. simpl in *. auto.
 - simpl. unfold SecurityModeCommand__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SecurityModeCommand__Format : T_Format SecurityModeCommand__Type SecurityModeCommand__cond :=
        proj2_format  SecurityModeCommand__cond SecurityModeCommand__list__Format
    SecurityModeCommand__F1 SecurityModeCommand__F2 SecurityModeCommand__F1F2_cond  SecurityModeCommand__F1F2_cond2 SecurityModeCommand__F2F1_cond.
Opaque SecurityModeCommand__cond SecurityModeCommand__Format.

