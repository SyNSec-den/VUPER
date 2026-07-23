Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.UECapabilityEnquirySidelink_r16_IEs.

Opaque UECapabilityEnquirySidelink_r16_IEs__cond UECapabilityEnquirySidelink_r16_IEs__Format.

Record UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__cond (z : UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UECapabilityEnquirySidelink__criticalExtensions__Type : Set :=
  | UECapabilityEnquirySidelink__criticalExtensions__ueCapabilityEnquirySidelink_r16 : UECapabilityEnquirySidelink_r16_IEs__Type -> UECapabilityEnquirySidelink__criticalExtensions__Type
  | UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture : UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type -> UECapabilityEnquirySidelink__criticalExtensions__Type
.
Definition UECapabilityEnquirySidelink__criticalExtensions__list : list typ := (
typ_cons UECapabilityEnquirySidelink_r16_IEs__Type UECapabilityEnquirySidelink_r16_IEs__cond ::
typ_cons UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UECapabilityEnquirySidelink__criticalExtensions__cond (c : UECapabilityEnquirySidelink__criticalExtensions__Type) := 
  match c with
  | UECapabilityEnquirySidelink__criticalExtensions__ueCapabilityEnquirySidelink_r16 t => UECapabilityEnquirySidelink_r16_IEs__cond t 
  | UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture t => UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UECapabilityEnquirySidelink__criticalExtensions__len_helper1 : to_bit_sz (length UECapabilityEnquirySidelink__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UECapabilityEnquirySidelink__criticalExtensions__len_helper2 : 2 <= length2 UECapabilityEnquirySidelink__criticalExtensions__list.
 simpl. lia. Qed.
Record UECapabilityEnquirySidelink__Type : Set :=
  make__UECapabilityEnquirySidelink__Type {
    UECapabilityEnquirySidelink__rrc_TransactionIdentifier_r16 : RRC_TransactionIdentifier__Type ;
    UECapabilityEnquirySidelink__criticalExtensions : UECapabilityEnquirySidelink__criticalExtensions__Type ;
}.
Definition UECapabilityEnquirySidelink__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor UECapabilityEnquirySidelink__criticalExtensions__Type UECapabilityEnquirySidelink__criticalExtensions__cond ::
 nil).
Definition UECapabilityEnquirySidelink__cond z := 
  RRC_TransactionIdentifier__cond (UECapabilityEnquirySidelink__rrc_TransactionIdentifier_r16 z) /\
  UECapabilityEnquirySidelink__criticalExtensions__cond (UECapabilityEnquirySidelink__criticalExtensions z) /\
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
Definition UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__helper : forall a : UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Format : T_Format UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type)
    UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__cond UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Format.


Definition UECapabilityEnquirySidelink__criticalExtensions__Format_Type := Eval cbn in get_formats UECapabilityEnquirySidelink__criticalExtensions__list.
Definition UECapabilityEnquirySidelink__criticalExtensions__Format_list : UECapabilityEnquirySidelink__criticalExtensions__Format_Type :=
  (UECapabilityEnquirySidelink_r16_IEs__Format, (UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UECapabilityEnquirySidelink__criticalExtensions__list__Format := Eval compute in choice_format UECapabilityEnquirySidelink__criticalExtensions__list UECapabilityEnquirySidelink__criticalExtensions__len_helper1 UECapabilityEnquirySidelink__criticalExtensions__len_helper2  UECapabilityEnquirySidelink__criticalExtensions__Format_list.
Definition UECapabilityEnquirySidelink__criticalExtensions__F1 (z : UECapabilityEnquirySidelink__criticalExtensions__Type) : (choice UECapabilityEnquirySidelink__criticalExtensions__list) :=
  match z with
   | UECapabilityEnquirySidelink__criticalExtensions__ueCapabilityEnquirySidelink_r16 t => existT _ 0 t
  | UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UECapabilityEnquirySidelink__criticalExtensions__g := (fun n => typ_set (get_nth_typ UECapabilityEnquirySidelink__criticalExtensions__list n)).
Definition UECapabilityEnquirySidelink__criticalExtensions__F2 (y : choice UECapabilityEnquirySidelink__criticalExtensions__list) : UECapabilityEnquirySidelink__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UECapabilityEnquirySidelink__criticalExtensions__g n -> UECapabilityEnquirySidelink__criticalExtensions__Type) with
    | 0 => fun (t : UECapabilityEnquirySidelink_r16_IEs__Type) => UECapabilityEnquirySidelink__criticalExtensions__ueCapabilityEnquirySidelink_r16 t 
    | 1 => fun (t : UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture__Type) => UECapabilityEnquirySidelink__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UECapabilityEnquirySidelink__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UECapabilityEnquirySidelink__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UECapabilityEnquirySidelink__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UECapabilityEnquirySidelink__criticalExtensions__Type with end) n0
           end t0).

Lemma UECapabilityEnquirySidelink__criticalExtensions__helper2 :  forall (y : UECapabilityEnquirySidelink__criticalExtensions__Type), UECapabilityEnquirySidelink__criticalExtensions__cond y -> choice_cond UECapabilityEnquirySidelink__criticalExtensions__list (UECapabilityEnquirySidelink__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UECapabilityEnquirySidelink__criticalExtensions__helper3 :  forall (y : UECapabilityEnquirySidelink__criticalExtensions__Type), UECapabilityEnquirySidelink__criticalExtensions__F2 (UECapabilityEnquirySidelink__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UECapabilityEnquirySidelink__criticalExtensions__helper4 : (forall b : choice UECapabilityEnquirySidelink__criticalExtensions__list, choice_cond UECapabilityEnquirySidelink__criticalExtensions__list b -> UECapabilityEnquirySidelink__criticalExtensions__cond (UECapabilityEnquirySidelink__criticalExtensions__F2 b) /\ UECapabilityEnquirySidelink__criticalExtensions__F1 (UECapabilityEnquirySidelink__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UECapabilityEnquirySidelink__criticalExtensions__F1 UECapabilityEnquirySidelink__criticalExtensions__F2.
Definition UECapabilityEnquirySidelink__criticalExtensions__Format : T_Format UECapabilityEnquirySidelink__criticalExtensions__Type UECapabilityEnquirySidelink__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UECapabilityEnquirySidelink__criticalExtensions__cond UECapabilityEnquirySidelink__criticalExtensions__list__Format UECapabilityEnquirySidelink__criticalExtensions__F1 UECapabilityEnquirySidelink__criticalExtensions__F2 UECapabilityEnquirySidelink__criticalExtensions__helper2 UECapabilityEnquirySidelink__criticalExtensions__helper3 UECapabilityEnquirySidelink__criticalExtensions__helper4.
Opaque UECapabilityEnquirySidelink__criticalExtensions__cond UECapabilityEnquirySidelink__criticalExtensions__Format.


Definition UECapabilityEnquirySidelink__Format_Type := Eval cbn in seq_format_prod UECapabilityEnquirySidelink__list.
Definition UECapabilityEnquirySidelink__Format_list : UECapabilityEnquirySidelink__Format_Type :=
  (RRC_TransactionIdentifier__Format, (UECapabilityEnquirySidelink__criticalExtensions__Format, unit_format)).
Definition UECapabilityEnquirySidelink__list__Format := (*Eval compute in *) seq_format UECapabilityEnquirySidelink__list UECapabilityEnquirySidelink__Format_list.
Definition UECapabilityEnquirySidelink__F1 z :=
  (UECapabilityEnquirySidelink__rrc_TransactionIdentifier_r16 z, (UECapabilityEnquirySidelink__criticalExtensions z, tt)).
Definition UECapabilityEnquirySidelink__F2 (y : seq_type UECapabilityEnquirySidelink__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UECapabilityEnquirySidelink__Type i0 i1
  end.
Lemma UECapabilityEnquirySidelink__F1F2_cond (z : UECapabilityEnquirySidelink__Type)
  : UECapabilityEnquirySidelink__cond z ->
  (seq_cond UECapabilityEnquirySidelink__list (UECapabilityEnquirySidelink__F1 z)).
intro H. unfold UECapabilityEnquirySidelink__cond in H. simpl. auto. Qed.
Lemma UECapabilityEnquirySidelink__F1F2_cond2 (z : UECapabilityEnquirySidelink__Type)
 : UECapabilityEnquirySidelink__F2 (UECapabilityEnquirySidelink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UECapabilityEnquirySidelink__F2F1_cond (y : seq_type UECapabilityEnquirySidelink__list)
  : seq_cond UECapabilityEnquirySidelink__list y ->
 (UECapabilityEnquirySidelink__cond (UECapabilityEnquirySidelink__F2 y)) /\  UECapabilityEnquirySidelink__F1 (UECapabilityEnquirySidelink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UECapabilityEnquirySidelink__cond. simpl in *. auto.
 - simpl. unfold UECapabilityEnquirySidelink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UECapabilityEnquirySidelink__Format : T_Format UECapabilityEnquirySidelink__Type UECapabilityEnquirySidelink__cond :=
        proj2_format  UECapabilityEnquirySidelink__cond UECapabilityEnquirySidelink__list__Format
    UECapabilityEnquirySidelink__F1 UECapabilityEnquirySidelink__F2 UECapabilityEnquirySidelink__F1F2_cond  UECapabilityEnquirySidelink__F1F2_cond2 UECapabilityEnquirySidelink__F2F1_cond.
Opaque UECapabilityEnquirySidelink__cond UECapabilityEnquirySidelink__Format.

