Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.UECapabilityInformationSidelink_r16_IEs.

Opaque UECapabilityInformationSidelink_r16_IEs__cond UECapabilityInformationSidelink_r16_IEs__Format.

Record UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__cond (z : UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UECapabilityInformationSidelink__criticalExtensions__Type : Set :=
  | UECapabilityInformationSidelink__criticalExtensions__ueCapabilityInformationSidelink_r16 : UECapabilityInformationSidelink_r16_IEs__Type -> UECapabilityInformationSidelink__criticalExtensions__Type
  | UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture : UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type -> UECapabilityInformationSidelink__criticalExtensions__Type
.
Definition UECapabilityInformationSidelink__criticalExtensions__list : list typ := (
typ_cons UECapabilityInformationSidelink_r16_IEs__Type UECapabilityInformationSidelink_r16_IEs__cond ::
typ_cons UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UECapabilityInformationSidelink__criticalExtensions__cond (c : UECapabilityInformationSidelink__criticalExtensions__Type) := 
  match c with
  | UECapabilityInformationSidelink__criticalExtensions__ueCapabilityInformationSidelink_r16 t => UECapabilityInformationSidelink_r16_IEs__cond t 
  | UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture t => UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UECapabilityInformationSidelink__criticalExtensions__len_helper1 : to_bit_sz (length UECapabilityInformationSidelink__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UECapabilityInformationSidelink__criticalExtensions__len_helper2 : 2 <= length2 UECapabilityInformationSidelink__criticalExtensions__list.
 simpl. lia. Qed.
Record UECapabilityInformationSidelink__Type : Set :=
  make__UECapabilityInformationSidelink__Type {
    UECapabilityInformationSidelink__rrc_TransactionIdentifier_r16 : RRC_TransactionIdentifier__Type ;
    UECapabilityInformationSidelink__criticalExtensions : UECapabilityInformationSidelink__criticalExtensions__Type ;
}.
Definition UECapabilityInformationSidelink__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor UECapabilityInformationSidelink__criticalExtensions__Type UECapabilityInformationSidelink__criticalExtensions__cond ::
 nil).
Definition UECapabilityInformationSidelink__cond z := 
  RRC_TransactionIdentifier__cond (UECapabilityInformationSidelink__rrc_TransactionIdentifier_r16 z) /\
  UECapabilityInformationSidelink__criticalExtensions__cond (UECapabilityInformationSidelink__criticalExtensions z) /\
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
Definition UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__helper : forall a : UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Format : T_Format UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type)
    UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__cond UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Format.


Definition UECapabilityInformationSidelink__criticalExtensions__Format_Type := Eval cbn in get_formats UECapabilityInformationSidelink__criticalExtensions__list.
Definition UECapabilityInformationSidelink__criticalExtensions__Format_list : UECapabilityInformationSidelink__criticalExtensions__Format_Type :=
  (UECapabilityInformationSidelink_r16_IEs__Format, (UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UECapabilityInformationSidelink__criticalExtensions__list__Format := Eval compute in choice_format UECapabilityInformationSidelink__criticalExtensions__list UECapabilityInformationSidelink__criticalExtensions__len_helper1 UECapabilityInformationSidelink__criticalExtensions__len_helper2  UECapabilityInformationSidelink__criticalExtensions__Format_list.
Definition UECapabilityInformationSidelink__criticalExtensions__F1 (z : UECapabilityInformationSidelink__criticalExtensions__Type) : (choice UECapabilityInformationSidelink__criticalExtensions__list) :=
  match z with
   | UECapabilityInformationSidelink__criticalExtensions__ueCapabilityInformationSidelink_r16 t => existT _ 0 t
  | UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UECapabilityInformationSidelink__criticalExtensions__g := (fun n => typ_set (get_nth_typ UECapabilityInformationSidelink__criticalExtensions__list n)).
Definition UECapabilityInformationSidelink__criticalExtensions__F2 (y : choice UECapabilityInformationSidelink__criticalExtensions__list) : UECapabilityInformationSidelink__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UECapabilityInformationSidelink__criticalExtensions__g n -> UECapabilityInformationSidelink__criticalExtensions__Type) with
    | 0 => fun (t : UECapabilityInformationSidelink_r16_IEs__Type) => UECapabilityInformationSidelink__criticalExtensions__ueCapabilityInformationSidelink_r16 t 
    | 1 => fun (t : UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture__Type) => UECapabilityInformationSidelink__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UECapabilityInformationSidelink__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UECapabilityInformationSidelink__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UECapabilityInformationSidelink__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UECapabilityInformationSidelink__criticalExtensions__Type with end) n0
           end t0).

Lemma UECapabilityInformationSidelink__criticalExtensions__helper2 :  forall (y : UECapabilityInformationSidelink__criticalExtensions__Type), UECapabilityInformationSidelink__criticalExtensions__cond y -> choice_cond UECapabilityInformationSidelink__criticalExtensions__list (UECapabilityInformationSidelink__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UECapabilityInformationSidelink__criticalExtensions__helper3 :  forall (y : UECapabilityInformationSidelink__criticalExtensions__Type), UECapabilityInformationSidelink__criticalExtensions__F2 (UECapabilityInformationSidelink__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UECapabilityInformationSidelink__criticalExtensions__helper4 : (forall b : choice UECapabilityInformationSidelink__criticalExtensions__list, choice_cond UECapabilityInformationSidelink__criticalExtensions__list b -> UECapabilityInformationSidelink__criticalExtensions__cond (UECapabilityInformationSidelink__criticalExtensions__F2 b) /\ UECapabilityInformationSidelink__criticalExtensions__F1 (UECapabilityInformationSidelink__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UECapabilityInformationSidelink__criticalExtensions__F1 UECapabilityInformationSidelink__criticalExtensions__F2.
Definition UECapabilityInformationSidelink__criticalExtensions__Format : T_Format UECapabilityInformationSidelink__criticalExtensions__Type UECapabilityInformationSidelink__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UECapabilityInformationSidelink__criticalExtensions__cond UECapabilityInformationSidelink__criticalExtensions__list__Format UECapabilityInformationSidelink__criticalExtensions__F1 UECapabilityInformationSidelink__criticalExtensions__F2 UECapabilityInformationSidelink__criticalExtensions__helper2 UECapabilityInformationSidelink__criticalExtensions__helper3 UECapabilityInformationSidelink__criticalExtensions__helper4.
Opaque UECapabilityInformationSidelink__criticalExtensions__cond UECapabilityInformationSidelink__criticalExtensions__Format.


Definition UECapabilityInformationSidelink__Format_Type := Eval cbn in seq_format_prod UECapabilityInformationSidelink__list.
Definition UECapabilityInformationSidelink__Format_list : UECapabilityInformationSidelink__Format_Type :=
  (RRC_TransactionIdentifier__Format, (UECapabilityInformationSidelink__criticalExtensions__Format, unit_format)).
Definition UECapabilityInformationSidelink__list__Format := (*Eval compute in *) seq_format UECapabilityInformationSidelink__list UECapabilityInformationSidelink__Format_list.
Definition UECapabilityInformationSidelink__F1 z :=
  (UECapabilityInformationSidelink__rrc_TransactionIdentifier_r16 z, (UECapabilityInformationSidelink__criticalExtensions z, tt)).
Definition UECapabilityInformationSidelink__F2 (y : seq_type UECapabilityInformationSidelink__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UECapabilityInformationSidelink__Type i0 i1
  end.
Lemma UECapabilityInformationSidelink__F1F2_cond (z : UECapabilityInformationSidelink__Type)
  : UECapabilityInformationSidelink__cond z ->
  (seq_cond UECapabilityInformationSidelink__list (UECapabilityInformationSidelink__F1 z)).
intro H. unfold UECapabilityInformationSidelink__cond in H. simpl. auto. Qed.
Lemma UECapabilityInformationSidelink__F1F2_cond2 (z : UECapabilityInformationSidelink__Type)
 : UECapabilityInformationSidelink__F2 (UECapabilityInformationSidelink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UECapabilityInformationSidelink__F2F1_cond (y : seq_type UECapabilityInformationSidelink__list)
  : seq_cond UECapabilityInformationSidelink__list y ->
 (UECapabilityInformationSidelink__cond (UECapabilityInformationSidelink__F2 y)) /\  UECapabilityInformationSidelink__F1 (UECapabilityInformationSidelink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UECapabilityInformationSidelink__cond. simpl in *. auto.
 - simpl. unfold UECapabilityInformationSidelink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UECapabilityInformationSidelink__Format : T_Format UECapabilityInformationSidelink__Type UECapabilityInformationSidelink__cond :=
        proj2_format  UECapabilityInformationSidelink__cond UECapabilityInformationSidelink__list__Format
    UECapabilityInformationSidelink__F1 UECapabilityInformationSidelink__F2 UECapabilityInformationSidelink__F1F2_cond  UECapabilityInformationSidelink__F1F2_cond2 UECapabilityInformationSidelink__F2F1_cond.
Opaque UECapabilityInformationSidelink__cond UECapabilityInformationSidelink__Format.

