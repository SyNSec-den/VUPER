Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.UECapabilityEnquiry_IEs.

Opaque UECapabilityEnquiry_IEs__cond UECapabilityEnquiry_IEs__Format.

Record UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__cond (z : UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UECapabilityEnquiry__criticalExtensions__Type : Set :=
  | UECapabilityEnquiry__criticalExtensions__ueCapabilityEnquiry : UECapabilityEnquiry_IEs__Type -> UECapabilityEnquiry__criticalExtensions__Type
  | UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture : UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type -> UECapabilityEnquiry__criticalExtensions__Type
.
Definition UECapabilityEnquiry__criticalExtensions__list : list typ := (
typ_cons UECapabilityEnquiry_IEs__Type UECapabilityEnquiry_IEs__cond ::
typ_cons UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UECapabilityEnquiry__criticalExtensions__cond (c : UECapabilityEnquiry__criticalExtensions__Type) := 
  match c with
  | UECapabilityEnquiry__criticalExtensions__ueCapabilityEnquiry t => UECapabilityEnquiry_IEs__cond t 
  | UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture t => UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UECapabilityEnquiry__criticalExtensions__len_helper1 : to_bit_sz (length UECapabilityEnquiry__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UECapabilityEnquiry__criticalExtensions__len_helper2 : 2 <= length2 UECapabilityEnquiry__criticalExtensions__list.
 simpl. lia. Qed.
Record UECapabilityEnquiry__Type : Set :=
  make__UECapabilityEnquiry__Type {
    UECapabilityEnquiry__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    UECapabilityEnquiry__criticalExtensions : UECapabilityEnquiry__criticalExtensions__Type ;
}.
Definition UECapabilityEnquiry__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor UECapabilityEnquiry__criticalExtensions__Type UECapabilityEnquiry__criticalExtensions__cond ::
 nil).
Definition UECapabilityEnquiry__cond z := 
  RRC_TransactionIdentifier__cond (UECapabilityEnquiry__rrc_TransactionIdentifier z) /\
  UECapabilityEnquiry__criticalExtensions__cond (UECapabilityEnquiry__criticalExtensions z) /\
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
Definition UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__helper : forall a : UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Format : T_Format UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type)
    UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__cond UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Format.


Definition UECapabilityEnquiry__criticalExtensions__Format_Type := Eval cbn in get_formats UECapabilityEnquiry__criticalExtensions__list.
Definition UECapabilityEnquiry__criticalExtensions__Format_list : UECapabilityEnquiry__criticalExtensions__Format_Type :=
  (UECapabilityEnquiry_IEs__Format, (UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UECapabilityEnquiry__criticalExtensions__list__Format := Eval compute in choice_format UECapabilityEnquiry__criticalExtensions__list UECapabilityEnquiry__criticalExtensions__len_helper1 UECapabilityEnquiry__criticalExtensions__len_helper2  UECapabilityEnquiry__criticalExtensions__Format_list.
Definition UECapabilityEnquiry__criticalExtensions__F1 (z : UECapabilityEnquiry__criticalExtensions__Type) : (choice UECapabilityEnquiry__criticalExtensions__list) :=
  match z with
   | UECapabilityEnquiry__criticalExtensions__ueCapabilityEnquiry t => existT _ 0 t
  | UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UECapabilityEnquiry__criticalExtensions__g := (fun n => typ_set (get_nth_typ UECapabilityEnquiry__criticalExtensions__list n)).
Definition UECapabilityEnquiry__criticalExtensions__F2 (y : choice UECapabilityEnquiry__criticalExtensions__list) : UECapabilityEnquiry__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UECapabilityEnquiry__criticalExtensions__g n -> UECapabilityEnquiry__criticalExtensions__Type) with
    | 0 => fun (t : UECapabilityEnquiry_IEs__Type) => UECapabilityEnquiry__criticalExtensions__ueCapabilityEnquiry t 
    | 1 => fun (t : UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture__Type) => UECapabilityEnquiry__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UECapabilityEnquiry__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UECapabilityEnquiry__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UECapabilityEnquiry__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UECapabilityEnquiry__criticalExtensions__Type with end) n0
           end t0).

Lemma UECapabilityEnquiry__criticalExtensions__helper2 :  forall (y : UECapabilityEnquiry__criticalExtensions__Type), UECapabilityEnquiry__criticalExtensions__cond y -> choice_cond UECapabilityEnquiry__criticalExtensions__list (UECapabilityEnquiry__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UECapabilityEnquiry__criticalExtensions__helper3 :  forall (y : UECapabilityEnquiry__criticalExtensions__Type), UECapabilityEnquiry__criticalExtensions__F2 (UECapabilityEnquiry__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UECapabilityEnquiry__criticalExtensions__helper4 : (forall b : choice UECapabilityEnquiry__criticalExtensions__list, choice_cond UECapabilityEnquiry__criticalExtensions__list b -> UECapabilityEnquiry__criticalExtensions__cond (UECapabilityEnquiry__criticalExtensions__F2 b) /\ UECapabilityEnquiry__criticalExtensions__F1 (UECapabilityEnquiry__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UECapabilityEnquiry__criticalExtensions__F1 UECapabilityEnquiry__criticalExtensions__F2.
Definition UECapabilityEnquiry__criticalExtensions__Format : T_Format UECapabilityEnquiry__criticalExtensions__Type UECapabilityEnquiry__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UECapabilityEnquiry__criticalExtensions__cond UECapabilityEnquiry__criticalExtensions__list__Format UECapabilityEnquiry__criticalExtensions__F1 UECapabilityEnquiry__criticalExtensions__F2 UECapabilityEnquiry__criticalExtensions__helper2 UECapabilityEnquiry__criticalExtensions__helper3 UECapabilityEnquiry__criticalExtensions__helper4.
Opaque UECapabilityEnquiry__criticalExtensions__cond UECapabilityEnquiry__criticalExtensions__Format.


Definition UECapabilityEnquiry__Format_Type := Eval cbn in seq_format_prod UECapabilityEnquiry__list.
Definition UECapabilityEnquiry__Format_list : UECapabilityEnquiry__Format_Type :=
  (RRC_TransactionIdentifier__Format, (UECapabilityEnquiry__criticalExtensions__Format, unit_format)).
Definition UECapabilityEnquiry__list__Format := (*Eval compute in *) seq_format UECapabilityEnquiry__list UECapabilityEnquiry__Format_list.
Definition UECapabilityEnquiry__F1 z :=
  (UECapabilityEnquiry__rrc_TransactionIdentifier z, (UECapabilityEnquiry__criticalExtensions z, tt)).
Definition UECapabilityEnquiry__F2 (y : seq_type UECapabilityEnquiry__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UECapabilityEnquiry__Type i0 i1
  end.
Lemma UECapabilityEnquiry__F1F2_cond (z : UECapabilityEnquiry__Type)
  : UECapabilityEnquiry__cond z ->
  (seq_cond UECapabilityEnquiry__list (UECapabilityEnquiry__F1 z)).
intro H. unfold UECapabilityEnquiry__cond in H. simpl. auto. Qed.
Lemma UECapabilityEnquiry__F1F2_cond2 (z : UECapabilityEnquiry__Type)
 : UECapabilityEnquiry__F2 (UECapabilityEnquiry__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UECapabilityEnquiry__F2F1_cond (y : seq_type UECapabilityEnquiry__list)
  : seq_cond UECapabilityEnquiry__list y ->
 (UECapabilityEnquiry__cond (UECapabilityEnquiry__F2 y)) /\  UECapabilityEnquiry__F1 (UECapabilityEnquiry__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UECapabilityEnquiry__cond. simpl in *. auto.
 - simpl. unfold UECapabilityEnquiry__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UECapabilityEnquiry__Format : T_Format UECapabilityEnquiry__Type UECapabilityEnquiry__cond :=
        proj2_format  UECapabilityEnquiry__cond UECapabilityEnquiry__list__Format
    UECapabilityEnquiry__F1 UECapabilityEnquiry__F2 UECapabilityEnquiry__F1F2_cond  UECapabilityEnquiry__F1F2_cond2 UECapabilityEnquiry__F2F1_cond.
Opaque UECapabilityEnquiry__cond UECapabilityEnquiry__Format.

