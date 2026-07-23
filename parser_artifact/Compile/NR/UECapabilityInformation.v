Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.UECapabilityInformation_IEs.

Opaque UECapabilityInformation_IEs__cond UECapabilityInformation_IEs__Format.

Record UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond (z : UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UECapabilityInformation__criticalExtensions__Type : Set :=
  | UECapabilityInformation__criticalExtensions__ueCapabilityInformation : UECapabilityInformation_IEs__Type -> UECapabilityInformation__criticalExtensions__Type
  | UECapabilityInformation__criticalExtensions__criticalExtensionsFuture : UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type -> UECapabilityInformation__criticalExtensions__Type
.
Definition UECapabilityInformation__criticalExtensions__list : list typ := (
typ_cons UECapabilityInformation_IEs__Type UECapabilityInformation_IEs__cond ::
typ_cons UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UECapabilityInformation__criticalExtensions__cond (c : UECapabilityInformation__criticalExtensions__Type) := 
  match c with
  | UECapabilityInformation__criticalExtensions__ueCapabilityInformation t => UECapabilityInformation_IEs__cond t 
  | UECapabilityInformation__criticalExtensions__criticalExtensionsFuture t => UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UECapabilityInformation__criticalExtensions__len_helper1 : to_bit_sz (length UECapabilityInformation__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UECapabilityInformation__criticalExtensions__len_helper2 : 2 <= length2 UECapabilityInformation__criticalExtensions__list.
 simpl. lia. Qed.
Record UECapabilityInformation__Type : Set :=
  make__UECapabilityInformation__Type {
    UECapabilityInformation__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    UECapabilityInformation__criticalExtensions : UECapabilityInformation__criticalExtensions__Type ;
}.
Definition UECapabilityInformation__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor UECapabilityInformation__criticalExtensions__Type UECapabilityInformation__criticalExtensions__cond ::
 nil).
Definition UECapabilityInformation__cond z := 
  RRC_TransactionIdentifier__cond (UECapabilityInformation__rrc_TransactionIdentifier z) /\
  UECapabilityInformation__criticalExtensions__cond (UECapabilityInformation__criticalExtensions z) /\
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
Definition UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__helper : forall a : UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Format : T_Format UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type)
    UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Format.


Definition UECapabilityInformation__criticalExtensions__Format_Type := Eval cbn in get_formats UECapabilityInformation__criticalExtensions__list.
Definition UECapabilityInformation__criticalExtensions__Format_list : UECapabilityInformation__criticalExtensions__Format_Type :=
  (UECapabilityInformation_IEs__Format, (UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UECapabilityInformation__criticalExtensions__list__Format := Eval compute in choice_format UECapabilityInformation__criticalExtensions__list UECapabilityInformation__criticalExtensions__len_helper1 UECapabilityInformation__criticalExtensions__len_helper2  UECapabilityInformation__criticalExtensions__Format_list.
Definition UECapabilityInformation__criticalExtensions__F1 (z : UECapabilityInformation__criticalExtensions__Type) : (choice UECapabilityInformation__criticalExtensions__list) :=
  match z with
   | UECapabilityInformation__criticalExtensions__ueCapabilityInformation t => existT _ 0 t
  | UECapabilityInformation__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UECapabilityInformation__criticalExtensions__g := (fun n => typ_set (get_nth_typ UECapabilityInformation__criticalExtensions__list n)).
Definition UECapabilityInformation__criticalExtensions__F2 (y : choice UECapabilityInformation__criticalExtensions__list) : UECapabilityInformation__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UECapabilityInformation__criticalExtensions__g n -> UECapabilityInformation__criticalExtensions__Type) with
    | 0 => fun (t : UECapabilityInformation_IEs__Type) => UECapabilityInformation__criticalExtensions__ueCapabilityInformation t 
    | 1 => fun (t : UECapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type) => UECapabilityInformation__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UECapabilityInformation__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UECapabilityInformation__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UECapabilityInformation__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UECapabilityInformation__criticalExtensions__Type with end) n0
           end t0).

Lemma UECapabilityInformation__criticalExtensions__helper2 :  forall (y : UECapabilityInformation__criticalExtensions__Type), UECapabilityInformation__criticalExtensions__cond y -> choice_cond UECapabilityInformation__criticalExtensions__list (UECapabilityInformation__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UECapabilityInformation__criticalExtensions__helper3 :  forall (y : UECapabilityInformation__criticalExtensions__Type), UECapabilityInformation__criticalExtensions__F2 (UECapabilityInformation__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UECapabilityInformation__criticalExtensions__helper4 : (forall b : choice UECapabilityInformation__criticalExtensions__list, choice_cond UECapabilityInformation__criticalExtensions__list b -> UECapabilityInformation__criticalExtensions__cond (UECapabilityInformation__criticalExtensions__F2 b) /\ UECapabilityInformation__criticalExtensions__F1 (UECapabilityInformation__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UECapabilityInformation__criticalExtensions__F1 UECapabilityInformation__criticalExtensions__F2.
Definition UECapabilityInformation__criticalExtensions__Format : T_Format UECapabilityInformation__criticalExtensions__Type UECapabilityInformation__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UECapabilityInformation__criticalExtensions__cond UECapabilityInformation__criticalExtensions__list__Format UECapabilityInformation__criticalExtensions__F1 UECapabilityInformation__criticalExtensions__F2 UECapabilityInformation__criticalExtensions__helper2 UECapabilityInformation__criticalExtensions__helper3 UECapabilityInformation__criticalExtensions__helper4.
Opaque UECapabilityInformation__criticalExtensions__cond UECapabilityInformation__criticalExtensions__Format.


Definition UECapabilityInformation__Format_Type := Eval cbn in seq_format_prod UECapabilityInformation__list.
Definition UECapabilityInformation__Format_list : UECapabilityInformation__Format_Type :=
  (RRC_TransactionIdentifier__Format, (UECapabilityInformation__criticalExtensions__Format, unit_format)).
Definition UECapabilityInformation__list__Format := (*Eval compute in *) seq_format UECapabilityInformation__list UECapabilityInformation__Format_list.
Definition UECapabilityInformation__F1 z :=
  (UECapabilityInformation__rrc_TransactionIdentifier z, (UECapabilityInformation__criticalExtensions z, tt)).
Definition UECapabilityInformation__F2 (y : seq_type UECapabilityInformation__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UECapabilityInformation__Type i0 i1
  end.
Lemma UECapabilityInformation__F1F2_cond (z : UECapabilityInformation__Type)
  : UECapabilityInformation__cond z ->
  (seq_cond UECapabilityInformation__list (UECapabilityInformation__F1 z)).
intro H. unfold UECapabilityInformation__cond in H. simpl. auto. Qed.
Lemma UECapabilityInformation__F1F2_cond2 (z : UECapabilityInformation__Type)
 : UECapabilityInformation__F2 (UECapabilityInformation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UECapabilityInformation__F2F1_cond (y : seq_type UECapabilityInformation__list)
  : seq_cond UECapabilityInformation__list y ->
 (UECapabilityInformation__cond (UECapabilityInformation__F2 y)) /\  UECapabilityInformation__F1 (UECapabilityInformation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UECapabilityInformation__cond. simpl in *. auto.
 - simpl. unfold UECapabilityInformation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UECapabilityInformation__Format : T_Format UECapabilityInformation__Type UECapabilityInformation__cond :=
        proj2_format  UECapabilityInformation__cond UECapabilityInformation__list__Format
    UECapabilityInformation__F1 UECapabilityInformation__F2 UECapabilityInformation__F1F2_cond  UECapabilityInformation__F1F2_cond2 UECapabilityInformation__F2F1_cond.
Opaque UECapabilityInformation__cond UECapabilityInformation__Format.

