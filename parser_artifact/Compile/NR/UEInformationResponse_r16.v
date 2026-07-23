Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.UEInformationResponse_r16_IEs.

Opaque UEInformationResponse_r16_IEs__cond UEInformationResponse_r16_IEs__Format.

Record UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__cond (z : UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UEInformationResponse_r16__criticalExtensions__Type : Set :=
  | UEInformationResponse_r16__criticalExtensions__ueInformationResponse_r16 : UEInformationResponse_r16_IEs__Type -> UEInformationResponse_r16__criticalExtensions__Type
  | UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture : UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type -> UEInformationResponse_r16__criticalExtensions__Type
.
Definition UEInformationResponse_r16__criticalExtensions__list : list typ := (
typ_cons UEInformationResponse_r16_IEs__Type UEInformationResponse_r16_IEs__cond ::
typ_cons UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UEInformationResponse_r16__criticalExtensions__cond (c : UEInformationResponse_r16__criticalExtensions__Type) := 
  match c with
  | UEInformationResponse_r16__criticalExtensions__ueInformationResponse_r16 t => UEInformationResponse_r16_IEs__cond t 
  | UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture t => UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UEInformationResponse_r16__criticalExtensions__len_helper1 : to_bit_sz (length UEInformationResponse_r16__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UEInformationResponse_r16__criticalExtensions__len_helper2 : 2 <= length2 UEInformationResponse_r16__criticalExtensions__list.
 simpl. lia. Qed.
Record UEInformationResponse_r16__Type : Set :=
  make__UEInformationResponse_r16__Type {
    UEInformationResponse_r16__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    UEInformationResponse_r16__criticalExtensions : UEInformationResponse_r16__criticalExtensions__Type ;
}.
Definition UEInformationResponse_r16__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor UEInformationResponse_r16__criticalExtensions__Type UEInformationResponse_r16__criticalExtensions__cond ::
 nil).
Definition UEInformationResponse_r16__cond z := 
  RRC_TransactionIdentifier__cond (UEInformationResponse_r16__rrc_TransactionIdentifier z) /\
  UEInformationResponse_r16__criticalExtensions__cond (UEInformationResponse_r16__criticalExtensions z) /\
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
Definition UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__helper : forall a : UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Format : T_Format UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type)
    UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__cond UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Format.


Definition UEInformationResponse_r16__criticalExtensions__Format_Type := Eval cbn in get_formats UEInformationResponse_r16__criticalExtensions__list.
Definition UEInformationResponse_r16__criticalExtensions__Format_list : UEInformationResponse_r16__criticalExtensions__Format_Type :=
  (UEInformationResponse_r16_IEs__Format, (UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UEInformationResponse_r16__criticalExtensions__list__Format := Eval compute in choice_format UEInformationResponse_r16__criticalExtensions__list UEInformationResponse_r16__criticalExtensions__len_helper1 UEInformationResponse_r16__criticalExtensions__len_helper2  UEInformationResponse_r16__criticalExtensions__Format_list.
Definition UEInformationResponse_r16__criticalExtensions__F1 (z : UEInformationResponse_r16__criticalExtensions__Type) : (choice UEInformationResponse_r16__criticalExtensions__list) :=
  match z with
   | UEInformationResponse_r16__criticalExtensions__ueInformationResponse_r16 t => existT _ 0 t
  | UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UEInformationResponse_r16__criticalExtensions__g := (fun n => typ_set (get_nth_typ UEInformationResponse_r16__criticalExtensions__list n)).
Definition UEInformationResponse_r16__criticalExtensions__F2 (y : choice UEInformationResponse_r16__criticalExtensions__list) : UEInformationResponse_r16__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UEInformationResponse_r16__criticalExtensions__g n -> UEInformationResponse_r16__criticalExtensions__Type) with
    | 0 => fun (t : UEInformationResponse_r16_IEs__Type) => UEInformationResponse_r16__criticalExtensions__ueInformationResponse_r16 t 
    | 1 => fun (t : UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture__Type) => UEInformationResponse_r16__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UEInformationResponse_r16__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UEInformationResponse_r16__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UEInformationResponse_r16__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UEInformationResponse_r16__criticalExtensions__Type with end) n0
           end t0).

Lemma UEInformationResponse_r16__criticalExtensions__helper2 :  forall (y : UEInformationResponse_r16__criticalExtensions__Type), UEInformationResponse_r16__criticalExtensions__cond y -> choice_cond UEInformationResponse_r16__criticalExtensions__list (UEInformationResponse_r16__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UEInformationResponse_r16__criticalExtensions__helper3 :  forall (y : UEInformationResponse_r16__criticalExtensions__Type), UEInformationResponse_r16__criticalExtensions__F2 (UEInformationResponse_r16__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UEInformationResponse_r16__criticalExtensions__helper4 : (forall b : choice UEInformationResponse_r16__criticalExtensions__list, choice_cond UEInformationResponse_r16__criticalExtensions__list b -> UEInformationResponse_r16__criticalExtensions__cond (UEInformationResponse_r16__criticalExtensions__F2 b) /\ UEInformationResponse_r16__criticalExtensions__F1 (UEInformationResponse_r16__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UEInformationResponse_r16__criticalExtensions__F1 UEInformationResponse_r16__criticalExtensions__F2.
Definition UEInformationResponse_r16__criticalExtensions__Format : T_Format UEInformationResponse_r16__criticalExtensions__Type UEInformationResponse_r16__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UEInformationResponse_r16__criticalExtensions__cond UEInformationResponse_r16__criticalExtensions__list__Format UEInformationResponse_r16__criticalExtensions__F1 UEInformationResponse_r16__criticalExtensions__F2 UEInformationResponse_r16__criticalExtensions__helper2 UEInformationResponse_r16__criticalExtensions__helper3 UEInformationResponse_r16__criticalExtensions__helper4.
Opaque UEInformationResponse_r16__criticalExtensions__cond UEInformationResponse_r16__criticalExtensions__Format.


Definition UEInformationResponse_r16__Format_Type := Eval cbn in seq_format_prod UEInformationResponse_r16__list.
Definition UEInformationResponse_r16__Format_list : UEInformationResponse_r16__Format_Type :=
  (RRC_TransactionIdentifier__Format, (UEInformationResponse_r16__criticalExtensions__Format, unit_format)).
Definition UEInformationResponse_r16__list__Format := (*Eval compute in *) seq_format UEInformationResponse_r16__list UEInformationResponse_r16__Format_list.
Definition UEInformationResponse_r16__F1 z :=
  (UEInformationResponse_r16__rrc_TransactionIdentifier z, (UEInformationResponse_r16__criticalExtensions z, tt)).
Definition UEInformationResponse_r16__F2 (y : seq_type UEInformationResponse_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__UEInformationResponse_r16__Type i0 i1
  end.
Lemma UEInformationResponse_r16__F1F2_cond (z : UEInformationResponse_r16__Type)
  : UEInformationResponse_r16__cond z ->
  (seq_cond UEInformationResponse_r16__list (UEInformationResponse_r16__F1 z)).
intro H. unfold UEInformationResponse_r16__cond in H. simpl. auto. Qed.
Lemma UEInformationResponse_r16__F1F2_cond2 (z : UEInformationResponse_r16__Type)
 : UEInformationResponse_r16__F2 (UEInformationResponse_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEInformationResponse_r16__F2F1_cond (y : seq_type UEInformationResponse_r16__list)
  : seq_cond UEInformationResponse_r16__list y ->
 (UEInformationResponse_r16__cond (UEInformationResponse_r16__F2 y)) /\  UEInformationResponse_r16__F1 (UEInformationResponse_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEInformationResponse_r16__cond. simpl in *. auto.
 - simpl. unfold UEInformationResponse_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEInformationResponse_r16__Format : T_Format UEInformationResponse_r16__Type UEInformationResponse_r16__cond :=
        proj2_format  UEInformationResponse_r16__cond UEInformationResponse_r16__list__Format
    UEInformationResponse_r16__F1 UEInformationResponse_r16__F2 UEInformationResponse_r16__F1F2_cond  UEInformationResponse_r16__F1F2_cond2 UEInformationResponse_r16__F2F1_cond.
Opaque UEInformationResponse_r16__cond UEInformationResponse_r16__Format.

