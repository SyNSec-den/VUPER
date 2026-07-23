Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.DLInformationTransfer_IEs.

Opaque DLInformationTransfer_IEs__cond DLInformationTransfer_IEs__Format.

Record DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type : Set := make__DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond (z : DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive DLInformationTransfer__criticalExtensions__Type : Set :=
  | DLInformationTransfer__criticalExtensions__dlInformationTransfer : DLInformationTransfer_IEs__Type -> DLInformationTransfer__criticalExtensions__Type
  | DLInformationTransfer__criticalExtensions__criticalExtensionsFuture : DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type -> DLInformationTransfer__criticalExtensions__Type
.
Definition DLInformationTransfer__criticalExtensions__list : list typ := (
typ_cons DLInformationTransfer_IEs__Type DLInformationTransfer_IEs__cond ::
typ_cons DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition DLInformationTransfer__criticalExtensions__cond (c : DLInformationTransfer__criticalExtensions__Type) := 
  match c with
  | DLInformationTransfer__criticalExtensions__dlInformationTransfer t => DLInformationTransfer_IEs__cond t 
  | DLInformationTransfer__criticalExtensions__criticalExtensionsFuture t => DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma DLInformationTransfer__criticalExtensions__len_helper1 : to_bit_sz (length DLInformationTransfer__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DLInformationTransfer__criticalExtensions__len_helper2 : 2 <= length2 DLInformationTransfer__criticalExtensions__list.
 simpl. lia. Qed.
Record DLInformationTransfer__Type : Set :=
  make__DLInformationTransfer__Type {
    DLInformationTransfer__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    DLInformationTransfer__criticalExtensions : DLInformationTransfer__criticalExtensions__Type ;
}.
Definition DLInformationTransfer__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor DLInformationTransfer__criticalExtensions__Type DLInformationTransfer__criticalExtensions__cond ::
 nil).
Definition DLInformationTransfer__cond z := 
  RRC_TransactionIdentifier__cond (DLInformationTransfer__rrc_TransactionIdentifier z) /\
  DLInformationTransfer__criticalExtensions__cond (DLInformationTransfer__criticalExtensions z) /\
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
Definition DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__helper : forall a : DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Format : T_Format DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type)
    DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Format.


Definition DLInformationTransfer__criticalExtensions__Format_Type := Eval cbn in get_formats DLInformationTransfer__criticalExtensions__list.
Definition DLInformationTransfer__criticalExtensions__Format_list : DLInformationTransfer__criticalExtensions__Format_Type :=
  (DLInformationTransfer_IEs__Format, (DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition DLInformationTransfer__criticalExtensions__list__Format := Eval compute in choice_format DLInformationTransfer__criticalExtensions__list DLInformationTransfer__criticalExtensions__len_helper1 DLInformationTransfer__criticalExtensions__len_helper2  DLInformationTransfer__criticalExtensions__Format_list.
Definition DLInformationTransfer__criticalExtensions__F1 (z : DLInformationTransfer__criticalExtensions__Type) : (choice DLInformationTransfer__criticalExtensions__list) :=
  match z with
   | DLInformationTransfer__criticalExtensions__dlInformationTransfer t => existT _ 0 t
  | DLInformationTransfer__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition DLInformationTransfer__criticalExtensions__g := (fun n => typ_set (get_nth_typ DLInformationTransfer__criticalExtensions__list n)).
Definition DLInformationTransfer__criticalExtensions__F2 (y : choice DLInformationTransfer__criticalExtensions__list) : DLInformationTransfer__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DLInformationTransfer__criticalExtensions__g n -> DLInformationTransfer__criticalExtensions__Type) with
    | 0 => fun (t : DLInformationTransfer_IEs__Type) => DLInformationTransfer__criticalExtensions__dlInformationTransfer t 
    | 1 => fun (t : DLInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type) => DLInformationTransfer__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : DLInformationTransfer__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ DLInformationTransfer__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DLInformationTransfer__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return DLInformationTransfer__criticalExtensions__Type with end) n0
           end t0).

Lemma DLInformationTransfer__criticalExtensions__helper2 :  forall (y : DLInformationTransfer__criticalExtensions__Type), DLInformationTransfer__criticalExtensions__cond y -> choice_cond DLInformationTransfer__criticalExtensions__list (DLInformationTransfer__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DLInformationTransfer__criticalExtensions__helper3 :  forall (y : DLInformationTransfer__criticalExtensions__Type), DLInformationTransfer__criticalExtensions__F2 (DLInformationTransfer__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DLInformationTransfer__criticalExtensions__helper4 : (forall b : choice DLInformationTransfer__criticalExtensions__list, choice_cond DLInformationTransfer__criticalExtensions__list b -> DLInformationTransfer__criticalExtensions__cond (DLInformationTransfer__criticalExtensions__F2 b) /\ DLInformationTransfer__criticalExtensions__F1 (DLInformationTransfer__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DLInformationTransfer__criticalExtensions__F1 DLInformationTransfer__criticalExtensions__F2.
Definition DLInformationTransfer__criticalExtensions__Format : T_Format DLInformationTransfer__criticalExtensions__Type DLInformationTransfer__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format DLInformationTransfer__criticalExtensions__cond DLInformationTransfer__criticalExtensions__list__Format DLInformationTransfer__criticalExtensions__F1 DLInformationTransfer__criticalExtensions__F2 DLInformationTransfer__criticalExtensions__helper2 DLInformationTransfer__criticalExtensions__helper3 DLInformationTransfer__criticalExtensions__helper4.
Opaque DLInformationTransfer__criticalExtensions__cond DLInformationTransfer__criticalExtensions__Format.


Definition DLInformationTransfer__Format_Type := Eval cbn in seq_format_prod DLInformationTransfer__list.
Definition DLInformationTransfer__Format_list : DLInformationTransfer__Format_Type :=
  (RRC_TransactionIdentifier__Format, (DLInformationTransfer__criticalExtensions__Format, unit_format)).
Definition DLInformationTransfer__list__Format := (*Eval compute in *) seq_format DLInformationTransfer__list DLInformationTransfer__Format_list.
Definition DLInformationTransfer__F1 z :=
  (DLInformationTransfer__rrc_TransactionIdentifier z, (DLInformationTransfer__criticalExtensions z, tt)).
Definition DLInformationTransfer__F2 (y : seq_type DLInformationTransfer__list) :=
  match y with
  | (i0, (i1, _))=>
    make__DLInformationTransfer__Type i0 i1
  end.
Lemma DLInformationTransfer__F1F2_cond (z : DLInformationTransfer__Type)
  : DLInformationTransfer__cond z ->
  (seq_cond DLInformationTransfer__list (DLInformationTransfer__F1 z)).
intro H. unfold DLInformationTransfer__cond in H. simpl. auto. Qed.
Lemma DLInformationTransfer__F1F2_cond2 (z : DLInformationTransfer__Type)
 : DLInformationTransfer__F2 (DLInformationTransfer__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DLInformationTransfer__F2F1_cond (y : seq_type DLInformationTransfer__list)
  : seq_cond DLInformationTransfer__list y ->
 (DLInformationTransfer__cond (DLInformationTransfer__F2 y)) /\  DLInformationTransfer__F1 (DLInformationTransfer__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DLInformationTransfer__cond. simpl in *. auto.
 - simpl. unfold DLInformationTransfer__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DLInformationTransfer__Format : T_Format DLInformationTransfer__Type DLInformationTransfer__cond :=
        proj2_format  DLInformationTransfer__cond DLInformationTransfer__list__Format
    DLInformationTransfer__F1 DLInformationTransfer__F2 DLInformationTransfer__F1F2_cond  DLInformationTransfer__F1F2_cond2 DLInformationTransfer__F2F1_cond.
Opaque DLInformationTransfer__cond DLInformationTransfer__Format.

