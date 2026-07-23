Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCReconfigurationFailureSidelink_r16_IEs.

Opaque RRCReconfigurationFailureSidelink_r16_IEs__cond RRCReconfigurationFailureSidelink_r16_IEs__Format.

Record RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__cond (z : RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCReconfigurationFailureSidelink__criticalExtensions__Type : Set :=
  | RRCReconfigurationFailureSidelink__criticalExtensions__rrcReconfigurationFailureSidelink_r16 : RRCReconfigurationFailureSidelink_r16_IEs__Type -> RRCReconfigurationFailureSidelink__criticalExtensions__Type
  | RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture : RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type -> RRCReconfigurationFailureSidelink__criticalExtensions__Type
.
Definition RRCReconfigurationFailureSidelink__criticalExtensions__list : list typ := (
typ_cons RRCReconfigurationFailureSidelink_r16_IEs__Type RRCReconfigurationFailureSidelink_r16_IEs__cond ::
typ_cons RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCReconfigurationFailureSidelink__criticalExtensions__cond (c : RRCReconfigurationFailureSidelink__criticalExtensions__Type) := 
  match c with
  | RRCReconfigurationFailureSidelink__criticalExtensions__rrcReconfigurationFailureSidelink_r16 t => RRCReconfigurationFailureSidelink_r16_IEs__cond t 
  | RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture t => RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCReconfigurationFailureSidelink__criticalExtensions__len_helper1 : to_bit_sz (length RRCReconfigurationFailureSidelink__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCReconfigurationFailureSidelink__criticalExtensions__len_helper2 : 2 <= length2 RRCReconfigurationFailureSidelink__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCReconfigurationFailureSidelink__Type : Set :=
  make__RRCReconfigurationFailureSidelink__Type {
    RRCReconfigurationFailureSidelink__rrc_TransactionIdentifier_r16 : RRC_TransactionIdentifier__Type ;
    RRCReconfigurationFailureSidelink__criticalExtensions : RRCReconfigurationFailureSidelink__criticalExtensions__Type ;
}.
Definition RRCReconfigurationFailureSidelink__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCReconfigurationFailureSidelink__criticalExtensions__Type RRCReconfigurationFailureSidelink__criticalExtensions__cond ::
 nil).
Definition RRCReconfigurationFailureSidelink__cond z := 
  RRC_TransactionIdentifier__cond (RRCReconfigurationFailureSidelink__rrc_TransactionIdentifier_r16 z) /\
  RRCReconfigurationFailureSidelink__criticalExtensions__cond (RRCReconfigurationFailureSidelink__criticalExtensions z) /\
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
Definition RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type)
    RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__cond RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCReconfigurationFailureSidelink__criticalExtensions__Format_Type := Eval cbn in get_formats RRCReconfigurationFailureSidelink__criticalExtensions__list.
Definition RRCReconfigurationFailureSidelink__criticalExtensions__Format_list : RRCReconfigurationFailureSidelink__criticalExtensions__Format_Type :=
  (RRCReconfigurationFailureSidelink_r16_IEs__Format, (RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCReconfigurationFailureSidelink__criticalExtensions__list__Format := Eval compute in choice_format RRCReconfigurationFailureSidelink__criticalExtensions__list RRCReconfigurationFailureSidelink__criticalExtensions__len_helper1 RRCReconfigurationFailureSidelink__criticalExtensions__len_helper2  RRCReconfigurationFailureSidelink__criticalExtensions__Format_list.
Definition RRCReconfigurationFailureSidelink__criticalExtensions__F1 (z : RRCReconfigurationFailureSidelink__criticalExtensions__Type) : (choice RRCReconfigurationFailureSidelink__criticalExtensions__list) :=
  match z with
   | RRCReconfigurationFailureSidelink__criticalExtensions__rrcReconfigurationFailureSidelink_r16 t => existT _ 0 t
  | RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCReconfigurationFailureSidelink__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCReconfigurationFailureSidelink__criticalExtensions__list n)).
Definition RRCReconfigurationFailureSidelink__criticalExtensions__F2 (y : choice RRCReconfigurationFailureSidelink__criticalExtensions__list) : RRCReconfigurationFailureSidelink__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCReconfigurationFailureSidelink__criticalExtensions__g n -> RRCReconfigurationFailureSidelink__criticalExtensions__Type) with
    | 0 => fun (t : RRCReconfigurationFailureSidelink_r16_IEs__Type) => RRCReconfigurationFailureSidelink__criticalExtensions__rrcReconfigurationFailureSidelink_r16 t 
    | 1 => fun (t : RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture__Type) => RRCReconfigurationFailureSidelink__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCReconfigurationFailureSidelink__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCReconfigurationFailureSidelink__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCReconfigurationFailureSidelink__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCReconfigurationFailureSidelink__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCReconfigurationFailureSidelink__criticalExtensions__helper2 :  forall (y : RRCReconfigurationFailureSidelink__criticalExtensions__Type), RRCReconfigurationFailureSidelink__criticalExtensions__cond y -> choice_cond RRCReconfigurationFailureSidelink__criticalExtensions__list (RRCReconfigurationFailureSidelink__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCReconfigurationFailureSidelink__criticalExtensions__helper3 :  forall (y : RRCReconfigurationFailureSidelink__criticalExtensions__Type), RRCReconfigurationFailureSidelink__criticalExtensions__F2 (RRCReconfigurationFailureSidelink__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCReconfigurationFailureSidelink__criticalExtensions__helper4 : (forall b : choice RRCReconfigurationFailureSidelink__criticalExtensions__list, choice_cond RRCReconfigurationFailureSidelink__criticalExtensions__list b -> RRCReconfigurationFailureSidelink__criticalExtensions__cond (RRCReconfigurationFailureSidelink__criticalExtensions__F2 b) /\ RRCReconfigurationFailureSidelink__criticalExtensions__F1 (RRCReconfigurationFailureSidelink__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCReconfigurationFailureSidelink__criticalExtensions__F1 RRCReconfigurationFailureSidelink__criticalExtensions__F2.
Definition RRCReconfigurationFailureSidelink__criticalExtensions__Format : T_Format RRCReconfigurationFailureSidelink__criticalExtensions__Type RRCReconfigurationFailureSidelink__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCReconfigurationFailureSidelink__criticalExtensions__cond RRCReconfigurationFailureSidelink__criticalExtensions__list__Format RRCReconfigurationFailureSidelink__criticalExtensions__F1 RRCReconfigurationFailureSidelink__criticalExtensions__F2 RRCReconfigurationFailureSidelink__criticalExtensions__helper2 RRCReconfigurationFailureSidelink__criticalExtensions__helper3 RRCReconfigurationFailureSidelink__criticalExtensions__helper4.
Opaque RRCReconfigurationFailureSidelink__criticalExtensions__cond RRCReconfigurationFailureSidelink__criticalExtensions__Format.


Definition RRCReconfigurationFailureSidelink__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationFailureSidelink__list.
Definition RRCReconfigurationFailureSidelink__Format_list : RRCReconfigurationFailureSidelink__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCReconfigurationFailureSidelink__criticalExtensions__Format, unit_format)).
Definition RRCReconfigurationFailureSidelink__list__Format := (*Eval compute in *) seq_format RRCReconfigurationFailureSidelink__list RRCReconfigurationFailureSidelink__Format_list.
Definition RRCReconfigurationFailureSidelink__F1 z :=
  (RRCReconfigurationFailureSidelink__rrc_TransactionIdentifier_r16 z, (RRCReconfigurationFailureSidelink__criticalExtensions z, tt)).
Definition RRCReconfigurationFailureSidelink__F2 (y : seq_type RRCReconfigurationFailureSidelink__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCReconfigurationFailureSidelink__Type i0 i1
  end.
Lemma RRCReconfigurationFailureSidelink__F1F2_cond (z : RRCReconfigurationFailureSidelink__Type)
  : RRCReconfigurationFailureSidelink__cond z ->
  (seq_cond RRCReconfigurationFailureSidelink__list (RRCReconfigurationFailureSidelink__F1 z)).
intro H. unfold RRCReconfigurationFailureSidelink__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationFailureSidelink__F1F2_cond2 (z : RRCReconfigurationFailureSidelink__Type)
 : RRCReconfigurationFailureSidelink__F2 (RRCReconfigurationFailureSidelink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationFailureSidelink__F2F1_cond (y : seq_type RRCReconfigurationFailureSidelink__list)
  : seq_cond RRCReconfigurationFailureSidelink__list y ->
 (RRCReconfigurationFailureSidelink__cond (RRCReconfigurationFailureSidelink__F2 y)) /\  RRCReconfigurationFailureSidelink__F1 (RRCReconfigurationFailureSidelink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationFailureSidelink__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationFailureSidelink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationFailureSidelink__Format : T_Format RRCReconfigurationFailureSidelink__Type RRCReconfigurationFailureSidelink__cond :=
        proj2_format  RRCReconfigurationFailureSidelink__cond RRCReconfigurationFailureSidelink__list__Format
    RRCReconfigurationFailureSidelink__F1 RRCReconfigurationFailureSidelink__F2 RRCReconfigurationFailureSidelink__F1F2_cond  RRCReconfigurationFailureSidelink__F1F2_cond2 RRCReconfigurationFailureSidelink__F2F1_cond.
Opaque RRCReconfigurationFailureSidelink__cond RRCReconfigurationFailureSidelink__Format.

