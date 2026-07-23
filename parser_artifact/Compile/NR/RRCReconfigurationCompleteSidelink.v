Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCReconfigurationCompleteSidelink_r16_IEs.

Opaque RRCReconfigurationCompleteSidelink_r16_IEs__cond RRCReconfigurationCompleteSidelink_r16_IEs__Format.

Record RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__cond (z : RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCReconfigurationCompleteSidelink__criticalExtensions__Type : Set :=
  | RRCReconfigurationCompleteSidelink__criticalExtensions__rrcReconfigurationCompleteSidelink_r16 : RRCReconfigurationCompleteSidelink_r16_IEs__Type -> RRCReconfigurationCompleteSidelink__criticalExtensions__Type
  | RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture : RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type -> RRCReconfigurationCompleteSidelink__criticalExtensions__Type
.
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__list : list typ := (
typ_cons RRCReconfigurationCompleteSidelink_r16_IEs__Type RRCReconfigurationCompleteSidelink_r16_IEs__cond ::
typ_cons RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__cond (c : RRCReconfigurationCompleteSidelink__criticalExtensions__Type) := 
  match c with
  | RRCReconfigurationCompleteSidelink__criticalExtensions__rrcReconfigurationCompleteSidelink_r16 t => RRCReconfigurationCompleteSidelink_r16_IEs__cond t 
  | RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture t => RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCReconfigurationCompleteSidelink__criticalExtensions__len_helper1 : to_bit_sz (length RRCReconfigurationCompleteSidelink__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCReconfigurationCompleteSidelink__criticalExtensions__len_helper2 : 2 <= length2 RRCReconfigurationCompleteSidelink__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCReconfigurationCompleteSidelink__Type : Set :=
  make__RRCReconfigurationCompleteSidelink__Type {
    RRCReconfigurationCompleteSidelink__rrc_TransactionIdentifier_r16 : RRC_TransactionIdentifier__Type ;
    RRCReconfigurationCompleteSidelink__criticalExtensions : RRCReconfigurationCompleteSidelink__criticalExtensions__Type ;
}.
Definition RRCReconfigurationCompleteSidelink__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCReconfigurationCompleteSidelink__criticalExtensions__Type RRCReconfigurationCompleteSidelink__criticalExtensions__cond ::
 nil).
Definition RRCReconfigurationCompleteSidelink__cond z := 
  RRC_TransactionIdentifier__cond (RRCReconfigurationCompleteSidelink__rrc_TransactionIdentifier_r16 z) /\
  RRCReconfigurationCompleteSidelink__criticalExtensions__cond (RRCReconfigurationCompleteSidelink__criticalExtensions z) /\
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
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type)
    RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__cond RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCReconfigurationCompleteSidelink__criticalExtensions__Format_Type := Eval cbn in get_formats RRCReconfigurationCompleteSidelink__criticalExtensions__list.
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__Format_list : RRCReconfigurationCompleteSidelink__criticalExtensions__Format_Type :=
  (RRCReconfigurationCompleteSidelink_r16_IEs__Format, (RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__list__Format := Eval compute in choice_format RRCReconfigurationCompleteSidelink__criticalExtensions__list RRCReconfigurationCompleteSidelink__criticalExtensions__len_helper1 RRCReconfigurationCompleteSidelink__criticalExtensions__len_helper2  RRCReconfigurationCompleteSidelink__criticalExtensions__Format_list.
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__F1 (z : RRCReconfigurationCompleteSidelink__criticalExtensions__Type) : (choice RRCReconfigurationCompleteSidelink__criticalExtensions__list) :=
  match z with
   | RRCReconfigurationCompleteSidelink__criticalExtensions__rrcReconfigurationCompleteSidelink_r16 t => existT _ 0 t
  | RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCReconfigurationCompleteSidelink__criticalExtensions__list n)).
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__F2 (y : choice RRCReconfigurationCompleteSidelink__criticalExtensions__list) : RRCReconfigurationCompleteSidelink__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCReconfigurationCompleteSidelink__criticalExtensions__g n -> RRCReconfigurationCompleteSidelink__criticalExtensions__Type) with
    | 0 => fun (t : RRCReconfigurationCompleteSidelink_r16_IEs__Type) => RRCReconfigurationCompleteSidelink__criticalExtensions__rrcReconfigurationCompleteSidelink_r16 t 
    | 1 => fun (t : RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture__Type) => RRCReconfigurationCompleteSidelink__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCReconfigurationCompleteSidelink__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCReconfigurationCompleteSidelink__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCReconfigurationCompleteSidelink__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCReconfigurationCompleteSidelink__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCReconfigurationCompleteSidelink__criticalExtensions__helper2 :  forall (y : RRCReconfigurationCompleteSidelink__criticalExtensions__Type), RRCReconfigurationCompleteSidelink__criticalExtensions__cond y -> choice_cond RRCReconfigurationCompleteSidelink__criticalExtensions__list (RRCReconfigurationCompleteSidelink__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCReconfigurationCompleteSidelink__criticalExtensions__helper3 :  forall (y : RRCReconfigurationCompleteSidelink__criticalExtensions__Type), RRCReconfigurationCompleteSidelink__criticalExtensions__F2 (RRCReconfigurationCompleteSidelink__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCReconfigurationCompleteSidelink__criticalExtensions__helper4 : (forall b : choice RRCReconfigurationCompleteSidelink__criticalExtensions__list, choice_cond RRCReconfigurationCompleteSidelink__criticalExtensions__list b -> RRCReconfigurationCompleteSidelink__criticalExtensions__cond (RRCReconfigurationCompleteSidelink__criticalExtensions__F2 b) /\ RRCReconfigurationCompleteSidelink__criticalExtensions__F1 (RRCReconfigurationCompleteSidelink__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCReconfigurationCompleteSidelink__criticalExtensions__F1 RRCReconfigurationCompleteSidelink__criticalExtensions__F2.
Definition RRCReconfigurationCompleteSidelink__criticalExtensions__Format : T_Format RRCReconfigurationCompleteSidelink__criticalExtensions__Type RRCReconfigurationCompleteSidelink__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCReconfigurationCompleteSidelink__criticalExtensions__cond RRCReconfigurationCompleteSidelink__criticalExtensions__list__Format RRCReconfigurationCompleteSidelink__criticalExtensions__F1 RRCReconfigurationCompleteSidelink__criticalExtensions__F2 RRCReconfigurationCompleteSidelink__criticalExtensions__helper2 RRCReconfigurationCompleteSidelink__criticalExtensions__helper3 RRCReconfigurationCompleteSidelink__criticalExtensions__helper4.
Opaque RRCReconfigurationCompleteSidelink__criticalExtensions__cond RRCReconfigurationCompleteSidelink__criticalExtensions__Format.


Definition RRCReconfigurationCompleteSidelink__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationCompleteSidelink__list.
Definition RRCReconfigurationCompleteSidelink__Format_list : RRCReconfigurationCompleteSidelink__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCReconfigurationCompleteSidelink__criticalExtensions__Format, unit_format)).
Definition RRCReconfigurationCompleteSidelink__list__Format := (*Eval compute in *) seq_format RRCReconfigurationCompleteSidelink__list RRCReconfigurationCompleteSidelink__Format_list.
Definition RRCReconfigurationCompleteSidelink__F1 z :=
  (RRCReconfigurationCompleteSidelink__rrc_TransactionIdentifier_r16 z, (RRCReconfigurationCompleteSidelink__criticalExtensions z, tt)).
Definition RRCReconfigurationCompleteSidelink__F2 (y : seq_type RRCReconfigurationCompleteSidelink__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCReconfigurationCompleteSidelink__Type i0 i1
  end.
Lemma RRCReconfigurationCompleteSidelink__F1F2_cond (z : RRCReconfigurationCompleteSidelink__Type)
  : RRCReconfigurationCompleteSidelink__cond z ->
  (seq_cond RRCReconfigurationCompleteSidelink__list (RRCReconfigurationCompleteSidelink__F1 z)).
intro H. unfold RRCReconfigurationCompleteSidelink__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationCompleteSidelink__F1F2_cond2 (z : RRCReconfigurationCompleteSidelink__Type)
 : RRCReconfigurationCompleteSidelink__F2 (RRCReconfigurationCompleteSidelink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationCompleteSidelink__F2F1_cond (y : seq_type RRCReconfigurationCompleteSidelink__list)
  : seq_cond RRCReconfigurationCompleteSidelink__list y ->
 (RRCReconfigurationCompleteSidelink__cond (RRCReconfigurationCompleteSidelink__F2 y)) /\  RRCReconfigurationCompleteSidelink__F1 (RRCReconfigurationCompleteSidelink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationCompleteSidelink__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationCompleteSidelink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationCompleteSidelink__Format : T_Format RRCReconfigurationCompleteSidelink__Type RRCReconfigurationCompleteSidelink__cond :=
        proj2_format  RRCReconfigurationCompleteSidelink__cond RRCReconfigurationCompleteSidelink__list__Format
    RRCReconfigurationCompleteSidelink__F1 RRCReconfigurationCompleteSidelink__F2 RRCReconfigurationCompleteSidelink__F1F2_cond  RRCReconfigurationCompleteSidelink__F1F2_cond2 RRCReconfigurationCompleteSidelink__F2F1_cond.
Opaque RRCReconfigurationCompleteSidelink__cond RRCReconfigurationCompleteSidelink__Format.

