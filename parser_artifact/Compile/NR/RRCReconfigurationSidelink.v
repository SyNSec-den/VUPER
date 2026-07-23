Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCReconfigurationSidelink_r16_IEs.

Opaque RRCReconfigurationSidelink_r16_IEs__cond RRCReconfigurationSidelink_r16_IEs__Format.

Record RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__cond (z : RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCReconfigurationSidelink__criticalExtensions__Type : Set :=
  | RRCReconfigurationSidelink__criticalExtensions__rrcReconfigurationSidelink_r16 : RRCReconfigurationSidelink_r16_IEs__Type -> RRCReconfigurationSidelink__criticalExtensions__Type
  | RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture : RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type -> RRCReconfigurationSidelink__criticalExtensions__Type
.
Definition RRCReconfigurationSidelink__criticalExtensions__list : list typ := (
typ_cons RRCReconfigurationSidelink_r16_IEs__Type RRCReconfigurationSidelink_r16_IEs__cond ::
typ_cons RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCReconfigurationSidelink__criticalExtensions__cond (c : RRCReconfigurationSidelink__criticalExtensions__Type) := 
  match c with
  | RRCReconfigurationSidelink__criticalExtensions__rrcReconfigurationSidelink_r16 t => RRCReconfigurationSidelink_r16_IEs__cond t 
  | RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture t => RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCReconfigurationSidelink__criticalExtensions__len_helper1 : to_bit_sz (length RRCReconfigurationSidelink__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCReconfigurationSidelink__criticalExtensions__len_helper2 : 2 <= length2 RRCReconfigurationSidelink__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCReconfigurationSidelink__Type : Set :=
  make__RRCReconfigurationSidelink__Type {
    RRCReconfigurationSidelink__rrc_TransactionIdentifier_r16 : RRC_TransactionIdentifier__Type ;
    RRCReconfigurationSidelink__criticalExtensions : RRCReconfigurationSidelink__criticalExtensions__Type ;
}.
Definition RRCReconfigurationSidelink__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCReconfigurationSidelink__criticalExtensions__Type RRCReconfigurationSidelink__criticalExtensions__cond ::
 nil).
Definition RRCReconfigurationSidelink__cond z := 
  RRC_TransactionIdentifier__cond (RRCReconfigurationSidelink__rrc_TransactionIdentifier_r16 z) /\
  RRCReconfigurationSidelink__criticalExtensions__cond (RRCReconfigurationSidelink__criticalExtensions z) /\
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
Definition RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type)
    RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__cond RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCReconfigurationSidelink__criticalExtensions__Format_Type := Eval cbn in get_formats RRCReconfigurationSidelink__criticalExtensions__list.
Definition RRCReconfigurationSidelink__criticalExtensions__Format_list : RRCReconfigurationSidelink__criticalExtensions__Format_Type :=
  (RRCReconfigurationSidelink_r16_IEs__Format, (RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCReconfigurationSidelink__criticalExtensions__list__Format := Eval compute in choice_format RRCReconfigurationSidelink__criticalExtensions__list RRCReconfigurationSidelink__criticalExtensions__len_helper1 RRCReconfigurationSidelink__criticalExtensions__len_helper2  RRCReconfigurationSidelink__criticalExtensions__Format_list.
Definition RRCReconfigurationSidelink__criticalExtensions__F1 (z : RRCReconfigurationSidelink__criticalExtensions__Type) : (choice RRCReconfigurationSidelink__criticalExtensions__list) :=
  match z with
   | RRCReconfigurationSidelink__criticalExtensions__rrcReconfigurationSidelink_r16 t => existT _ 0 t
  | RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCReconfigurationSidelink__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCReconfigurationSidelink__criticalExtensions__list n)).
Definition RRCReconfigurationSidelink__criticalExtensions__F2 (y : choice RRCReconfigurationSidelink__criticalExtensions__list) : RRCReconfigurationSidelink__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCReconfigurationSidelink__criticalExtensions__g n -> RRCReconfigurationSidelink__criticalExtensions__Type) with
    | 0 => fun (t : RRCReconfigurationSidelink_r16_IEs__Type) => RRCReconfigurationSidelink__criticalExtensions__rrcReconfigurationSidelink_r16 t 
    | 1 => fun (t : RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture__Type) => RRCReconfigurationSidelink__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCReconfigurationSidelink__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCReconfigurationSidelink__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCReconfigurationSidelink__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCReconfigurationSidelink__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCReconfigurationSidelink__criticalExtensions__helper2 :  forall (y : RRCReconfigurationSidelink__criticalExtensions__Type), RRCReconfigurationSidelink__criticalExtensions__cond y -> choice_cond RRCReconfigurationSidelink__criticalExtensions__list (RRCReconfigurationSidelink__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCReconfigurationSidelink__criticalExtensions__helper3 :  forall (y : RRCReconfigurationSidelink__criticalExtensions__Type), RRCReconfigurationSidelink__criticalExtensions__F2 (RRCReconfigurationSidelink__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCReconfigurationSidelink__criticalExtensions__helper4 : (forall b : choice RRCReconfigurationSidelink__criticalExtensions__list, choice_cond RRCReconfigurationSidelink__criticalExtensions__list b -> RRCReconfigurationSidelink__criticalExtensions__cond (RRCReconfigurationSidelink__criticalExtensions__F2 b) /\ RRCReconfigurationSidelink__criticalExtensions__F1 (RRCReconfigurationSidelink__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCReconfigurationSidelink__criticalExtensions__F1 RRCReconfigurationSidelink__criticalExtensions__F2.
Definition RRCReconfigurationSidelink__criticalExtensions__Format : T_Format RRCReconfigurationSidelink__criticalExtensions__Type RRCReconfigurationSidelink__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCReconfigurationSidelink__criticalExtensions__cond RRCReconfigurationSidelink__criticalExtensions__list__Format RRCReconfigurationSidelink__criticalExtensions__F1 RRCReconfigurationSidelink__criticalExtensions__F2 RRCReconfigurationSidelink__criticalExtensions__helper2 RRCReconfigurationSidelink__criticalExtensions__helper3 RRCReconfigurationSidelink__criticalExtensions__helper4.
Opaque RRCReconfigurationSidelink__criticalExtensions__cond RRCReconfigurationSidelink__criticalExtensions__Format.


Definition RRCReconfigurationSidelink__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationSidelink__list.
Definition RRCReconfigurationSidelink__Format_list : RRCReconfigurationSidelink__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCReconfigurationSidelink__criticalExtensions__Format, unit_format)).
Definition RRCReconfigurationSidelink__list__Format := (*Eval compute in *) seq_format RRCReconfigurationSidelink__list RRCReconfigurationSidelink__Format_list.
Definition RRCReconfigurationSidelink__F1 z :=
  (RRCReconfigurationSidelink__rrc_TransactionIdentifier_r16 z, (RRCReconfigurationSidelink__criticalExtensions z, tt)).
Definition RRCReconfigurationSidelink__F2 (y : seq_type RRCReconfigurationSidelink__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCReconfigurationSidelink__Type i0 i1
  end.
Lemma RRCReconfigurationSidelink__F1F2_cond (z : RRCReconfigurationSidelink__Type)
  : RRCReconfigurationSidelink__cond z ->
  (seq_cond RRCReconfigurationSidelink__list (RRCReconfigurationSidelink__F1 z)).
intro H. unfold RRCReconfigurationSidelink__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationSidelink__F1F2_cond2 (z : RRCReconfigurationSidelink__Type)
 : RRCReconfigurationSidelink__F2 (RRCReconfigurationSidelink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationSidelink__F2F1_cond (y : seq_type RRCReconfigurationSidelink__list)
  : seq_cond RRCReconfigurationSidelink__list y ->
 (RRCReconfigurationSidelink__cond (RRCReconfigurationSidelink__F2 y)) /\  RRCReconfigurationSidelink__F1 (RRCReconfigurationSidelink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationSidelink__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationSidelink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationSidelink__Format : T_Format RRCReconfigurationSidelink__Type RRCReconfigurationSidelink__cond :=
        proj2_format  RRCReconfigurationSidelink__cond RRCReconfigurationSidelink__list__Format
    RRCReconfigurationSidelink__F1 RRCReconfigurationSidelink__F2 RRCReconfigurationSidelink__F1F2_cond  RRCReconfigurationSidelink__F1F2_cond2 RRCReconfigurationSidelink__F2F1_cond.
Opaque RRCReconfigurationSidelink__cond RRCReconfigurationSidelink__Format.

