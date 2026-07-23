Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCReconfigurationComplete_IEs.

Opaque RRCReconfigurationComplete_IEs__cond RRCReconfigurationComplete_IEs__Format.

Record RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__cond (z : RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCReconfigurationComplete__criticalExtensions__Type : Set :=
  | RRCReconfigurationComplete__criticalExtensions__rrcReconfigurationComplete : RRCReconfigurationComplete_IEs__Type -> RRCReconfigurationComplete__criticalExtensions__Type
  | RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture : RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type -> RRCReconfigurationComplete__criticalExtensions__Type
.
Definition RRCReconfigurationComplete__criticalExtensions__list : list typ := (
typ_cons RRCReconfigurationComplete_IEs__Type RRCReconfigurationComplete_IEs__cond ::
typ_cons RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCReconfigurationComplete__criticalExtensions__cond (c : RRCReconfigurationComplete__criticalExtensions__Type) := 
  match c with
  | RRCReconfigurationComplete__criticalExtensions__rrcReconfigurationComplete t => RRCReconfigurationComplete_IEs__cond t 
  | RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture t => RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCReconfigurationComplete__criticalExtensions__len_helper1 : to_bit_sz (length RRCReconfigurationComplete__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCReconfigurationComplete__criticalExtensions__len_helper2 : 2 <= length2 RRCReconfigurationComplete__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCReconfigurationComplete__Type : Set :=
  make__RRCReconfigurationComplete__Type {
    RRCReconfigurationComplete__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    RRCReconfigurationComplete__criticalExtensions : RRCReconfigurationComplete__criticalExtensions__Type ;
}.
Definition RRCReconfigurationComplete__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCReconfigurationComplete__criticalExtensions__Type RRCReconfigurationComplete__criticalExtensions__cond ::
 nil).
Definition RRCReconfigurationComplete__cond z := 
  RRC_TransactionIdentifier__cond (RRCReconfigurationComplete__rrc_TransactionIdentifier z) /\
  RRCReconfigurationComplete__criticalExtensions__cond (RRCReconfigurationComplete__criticalExtensions z) /\
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
Definition RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type)
    RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__cond RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCReconfigurationComplete__criticalExtensions__Format_Type := Eval cbn in get_formats RRCReconfigurationComplete__criticalExtensions__list.
Definition RRCReconfigurationComplete__criticalExtensions__Format_list : RRCReconfigurationComplete__criticalExtensions__Format_Type :=
  (RRCReconfigurationComplete_IEs__Format, (RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCReconfigurationComplete__criticalExtensions__list__Format := Eval compute in choice_format RRCReconfigurationComplete__criticalExtensions__list RRCReconfigurationComplete__criticalExtensions__len_helper1 RRCReconfigurationComplete__criticalExtensions__len_helper2  RRCReconfigurationComplete__criticalExtensions__Format_list.
Definition RRCReconfigurationComplete__criticalExtensions__F1 (z : RRCReconfigurationComplete__criticalExtensions__Type) : (choice RRCReconfigurationComplete__criticalExtensions__list) :=
  match z with
   | RRCReconfigurationComplete__criticalExtensions__rrcReconfigurationComplete t => existT _ 0 t
  | RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCReconfigurationComplete__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCReconfigurationComplete__criticalExtensions__list n)).
Definition RRCReconfigurationComplete__criticalExtensions__F2 (y : choice RRCReconfigurationComplete__criticalExtensions__list) : RRCReconfigurationComplete__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCReconfigurationComplete__criticalExtensions__g n -> RRCReconfigurationComplete__criticalExtensions__Type) with
    | 0 => fun (t : RRCReconfigurationComplete_IEs__Type) => RRCReconfigurationComplete__criticalExtensions__rrcReconfigurationComplete t 
    | 1 => fun (t : RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture__Type) => RRCReconfigurationComplete__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCReconfigurationComplete__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCReconfigurationComplete__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCReconfigurationComplete__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCReconfigurationComplete__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCReconfigurationComplete__criticalExtensions__helper2 :  forall (y : RRCReconfigurationComplete__criticalExtensions__Type), RRCReconfigurationComplete__criticalExtensions__cond y -> choice_cond RRCReconfigurationComplete__criticalExtensions__list (RRCReconfigurationComplete__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCReconfigurationComplete__criticalExtensions__helper3 :  forall (y : RRCReconfigurationComplete__criticalExtensions__Type), RRCReconfigurationComplete__criticalExtensions__F2 (RRCReconfigurationComplete__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCReconfigurationComplete__criticalExtensions__helper4 : (forall b : choice RRCReconfigurationComplete__criticalExtensions__list, choice_cond RRCReconfigurationComplete__criticalExtensions__list b -> RRCReconfigurationComplete__criticalExtensions__cond (RRCReconfigurationComplete__criticalExtensions__F2 b) /\ RRCReconfigurationComplete__criticalExtensions__F1 (RRCReconfigurationComplete__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCReconfigurationComplete__criticalExtensions__F1 RRCReconfigurationComplete__criticalExtensions__F2.
Definition RRCReconfigurationComplete__criticalExtensions__Format : T_Format RRCReconfigurationComplete__criticalExtensions__Type RRCReconfigurationComplete__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCReconfigurationComplete__criticalExtensions__cond RRCReconfigurationComplete__criticalExtensions__list__Format RRCReconfigurationComplete__criticalExtensions__F1 RRCReconfigurationComplete__criticalExtensions__F2 RRCReconfigurationComplete__criticalExtensions__helper2 RRCReconfigurationComplete__criticalExtensions__helper3 RRCReconfigurationComplete__criticalExtensions__helper4.
Opaque RRCReconfigurationComplete__criticalExtensions__cond RRCReconfigurationComplete__criticalExtensions__Format.


Definition RRCReconfigurationComplete__Format_Type := Eval cbn in seq_format_prod RRCReconfigurationComplete__list.
Definition RRCReconfigurationComplete__Format_list : RRCReconfigurationComplete__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCReconfigurationComplete__criticalExtensions__Format, unit_format)).
Definition RRCReconfigurationComplete__list__Format := (*Eval compute in *) seq_format RRCReconfigurationComplete__list RRCReconfigurationComplete__Format_list.
Definition RRCReconfigurationComplete__F1 z :=
  (RRCReconfigurationComplete__rrc_TransactionIdentifier z, (RRCReconfigurationComplete__criticalExtensions z, tt)).
Definition RRCReconfigurationComplete__F2 (y : seq_type RRCReconfigurationComplete__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCReconfigurationComplete__Type i0 i1
  end.
Lemma RRCReconfigurationComplete__F1F2_cond (z : RRCReconfigurationComplete__Type)
  : RRCReconfigurationComplete__cond z ->
  (seq_cond RRCReconfigurationComplete__list (RRCReconfigurationComplete__F1 z)).
intro H. unfold RRCReconfigurationComplete__cond in H. simpl. auto. Qed.
Lemma RRCReconfigurationComplete__F1F2_cond2 (z : RRCReconfigurationComplete__Type)
 : RRCReconfigurationComplete__F2 (RRCReconfigurationComplete__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfigurationComplete__F2F1_cond (y : seq_type RRCReconfigurationComplete__list)
  : seq_cond RRCReconfigurationComplete__list y ->
 (RRCReconfigurationComplete__cond (RRCReconfigurationComplete__F2 y)) /\  RRCReconfigurationComplete__F1 (RRCReconfigurationComplete__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfigurationComplete__cond. simpl in *. auto.
 - simpl. unfold RRCReconfigurationComplete__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfigurationComplete__Format : T_Format RRCReconfigurationComplete__Type RRCReconfigurationComplete__cond :=
        proj2_format  RRCReconfigurationComplete__cond RRCReconfigurationComplete__list__Format
    RRCReconfigurationComplete__F1 RRCReconfigurationComplete__F2 RRCReconfigurationComplete__F1F2_cond  RRCReconfigurationComplete__F1F2_cond2 RRCReconfigurationComplete__F2F1_cond.
Opaque RRCReconfigurationComplete__cond RRCReconfigurationComplete__Format.

