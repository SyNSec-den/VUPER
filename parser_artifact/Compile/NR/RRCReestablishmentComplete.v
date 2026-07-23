Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCReestablishmentComplete_IEs.

Opaque RRCReestablishmentComplete_IEs__cond RRCReestablishmentComplete_IEs__Format.

Record RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__cond (z : RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCReestablishmentComplete__criticalExtensions__Type : Set :=
  | RRCReestablishmentComplete__criticalExtensions__rrcReestablishmentComplete : RRCReestablishmentComplete_IEs__Type -> RRCReestablishmentComplete__criticalExtensions__Type
  | RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture : RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type -> RRCReestablishmentComplete__criticalExtensions__Type
.
Definition RRCReestablishmentComplete__criticalExtensions__list : list typ := (
typ_cons RRCReestablishmentComplete_IEs__Type RRCReestablishmentComplete_IEs__cond ::
typ_cons RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCReestablishmentComplete__criticalExtensions__cond (c : RRCReestablishmentComplete__criticalExtensions__Type) := 
  match c with
  | RRCReestablishmentComplete__criticalExtensions__rrcReestablishmentComplete t => RRCReestablishmentComplete_IEs__cond t 
  | RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture t => RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCReestablishmentComplete__criticalExtensions__len_helper1 : to_bit_sz (length RRCReestablishmentComplete__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCReestablishmentComplete__criticalExtensions__len_helper2 : 2 <= length2 RRCReestablishmentComplete__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCReestablishmentComplete__Type : Set :=
  make__RRCReestablishmentComplete__Type {
    RRCReestablishmentComplete__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    RRCReestablishmentComplete__criticalExtensions : RRCReestablishmentComplete__criticalExtensions__Type ;
}.
Definition RRCReestablishmentComplete__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCReestablishmentComplete__criticalExtensions__Type RRCReestablishmentComplete__criticalExtensions__cond ::
 nil).
Definition RRCReestablishmentComplete__cond z := 
  RRC_TransactionIdentifier__cond (RRCReestablishmentComplete__rrc_TransactionIdentifier z) /\
  RRCReestablishmentComplete__criticalExtensions__cond (RRCReestablishmentComplete__criticalExtensions z) /\
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
Definition RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type)
    RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__cond RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCReestablishmentComplete__criticalExtensions__Format_Type := Eval cbn in get_formats RRCReestablishmentComplete__criticalExtensions__list.
Definition RRCReestablishmentComplete__criticalExtensions__Format_list : RRCReestablishmentComplete__criticalExtensions__Format_Type :=
  (RRCReestablishmentComplete_IEs__Format, (RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCReestablishmentComplete__criticalExtensions__list__Format := Eval compute in choice_format RRCReestablishmentComplete__criticalExtensions__list RRCReestablishmentComplete__criticalExtensions__len_helper1 RRCReestablishmentComplete__criticalExtensions__len_helper2  RRCReestablishmentComplete__criticalExtensions__Format_list.
Definition RRCReestablishmentComplete__criticalExtensions__F1 (z : RRCReestablishmentComplete__criticalExtensions__Type) : (choice RRCReestablishmentComplete__criticalExtensions__list) :=
  match z with
   | RRCReestablishmentComplete__criticalExtensions__rrcReestablishmentComplete t => existT _ 0 t
  | RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCReestablishmentComplete__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCReestablishmentComplete__criticalExtensions__list n)).
Definition RRCReestablishmentComplete__criticalExtensions__F2 (y : choice RRCReestablishmentComplete__criticalExtensions__list) : RRCReestablishmentComplete__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCReestablishmentComplete__criticalExtensions__g n -> RRCReestablishmentComplete__criticalExtensions__Type) with
    | 0 => fun (t : RRCReestablishmentComplete_IEs__Type) => RRCReestablishmentComplete__criticalExtensions__rrcReestablishmentComplete t 
    | 1 => fun (t : RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture__Type) => RRCReestablishmentComplete__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCReestablishmentComplete__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCReestablishmentComplete__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCReestablishmentComplete__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCReestablishmentComplete__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCReestablishmentComplete__criticalExtensions__helper2 :  forall (y : RRCReestablishmentComplete__criticalExtensions__Type), RRCReestablishmentComplete__criticalExtensions__cond y -> choice_cond RRCReestablishmentComplete__criticalExtensions__list (RRCReestablishmentComplete__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCReestablishmentComplete__criticalExtensions__helper3 :  forall (y : RRCReestablishmentComplete__criticalExtensions__Type), RRCReestablishmentComplete__criticalExtensions__F2 (RRCReestablishmentComplete__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCReestablishmentComplete__criticalExtensions__helper4 : (forall b : choice RRCReestablishmentComplete__criticalExtensions__list, choice_cond RRCReestablishmentComplete__criticalExtensions__list b -> RRCReestablishmentComplete__criticalExtensions__cond (RRCReestablishmentComplete__criticalExtensions__F2 b) /\ RRCReestablishmentComplete__criticalExtensions__F1 (RRCReestablishmentComplete__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCReestablishmentComplete__criticalExtensions__F1 RRCReestablishmentComplete__criticalExtensions__F2.
Definition RRCReestablishmentComplete__criticalExtensions__Format : T_Format RRCReestablishmentComplete__criticalExtensions__Type RRCReestablishmentComplete__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCReestablishmentComplete__criticalExtensions__cond RRCReestablishmentComplete__criticalExtensions__list__Format RRCReestablishmentComplete__criticalExtensions__F1 RRCReestablishmentComplete__criticalExtensions__F2 RRCReestablishmentComplete__criticalExtensions__helper2 RRCReestablishmentComplete__criticalExtensions__helper3 RRCReestablishmentComplete__criticalExtensions__helper4.
Opaque RRCReestablishmentComplete__criticalExtensions__cond RRCReestablishmentComplete__criticalExtensions__Format.


Definition RRCReestablishmentComplete__Format_Type := Eval cbn in seq_format_prod RRCReestablishmentComplete__list.
Definition RRCReestablishmentComplete__Format_list : RRCReestablishmentComplete__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCReestablishmentComplete__criticalExtensions__Format, unit_format)).
Definition RRCReestablishmentComplete__list__Format := (*Eval compute in *) seq_format RRCReestablishmentComplete__list RRCReestablishmentComplete__Format_list.
Definition RRCReestablishmentComplete__F1 z :=
  (RRCReestablishmentComplete__rrc_TransactionIdentifier z, (RRCReestablishmentComplete__criticalExtensions z, tt)).
Definition RRCReestablishmentComplete__F2 (y : seq_type RRCReestablishmentComplete__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCReestablishmentComplete__Type i0 i1
  end.
Lemma RRCReestablishmentComplete__F1F2_cond (z : RRCReestablishmentComplete__Type)
  : RRCReestablishmentComplete__cond z ->
  (seq_cond RRCReestablishmentComplete__list (RRCReestablishmentComplete__F1 z)).
intro H. unfold RRCReestablishmentComplete__cond in H. simpl. auto. Qed.
Lemma RRCReestablishmentComplete__F1F2_cond2 (z : RRCReestablishmentComplete__Type)
 : RRCReestablishmentComplete__F2 (RRCReestablishmentComplete__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReestablishmentComplete__F2F1_cond (y : seq_type RRCReestablishmentComplete__list)
  : seq_cond RRCReestablishmentComplete__list y ->
 (RRCReestablishmentComplete__cond (RRCReestablishmentComplete__F2 y)) /\  RRCReestablishmentComplete__F1 (RRCReestablishmentComplete__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReestablishmentComplete__cond. simpl in *. auto.
 - simpl. unfold RRCReestablishmentComplete__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReestablishmentComplete__Format : T_Format RRCReestablishmentComplete__Type RRCReestablishmentComplete__cond :=
        proj2_format  RRCReestablishmentComplete__cond RRCReestablishmentComplete__list__Format
    RRCReestablishmentComplete__F1 RRCReestablishmentComplete__F2 RRCReestablishmentComplete__F1F2_cond  RRCReestablishmentComplete__F1F2_cond2 RRCReestablishmentComplete__F2F1_cond.
Opaque RRCReestablishmentComplete__cond RRCReestablishmentComplete__Format.

