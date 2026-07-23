Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCReconfiguration_IEs.

Opaque RRCReconfiguration_IEs__cond RRCReconfiguration_IEs__Format.

Record RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__cond (z : RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCReconfiguration__criticalExtensions__Type : Set :=
  | RRCReconfiguration__criticalExtensions__rrcReconfiguration : RRCReconfiguration_IEs__Type -> RRCReconfiguration__criticalExtensions__Type
  | RRCReconfiguration__criticalExtensions__criticalExtensionsFuture : RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type -> RRCReconfiguration__criticalExtensions__Type
.
Definition RRCReconfiguration__criticalExtensions__list : list typ := (
typ_cons RRCReconfiguration_IEs__Type RRCReconfiguration_IEs__cond ::
typ_cons RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCReconfiguration__criticalExtensions__cond (c : RRCReconfiguration__criticalExtensions__Type) := 
  match c with
  | RRCReconfiguration__criticalExtensions__rrcReconfiguration t => RRCReconfiguration_IEs__cond t 
  | RRCReconfiguration__criticalExtensions__criticalExtensionsFuture t => RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCReconfiguration__criticalExtensions__len_helper1 : to_bit_sz (length RRCReconfiguration__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCReconfiguration__criticalExtensions__len_helper2 : 2 <= length2 RRCReconfiguration__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCReconfiguration__Type : Set :=
  make__RRCReconfiguration__Type {
    RRCReconfiguration__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    RRCReconfiguration__criticalExtensions : RRCReconfiguration__criticalExtensions__Type ;
}.
Definition RRCReconfiguration__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCReconfiguration__criticalExtensions__Type RRCReconfiguration__criticalExtensions__cond ::
 nil).
Definition RRCReconfiguration__cond z := 
  RRC_TransactionIdentifier__cond (RRCReconfiguration__rrc_TransactionIdentifier z) /\
  RRCReconfiguration__criticalExtensions__cond (RRCReconfiguration__criticalExtensions z) /\
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
Definition RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type)
    RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__cond RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCReconfiguration__criticalExtensions__Format_Type := Eval cbn in get_formats RRCReconfiguration__criticalExtensions__list.
Definition RRCReconfiguration__criticalExtensions__Format_list : RRCReconfiguration__criticalExtensions__Format_Type :=
  (RRCReconfiguration_IEs__Format, (RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCReconfiguration__criticalExtensions__list__Format := Eval compute in choice_format RRCReconfiguration__criticalExtensions__list RRCReconfiguration__criticalExtensions__len_helper1 RRCReconfiguration__criticalExtensions__len_helper2  RRCReconfiguration__criticalExtensions__Format_list.
Definition RRCReconfiguration__criticalExtensions__F1 (z : RRCReconfiguration__criticalExtensions__Type) : (choice RRCReconfiguration__criticalExtensions__list) :=
  match z with
   | RRCReconfiguration__criticalExtensions__rrcReconfiguration t => existT _ 0 t
  | RRCReconfiguration__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCReconfiguration__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCReconfiguration__criticalExtensions__list n)).
Definition RRCReconfiguration__criticalExtensions__F2 (y : choice RRCReconfiguration__criticalExtensions__list) : RRCReconfiguration__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCReconfiguration__criticalExtensions__g n -> RRCReconfiguration__criticalExtensions__Type) with
    | 0 => fun (t : RRCReconfiguration_IEs__Type) => RRCReconfiguration__criticalExtensions__rrcReconfiguration t 
    | 1 => fun (t : RRCReconfiguration__criticalExtensions__criticalExtensionsFuture__Type) => RRCReconfiguration__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCReconfiguration__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCReconfiguration__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCReconfiguration__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCReconfiguration__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCReconfiguration__criticalExtensions__helper2 :  forall (y : RRCReconfiguration__criticalExtensions__Type), RRCReconfiguration__criticalExtensions__cond y -> choice_cond RRCReconfiguration__criticalExtensions__list (RRCReconfiguration__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCReconfiguration__criticalExtensions__helper3 :  forall (y : RRCReconfiguration__criticalExtensions__Type), RRCReconfiguration__criticalExtensions__F2 (RRCReconfiguration__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCReconfiguration__criticalExtensions__helper4 : (forall b : choice RRCReconfiguration__criticalExtensions__list, choice_cond RRCReconfiguration__criticalExtensions__list b -> RRCReconfiguration__criticalExtensions__cond (RRCReconfiguration__criticalExtensions__F2 b) /\ RRCReconfiguration__criticalExtensions__F1 (RRCReconfiguration__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCReconfiguration__criticalExtensions__F1 RRCReconfiguration__criticalExtensions__F2.
Definition RRCReconfiguration__criticalExtensions__Format : T_Format RRCReconfiguration__criticalExtensions__Type RRCReconfiguration__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCReconfiguration__criticalExtensions__cond RRCReconfiguration__criticalExtensions__list__Format RRCReconfiguration__criticalExtensions__F1 RRCReconfiguration__criticalExtensions__F2 RRCReconfiguration__criticalExtensions__helper2 RRCReconfiguration__criticalExtensions__helper3 RRCReconfiguration__criticalExtensions__helper4.
Opaque RRCReconfiguration__criticalExtensions__cond RRCReconfiguration__criticalExtensions__Format.


Definition RRCReconfiguration__Format_Type := Eval cbn in seq_format_prod RRCReconfiguration__list.
Definition RRCReconfiguration__Format_list : RRCReconfiguration__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCReconfiguration__criticalExtensions__Format, unit_format)).
Definition RRCReconfiguration__list__Format := (*Eval compute in *) seq_format RRCReconfiguration__list RRCReconfiguration__Format_list.
Definition RRCReconfiguration__F1 z :=
  (RRCReconfiguration__rrc_TransactionIdentifier z, (RRCReconfiguration__criticalExtensions z, tt)).
Definition RRCReconfiguration__F2 (y : seq_type RRCReconfiguration__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCReconfiguration__Type i0 i1
  end.
Lemma RRCReconfiguration__F1F2_cond (z : RRCReconfiguration__Type)
  : RRCReconfiguration__cond z ->
  (seq_cond RRCReconfiguration__list (RRCReconfiguration__F1 z)).
intro H. unfold RRCReconfiguration__cond in H. simpl. auto. Qed.
Lemma RRCReconfiguration__F1F2_cond2 (z : RRCReconfiguration__Type)
 : RRCReconfiguration__F2 (RRCReconfiguration__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCReconfiguration__F2F1_cond (y : seq_type RRCReconfiguration__list)
  : seq_cond RRCReconfiguration__list y ->
 (RRCReconfiguration__cond (RRCReconfiguration__F2 y)) /\  RRCReconfiguration__F1 (RRCReconfiguration__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCReconfiguration__cond. simpl in *. auto.
 - simpl. unfold RRCReconfiguration__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCReconfiguration__Format : T_Format RRCReconfiguration__Type RRCReconfiguration__cond :=
        proj2_format  RRCReconfiguration__cond RRCReconfiguration__list__Format
    RRCReconfiguration__F1 RRCReconfiguration__F2 RRCReconfiguration__F1F2_cond  RRCReconfiguration__F1F2_cond2 RRCReconfiguration__F2F1_cond.
Opaque RRCReconfiguration__cond RRCReconfiguration__Format.

