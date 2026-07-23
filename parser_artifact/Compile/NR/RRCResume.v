Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCResume_IEs.

Opaque RRCResume_IEs__cond RRCResume_IEs__Format.

Record RRCResume__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCResume__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCResume__criticalExtensions__criticalExtensionsFuture__cond (z : RRCResume__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCResume__criticalExtensions__Type : Set :=
  | RRCResume__criticalExtensions__rrcResume : RRCResume_IEs__Type -> RRCResume__criticalExtensions__Type
  | RRCResume__criticalExtensions__criticalExtensionsFuture : RRCResume__criticalExtensions__criticalExtensionsFuture__Type -> RRCResume__criticalExtensions__Type
.
Definition RRCResume__criticalExtensions__list : list typ := (
typ_cons RRCResume_IEs__Type RRCResume_IEs__cond ::
typ_cons RRCResume__criticalExtensions__criticalExtensionsFuture__Type RRCResume__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCResume__criticalExtensions__cond (c : RRCResume__criticalExtensions__Type) := 
  match c with
  | RRCResume__criticalExtensions__rrcResume t => RRCResume_IEs__cond t 
  | RRCResume__criticalExtensions__criticalExtensionsFuture t => RRCResume__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCResume__criticalExtensions__len_helper1 : to_bit_sz (length RRCResume__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCResume__criticalExtensions__len_helper2 : 2 <= length2 RRCResume__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCResume__Type : Set :=
  make__RRCResume__Type {
    RRCResume__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    RRCResume__criticalExtensions : RRCResume__criticalExtensions__Type ;
}.
Definition RRCResume__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCResume__criticalExtensions__Type RRCResume__criticalExtensions__cond ::
 nil).
Definition RRCResume__cond z := 
  RRC_TransactionIdentifier__cond (RRCResume__rrc_TransactionIdentifier z) /\
  RRCResume__criticalExtensions__cond (RRCResume__criticalExtensions z) /\
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
Definition RRCResume__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCResume__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCResume__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCResume__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCResume__criticalExtensions__criticalExtensionsFuture__Type RRCResume__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCResume__criticalExtensions__criticalExtensionsFuture__Type)
    RRCResume__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCResume__criticalExtensions__criticalExtensionsFuture__cond RRCResume__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCResume__criticalExtensions__Format_Type := Eval cbn in get_formats RRCResume__criticalExtensions__list.
Definition RRCResume__criticalExtensions__Format_list : RRCResume__criticalExtensions__Format_Type :=
  (RRCResume_IEs__Format, (RRCResume__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCResume__criticalExtensions__list__Format := Eval compute in choice_format RRCResume__criticalExtensions__list RRCResume__criticalExtensions__len_helper1 RRCResume__criticalExtensions__len_helper2  RRCResume__criticalExtensions__Format_list.
Definition RRCResume__criticalExtensions__F1 (z : RRCResume__criticalExtensions__Type) : (choice RRCResume__criticalExtensions__list) :=
  match z with
   | RRCResume__criticalExtensions__rrcResume t => existT _ 0 t
  | RRCResume__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCResume__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCResume__criticalExtensions__list n)).
Definition RRCResume__criticalExtensions__F2 (y : choice RRCResume__criticalExtensions__list) : RRCResume__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCResume__criticalExtensions__g n -> RRCResume__criticalExtensions__Type) with
    | 0 => fun (t : RRCResume_IEs__Type) => RRCResume__criticalExtensions__rrcResume t 
    | 1 => fun (t : RRCResume__criticalExtensions__criticalExtensionsFuture__Type) => RRCResume__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCResume__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCResume__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCResume__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCResume__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCResume__criticalExtensions__helper2 :  forall (y : RRCResume__criticalExtensions__Type), RRCResume__criticalExtensions__cond y -> choice_cond RRCResume__criticalExtensions__list (RRCResume__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCResume__criticalExtensions__helper3 :  forall (y : RRCResume__criticalExtensions__Type), RRCResume__criticalExtensions__F2 (RRCResume__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCResume__criticalExtensions__helper4 : (forall b : choice RRCResume__criticalExtensions__list, choice_cond RRCResume__criticalExtensions__list b -> RRCResume__criticalExtensions__cond (RRCResume__criticalExtensions__F2 b) /\ RRCResume__criticalExtensions__F1 (RRCResume__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCResume__criticalExtensions__F1 RRCResume__criticalExtensions__F2.
Definition RRCResume__criticalExtensions__Format : T_Format RRCResume__criticalExtensions__Type RRCResume__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCResume__criticalExtensions__cond RRCResume__criticalExtensions__list__Format RRCResume__criticalExtensions__F1 RRCResume__criticalExtensions__F2 RRCResume__criticalExtensions__helper2 RRCResume__criticalExtensions__helper3 RRCResume__criticalExtensions__helper4.
Opaque RRCResume__criticalExtensions__cond RRCResume__criticalExtensions__Format.


Definition RRCResume__Format_Type := Eval cbn in seq_format_prod RRCResume__list.
Definition RRCResume__Format_list : RRCResume__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCResume__criticalExtensions__Format, unit_format)).
Definition RRCResume__list__Format := (*Eval compute in *) seq_format RRCResume__list RRCResume__Format_list.
Definition RRCResume__F1 z :=
  (RRCResume__rrc_TransactionIdentifier z, (RRCResume__criticalExtensions z, tt)).
Definition RRCResume__F2 (y : seq_type RRCResume__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCResume__Type i0 i1
  end.
Lemma RRCResume__F1F2_cond (z : RRCResume__Type)
  : RRCResume__cond z ->
  (seq_cond RRCResume__list (RRCResume__F1 z)).
intro H. unfold RRCResume__cond in H. simpl. auto. Qed.
Lemma RRCResume__F1F2_cond2 (z : RRCResume__Type)
 : RRCResume__F2 (RRCResume__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCResume__F2F1_cond (y : seq_type RRCResume__list)
  : seq_cond RRCResume__list y ->
 (RRCResume__cond (RRCResume__F2 y)) /\  RRCResume__F1 (RRCResume__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCResume__cond. simpl in *. auto.
 - simpl. unfold RRCResume__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCResume__Format : T_Format RRCResume__Type RRCResume__cond :=
        proj2_format  RRCResume__cond RRCResume__list__Format
    RRCResume__F1 RRCResume__F2 RRCResume__F1F2_cond  RRCResume__F1F2_cond2 RRCResume__F2F1_cond.
Opaque RRCResume__cond RRCResume__Format.

