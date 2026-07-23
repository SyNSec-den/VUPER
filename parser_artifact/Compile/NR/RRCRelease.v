Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCRelease_IEs.

Opaque RRCRelease_IEs__cond RRCRelease_IEs__Format.

Record RRCRelease__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCRelease__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCRelease__criticalExtensions__criticalExtensionsFuture__cond (z : RRCRelease__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCRelease__criticalExtensions__Type : Set :=
  | RRCRelease__criticalExtensions__rrcRelease : RRCRelease_IEs__Type -> RRCRelease__criticalExtensions__Type
  | RRCRelease__criticalExtensions__criticalExtensionsFuture : RRCRelease__criticalExtensions__criticalExtensionsFuture__Type -> RRCRelease__criticalExtensions__Type
.
Definition RRCRelease__criticalExtensions__list : list typ := (
typ_cons RRCRelease_IEs__Type RRCRelease_IEs__cond ::
typ_cons RRCRelease__criticalExtensions__criticalExtensionsFuture__Type RRCRelease__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCRelease__criticalExtensions__cond (c : RRCRelease__criticalExtensions__Type) := 
  match c with
  | RRCRelease__criticalExtensions__rrcRelease t => RRCRelease_IEs__cond t 
  | RRCRelease__criticalExtensions__criticalExtensionsFuture t => RRCRelease__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCRelease__criticalExtensions__len_helper1 : to_bit_sz (length RRCRelease__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCRelease__criticalExtensions__len_helper2 : 2 <= length2 RRCRelease__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCRelease__Type : Set :=
  make__RRCRelease__Type {
    RRCRelease__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    RRCRelease__criticalExtensions : RRCRelease__criticalExtensions__Type ;
}.
Definition RRCRelease__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCRelease__criticalExtensions__Type RRCRelease__criticalExtensions__cond ::
 nil).
Definition RRCRelease__cond z := 
  RRC_TransactionIdentifier__cond (RRCRelease__rrc_TransactionIdentifier z) /\
  RRCRelease__criticalExtensions__cond (RRCRelease__criticalExtensions z) /\
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
Definition RRCRelease__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCRelease__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCRelease__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCRelease__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCRelease__criticalExtensions__criticalExtensionsFuture__Type RRCRelease__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCRelease__criticalExtensions__criticalExtensionsFuture__Type)
    RRCRelease__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCRelease__criticalExtensions__criticalExtensionsFuture__cond RRCRelease__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCRelease__criticalExtensions__Format_Type := Eval cbn in get_formats RRCRelease__criticalExtensions__list.
Definition RRCRelease__criticalExtensions__Format_list : RRCRelease__criticalExtensions__Format_Type :=
  (RRCRelease_IEs__Format, (RRCRelease__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCRelease__criticalExtensions__list__Format := Eval compute in choice_format RRCRelease__criticalExtensions__list RRCRelease__criticalExtensions__len_helper1 RRCRelease__criticalExtensions__len_helper2  RRCRelease__criticalExtensions__Format_list.
Definition RRCRelease__criticalExtensions__F1 (z : RRCRelease__criticalExtensions__Type) : (choice RRCRelease__criticalExtensions__list) :=
  match z with
   | RRCRelease__criticalExtensions__rrcRelease t => existT _ 0 t
  | RRCRelease__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCRelease__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCRelease__criticalExtensions__list n)).
Definition RRCRelease__criticalExtensions__F2 (y : choice RRCRelease__criticalExtensions__list) : RRCRelease__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCRelease__criticalExtensions__g n -> RRCRelease__criticalExtensions__Type) with
    | 0 => fun (t : RRCRelease_IEs__Type) => RRCRelease__criticalExtensions__rrcRelease t 
    | 1 => fun (t : RRCRelease__criticalExtensions__criticalExtensionsFuture__Type) => RRCRelease__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCRelease__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCRelease__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCRelease__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCRelease__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCRelease__criticalExtensions__helper2 :  forall (y : RRCRelease__criticalExtensions__Type), RRCRelease__criticalExtensions__cond y -> choice_cond RRCRelease__criticalExtensions__list (RRCRelease__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCRelease__criticalExtensions__helper3 :  forall (y : RRCRelease__criticalExtensions__Type), RRCRelease__criticalExtensions__F2 (RRCRelease__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCRelease__criticalExtensions__helper4 : (forall b : choice RRCRelease__criticalExtensions__list, choice_cond RRCRelease__criticalExtensions__list b -> RRCRelease__criticalExtensions__cond (RRCRelease__criticalExtensions__F2 b) /\ RRCRelease__criticalExtensions__F1 (RRCRelease__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCRelease__criticalExtensions__F1 RRCRelease__criticalExtensions__F2.
Definition RRCRelease__criticalExtensions__Format : T_Format RRCRelease__criticalExtensions__Type RRCRelease__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCRelease__criticalExtensions__cond RRCRelease__criticalExtensions__list__Format RRCRelease__criticalExtensions__F1 RRCRelease__criticalExtensions__F2 RRCRelease__criticalExtensions__helper2 RRCRelease__criticalExtensions__helper3 RRCRelease__criticalExtensions__helper4.
Opaque RRCRelease__criticalExtensions__cond RRCRelease__criticalExtensions__Format.


Definition RRCRelease__Format_Type := Eval cbn in seq_format_prod RRCRelease__list.
Definition RRCRelease__Format_list : RRCRelease__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCRelease__criticalExtensions__Format, unit_format)).
Definition RRCRelease__list__Format := (*Eval compute in *) seq_format RRCRelease__list RRCRelease__Format_list.
Definition RRCRelease__F1 z :=
  (RRCRelease__rrc_TransactionIdentifier z, (RRCRelease__criticalExtensions z, tt)).
Definition RRCRelease__F2 (y : seq_type RRCRelease__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCRelease__Type i0 i1
  end.
Lemma RRCRelease__F1F2_cond (z : RRCRelease__Type)
  : RRCRelease__cond z ->
  (seq_cond RRCRelease__list (RRCRelease__F1 z)).
intro H. unfold RRCRelease__cond in H. simpl. auto. Qed.
Lemma RRCRelease__F1F2_cond2 (z : RRCRelease__Type)
 : RRCRelease__F2 (RRCRelease__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCRelease__F2F1_cond (y : seq_type RRCRelease__list)
  : seq_cond RRCRelease__list y ->
 (RRCRelease__cond (RRCRelease__F2 y)) /\  RRCRelease__F1 (RRCRelease__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCRelease__cond. simpl in *. auto.
 - simpl. unfold RRCRelease__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCRelease__Format : T_Format RRCRelease__Type RRCRelease__cond :=
        proj2_format  RRCRelease__cond RRCRelease__list__Format
    RRCRelease__F1 RRCRelease__F2 RRCRelease__F1F2_cond  RRCRelease__F1F2_cond2 RRCRelease__F2F1_cond.
Opaque RRCRelease__cond RRCRelease__Format.

