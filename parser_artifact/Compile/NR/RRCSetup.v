Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCSetup_IEs.

Opaque RRCSetup_IEs__cond RRCSetup_IEs__Format.

Record RRCSetup__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCSetup__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCSetup__criticalExtensions__criticalExtensionsFuture__cond (z : RRCSetup__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCSetup__criticalExtensions__Type : Set :=
  | RRCSetup__criticalExtensions__rrcSetup : RRCSetup_IEs__Type -> RRCSetup__criticalExtensions__Type
  | RRCSetup__criticalExtensions__criticalExtensionsFuture : RRCSetup__criticalExtensions__criticalExtensionsFuture__Type -> RRCSetup__criticalExtensions__Type
.
Definition RRCSetup__criticalExtensions__list : list typ := (
typ_cons RRCSetup_IEs__Type RRCSetup_IEs__cond ::
typ_cons RRCSetup__criticalExtensions__criticalExtensionsFuture__Type RRCSetup__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCSetup__criticalExtensions__cond (c : RRCSetup__criticalExtensions__Type) := 
  match c with
  | RRCSetup__criticalExtensions__rrcSetup t => RRCSetup_IEs__cond t 
  | RRCSetup__criticalExtensions__criticalExtensionsFuture t => RRCSetup__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCSetup__criticalExtensions__len_helper1 : to_bit_sz (length RRCSetup__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCSetup__criticalExtensions__len_helper2 : 2 <= length2 RRCSetup__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCSetup__Type : Set :=
  make__RRCSetup__Type {
    RRCSetup__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    RRCSetup__criticalExtensions : RRCSetup__criticalExtensions__Type ;
}.
Definition RRCSetup__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCSetup__criticalExtensions__Type RRCSetup__criticalExtensions__cond ::
 nil).
Definition RRCSetup__cond z := 
  RRC_TransactionIdentifier__cond (RRCSetup__rrc_TransactionIdentifier z) /\
  RRCSetup__criticalExtensions__cond (RRCSetup__criticalExtensions z) /\
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
Definition RRCSetup__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCSetup__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCSetup__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCSetup__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCSetup__criticalExtensions__criticalExtensionsFuture__Type RRCSetup__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCSetup__criticalExtensions__criticalExtensionsFuture__Type)
    RRCSetup__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCSetup__criticalExtensions__criticalExtensionsFuture__cond RRCSetup__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCSetup__criticalExtensions__Format_Type := Eval cbn in get_formats RRCSetup__criticalExtensions__list.
Definition RRCSetup__criticalExtensions__Format_list : RRCSetup__criticalExtensions__Format_Type :=
  (RRCSetup_IEs__Format, (RRCSetup__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCSetup__criticalExtensions__list__Format := Eval compute in choice_format RRCSetup__criticalExtensions__list RRCSetup__criticalExtensions__len_helper1 RRCSetup__criticalExtensions__len_helper2  RRCSetup__criticalExtensions__Format_list.
Definition RRCSetup__criticalExtensions__F1 (z : RRCSetup__criticalExtensions__Type) : (choice RRCSetup__criticalExtensions__list) :=
  match z with
   | RRCSetup__criticalExtensions__rrcSetup t => existT _ 0 t
  | RRCSetup__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCSetup__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCSetup__criticalExtensions__list n)).
Definition RRCSetup__criticalExtensions__F2 (y : choice RRCSetup__criticalExtensions__list) : RRCSetup__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCSetup__criticalExtensions__g n -> RRCSetup__criticalExtensions__Type) with
    | 0 => fun (t : RRCSetup_IEs__Type) => RRCSetup__criticalExtensions__rrcSetup t 
    | 1 => fun (t : RRCSetup__criticalExtensions__criticalExtensionsFuture__Type) => RRCSetup__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCSetup__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCSetup__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCSetup__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCSetup__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCSetup__criticalExtensions__helper2 :  forall (y : RRCSetup__criticalExtensions__Type), RRCSetup__criticalExtensions__cond y -> choice_cond RRCSetup__criticalExtensions__list (RRCSetup__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCSetup__criticalExtensions__helper3 :  forall (y : RRCSetup__criticalExtensions__Type), RRCSetup__criticalExtensions__F2 (RRCSetup__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCSetup__criticalExtensions__helper4 : (forall b : choice RRCSetup__criticalExtensions__list, choice_cond RRCSetup__criticalExtensions__list b -> RRCSetup__criticalExtensions__cond (RRCSetup__criticalExtensions__F2 b) /\ RRCSetup__criticalExtensions__F1 (RRCSetup__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCSetup__criticalExtensions__F1 RRCSetup__criticalExtensions__F2.
Definition RRCSetup__criticalExtensions__Format : T_Format RRCSetup__criticalExtensions__Type RRCSetup__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCSetup__criticalExtensions__cond RRCSetup__criticalExtensions__list__Format RRCSetup__criticalExtensions__F1 RRCSetup__criticalExtensions__F2 RRCSetup__criticalExtensions__helper2 RRCSetup__criticalExtensions__helper3 RRCSetup__criticalExtensions__helper4.
Opaque RRCSetup__criticalExtensions__cond RRCSetup__criticalExtensions__Format.


Definition RRCSetup__Format_Type := Eval cbn in seq_format_prod RRCSetup__list.
Definition RRCSetup__Format_list : RRCSetup__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCSetup__criticalExtensions__Format, unit_format)).
Definition RRCSetup__list__Format := (*Eval compute in *) seq_format RRCSetup__list RRCSetup__Format_list.
Definition RRCSetup__F1 z :=
  (RRCSetup__rrc_TransactionIdentifier z, (RRCSetup__criticalExtensions z, tt)).
Definition RRCSetup__F2 (y : seq_type RRCSetup__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCSetup__Type i0 i1
  end.
Lemma RRCSetup__F1F2_cond (z : RRCSetup__Type)
  : RRCSetup__cond z ->
  (seq_cond RRCSetup__list (RRCSetup__F1 z)).
intro H. unfold RRCSetup__cond in H. simpl. auto. Qed.
Lemma RRCSetup__F1F2_cond2 (z : RRCSetup__Type)
 : RRCSetup__F2 (RRCSetup__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCSetup__F2F1_cond (y : seq_type RRCSetup__list)
  : seq_cond RRCSetup__list y ->
 (RRCSetup__cond (RRCSetup__F2 y)) /\  RRCSetup__F1 (RRCSetup__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCSetup__cond. simpl in *. auto.
 - simpl. unfold RRCSetup__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCSetup__Format : T_Format RRCSetup__Type RRCSetup__cond :=
        proj2_format  RRCSetup__cond RRCSetup__list__Format
    RRCSetup__F1 RRCSetup__F2 RRCSetup__F1F2_cond  RRCSetup__F1F2_cond2 RRCSetup__F2F1_cond.
Opaque RRCSetup__cond RRCSetup__Format.

