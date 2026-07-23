Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.RRCSetupComplete_IEs.

Opaque RRCSetupComplete_IEs__cond RRCSetupComplete_IEs__Format.

Record RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type : Set := make__RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__cond (z : RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive RRCSetupComplete__criticalExtensions__Type : Set :=
  | RRCSetupComplete__criticalExtensions__rrcSetupComplete : RRCSetupComplete_IEs__Type -> RRCSetupComplete__criticalExtensions__Type
  | RRCSetupComplete__criticalExtensions__criticalExtensionsFuture : RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type -> RRCSetupComplete__criticalExtensions__Type
.
Definition RRCSetupComplete__criticalExtensions__list : list typ := (
typ_cons RRCSetupComplete_IEs__Type RRCSetupComplete_IEs__cond ::
typ_cons RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition RRCSetupComplete__criticalExtensions__cond (c : RRCSetupComplete__criticalExtensions__Type) := 
  match c with
  | RRCSetupComplete__criticalExtensions__rrcSetupComplete t => RRCSetupComplete_IEs__cond t 
  | RRCSetupComplete__criticalExtensions__criticalExtensionsFuture t => RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma RRCSetupComplete__criticalExtensions__len_helper1 : to_bit_sz (length RRCSetupComplete__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RRCSetupComplete__criticalExtensions__len_helper2 : 2 <= length2 RRCSetupComplete__criticalExtensions__list.
 simpl. lia. Qed.
Record RRCSetupComplete__Type : Set :=
  make__RRCSetupComplete__Type {
    RRCSetupComplete__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    RRCSetupComplete__criticalExtensions : RRCSetupComplete__criticalExtensions__Type ;
}.
Definition RRCSetupComplete__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor RRCSetupComplete__criticalExtensions__Type RRCSetupComplete__criticalExtensions__cond ::
 nil).
Definition RRCSetupComplete__cond z := 
  RRC_TransactionIdentifier__cond (RRCSetupComplete__rrc_TransactionIdentifier z) /\
  RRCSetupComplete__criticalExtensions__cond (RRCSetupComplete__criticalExtensions z) /\
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
Definition RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__helper : forall a : RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Format : T_Format RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type)
    RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__cond RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Format.


Definition RRCSetupComplete__criticalExtensions__Format_Type := Eval cbn in get_formats RRCSetupComplete__criticalExtensions__list.
Definition RRCSetupComplete__criticalExtensions__Format_list : RRCSetupComplete__criticalExtensions__Format_Type :=
  (RRCSetupComplete_IEs__Format, (RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition RRCSetupComplete__criticalExtensions__list__Format := Eval compute in choice_format RRCSetupComplete__criticalExtensions__list RRCSetupComplete__criticalExtensions__len_helper1 RRCSetupComplete__criticalExtensions__len_helper2  RRCSetupComplete__criticalExtensions__Format_list.
Definition RRCSetupComplete__criticalExtensions__F1 (z : RRCSetupComplete__criticalExtensions__Type) : (choice RRCSetupComplete__criticalExtensions__list) :=
  match z with
   | RRCSetupComplete__criticalExtensions__rrcSetupComplete t => existT _ 0 t
  | RRCSetupComplete__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition RRCSetupComplete__criticalExtensions__g := (fun n => typ_set (get_nth_typ RRCSetupComplete__criticalExtensions__list n)).
Definition RRCSetupComplete__criticalExtensions__F2 (y : choice RRCSetupComplete__criticalExtensions__list) : RRCSetupComplete__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RRCSetupComplete__criticalExtensions__g n -> RRCSetupComplete__criticalExtensions__Type) with
    | 0 => fun (t : RRCSetupComplete_IEs__Type) => RRCSetupComplete__criticalExtensions__rrcSetupComplete t 
    | 1 => fun (t : RRCSetupComplete__criticalExtensions__criticalExtensionsFuture__Type) => RRCSetupComplete__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RRCSetupComplete__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RRCSetupComplete__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RRCSetupComplete__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RRCSetupComplete__criticalExtensions__Type with end) n0
           end t0).

Lemma RRCSetupComplete__criticalExtensions__helper2 :  forall (y : RRCSetupComplete__criticalExtensions__Type), RRCSetupComplete__criticalExtensions__cond y -> choice_cond RRCSetupComplete__criticalExtensions__list (RRCSetupComplete__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RRCSetupComplete__criticalExtensions__helper3 :  forall (y : RRCSetupComplete__criticalExtensions__Type), RRCSetupComplete__criticalExtensions__F2 (RRCSetupComplete__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RRCSetupComplete__criticalExtensions__helper4 : (forall b : choice RRCSetupComplete__criticalExtensions__list, choice_cond RRCSetupComplete__criticalExtensions__list b -> RRCSetupComplete__criticalExtensions__cond (RRCSetupComplete__criticalExtensions__F2 b) /\ RRCSetupComplete__criticalExtensions__F1 (RRCSetupComplete__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RRCSetupComplete__criticalExtensions__F1 RRCSetupComplete__criticalExtensions__F2.
Definition RRCSetupComplete__criticalExtensions__Format : T_Format RRCSetupComplete__criticalExtensions__Type RRCSetupComplete__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format RRCSetupComplete__criticalExtensions__cond RRCSetupComplete__criticalExtensions__list__Format RRCSetupComplete__criticalExtensions__F1 RRCSetupComplete__criticalExtensions__F2 RRCSetupComplete__criticalExtensions__helper2 RRCSetupComplete__criticalExtensions__helper3 RRCSetupComplete__criticalExtensions__helper4.
Opaque RRCSetupComplete__criticalExtensions__cond RRCSetupComplete__criticalExtensions__Format.


Definition RRCSetupComplete__Format_Type := Eval cbn in seq_format_prod RRCSetupComplete__list.
Definition RRCSetupComplete__Format_list : RRCSetupComplete__Format_Type :=
  (RRC_TransactionIdentifier__Format, (RRCSetupComplete__criticalExtensions__Format, unit_format)).
Definition RRCSetupComplete__list__Format := (*Eval compute in *) seq_format RRCSetupComplete__list RRCSetupComplete__Format_list.
Definition RRCSetupComplete__F1 z :=
  (RRCSetupComplete__rrc_TransactionIdentifier z, (RRCSetupComplete__criticalExtensions z, tt)).
Definition RRCSetupComplete__F2 (y : seq_type RRCSetupComplete__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RRCSetupComplete__Type i0 i1
  end.
Lemma RRCSetupComplete__F1F2_cond (z : RRCSetupComplete__Type)
  : RRCSetupComplete__cond z ->
  (seq_cond RRCSetupComplete__list (RRCSetupComplete__F1 z)).
intro H. unfold RRCSetupComplete__cond in H. simpl. auto. Qed.
Lemma RRCSetupComplete__F1F2_cond2 (z : RRCSetupComplete__Type)
 : RRCSetupComplete__F2 (RRCSetupComplete__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCSetupComplete__F2F1_cond (y : seq_type RRCSetupComplete__list)
  : seq_cond RRCSetupComplete__list y ->
 (RRCSetupComplete__cond (RRCSetupComplete__F2 y)) /\  RRCSetupComplete__F1 (RRCSetupComplete__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCSetupComplete__cond. simpl in *. auto.
 - simpl. unfold RRCSetupComplete__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCSetupComplete__Format : T_Format RRCSetupComplete__Type RRCSetupComplete__cond :=
        proj2_format  RRCSetupComplete__cond RRCSetupComplete__list__Format
    RRCSetupComplete__F1 RRCSetupComplete__F2 RRCSetupComplete__F1F2_cond  RRCSetupComplete__F1F2_cond2 RRCSetupComplete__F2F1_cond.
Opaque RRCSetupComplete__cond RRCSetupComplete__Format.

