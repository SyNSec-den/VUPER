Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SCGFailureInformation_IEs.

Opaque SCGFailureInformation_IEs__cond SCGFailureInformation_IEs__Format.

Record SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type : Set := make__SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__cond (z : SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive SCGFailureInformation__criticalExtensions__Type : Set :=
  | SCGFailureInformation__criticalExtensions__scgFailureInformation : SCGFailureInformation_IEs__Type -> SCGFailureInformation__criticalExtensions__Type
  | SCGFailureInformation__criticalExtensions__criticalExtensionsFuture : SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type -> SCGFailureInformation__criticalExtensions__Type
.
Definition SCGFailureInformation__criticalExtensions__list : list typ := (
typ_cons SCGFailureInformation_IEs__Type SCGFailureInformation_IEs__cond ::
typ_cons SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition SCGFailureInformation__criticalExtensions__cond (c : SCGFailureInformation__criticalExtensions__Type) := 
  match c with
  | SCGFailureInformation__criticalExtensions__scgFailureInformation t => SCGFailureInformation_IEs__cond t 
  | SCGFailureInformation__criticalExtensions__criticalExtensionsFuture t => SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma SCGFailureInformation__criticalExtensions__len_helper1 : to_bit_sz (length SCGFailureInformation__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SCGFailureInformation__criticalExtensions__len_helper2 : 2 <= length2 SCGFailureInformation__criticalExtensions__list.
 simpl. lia. Qed.
Record SCGFailureInformation__Type : Set :=
  make__SCGFailureInformation__Type {
    SCGFailureInformation__criticalExtensions : SCGFailureInformation__criticalExtensions__Type ;
}.
Definition SCGFailureInformation__list := (
 Nor SCGFailureInformation__criticalExtensions__Type SCGFailureInformation__criticalExtensions__cond ::
 nil).
Definition SCGFailureInformation__cond z := 
  SCGFailureInformation__criticalExtensions__cond (SCGFailureInformation__criticalExtensions z) /\
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
Definition SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__helper : forall a : SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Format : T_Format SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type)
    SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__cond SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Format.


Definition SCGFailureInformation__criticalExtensions__Format_Type := Eval cbn in get_formats SCGFailureInformation__criticalExtensions__list.
Definition SCGFailureInformation__criticalExtensions__Format_list : SCGFailureInformation__criticalExtensions__Format_Type :=
  (SCGFailureInformation_IEs__Format, (SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition SCGFailureInformation__criticalExtensions__list__Format := Eval compute in choice_format SCGFailureInformation__criticalExtensions__list SCGFailureInformation__criticalExtensions__len_helper1 SCGFailureInformation__criticalExtensions__len_helper2  SCGFailureInformation__criticalExtensions__Format_list.
Definition SCGFailureInformation__criticalExtensions__F1 (z : SCGFailureInformation__criticalExtensions__Type) : (choice SCGFailureInformation__criticalExtensions__list) :=
  match z with
   | SCGFailureInformation__criticalExtensions__scgFailureInformation t => existT _ 0 t
  | SCGFailureInformation__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition SCGFailureInformation__criticalExtensions__g := (fun n => typ_set (get_nth_typ SCGFailureInformation__criticalExtensions__list n)).
Definition SCGFailureInformation__criticalExtensions__F2 (y : choice SCGFailureInformation__criticalExtensions__list) : SCGFailureInformation__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SCGFailureInformation__criticalExtensions__g n -> SCGFailureInformation__criticalExtensions__Type) with
    | 0 => fun (t : SCGFailureInformation_IEs__Type) => SCGFailureInformation__criticalExtensions__scgFailureInformation t 
    | 1 => fun (t : SCGFailureInformation__criticalExtensions__criticalExtensionsFuture__Type) => SCGFailureInformation__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SCGFailureInformation__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SCGFailureInformation__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SCGFailureInformation__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SCGFailureInformation__criticalExtensions__Type with end) n0
           end t0).

Lemma SCGFailureInformation__criticalExtensions__helper2 :  forall (y : SCGFailureInformation__criticalExtensions__Type), SCGFailureInformation__criticalExtensions__cond y -> choice_cond SCGFailureInformation__criticalExtensions__list (SCGFailureInformation__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SCGFailureInformation__criticalExtensions__helper3 :  forall (y : SCGFailureInformation__criticalExtensions__Type), SCGFailureInformation__criticalExtensions__F2 (SCGFailureInformation__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SCGFailureInformation__criticalExtensions__helper4 : (forall b : choice SCGFailureInformation__criticalExtensions__list, choice_cond SCGFailureInformation__criticalExtensions__list b -> SCGFailureInformation__criticalExtensions__cond (SCGFailureInformation__criticalExtensions__F2 b) /\ SCGFailureInformation__criticalExtensions__F1 (SCGFailureInformation__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SCGFailureInformation__criticalExtensions__F1 SCGFailureInformation__criticalExtensions__F2.
Definition SCGFailureInformation__criticalExtensions__Format : T_Format SCGFailureInformation__criticalExtensions__Type SCGFailureInformation__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format SCGFailureInformation__criticalExtensions__cond SCGFailureInformation__criticalExtensions__list__Format SCGFailureInformation__criticalExtensions__F1 SCGFailureInformation__criticalExtensions__F2 SCGFailureInformation__criticalExtensions__helper2 SCGFailureInformation__criticalExtensions__helper3 SCGFailureInformation__criticalExtensions__helper4.
Opaque SCGFailureInformation__criticalExtensions__cond SCGFailureInformation__criticalExtensions__Format.


Definition SCGFailureInformation__Format_Type := Eval cbn in seq_format_prod SCGFailureInformation__list.
Definition SCGFailureInformation__Format_list : SCGFailureInformation__Format_Type :=
  (SCGFailureInformation__criticalExtensions__Format, unit_format).
Definition SCGFailureInformation__list__Format := (*Eval compute in *) seq_format SCGFailureInformation__list SCGFailureInformation__Format_list.
Definition SCGFailureInformation__F1 z :=
  (SCGFailureInformation__criticalExtensions z, tt).
Definition SCGFailureInformation__F2 (y : seq_type SCGFailureInformation__list) :=
  match y with
  | (i0, _)=>
    make__SCGFailureInformation__Type i0
  end.
Lemma SCGFailureInformation__F1F2_cond (z : SCGFailureInformation__Type)
  : SCGFailureInformation__cond z ->
  (seq_cond SCGFailureInformation__list (SCGFailureInformation__F1 z)).
intro H. unfold SCGFailureInformation__cond in H. simpl. auto. Qed.
Lemma SCGFailureInformation__F1F2_cond2 (z : SCGFailureInformation__Type)
 : SCGFailureInformation__F2 (SCGFailureInformation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SCGFailureInformation__F2F1_cond (y : seq_type SCGFailureInformation__list)
  : seq_cond SCGFailureInformation__list y ->
 (SCGFailureInformation__cond (SCGFailureInformation__F2 y)) /\  SCGFailureInformation__F1 (SCGFailureInformation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SCGFailureInformation__cond. simpl in *. auto.
 - simpl. unfold SCGFailureInformation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SCGFailureInformation__Format : T_Format SCGFailureInformation__Type SCGFailureInformation__cond :=
        proj2_format  SCGFailureInformation__cond SCGFailureInformation__list__Format
    SCGFailureInformation__F1 SCGFailureInformation__F2 SCGFailureInformation__F1F2_cond  SCGFailureInformation__F1F2_cond2 SCGFailureInformation__F2F1_cond.
Opaque SCGFailureInformation__cond SCGFailureInformation__Format.

