Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SCGFailureInformationEUTRA_IEs.

Opaque SCGFailureInformationEUTRA_IEs__cond SCGFailureInformationEUTRA_IEs__Format.

Record SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type : Set := make__SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__cond (z : SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive SCGFailureInformationEUTRA__criticalExtensions__Type : Set :=
  | SCGFailureInformationEUTRA__criticalExtensions__scgFailureInformationEUTRA : SCGFailureInformationEUTRA_IEs__Type -> SCGFailureInformationEUTRA__criticalExtensions__Type
  | SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture : SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type -> SCGFailureInformationEUTRA__criticalExtensions__Type
.
Definition SCGFailureInformationEUTRA__criticalExtensions__list : list typ := (
typ_cons SCGFailureInformationEUTRA_IEs__Type SCGFailureInformationEUTRA_IEs__cond ::
typ_cons SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition SCGFailureInformationEUTRA__criticalExtensions__cond (c : SCGFailureInformationEUTRA__criticalExtensions__Type) := 
  match c with
  | SCGFailureInformationEUTRA__criticalExtensions__scgFailureInformationEUTRA t => SCGFailureInformationEUTRA_IEs__cond t 
  | SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture t => SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma SCGFailureInformationEUTRA__criticalExtensions__len_helper1 : to_bit_sz (length SCGFailureInformationEUTRA__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SCGFailureInformationEUTRA__criticalExtensions__len_helper2 : 2 <= length2 SCGFailureInformationEUTRA__criticalExtensions__list.
 simpl. lia. Qed.
Record SCGFailureInformationEUTRA__Type : Set :=
  make__SCGFailureInformationEUTRA__Type {
    SCGFailureInformationEUTRA__criticalExtensions : SCGFailureInformationEUTRA__criticalExtensions__Type ;
}.
Definition SCGFailureInformationEUTRA__list := (
 Nor SCGFailureInformationEUTRA__criticalExtensions__Type SCGFailureInformationEUTRA__criticalExtensions__cond ::
 nil).
Definition SCGFailureInformationEUTRA__cond z := 
  SCGFailureInformationEUTRA__criticalExtensions__cond (SCGFailureInformationEUTRA__criticalExtensions z) /\
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
Definition SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__helper : forall a : SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Format : T_Format SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type)
    SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__cond SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Format.


Definition SCGFailureInformationEUTRA__criticalExtensions__Format_Type := Eval cbn in get_formats SCGFailureInformationEUTRA__criticalExtensions__list.
Definition SCGFailureInformationEUTRA__criticalExtensions__Format_list : SCGFailureInformationEUTRA__criticalExtensions__Format_Type :=
  (SCGFailureInformationEUTRA_IEs__Format, (SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition SCGFailureInformationEUTRA__criticalExtensions__list__Format := Eval compute in choice_format SCGFailureInformationEUTRA__criticalExtensions__list SCGFailureInformationEUTRA__criticalExtensions__len_helper1 SCGFailureInformationEUTRA__criticalExtensions__len_helper2  SCGFailureInformationEUTRA__criticalExtensions__Format_list.
Definition SCGFailureInformationEUTRA__criticalExtensions__F1 (z : SCGFailureInformationEUTRA__criticalExtensions__Type) : (choice SCGFailureInformationEUTRA__criticalExtensions__list) :=
  match z with
   | SCGFailureInformationEUTRA__criticalExtensions__scgFailureInformationEUTRA t => existT _ 0 t
  | SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition SCGFailureInformationEUTRA__criticalExtensions__g := (fun n => typ_set (get_nth_typ SCGFailureInformationEUTRA__criticalExtensions__list n)).
Definition SCGFailureInformationEUTRA__criticalExtensions__F2 (y : choice SCGFailureInformationEUTRA__criticalExtensions__list) : SCGFailureInformationEUTRA__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SCGFailureInformationEUTRA__criticalExtensions__g n -> SCGFailureInformationEUTRA__criticalExtensions__Type) with
    | 0 => fun (t : SCGFailureInformationEUTRA_IEs__Type) => SCGFailureInformationEUTRA__criticalExtensions__scgFailureInformationEUTRA t 
    | 1 => fun (t : SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture__Type) => SCGFailureInformationEUTRA__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SCGFailureInformationEUTRA__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SCGFailureInformationEUTRA__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SCGFailureInformationEUTRA__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SCGFailureInformationEUTRA__criticalExtensions__Type with end) n0
           end t0).

Lemma SCGFailureInformationEUTRA__criticalExtensions__helper2 :  forall (y : SCGFailureInformationEUTRA__criticalExtensions__Type), SCGFailureInformationEUTRA__criticalExtensions__cond y -> choice_cond SCGFailureInformationEUTRA__criticalExtensions__list (SCGFailureInformationEUTRA__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SCGFailureInformationEUTRA__criticalExtensions__helper3 :  forall (y : SCGFailureInformationEUTRA__criticalExtensions__Type), SCGFailureInformationEUTRA__criticalExtensions__F2 (SCGFailureInformationEUTRA__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SCGFailureInformationEUTRA__criticalExtensions__helper4 : (forall b : choice SCGFailureInformationEUTRA__criticalExtensions__list, choice_cond SCGFailureInformationEUTRA__criticalExtensions__list b -> SCGFailureInformationEUTRA__criticalExtensions__cond (SCGFailureInformationEUTRA__criticalExtensions__F2 b) /\ SCGFailureInformationEUTRA__criticalExtensions__F1 (SCGFailureInformationEUTRA__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SCGFailureInformationEUTRA__criticalExtensions__F1 SCGFailureInformationEUTRA__criticalExtensions__F2.
Definition SCGFailureInformationEUTRA__criticalExtensions__Format : T_Format SCGFailureInformationEUTRA__criticalExtensions__Type SCGFailureInformationEUTRA__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format SCGFailureInformationEUTRA__criticalExtensions__cond SCGFailureInformationEUTRA__criticalExtensions__list__Format SCGFailureInformationEUTRA__criticalExtensions__F1 SCGFailureInformationEUTRA__criticalExtensions__F2 SCGFailureInformationEUTRA__criticalExtensions__helper2 SCGFailureInformationEUTRA__criticalExtensions__helper3 SCGFailureInformationEUTRA__criticalExtensions__helper4.
Opaque SCGFailureInformationEUTRA__criticalExtensions__cond SCGFailureInformationEUTRA__criticalExtensions__Format.


Definition SCGFailureInformationEUTRA__Format_Type := Eval cbn in seq_format_prod SCGFailureInformationEUTRA__list.
Definition SCGFailureInformationEUTRA__Format_list : SCGFailureInformationEUTRA__Format_Type :=
  (SCGFailureInformationEUTRA__criticalExtensions__Format, unit_format).
Definition SCGFailureInformationEUTRA__list__Format := (*Eval compute in *) seq_format SCGFailureInformationEUTRA__list SCGFailureInformationEUTRA__Format_list.
Definition SCGFailureInformationEUTRA__F1 z :=
  (SCGFailureInformationEUTRA__criticalExtensions z, tt).
Definition SCGFailureInformationEUTRA__F2 (y : seq_type SCGFailureInformationEUTRA__list) :=
  match y with
  | (i0, _)=>
    make__SCGFailureInformationEUTRA__Type i0
  end.
Lemma SCGFailureInformationEUTRA__F1F2_cond (z : SCGFailureInformationEUTRA__Type)
  : SCGFailureInformationEUTRA__cond z ->
  (seq_cond SCGFailureInformationEUTRA__list (SCGFailureInformationEUTRA__F1 z)).
intro H. unfold SCGFailureInformationEUTRA__cond in H. simpl. auto. Qed.
Lemma SCGFailureInformationEUTRA__F1F2_cond2 (z : SCGFailureInformationEUTRA__Type)
 : SCGFailureInformationEUTRA__F2 (SCGFailureInformationEUTRA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SCGFailureInformationEUTRA__F2F1_cond (y : seq_type SCGFailureInformationEUTRA__list)
  : seq_cond SCGFailureInformationEUTRA__list y ->
 (SCGFailureInformationEUTRA__cond (SCGFailureInformationEUTRA__F2 y)) /\  SCGFailureInformationEUTRA__F1 (SCGFailureInformationEUTRA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SCGFailureInformationEUTRA__cond. simpl in *. auto.
 - simpl. unfold SCGFailureInformationEUTRA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SCGFailureInformationEUTRA__Format : T_Format SCGFailureInformationEUTRA__Type SCGFailureInformationEUTRA__cond :=
        proj2_format  SCGFailureInformationEUTRA__cond SCGFailureInformationEUTRA__list__Format
    SCGFailureInformationEUTRA__F1 SCGFailureInformationEUTRA__F2 SCGFailureInformationEUTRA__F1F2_cond  SCGFailureInformationEUTRA__F1F2_cond2 SCGFailureInformationEUTRA__F2F1_cond.
Opaque SCGFailureInformationEUTRA__cond SCGFailureInformationEUTRA__Format.

