Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.CounterCheck_IEs.

Opaque CounterCheck_IEs__cond CounterCheck_IEs__Format.

Record CounterCheck__criticalExtensions__criticalExtensionsFuture__Type : Set := make__CounterCheck__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition CounterCheck__criticalExtensions__criticalExtensionsFuture__cond (z : CounterCheck__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive CounterCheck__criticalExtensions__Type : Set :=
  | CounterCheck__criticalExtensions__counterCheck : CounterCheck_IEs__Type -> CounterCheck__criticalExtensions__Type
  | CounterCheck__criticalExtensions__criticalExtensionsFuture : CounterCheck__criticalExtensions__criticalExtensionsFuture__Type -> CounterCheck__criticalExtensions__Type
.
Definition CounterCheck__criticalExtensions__list : list typ := (
typ_cons CounterCheck_IEs__Type CounterCheck_IEs__cond ::
typ_cons CounterCheck__criticalExtensions__criticalExtensionsFuture__Type CounterCheck__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition CounterCheck__criticalExtensions__cond (c : CounterCheck__criticalExtensions__Type) := 
  match c with
  | CounterCheck__criticalExtensions__counterCheck t => CounterCheck_IEs__cond t 
  | CounterCheck__criticalExtensions__criticalExtensionsFuture t => CounterCheck__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma CounterCheck__criticalExtensions__len_helper1 : to_bit_sz (length CounterCheck__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CounterCheck__criticalExtensions__len_helper2 : 2 <= length2 CounterCheck__criticalExtensions__list.
 simpl. lia. Qed.
Record CounterCheck__Type : Set :=
  make__CounterCheck__Type {
    CounterCheck__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    CounterCheck__criticalExtensions : CounterCheck__criticalExtensions__Type ;
}.
Definition CounterCheck__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor CounterCheck__criticalExtensions__Type CounterCheck__criticalExtensions__cond ::
 nil).
Definition CounterCheck__cond z := 
  RRC_TransactionIdentifier__cond (CounterCheck__rrc_TransactionIdentifier z) /\
  CounterCheck__criticalExtensions__cond (CounterCheck__criticalExtensions z) /\
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
Definition CounterCheck__criticalExtensions__criticalExtensionsFuture__helper : forall a : CounterCheck__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__CounterCheck__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition CounterCheck__criticalExtensions__criticalExtensionsFuture__Format : T_Format CounterCheck__criticalExtensions__criticalExtensionsFuture__Type CounterCheck__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__CounterCheck__criticalExtensions__criticalExtensionsFuture__Type)
    CounterCheck__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque CounterCheck__criticalExtensions__criticalExtensionsFuture__cond CounterCheck__criticalExtensions__criticalExtensionsFuture__Format.


Definition CounterCheck__criticalExtensions__Format_Type := Eval cbn in get_formats CounterCheck__criticalExtensions__list.
Definition CounterCheck__criticalExtensions__Format_list : CounterCheck__criticalExtensions__Format_Type :=
  (CounterCheck_IEs__Format, (CounterCheck__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition CounterCheck__criticalExtensions__list__Format := Eval compute in choice_format CounterCheck__criticalExtensions__list CounterCheck__criticalExtensions__len_helper1 CounterCheck__criticalExtensions__len_helper2  CounterCheck__criticalExtensions__Format_list.
Definition CounterCheck__criticalExtensions__F1 (z : CounterCheck__criticalExtensions__Type) : (choice CounterCheck__criticalExtensions__list) :=
  match z with
   | CounterCheck__criticalExtensions__counterCheck t => existT _ 0 t
  | CounterCheck__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition CounterCheck__criticalExtensions__g := (fun n => typ_set (get_nth_typ CounterCheck__criticalExtensions__list n)).
Definition CounterCheck__criticalExtensions__F2 (y : choice CounterCheck__criticalExtensions__list) : CounterCheck__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CounterCheck__criticalExtensions__g n -> CounterCheck__criticalExtensions__Type) with
    | 0 => fun (t : CounterCheck_IEs__Type) => CounterCheck__criticalExtensions__counterCheck t 
    | 1 => fun (t : CounterCheck__criticalExtensions__criticalExtensionsFuture__Type) => CounterCheck__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CounterCheck__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CounterCheck__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CounterCheck__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CounterCheck__criticalExtensions__Type with end) n0
           end t0).

Lemma CounterCheck__criticalExtensions__helper2 :  forall (y : CounterCheck__criticalExtensions__Type), CounterCheck__criticalExtensions__cond y -> choice_cond CounterCheck__criticalExtensions__list (CounterCheck__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CounterCheck__criticalExtensions__helper3 :  forall (y : CounterCheck__criticalExtensions__Type), CounterCheck__criticalExtensions__F2 (CounterCheck__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CounterCheck__criticalExtensions__helper4 : (forall b : choice CounterCheck__criticalExtensions__list, choice_cond CounterCheck__criticalExtensions__list b -> CounterCheck__criticalExtensions__cond (CounterCheck__criticalExtensions__F2 b) /\ CounterCheck__criticalExtensions__F1 (CounterCheck__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CounterCheck__criticalExtensions__F1 CounterCheck__criticalExtensions__F2.
Definition CounterCheck__criticalExtensions__Format : T_Format CounterCheck__criticalExtensions__Type CounterCheck__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format CounterCheck__criticalExtensions__cond CounterCheck__criticalExtensions__list__Format CounterCheck__criticalExtensions__F1 CounterCheck__criticalExtensions__F2 CounterCheck__criticalExtensions__helper2 CounterCheck__criticalExtensions__helper3 CounterCheck__criticalExtensions__helper4.
Opaque CounterCheck__criticalExtensions__cond CounterCheck__criticalExtensions__Format.


Definition CounterCheck__Format_Type := Eval cbn in seq_format_prod CounterCheck__list.
Definition CounterCheck__Format_list : CounterCheck__Format_Type :=
  (RRC_TransactionIdentifier__Format, (CounterCheck__criticalExtensions__Format, unit_format)).
Definition CounterCheck__list__Format := (*Eval compute in *) seq_format CounterCheck__list CounterCheck__Format_list.
Definition CounterCheck__F1 z :=
  (CounterCheck__rrc_TransactionIdentifier z, (CounterCheck__criticalExtensions z, tt)).
Definition CounterCheck__F2 (y : seq_type CounterCheck__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CounterCheck__Type i0 i1
  end.
Lemma CounterCheck__F1F2_cond (z : CounterCheck__Type)
  : CounterCheck__cond z ->
  (seq_cond CounterCheck__list (CounterCheck__F1 z)).
intro H. unfold CounterCheck__cond in H. simpl. auto. Qed.
Lemma CounterCheck__F1F2_cond2 (z : CounterCheck__Type)
 : CounterCheck__F2 (CounterCheck__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CounterCheck__F2F1_cond (y : seq_type CounterCheck__list)
  : seq_cond CounterCheck__list y ->
 (CounterCheck__cond (CounterCheck__F2 y)) /\  CounterCheck__F1 (CounterCheck__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CounterCheck__cond. simpl in *. auto.
 - simpl. unfold CounterCheck__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CounterCheck__Format : T_Format CounterCheck__Type CounterCheck__cond :=
        proj2_format  CounterCheck__cond CounterCheck__list__Format
    CounterCheck__F1 CounterCheck__F2 CounterCheck__F1F2_cond  CounterCheck__F1F2_cond2 CounterCheck__F2F1_cond.
Opaque CounterCheck__cond CounterCheck__Format.

