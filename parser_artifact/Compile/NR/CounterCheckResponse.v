Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.CounterCheckResponse_IEs.

Opaque CounterCheckResponse_IEs__cond CounterCheckResponse_IEs__Format.

Record CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type : Set := make__CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__cond (z : CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive CounterCheckResponse__criticalExtensions__Type : Set :=
  | CounterCheckResponse__criticalExtensions__counterCheckResponse : CounterCheckResponse_IEs__Type -> CounterCheckResponse__criticalExtensions__Type
  | CounterCheckResponse__criticalExtensions__criticalExtensionsFuture : CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type -> CounterCheckResponse__criticalExtensions__Type
.
Definition CounterCheckResponse__criticalExtensions__list : list typ := (
typ_cons CounterCheckResponse_IEs__Type CounterCheckResponse_IEs__cond ::
typ_cons CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition CounterCheckResponse__criticalExtensions__cond (c : CounterCheckResponse__criticalExtensions__Type) := 
  match c with
  | CounterCheckResponse__criticalExtensions__counterCheckResponse t => CounterCheckResponse_IEs__cond t 
  | CounterCheckResponse__criticalExtensions__criticalExtensionsFuture t => CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma CounterCheckResponse__criticalExtensions__len_helper1 : to_bit_sz (length CounterCheckResponse__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CounterCheckResponse__criticalExtensions__len_helper2 : 2 <= length2 CounterCheckResponse__criticalExtensions__list.
 simpl. lia. Qed.
Record CounterCheckResponse__Type : Set :=
  make__CounterCheckResponse__Type {
    CounterCheckResponse__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    CounterCheckResponse__criticalExtensions : CounterCheckResponse__criticalExtensions__Type ;
}.
Definition CounterCheckResponse__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor CounterCheckResponse__criticalExtensions__Type CounterCheckResponse__criticalExtensions__cond ::
 nil).
Definition CounterCheckResponse__cond z := 
  RRC_TransactionIdentifier__cond (CounterCheckResponse__rrc_TransactionIdentifier z) /\
  CounterCheckResponse__criticalExtensions__cond (CounterCheckResponse__criticalExtensions z) /\
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
Definition CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__helper : forall a : CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Format : T_Format CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type)
    CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__cond CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Format.


Definition CounterCheckResponse__criticalExtensions__Format_Type := Eval cbn in get_formats CounterCheckResponse__criticalExtensions__list.
Definition CounterCheckResponse__criticalExtensions__Format_list : CounterCheckResponse__criticalExtensions__Format_Type :=
  (CounterCheckResponse_IEs__Format, (CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition CounterCheckResponse__criticalExtensions__list__Format := Eval compute in choice_format CounterCheckResponse__criticalExtensions__list CounterCheckResponse__criticalExtensions__len_helper1 CounterCheckResponse__criticalExtensions__len_helper2  CounterCheckResponse__criticalExtensions__Format_list.
Definition CounterCheckResponse__criticalExtensions__F1 (z : CounterCheckResponse__criticalExtensions__Type) : (choice CounterCheckResponse__criticalExtensions__list) :=
  match z with
   | CounterCheckResponse__criticalExtensions__counterCheckResponse t => existT _ 0 t
  | CounterCheckResponse__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition CounterCheckResponse__criticalExtensions__g := (fun n => typ_set (get_nth_typ CounterCheckResponse__criticalExtensions__list n)).
Definition CounterCheckResponse__criticalExtensions__F2 (y : choice CounterCheckResponse__criticalExtensions__list) : CounterCheckResponse__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CounterCheckResponse__criticalExtensions__g n -> CounterCheckResponse__criticalExtensions__Type) with
    | 0 => fun (t : CounterCheckResponse_IEs__Type) => CounterCheckResponse__criticalExtensions__counterCheckResponse t 
    | 1 => fun (t : CounterCheckResponse__criticalExtensions__criticalExtensionsFuture__Type) => CounterCheckResponse__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CounterCheckResponse__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CounterCheckResponse__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CounterCheckResponse__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CounterCheckResponse__criticalExtensions__Type with end) n0
           end t0).

Lemma CounterCheckResponse__criticalExtensions__helper2 :  forall (y : CounterCheckResponse__criticalExtensions__Type), CounterCheckResponse__criticalExtensions__cond y -> choice_cond CounterCheckResponse__criticalExtensions__list (CounterCheckResponse__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CounterCheckResponse__criticalExtensions__helper3 :  forall (y : CounterCheckResponse__criticalExtensions__Type), CounterCheckResponse__criticalExtensions__F2 (CounterCheckResponse__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CounterCheckResponse__criticalExtensions__helper4 : (forall b : choice CounterCheckResponse__criticalExtensions__list, choice_cond CounterCheckResponse__criticalExtensions__list b -> CounterCheckResponse__criticalExtensions__cond (CounterCheckResponse__criticalExtensions__F2 b) /\ CounterCheckResponse__criticalExtensions__F1 (CounterCheckResponse__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CounterCheckResponse__criticalExtensions__F1 CounterCheckResponse__criticalExtensions__F2.
Definition CounterCheckResponse__criticalExtensions__Format : T_Format CounterCheckResponse__criticalExtensions__Type CounterCheckResponse__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format CounterCheckResponse__criticalExtensions__cond CounterCheckResponse__criticalExtensions__list__Format CounterCheckResponse__criticalExtensions__F1 CounterCheckResponse__criticalExtensions__F2 CounterCheckResponse__criticalExtensions__helper2 CounterCheckResponse__criticalExtensions__helper3 CounterCheckResponse__criticalExtensions__helper4.
Opaque CounterCheckResponse__criticalExtensions__cond CounterCheckResponse__criticalExtensions__Format.


Definition CounterCheckResponse__Format_Type := Eval cbn in seq_format_prod CounterCheckResponse__list.
Definition CounterCheckResponse__Format_list : CounterCheckResponse__Format_Type :=
  (RRC_TransactionIdentifier__Format, (CounterCheckResponse__criticalExtensions__Format, unit_format)).
Definition CounterCheckResponse__list__Format := (*Eval compute in *) seq_format CounterCheckResponse__list CounterCheckResponse__Format_list.
Definition CounterCheckResponse__F1 z :=
  (CounterCheckResponse__rrc_TransactionIdentifier z, (CounterCheckResponse__criticalExtensions z, tt)).
Definition CounterCheckResponse__F2 (y : seq_type CounterCheckResponse__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CounterCheckResponse__Type i0 i1
  end.
Lemma CounterCheckResponse__F1F2_cond (z : CounterCheckResponse__Type)
  : CounterCheckResponse__cond z ->
  (seq_cond CounterCheckResponse__list (CounterCheckResponse__F1 z)).
intro H. unfold CounterCheckResponse__cond in H. simpl. auto. Qed.
Lemma CounterCheckResponse__F1F2_cond2 (z : CounterCheckResponse__Type)
 : CounterCheckResponse__F2 (CounterCheckResponse__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CounterCheckResponse__F2F1_cond (y : seq_type CounterCheckResponse__list)
  : seq_cond CounterCheckResponse__list y ->
 (CounterCheckResponse__cond (CounterCheckResponse__F2 y)) /\  CounterCheckResponse__F1 (CounterCheckResponse__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CounterCheckResponse__cond. simpl in *. auto.
 - simpl. unfold CounterCheckResponse__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CounterCheckResponse__Format : T_Format CounterCheckResponse__Type CounterCheckResponse__cond :=
        proj2_format  CounterCheckResponse__cond CounterCheckResponse__list__Format
    CounterCheckResponse__F1 CounterCheckResponse__F2 CounterCheckResponse__F1F2_cond  CounterCheckResponse__F1F2_cond2 CounterCheckResponse__F2F1_cond.
Opaque CounterCheckResponse__cond CounterCheckResponse__Format.

