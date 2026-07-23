Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ULInformationTransfer_IEs.

Opaque ULInformationTransfer_IEs__cond ULInformationTransfer_IEs__Format.

Record ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type : Set := make__ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond (z : ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive ULInformationTransfer__criticalExtensions__Type : Set :=
  | ULInformationTransfer__criticalExtensions__ulInformationTransfer : ULInformationTransfer_IEs__Type -> ULInformationTransfer__criticalExtensions__Type
  | ULInformationTransfer__criticalExtensions__criticalExtensionsFuture : ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type -> ULInformationTransfer__criticalExtensions__Type
.
Definition ULInformationTransfer__criticalExtensions__list : list typ := (
typ_cons ULInformationTransfer_IEs__Type ULInformationTransfer_IEs__cond ::
typ_cons ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition ULInformationTransfer__criticalExtensions__cond (c : ULInformationTransfer__criticalExtensions__Type) := 
  match c with
  | ULInformationTransfer__criticalExtensions__ulInformationTransfer t => ULInformationTransfer_IEs__cond t 
  | ULInformationTransfer__criticalExtensions__criticalExtensionsFuture t => ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma ULInformationTransfer__criticalExtensions__len_helper1 : to_bit_sz (length ULInformationTransfer__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ULInformationTransfer__criticalExtensions__len_helper2 : 2 <= length2 ULInformationTransfer__criticalExtensions__list.
 simpl. lia. Qed.
Record ULInformationTransfer__Type : Set :=
  make__ULInformationTransfer__Type {
    ULInformationTransfer__criticalExtensions : ULInformationTransfer__criticalExtensions__Type ;
}.
Definition ULInformationTransfer__list := (
 Nor ULInformationTransfer__criticalExtensions__Type ULInformationTransfer__criticalExtensions__cond ::
 nil).
Definition ULInformationTransfer__cond z := 
  ULInformationTransfer__criticalExtensions__cond (ULInformationTransfer__criticalExtensions z) /\
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
Definition ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__helper : forall a : ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Format : T_Format ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type)
    ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__cond ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Format.


Definition ULInformationTransfer__criticalExtensions__Format_Type := Eval cbn in get_formats ULInformationTransfer__criticalExtensions__list.
Definition ULInformationTransfer__criticalExtensions__Format_list : ULInformationTransfer__criticalExtensions__Format_Type :=
  (ULInformationTransfer_IEs__Format, (ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition ULInformationTransfer__criticalExtensions__list__Format := Eval compute in choice_format ULInformationTransfer__criticalExtensions__list ULInformationTransfer__criticalExtensions__len_helper1 ULInformationTransfer__criticalExtensions__len_helper2  ULInformationTransfer__criticalExtensions__Format_list.
Definition ULInformationTransfer__criticalExtensions__F1 (z : ULInformationTransfer__criticalExtensions__Type) : (choice ULInformationTransfer__criticalExtensions__list) :=
  match z with
   | ULInformationTransfer__criticalExtensions__ulInformationTransfer t => existT _ 0 t
  | ULInformationTransfer__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition ULInformationTransfer__criticalExtensions__g := (fun n => typ_set (get_nth_typ ULInformationTransfer__criticalExtensions__list n)).
Definition ULInformationTransfer__criticalExtensions__F2 (y : choice ULInformationTransfer__criticalExtensions__list) : ULInformationTransfer__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ULInformationTransfer__criticalExtensions__g n -> ULInformationTransfer__criticalExtensions__Type) with
    | 0 => fun (t : ULInformationTransfer_IEs__Type) => ULInformationTransfer__criticalExtensions__ulInformationTransfer t 
    | 1 => fun (t : ULInformationTransfer__criticalExtensions__criticalExtensionsFuture__Type) => ULInformationTransfer__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ULInformationTransfer__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ULInformationTransfer__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ULInformationTransfer__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ULInformationTransfer__criticalExtensions__Type with end) n0
           end t0).

Lemma ULInformationTransfer__criticalExtensions__helper2 :  forall (y : ULInformationTransfer__criticalExtensions__Type), ULInformationTransfer__criticalExtensions__cond y -> choice_cond ULInformationTransfer__criticalExtensions__list (ULInformationTransfer__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ULInformationTransfer__criticalExtensions__helper3 :  forall (y : ULInformationTransfer__criticalExtensions__Type), ULInformationTransfer__criticalExtensions__F2 (ULInformationTransfer__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ULInformationTransfer__criticalExtensions__helper4 : (forall b : choice ULInformationTransfer__criticalExtensions__list, choice_cond ULInformationTransfer__criticalExtensions__list b -> ULInformationTransfer__criticalExtensions__cond (ULInformationTransfer__criticalExtensions__F2 b) /\ ULInformationTransfer__criticalExtensions__F1 (ULInformationTransfer__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ULInformationTransfer__criticalExtensions__F1 ULInformationTransfer__criticalExtensions__F2.
Definition ULInformationTransfer__criticalExtensions__Format : T_Format ULInformationTransfer__criticalExtensions__Type ULInformationTransfer__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format ULInformationTransfer__criticalExtensions__cond ULInformationTransfer__criticalExtensions__list__Format ULInformationTransfer__criticalExtensions__F1 ULInformationTransfer__criticalExtensions__F2 ULInformationTransfer__criticalExtensions__helper2 ULInformationTransfer__criticalExtensions__helper3 ULInformationTransfer__criticalExtensions__helper4.
Opaque ULInformationTransfer__criticalExtensions__cond ULInformationTransfer__criticalExtensions__Format.


Definition ULInformationTransfer__Format_Type := Eval cbn in seq_format_prod ULInformationTransfer__list.
Definition ULInformationTransfer__Format_list : ULInformationTransfer__Format_Type :=
  (ULInformationTransfer__criticalExtensions__Format, unit_format).
Definition ULInformationTransfer__list__Format := (*Eval compute in *) seq_format ULInformationTransfer__list ULInformationTransfer__Format_list.
Definition ULInformationTransfer__F1 z :=
  (ULInformationTransfer__criticalExtensions z, tt).
Definition ULInformationTransfer__F2 (y : seq_type ULInformationTransfer__list) :=
  match y with
  | (i0, _)=>
    make__ULInformationTransfer__Type i0
  end.
Lemma ULInformationTransfer__F1F2_cond (z : ULInformationTransfer__Type)
  : ULInformationTransfer__cond z ->
  (seq_cond ULInformationTransfer__list (ULInformationTransfer__F1 z)).
intro H. unfold ULInformationTransfer__cond in H. simpl. auto. Qed.
Lemma ULInformationTransfer__F1F2_cond2 (z : ULInformationTransfer__Type)
 : ULInformationTransfer__F2 (ULInformationTransfer__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ULInformationTransfer__F2F1_cond (y : seq_type ULInformationTransfer__list)
  : seq_cond ULInformationTransfer__list y ->
 (ULInformationTransfer__cond (ULInformationTransfer__F2 y)) /\  ULInformationTransfer__F1 (ULInformationTransfer__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ULInformationTransfer__cond. simpl in *. auto.
 - simpl. unfold ULInformationTransfer__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ULInformationTransfer__Format : T_Format ULInformationTransfer__Type ULInformationTransfer__cond :=
        proj2_format  ULInformationTransfer__cond ULInformationTransfer__list__Format
    ULInformationTransfer__F1 ULInformationTransfer__F2 ULInformationTransfer__F1F2_cond  ULInformationTransfer__F1F2_cond2 ULInformationTransfer__F2F1_cond.
Opaque ULInformationTransfer__cond ULInformationTransfer__Format.

