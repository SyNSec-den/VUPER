Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ULDedicatedMessageSegment_r16_IEs.

Opaque ULDedicatedMessageSegment_r16_IEs__cond ULDedicatedMessageSegment_r16_IEs__Format.

Record ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type : Set := make__ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond (z : ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive ULDedicatedMessageSegment_r16__criticalExtensions__Type : Set :=
  | ULDedicatedMessageSegment_r16__criticalExtensions__ulDedicatedMessageSegment_r16 : ULDedicatedMessageSegment_r16_IEs__Type -> ULDedicatedMessageSegment_r16__criticalExtensions__Type
  | ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture : ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type -> ULDedicatedMessageSegment_r16__criticalExtensions__Type
.
Definition ULDedicatedMessageSegment_r16__criticalExtensions__list : list typ := (
typ_cons ULDedicatedMessageSegment_r16_IEs__Type ULDedicatedMessageSegment_r16_IEs__cond ::
typ_cons ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition ULDedicatedMessageSegment_r16__criticalExtensions__cond (c : ULDedicatedMessageSegment_r16__criticalExtensions__Type) := 
  match c with
  | ULDedicatedMessageSegment_r16__criticalExtensions__ulDedicatedMessageSegment_r16 t => ULDedicatedMessageSegment_r16_IEs__cond t 
  | ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture t => ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma ULDedicatedMessageSegment_r16__criticalExtensions__len_helper1 : to_bit_sz (length ULDedicatedMessageSegment_r16__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ULDedicatedMessageSegment_r16__criticalExtensions__len_helper2 : 2 <= length2 ULDedicatedMessageSegment_r16__criticalExtensions__list.
 simpl. lia. Qed.
Record ULDedicatedMessageSegment_r16__Type : Set :=
  make__ULDedicatedMessageSegment_r16__Type {
    ULDedicatedMessageSegment_r16__criticalExtensions : ULDedicatedMessageSegment_r16__criticalExtensions__Type ;
}.
Definition ULDedicatedMessageSegment_r16__list := (
 Nor ULDedicatedMessageSegment_r16__criticalExtensions__Type ULDedicatedMessageSegment_r16__criticalExtensions__cond ::
 nil).
Definition ULDedicatedMessageSegment_r16__cond z := 
  ULDedicatedMessageSegment_r16__criticalExtensions__cond (ULDedicatedMessageSegment_r16__criticalExtensions z) /\
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
Definition ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__helper : forall a : ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Format : T_Format ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type)
    ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Format.


Definition ULDedicatedMessageSegment_r16__criticalExtensions__Format_Type := Eval cbn in get_formats ULDedicatedMessageSegment_r16__criticalExtensions__list.
Definition ULDedicatedMessageSegment_r16__criticalExtensions__Format_list : ULDedicatedMessageSegment_r16__criticalExtensions__Format_Type :=
  (ULDedicatedMessageSegment_r16_IEs__Format, (ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition ULDedicatedMessageSegment_r16__criticalExtensions__list__Format := Eval compute in choice_format ULDedicatedMessageSegment_r16__criticalExtensions__list ULDedicatedMessageSegment_r16__criticalExtensions__len_helper1 ULDedicatedMessageSegment_r16__criticalExtensions__len_helper2  ULDedicatedMessageSegment_r16__criticalExtensions__Format_list.
Definition ULDedicatedMessageSegment_r16__criticalExtensions__F1 (z : ULDedicatedMessageSegment_r16__criticalExtensions__Type) : (choice ULDedicatedMessageSegment_r16__criticalExtensions__list) :=
  match z with
   | ULDedicatedMessageSegment_r16__criticalExtensions__ulDedicatedMessageSegment_r16 t => existT _ 0 t
  | ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition ULDedicatedMessageSegment_r16__criticalExtensions__g := (fun n => typ_set (get_nth_typ ULDedicatedMessageSegment_r16__criticalExtensions__list n)).
Definition ULDedicatedMessageSegment_r16__criticalExtensions__F2 (y : choice ULDedicatedMessageSegment_r16__criticalExtensions__list) : ULDedicatedMessageSegment_r16__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ULDedicatedMessageSegment_r16__criticalExtensions__g n -> ULDedicatedMessageSegment_r16__criticalExtensions__Type) with
    | 0 => fun (t : ULDedicatedMessageSegment_r16_IEs__Type) => ULDedicatedMessageSegment_r16__criticalExtensions__ulDedicatedMessageSegment_r16 t 
    | 1 => fun (t : ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type) => ULDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ULDedicatedMessageSegment_r16__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ULDedicatedMessageSegment_r16__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ULDedicatedMessageSegment_r16__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ULDedicatedMessageSegment_r16__criticalExtensions__Type with end) n0
           end t0).

Lemma ULDedicatedMessageSegment_r16__criticalExtensions__helper2 :  forall (y : ULDedicatedMessageSegment_r16__criticalExtensions__Type), ULDedicatedMessageSegment_r16__criticalExtensions__cond y -> choice_cond ULDedicatedMessageSegment_r16__criticalExtensions__list (ULDedicatedMessageSegment_r16__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ULDedicatedMessageSegment_r16__criticalExtensions__helper3 :  forall (y : ULDedicatedMessageSegment_r16__criticalExtensions__Type), ULDedicatedMessageSegment_r16__criticalExtensions__F2 (ULDedicatedMessageSegment_r16__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ULDedicatedMessageSegment_r16__criticalExtensions__helper4 : (forall b : choice ULDedicatedMessageSegment_r16__criticalExtensions__list, choice_cond ULDedicatedMessageSegment_r16__criticalExtensions__list b -> ULDedicatedMessageSegment_r16__criticalExtensions__cond (ULDedicatedMessageSegment_r16__criticalExtensions__F2 b) /\ ULDedicatedMessageSegment_r16__criticalExtensions__F1 (ULDedicatedMessageSegment_r16__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ULDedicatedMessageSegment_r16__criticalExtensions__F1 ULDedicatedMessageSegment_r16__criticalExtensions__F2.
Definition ULDedicatedMessageSegment_r16__criticalExtensions__Format : T_Format ULDedicatedMessageSegment_r16__criticalExtensions__Type ULDedicatedMessageSegment_r16__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format ULDedicatedMessageSegment_r16__criticalExtensions__cond ULDedicatedMessageSegment_r16__criticalExtensions__list__Format ULDedicatedMessageSegment_r16__criticalExtensions__F1 ULDedicatedMessageSegment_r16__criticalExtensions__F2 ULDedicatedMessageSegment_r16__criticalExtensions__helper2 ULDedicatedMessageSegment_r16__criticalExtensions__helper3 ULDedicatedMessageSegment_r16__criticalExtensions__helper4.
Opaque ULDedicatedMessageSegment_r16__criticalExtensions__cond ULDedicatedMessageSegment_r16__criticalExtensions__Format.


Definition ULDedicatedMessageSegment_r16__Format_Type := Eval cbn in seq_format_prod ULDedicatedMessageSegment_r16__list.
Definition ULDedicatedMessageSegment_r16__Format_list : ULDedicatedMessageSegment_r16__Format_Type :=
  (ULDedicatedMessageSegment_r16__criticalExtensions__Format, unit_format).
Definition ULDedicatedMessageSegment_r16__list__Format := (*Eval compute in *) seq_format ULDedicatedMessageSegment_r16__list ULDedicatedMessageSegment_r16__Format_list.
Definition ULDedicatedMessageSegment_r16__F1 z :=
  (ULDedicatedMessageSegment_r16__criticalExtensions z, tt).
Definition ULDedicatedMessageSegment_r16__F2 (y : seq_type ULDedicatedMessageSegment_r16__list) :=
  match y with
  | (i0, _)=>
    make__ULDedicatedMessageSegment_r16__Type i0
  end.
Lemma ULDedicatedMessageSegment_r16__F1F2_cond (z : ULDedicatedMessageSegment_r16__Type)
  : ULDedicatedMessageSegment_r16__cond z ->
  (seq_cond ULDedicatedMessageSegment_r16__list (ULDedicatedMessageSegment_r16__F1 z)).
intro H. unfold ULDedicatedMessageSegment_r16__cond in H. simpl. auto. Qed.
Lemma ULDedicatedMessageSegment_r16__F1F2_cond2 (z : ULDedicatedMessageSegment_r16__Type)
 : ULDedicatedMessageSegment_r16__F2 (ULDedicatedMessageSegment_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ULDedicatedMessageSegment_r16__F2F1_cond (y : seq_type ULDedicatedMessageSegment_r16__list)
  : seq_cond ULDedicatedMessageSegment_r16__list y ->
 (ULDedicatedMessageSegment_r16__cond (ULDedicatedMessageSegment_r16__F2 y)) /\  ULDedicatedMessageSegment_r16__F1 (ULDedicatedMessageSegment_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ULDedicatedMessageSegment_r16__cond. simpl in *. auto.
 - simpl. unfold ULDedicatedMessageSegment_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ULDedicatedMessageSegment_r16__Format : T_Format ULDedicatedMessageSegment_r16__Type ULDedicatedMessageSegment_r16__cond :=
        proj2_format  ULDedicatedMessageSegment_r16__cond ULDedicatedMessageSegment_r16__list__Format
    ULDedicatedMessageSegment_r16__F1 ULDedicatedMessageSegment_r16__F2 ULDedicatedMessageSegment_r16__F1F2_cond  ULDedicatedMessageSegment_r16__F1F2_cond2 ULDedicatedMessageSegment_r16__F2F1_cond.
Opaque ULDedicatedMessageSegment_r16__cond ULDedicatedMessageSegment_r16__Format.

