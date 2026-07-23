Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UEPositioningAssistanceInfo_r17_IEs.

Opaque UEPositioningAssistanceInfo_r17_IEs__cond UEPositioningAssistanceInfo_r17_IEs__Format.

Record UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__cond (z : UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UEPositioningAssistanceInfo_r17__criticalExtensions__Type : Set :=
  | UEPositioningAssistanceInfo_r17__criticalExtensions__uePositioningAssistanceInfo_r17 : UEPositioningAssistanceInfo_r17_IEs__Type -> UEPositioningAssistanceInfo_r17__criticalExtensions__Type
  | UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture : UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type -> UEPositioningAssistanceInfo_r17__criticalExtensions__Type
.
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__list : list typ := (
typ_cons UEPositioningAssistanceInfo_r17_IEs__Type UEPositioningAssistanceInfo_r17_IEs__cond ::
typ_cons UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__cond (c : UEPositioningAssistanceInfo_r17__criticalExtensions__Type) := 
  match c with
  | UEPositioningAssistanceInfo_r17__criticalExtensions__uePositioningAssistanceInfo_r17 t => UEPositioningAssistanceInfo_r17_IEs__cond t 
  | UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture t => UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UEPositioningAssistanceInfo_r17__criticalExtensions__len_helper1 : to_bit_sz (length UEPositioningAssistanceInfo_r17__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UEPositioningAssistanceInfo_r17__criticalExtensions__len_helper2 : 2 <= length2 UEPositioningAssistanceInfo_r17__criticalExtensions__list.
 simpl. lia. Qed.
Record UEPositioningAssistanceInfo_r17__Type : Set :=
  make__UEPositioningAssistanceInfo_r17__Type {
    UEPositioningAssistanceInfo_r17__criticalExtensions : UEPositioningAssistanceInfo_r17__criticalExtensions__Type ;
}.
Definition UEPositioningAssistanceInfo_r17__list := (
 Nor UEPositioningAssistanceInfo_r17__criticalExtensions__Type UEPositioningAssistanceInfo_r17__criticalExtensions__cond ::
 nil).
Definition UEPositioningAssistanceInfo_r17__cond z := 
  UEPositioningAssistanceInfo_r17__criticalExtensions__cond (UEPositioningAssistanceInfo_r17__criticalExtensions z) /\
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
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__helper : forall a : UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Format : T_Format UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type)
    UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__cond UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Format.


Definition UEPositioningAssistanceInfo_r17__criticalExtensions__Format_Type := Eval cbn in get_formats UEPositioningAssistanceInfo_r17__criticalExtensions__list.
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__Format_list : UEPositioningAssistanceInfo_r17__criticalExtensions__Format_Type :=
  (UEPositioningAssistanceInfo_r17_IEs__Format, (UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__list__Format := Eval compute in choice_format UEPositioningAssistanceInfo_r17__criticalExtensions__list UEPositioningAssistanceInfo_r17__criticalExtensions__len_helper1 UEPositioningAssistanceInfo_r17__criticalExtensions__len_helper2  UEPositioningAssistanceInfo_r17__criticalExtensions__Format_list.
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__F1 (z : UEPositioningAssistanceInfo_r17__criticalExtensions__Type) : (choice UEPositioningAssistanceInfo_r17__criticalExtensions__list) :=
  match z with
   | UEPositioningAssistanceInfo_r17__criticalExtensions__uePositioningAssistanceInfo_r17 t => existT _ 0 t
  | UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__g := (fun n => typ_set (get_nth_typ UEPositioningAssistanceInfo_r17__criticalExtensions__list n)).
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__F2 (y : choice UEPositioningAssistanceInfo_r17__criticalExtensions__list) : UEPositioningAssistanceInfo_r17__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UEPositioningAssistanceInfo_r17__criticalExtensions__g n -> UEPositioningAssistanceInfo_r17__criticalExtensions__Type) with
    | 0 => fun (t : UEPositioningAssistanceInfo_r17_IEs__Type) => UEPositioningAssistanceInfo_r17__criticalExtensions__uePositioningAssistanceInfo_r17 t 
    | 1 => fun (t : UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture__Type) => UEPositioningAssistanceInfo_r17__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UEPositioningAssistanceInfo_r17__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UEPositioningAssistanceInfo_r17__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UEPositioningAssistanceInfo_r17__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UEPositioningAssistanceInfo_r17__criticalExtensions__Type with end) n0
           end t0).

Lemma UEPositioningAssistanceInfo_r17__criticalExtensions__helper2 :  forall (y : UEPositioningAssistanceInfo_r17__criticalExtensions__Type), UEPositioningAssistanceInfo_r17__criticalExtensions__cond y -> choice_cond UEPositioningAssistanceInfo_r17__criticalExtensions__list (UEPositioningAssistanceInfo_r17__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UEPositioningAssistanceInfo_r17__criticalExtensions__helper3 :  forall (y : UEPositioningAssistanceInfo_r17__criticalExtensions__Type), UEPositioningAssistanceInfo_r17__criticalExtensions__F2 (UEPositioningAssistanceInfo_r17__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UEPositioningAssistanceInfo_r17__criticalExtensions__helper4 : (forall b : choice UEPositioningAssistanceInfo_r17__criticalExtensions__list, choice_cond UEPositioningAssistanceInfo_r17__criticalExtensions__list b -> UEPositioningAssistanceInfo_r17__criticalExtensions__cond (UEPositioningAssistanceInfo_r17__criticalExtensions__F2 b) /\ UEPositioningAssistanceInfo_r17__criticalExtensions__F1 (UEPositioningAssistanceInfo_r17__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UEPositioningAssistanceInfo_r17__criticalExtensions__F1 UEPositioningAssistanceInfo_r17__criticalExtensions__F2.
Definition UEPositioningAssistanceInfo_r17__criticalExtensions__Format : T_Format UEPositioningAssistanceInfo_r17__criticalExtensions__Type UEPositioningAssistanceInfo_r17__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UEPositioningAssistanceInfo_r17__criticalExtensions__cond UEPositioningAssistanceInfo_r17__criticalExtensions__list__Format UEPositioningAssistanceInfo_r17__criticalExtensions__F1 UEPositioningAssistanceInfo_r17__criticalExtensions__F2 UEPositioningAssistanceInfo_r17__criticalExtensions__helper2 UEPositioningAssistanceInfo_r17__criticalExtensions__helper3 UEPositioningAssistanceInfo_r17__criticalExtensions__helper4.
Opaque UEPositioningAssistanceInfo_r17__criticalExtensions__cond UEPositioningAssistanceInfo_r17__criticalExtensions__Format.


Definition UEPositioningAssistanceInfo_r17__Format_Type := Eval cbn in seq_format_prod UEPositioningAssistanceInfo_r17__list.
Definition UEPositioningAssistanceInfo_r17__Format_list : UEPositioningAssistanceInfo_r17__Format_Type :=
  (UEPositioningAssistanceInfo_r17__criticalExtensions__Format, unit_format).
Definition UEPositioningAssistanceInfo_r17__list__Format := (*Eval compute in *) seq_format UEPositioningAssistanceInfo_r17__list UEPositioningAssistanceInfo_r17__Format_list.
Definition UEPositioningAssistanceInfo_r17__F1 z :=
  (UEPositioningAssistanceInfo_r17__criticalExtensions z, tt).
Definition UEPositioningAssistanceInfo_r17__F2 (y : seq_type UEPositioningAssistanceInfo_r17__list) :=
  match y with
  | (i0, _)=>
    make__UEPositioningAssistanceInfo_r17__Type i0
  end.
Lemma UEPositioningAssistanceInfo_r17__F1F2_cond (z : UEPositioningAssistanceInfo_r17__Type)
  : UEPositioningAssistanceInfo_r17__cond z ->
  (seq_cond UEPositioningAssistanceInfo_r17__list (UEPositioningAssistanceInfo_r17__F1 z)).
intro H. unfold UEPositioningAssistanceInfo_r17__cond in H. simpl. auto. Qed.
Lemma UEPositioningAssistanceInfo_r17__F1F2_cond2 (z : UEPositioningAssistanceInfo_r17__Type)
 : UEPositioningAssistanceInfo_r17__F2 (UEPositioningAssistanceInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEPositioningAssistanceInfo_r17__F2F1_cond (y : seq_type UEPositioningAssistanceInfo_r17__list)
  : seq_cond UEPositioningAssistanceInfo_r17__list y ->
 (UEPositioningAssistanceInfo_r17__cond (UEPositioningAssistanceInfo_r17__F2 y)) /\  UEPositioningAssistanceInfo_r17__F1 (UEPositioningAssistanceInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEPositioningAssistanceInfo_r17__cond. simpl in *. auto.
 - simpl. unfold UEPositioningAssistanceInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEPositioningAssistanceInfo_r17__Format : T_Format UEPositioningAssistanceInfo_r17__Type UEPositioningAssistanceInfo_r17__cond :=
        proj2_format  UEPositioningAssistanceInfo_r17__cond UEPositioningAssistanceInfo_r17__list__Format
    UEPositioningAssistanceInfo_r17__F1 UEPositioningAssistanceInfo_r17__F2 UEPositioningAssistanceInfo_r17__F1F2_cond  UEPositioningAssistanceInfo_r17__F1F2_cond2 UEPositioningAssistanceInfo_r17__F2F1_cond.
Opaque UEPositioningAssistanceInfo_r17__cond UEPositioningAssistanceInfo_r17__Format.

