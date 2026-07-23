Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.UEAssistanceInformation_IEs.

Opaque UEAssistanceInformation_IEs__cond UEAssistanceInformation_IEs__Format.

Record UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__cond (z : UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UEAssistanceInformation__criticalExtensions__Type : Set :=
  | UEAssistanceInformation__criticalExtensions__ueAssistanceInformation : UEAssistanceInformation_IEs__Type -> UEAssistanceInformation__criticalExtensions__Type
  | UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture : UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type -> UEAssistanceInformation__criticalExtensions__Type
.
Definition UEAssistanceInformation__criticalExtensions__list : list typ := (
typ_cons UEAssistanceInformation_IEs__Type UEAssistanceInformation_IEs__cond ::
typ_cons UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UEAssistanceInformation__criticalExtensions__cond (c : UEAssistanceInformation__criticalExtensions__Type) := 
  match c with
  | UEAssistanceInformation__criticalExtensions__ueAssistanceInformation t => UEAssistanceInformation_IEs__cond t 
  | UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture t => UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UEAssistanceInformation__criticalExtensions__len_helper1 : to_bit_sz (length UEAssistanceInformation__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UEAssistanceInformation__criticalExtensions__len_helper2 : 2 <= length2 UEAssistanceInformation__criticalExtensions__list.
 simpl. lia. Qed.
Record UEAssistanceInformation__Type : Set :=
  make__UEAssistanceInformation__Type {
    UEAssistanceInformation__criticalExtensions : UEAssistanceInformation__criticalExtensions__Type ;
}.
Definition UEAssistanceInformation__list := (
 Nor UEAssistanceInformation__criticalExtensions__Type UEAssistanceInformation__criticalExtensions__cond ::
 nil).
Definition UEAssistanceInformation__cond z := 
  UEAssistanceInformation__criticalExtensions__cond (UEAssistanceInformation__criticalExtensions z) /\
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
Definition UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__helper : forall a : UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Format : T_Format UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type)
    UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__cond UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Format.


Definition UEAssistanceInformation__criticalExtensions__Format_Type := Eval cbn in get_formats UEAssistanceInformation__criticalExtensions__list.
Definition UEAssistanceInformation__criticalExtensions__Format_list : UEAssistanceInformation__criticalExtensions__Format_Type :=
  (UEAssistanceInformation_IEs__Format, (UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UEAssistanceInformation__criticalExtensions__list__Format := Eval compute in choice_format UEAssistanceInformation__criticalExtensions__list UEAssistanceInformation__criticalExtensions__len_helper1 UEAssistanceInformation__criticalExtensions__len_helper2  UEAssistanceInformation__criticalExtensions__Format_list.
Definition UEAssistanceInformation__criticalExtensions__F1 (z : UEAssistanceInformation__criticalExtensions__Type) : (choice UEAssistanceInformation__criticalExtensions__list) :=
  match z with
   | UEAssistanceInformation__criticalExtensions__ueAssistanceInformation t => existT _ 0 t
  | UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UEAssistanceInformation__criticalExtensions__g := (fun n => typ_set (get_nth_typ UEAssistanceInformation__criticalExtensions__list n)).
Definition UEAssistanceInformation__criticalExtensions__F2 (y : choice UEAssistanceInformation__criticalExtensions__list) : UEAssistanceInformation__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UEAssistanceInformation__criticalExtensions__g n -> UEAssistanceInformation__criticalExtensions__Type) with
    | 0 => fun (t : UEAssistanceInformation_IEs__Type) => UEAssistanceInformation__criticalExtensions__ueAssistanceInformation t 
    | 1 => fun (t : UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture__Type) => UEAssistanceInformation__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UEAssistanceInformation__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UEAssistanceInformation__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UEAssistanceInformation__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UEAssistanceInformation__criticalExtensions__Type with end) n0
           end t0).

Lemma UEAssistanceInformation__criticalExtensions__helper2 :  forall (y : UEAssistanceInformation__criticalExtensions__Type), UEAssistanceInformation__criticalExtensions__cond y -> choice_cond UEAssistanceInformation__criticalExtensions__list (UEAssistanceInformation__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UEAssistanceInformation__criticalExtensions__helper3 :  forall (y : UEAssistanceInformation__criticalExtensions__Type), UEAssistanceInformation__criticalExtensions__F2 (UEAssistanceInformation__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UEAssistanceInformation__criticalExtensions__helper4 : (forall b : choice UEAssistanceInformation__criticalExtensions__list, choice_cond UEAssistanceInformation__criticalExtensions__list b -> UEAssistanceInformation__criticalExtensions__cond (UEAssistanceInformation__criticalExtensions__F2 b) /\ UEAssistanceInformation__criticalExtensions__F1 (UEAssistanceInformation__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UEAssistanceInformation__criticalExtensions__F1 UEAssistanceInformation__criticalExtensions__F2.
Definition UEAssistanceInformation__criticalExtensions__Format : T_Format UEAssistanceInformation__criticalExtensions__Type UEAssistanceInformation__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UEAssistanceInformation__criticalExtensions__cond UEAssistanceInformation__criticalExtensions__list__Format UEAssistanceInformation__criticalExtensions__F1 UEAssistanceInformation__criticalExtensions__F2 UEAssistanceInformation__criticalExtensions__helper2 UEAssistanceInformation__criticalExtensions__helper3 UEAssistanceInformation__criticalExtensions__helper4.
Opaque UEAssistanceInformation__criticalExtensions__cond UEAssistanceInformation__criticalExtensions__Format.


Definition UEAssistanceInformation__Format_Type := Eval cbn in seq_format_prod UEAssistanceInformation__list.
Definition UEAssistanceInformation__Format_list : UEAssistanceInformation__Format_Type :=
  (UEAssistanceInformation__criticalExtensions__Format, unit_format).
Definition UEAssistanceInformation__list__Format := (*Eval compute in *) seq_format UEAssistanceInformation__list UEAssistanceInformation__Format_list.
Definition UEAssistanceInformation__F1 z :=
  (UEAssistanceInformation__criticalExtensions z, tt).
Definition UEAssistanceInformation__F2 (y : seq_type UEAssistanceInformation__list) :=
  match y with
  | (i0, _)=>
    make__UEAssistanceInformation__Type i0
  end.
Lemma UEAssistanceInformation__F1F2_cond (z : UEAssistanceInformation__Type)
  : UEAssistanceInformation__cond z ->
  (seq_cond UEAssistanceInformation__list (UEAssistanceInformation__F1 z)).
intro H. unfold UEAssistanceInformation__cond in H. simpl. auto. Qed.
Lemma UEAssistanceInformation__F1F2_cond2 (z : UEAssistanceInformation__Type)
 : UEAssistanceInformation__F2 (UEAssistanceInformation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEAssistanceInformation__F2F1_cond (y : seq_type UEAssistanceInformation__list)
  : seq_cond UEAssistanceInformation__list y ->
 (UEAssistanceInformation__cond (UEAssistanceInformation__F2 y)) /\  UEAssistanceInformation__F1 (UEAssistanceInformation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEAssistanceInformation__cond. simpl in *. auto.
 - simpl. unfold UEAssistanceInformation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEAssistanceInformation__Format : T_Format UEAssistanceInformation__Type UEAssistanceInformation__cond :=
        proj2_format  UEAssistanceInformation__cond UEAssistanceInformation__list__Format
    UEAssistanceInformation__F1 UEAssistanceInformation__F2 UEAssistanceInformation__F1F2_cond  UEAssistanceInformation__F1F2_cond2 UEAssistanceInformation__F2F1_cond.
Opaque UEAssistanceInformation__cond UEAssistanceInformation__Format.

