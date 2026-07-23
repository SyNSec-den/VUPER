Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.UEAssistanceInformationSidelink_r17_IEs.

Opaque UEAssistanceInformationSidelink_r17_IEs__cond UEAssistanceInformationSidelink_r17_IEs__Format.

Record UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond (z : UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UEAssistanceInformationSidelink_r17__criticalExtensions__Type : Set :=
  | UEAssistanceInformationSidelink_r17__criticalExtensions__ueAssistanceInformationSidelink_r17 : UEAssistanceInformationSidelink_r17_IEs__Type -> UEAssistanceInformationSidelink_r17__criticalExtensions__Type
  | UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture : UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type -> UEAssistanceInformationSidelink_r17__criticalExtensions__Type
.
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__list : list typ := (
typ_cons UEAssistanceInformationSidelink_r17_IEs__Type UEAssistanceInformationSidelink_r17_IEs__cond ::
typ_cons UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__cond (c : UEAssistanceInformationSidelink_r17__criticalExtensions__Type) := 
  match c with
  | UEAssistanceInformationSidelink_r17__criticalExtensions__ueAssistanceInformationSidelink_r17 t => UEAssistanceInformationSidelink_r17_IEs__cond t 
  | UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture t => UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UEAssistanceInformationSidelink_r17__criticalExtensions__len_helper1 : to_bit_sz (length UEAssistanceInformationSidelink_r17__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UEAssistanceInformationSidelink_r17__criticalExtensions__len_helper2 : 2 <= length2 UEAssistanceInformationSidelink_r17__criticalExtensions__list.
 simpl. lia. Qed.
Record UEAssistanceInformationSidelink_r17__Type : Set :=
  make__UEAssistanceInformationSidelink_r17__Type {
    UEAssistanceInformationSidelink_r17__criticalExtensions : UEAssistanceInformationSidelink_r17__criticalExtensions__Type ;
}.
Definition UEAssistanceInformationSidelink_r17__list := (
 Nor UEAssistanceInformationSidelink_r17__criticalExtensions__Type UEAssistanceInformationSidelink_r17__criticalExtensions__cond ::
 nil).
Definition UEAssistanceInformationSidelink_r17__cond z := 
  UEAssistanceInformationSidelink_r17__criticalExtensions__cond (UEAssistanceInformationSidelink_r17__criticalExtensions z) /\
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
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__helper : forall a : UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Format : T_Format UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type)
    UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__cond UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Format.


Definition UEAssistanceInformationSidelink_r17__criticalExtensions__Format_Type := Eval cbn in get_formats UEAssistanceInformationSidelink_r17__criticalExtensions__list.
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__Format_list : UEAssistanceInformationSidelink_r17__criticalExtensions__Format_Type :=
  (UEAssistanceInformationSidelink_r17_IEs__Format, (UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__list__Format := Eval compute in choice_format UEAssistanceInformationSidelink_r17__criticalExtensions__list UEAssistanceInformationSidelink_r17__criticalExtensions__len_helper1 UEAssistanceInformationSidelink_r17__criticalExtensions__len_helper2  UEAssistanceInformationSidelink_r17__criticalExtensions__Format_list.
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__F1 (z : UEAssistanceInformationSidelink_r17__criticalExtensions__Type) : (choice UEAssistanceInformationSidelink_r17__criticalExtensions__list) :=
  match z with
   | UEAssistanceInformationSidelink_r17__criticalExtensions__ueAssistanceInformationSidelink_r17 t => existT _ 0 t
  | UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__g := (fun n => typ_set (get_nth_typ UEAssistanceInformationSidelink_r17__criticalExtensions__list n)).
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__F2 (y : choice UEAssistanceInformationSidelink_r17__criticalExtensions__list) : UEAssistanceInformationSidelink_r17__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UEAssistanceInformationSidelink_r17__criticalExtensions__g n -> UEAssistanceInformationSidelink_r17__criticalExtensions__Type) with
    | 0 => fun (t : UEAssistanceInformationSidelink_r17_IEs__Type) => UEAssistanceInformationSidelink_r17__criticalExtensions__ueAssistanceInformationSidelink_r17 t 
    | 1 => fun (t : UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture__Type) => UEAssistanceInformationSidelink_r17__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UEAssistanceInformationSidelink_r17__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UEAssistanceInformationSidelink_r17__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UEAssistanceInformationSidelink_r17__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UEAssistanceInformationSidelink_r17__criticalExtensions__Type with end) n0
           end t0).

Lemma UEAssistanceInformationSidelink_r17__criticalExtensions__helper2 :  forall (y : UEAssistanceInformationSidelink_r17__criticalExtensions__Type), UEAssistanceInformationSidelink_r17__criticalExtensions__cond y -> choice_cond UEAssistanceInformationSidelink_r17__criticalExtensions__list (UEAssistanceInformationSidelink_r17__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UEAssistanceInformationSidelink_r17__criticalExtensions__helper3 :  forall (y : UEAssistanceInformationSidelink_r17__criticalExtensions__Type), UEAssistanceInformationSidelink_r17__criticalExtensions__F2 (UEAssistanceInformationSidelink_r17__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UEAssistanceInformationSidelink_r17__criticalExtensions__helper4 : (forall b : choice UEAssistanceInformationSidelink_r17__criticalExtensions__list, choice_cond UEAssistanceInformationSidelink_r17__criticalExtensions__list b -> UEAssistanceInformationSidelink_r17__criticalExtensions__cond (UEAssistanceInformationSidelink_r17__criticalExtensions__F2 b) /\ UEAssistanceInformationSidelink_r17__criticalExtensions__F1 (UEAssistanceInformationSidelink_r17__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UEAssistanceInformationSidelink_r17__criticalExtensions__F1 UEAssistanceInformationSidelink_r17__criticalExtensions__F2.
Definition UEAssistanceInformationSidelink_r17__criticalExtensions__Format : T_Format UEAssistanceInformationSidelink_r17__criticalExtensions__Type UEAssistanceInformationSidelink_r17__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UEAssistanceInformationSidelink_r17__criticalExtensions__cond UEAssistanceInformationSidelink_r17__criticalExtensions__list__Format UEAssistanceInformationSidelink_r17__criticalExtensions__F1 UEAssistanceInformationSidelink_r17__criticalExtensions__F2 UEAssistanceInformationSidelink_r17__criticalExtensions__helper2 UEAssistanceInformationSidelink_r17__criticalExtensions__helper3 UEAssistanceInformationSidelink_r17__criticalExtensions__helper4.
Opaque UEAssistanceInformationSidelink_r17__criticalExtensions__cond UEAssistanceInformationSidelink_r17__criticalExtensions__Format.


Definition UEAssistanceInformationSidelink_r17__Format_Type := Eval cbn in seq_format_prod UEAssistanceInformationSidelink_r17__list.
Definition UEAssistanceInformationSidelink_r17__Format_list : UEAssistanceInformationSidelink_r17__Format_Type :=
  (UEAssistanceInformationSidelink_r17__criticalExtensions__Format, unit_format).
Definition UEAssistanceInformationSidelink_r17__list__Format := (*Eval compute in *) seq_format UEAssistanceInformationSidelink_r17__list UEAssistanceInformationSidelink_r17__Format_list.
Definition UEAssistanceInformationSidelink_r17__F1 z :=
  (UEAssistanceInformationSidelink_r17__criticalExtensions z, tt).
Definition UEAssistanceInformationSidelink_r17__F2 (y : seq_type UEAssistanceInformationSidelink_r17__list) :=
  match y with
  | (i0, _)=>
    make__UEAssistanceInformationSidelink_r17__Type i0
  end.
Lemma UEAssistanceInformationSidelink_r17__F1F2_cond (z : UEAssistanceInformationSidelink_r17__Type)
  : UEAssistanceInformationSidelink_r17__cond z ->
  (seq_cond UEAssistanceInformationSidelink_r17__list (UEAssistanceInformationSidelink_r17__F1 z)).
intro H. unfold UEAssistanceInformationSidelink_r17__cond in H. simpl. auto. Qed.
Lemma UEAssistanceInformationSidelink_r17__F1F2_cond2 (z : UEAssistanceInformationSidelink_r17__Type)
 : UEAssistanceInformationSidelink_r17__F2 (UEAssistanceInformationSidelink_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEAssistanceInformationSidelink_r17__F2F1_cond (y : seq_type UEAssistanceInformationSidelink_r17__list)
  : seq_cond UEAssistanceInformationSidelink_r17__list y ->
 (UEAssistanceInformationSidelink_r17__cond (UEAssistanceInformationSidelink_r17__F2 y)) /\  UEAssistanceInformationSidelink_r17__F1 (UEAssistanceInformationSidelink_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEAssistanceInformationSidelink_r17__cond. simpl in *. auto.
 - simpl. unfold UEAssistanceInformationSidelink_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEAssistanceInformationSidelink_r17__Format : T_Format UEAssistanceInformationSidelink_r17__Type UEAssistanceInformationSidelink_r17__cond :=
        proj2_format  UEAssistanceInformationSidelink_r17__cond UEAssistanceInformationSidelink_r17__list__Format
    UEAssistanceInformationSidelink_r17__F1 UEAssistanceInformationSidelink_r17__F2 UEAssistanceInformationSidelink_r17__F1F2_cond  UEAssistanceInformationSidelink_r17__F1F2_cond2 UEAssistanceInformationSidelink_r17__F2F1_cond.
Opaque UEAssistanceInformationSidelink_r17__cond UEAssistanceInformationSidelink_r17__Format.

