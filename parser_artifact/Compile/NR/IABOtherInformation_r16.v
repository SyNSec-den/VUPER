Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRC_TransactionIdentifier.

Opaque RRC_TransactionIdentifier__cond RRC_TransactionIdentifier__Format.

Require Import NR.IABOtherInformation_r16_IEs.

Opaque IABOtherInformation_r16_IEs__cond IABOtherInformation_r16_IEs__Format.

Record IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type : Set := make__IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__cond (z : IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive IABOtherInformation_r16__criticalExtensions__Type : Set :=
  | IABOtherInformation_r16__criticalExtensions__iabOtherInformation_r16 : IABOtherInformation_r16_IEs__Type -> IABOtherInformation_r16__criticalExtensions__Type
  | IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture : IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type -> IABOtherInformation_r16__criticalExtensions__Type
.
Definition IABOtherInformation_r16__criticalExtensions__list : list typ := (
typ_cons IABOtherInformation_r16_IEs__Type IABOtherInformation_r16_IEs__cond ::
typ_cons IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition IABOtherInformation_r16__criticalExtensions__cond (c : IABOtherInformation_r16__criticalExtensions__Type) := 
  match c with
  | IABOtherInformation_r16__criticalExtensions__iabOtherInformation_r16 t => IABOtherInformation_r16_IEs__cond t 
  | IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture t => IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma IABOtherInformation_r16__criticalExtensions__len_helper1 : to_bit_sz (length IABOtherInformation_r16__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma IABOtherInformation_r16__criticalExtensions__len_helper2 : 2 <= length2 IABOtherInformation_r16__criticalExtensions__list.
 simpl. lia. Qed.
Record IABOtherInformation_r16__Type : Set :=
  make__IABOtherInformation_r16__Type {
    IABOtherInformation_r16__rrc_TransactionIdentifier : RRC_TransactionIdentifier__Type ;
    IABOtherInformation_r16__criticalExtensions : IABOtherInformation_r16__criticalExtensions__Type ;
}.
Definition IABOtherInformation_r16__list := (
 Nor RRC_TransactionIdentifier__Type RRC_TransactionIdentifier__cond ::
 Nor IABOtherInformation_r16__criticalExtensions__Type IABOtherInformation_r16__criticalExtensions__cond ::
 nil).
Definition IABOtherInformation_r16__cond z := 
  RRC_TransactionIdentifier__cond (IABOtherInformation_r16__rrc_TransactionIdentifier z) /\
  IABOtherInformation_r16__criticalExtensions__cond (IABOtherInformation_r16__criticalExtensions z) /\
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
Definition IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__helper : forall a : IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Format : T_Format IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type)
    IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__cond IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Format.


Definition IABOtherInformation_r16__criticalExtensions__Format_Type := Eval cbn in get_formats IABOtherInformation_r16__criticalExtensions__list.
Definition IABOtherInformation_r16__criticalExtensions__Format_list : IABOtherInformation_r16__criticalExtensions__Format_Type :=
  (IABOtherInformation_r16_IEs__Format, (IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition IABOtherInformation_r16__criticalExtensions__list__Format := Eval compute in choice_format IABOtherInformation_r16__criticalExtensions__list IABOtherInformation_r16__criticalExtensions__len_helper1 IABOtherInformation_r16__criticalExtensions__len_helper2  IABOtherInformation_r16__criticalExtensions__Format_list.
Definition IABOtherInformation_r16__criticalExtensions__F1 (z : IABOtherInformation_r16__criticalExtensions__Type) : (choice IABOtherInformation_r16__criticalExtensions__list) :=
  match z with
   | IABOtherInformation_r16__criticalExtensions__iabOtherInformation_r16 t => existT _ 0 t
  | IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition IABOtherInformation_r16__criticalExtensions__g := (fun n => typ_set (get_nth_typ IABOtherInformation_r16__criticalExtensions__list n)).
Definition IABOtherInformation_r16__criticalExtensions__F2 (y : choice IABOtherInformation_r16__criticalExtensions__list) : IABOtherInformation_r16__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (IABOtherInformation_r16__criticalExtensions__g n -> IABOtherInformation_r16__criticalExtensions__Type) with
    | 0 => fun (t : IABOtherInformation_r16_IEs__Type) => IABOtherInformation_r16__criticalExtensions__iabOtherInformation_r16 t 
    | 1 => fun (t : IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture__Type) => IABOtherInformation_r16__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : IABOtherInformation_r16__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ IABOtherInformation_r16__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len IABOtherInformation_r16__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return IABOtherInformation_r16__criticalExtensions__Type with end) n0
           end t0).

Lemma IABOtherInformation_r16__criticalExtensions__helper2 :  forall (y : IABOtherInformation_r16__criticalExtensions__Type), IABOtherInformation_r16__criticalExtensions__cond y -> choice_cond IABOtherInformation_r16__criticalExtensions__list (IABOtherInformation_r16__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma IABOtherInformation_r16__criticalExtensions__helper3 :  forall (y : IABOtherInformation_r16__criticalExtensions__Type), IABOtherInformation_r16__criticalExtensions__F2 (IABOtherInformation_r16__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma IABOtherInformation_r16__criticalExtensions__helper4 : (forall b : choice IABOtherInformation_r16__criticalExtensions__list, choice_cond IABOtherInformation_r16__criticalExtensions__list b -> IABOtherInformation_r16__criticalExtensions__cond (IABOtherInformation_r16__criticalExtensions__F2 b) /\ IABOtherInformation_r16__criticalExtensions__F1 (IABOtherInformation_r16__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length IABOtherInformation_r16__criticalExtensions__F1 IABOtherInformation_r16__criticalExtensions__F2.
Definition IABOtherInformation_r16__criticalExtensions__Format : T_Format IABOtherInformation_r16__criticalExtensions__Type IABOtherInformation_r16__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format IABOtherInformation_r16__criticalExtensions__cond IABOtherInformation_r16__criticalExtensions__list__Format IABOtherInformation_r16__criticalExtensions__F1 IABOtherInformation_r16__criticalExtensions__F2 IABOtherInformation_r16__criticalExtensions__helper2 IABOtherInformation_r16__criticalExtensions__helper3 IABOtherInformation_r16__criticalExtensions__helper4.
Opaque IABOtherInformation_r16__criticalExtensions__cond IABOtherInformation_r16__criticalExtensions__Format.


Definition IABOtherInformation_r16__Format_Type := Eval cbn in seq_format_prod IABOtherInformation_r16__list.
Definition IABOtherInformation_r16__Format_list : IABOtherInformation_r16__Format_Type :=
  (RRC_TransactionIdentifier__Format, (IABOtherInformation_r16__criticalExtensions__Format, unit_format)).
Definition IABOtherInformation_r16__list__Format := (*Eval compute in *) seq_format IABOtherInformation_r16__list IABOtherInformation_r16__Format_list.
Definition IABOtherInformation_r16__F1 z :=
  (IABOtherInformation_r16__rrc_TransactionIdentifier z, (IABOtherInformation_r16__criticalExtensions z, tt)).
Definition IABOtherInformation_r16__F2 (y : seq_type IABOtherInformation_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__IABOtherInformation_r16__Type i0 i1
  end.
Lemma IABOtherInformation_r16__F1F2_cond (z : IABOtherInformation_r16__Type)
  : IABOtherInformation_r16__cond z ->
  (seq_cond IABOtherInformation_r16__list (IABOtherInformation_r16__F1 z)).
intro H. unfold IABOtherInformation_r16__cond in H. simpl. auto. Qed.
Lemma IABOtherInformation_r16__F1F2_cond2 (z : IABOtherInformation_r16__Type)
 : IABOtherInformation_r16__F2 (IABOtherInformation_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma IABOtherInformation_r16__F2F1_cond (y : seq_type IABOtherInformation_r16__list)
  : seq_cond IABOtherInformation_r16__list y ->
 (IABOtherInformation_r16__cond (IABOtherInformation_r16__F2 y)) /\  IABOtherInformation_r16__F1 (IABOtherInformation_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold IABOtherInformation_r16__cond. simpl in *. auto.
 - simpl. unfold IABOtherInformation_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition IABOtherInformation_r16__Format : T_Format IABOtherInformation_r16__Type IABOtherInformation_r16__cond :=
        proj2_format  IABOtherInformation_r16__cond IABOtherInformation_r16__list__Format
    IABOtherInformation_r16__F1 IABOtherInformation_r16__F2 IABOtherInformation_r16__F1F2_cond  IABOtherInformation_r16__F1F2_cond2 IABOtherInformation_r16__F2F1_cond.
Opaque IABOtherInformation_r16__cond IABOtherInformation_r16__Format.

