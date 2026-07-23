Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DLDedicatedMessageSegment_r16_IEs.

Opaque DLDedicatedMessageSegment_r16_IEs__cond DLDedicatedMessageSegment_r16_IEs__Format.

Record DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type : Set := make__DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond (z : DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive DLDedicatedMessageSegment_r16__criticalExtensions__Type : Set :=
  | DLDedicatedMessageSegment_r16__criticalExtensions__dlDedicatedMessageSegment_r16 : DLDedicatedMessageSegment_r16_IEs__Type -> DLDedicatedMessageSegment_r16__criticalExtensions__Type
  | DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture : DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type -> DLDedicatedMessageSegment_r16__criticalExtensions__Type
.
Definition DLDedicatedMessageSegment_r16__criticalExtensions__list : list typ := (
typ_cons DLDedicatedMessageSegment_r16_IEs__Type DLDedicatedMessageSegment_r16_IEs__cond ::
typ_cons DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition DLDedicatedMessageSegment_r16__criticalExtensions__cond (c : DLDedicatedMessageSegment_r16__criticalExtensions__Type) := 
  match c with
  | DLDedicatedMessageSegment_r16__criticalExtensions__dlDedicatedMessageSegment_r16 t => DLDedicatedMessageSegment_r16_IEs__cond t 
  | DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture t => DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma DLDedicatedMessageSegment_r16__criticalExtensions__len_helper1 : to_bit_sz (length DLDedicatedMessageSegment_r16__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DLDedicatedMessageSegment_r16__criticalExtensions__len_helper2 : 2 <= length2 DLDedicatedMessageSegment_r16__criticalExtensions__list.
 simpl. lia. Qed.
Record DLDedicatedMessageSegment_r16__Type : Set :=
  make__DLDedicatedMessageSegment_r16__Type {
    DLDedicatedMessageSegment_r16__criticalExtensions : DLDedicatedMessageSegment_r16__criticalExtensions__Type ;
}.
Definition DLDedicatedMessageSegment_r16__list := (
 Nor DLDedicatedMessageSegment_r16__criticalExtensions__Type DLDedicatedMessageSegment_r16__criticalExtensions__cond ::
 nil).
Definition DLDedicatedMessageSegment_r16__cond z := 
  DLDedicatedMessageSegment_r16__criticalExtensions__cond (DLDedicatedMessageSegment_r16__criticalExtensions z) /\
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
Definition DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__helper : forall a : DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Format : T_Format DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type)
    DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__cond DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Format.


Definition DLDedicatedMessageSegment_r16__criticalExtensions__Format_Type := Eval cbn in get_formats DLDedicatedMessageSegment_r16__criticalExtensions__list.
Definition DLDedicatedMessageSegment_r16__criticalExtensions__Format_list : DLDedicatedMessageSegment_r16__criticalExtensions__Format_Type :=
  (DLDedicatedMessageSegment_r16_IEs__Format, (DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition DLDedicatedMessageSegment_r16__criticalExtensions__list__Format := Eval compute in choice_format DLDedicatedMessageSegment_r16__criticalExtensions__list DLDedicatedMessageSegment_r16__criticalExtensions__len_helper1 DLDedicatedMessageSegment_r16__criticalExtensions__len_helper2  DLDedicatedMessageSegment_r16__criticalExtensions__Format_list.
Definition DLDedicatedMessageSegment_r16__criticalExtensions__F1 (z : DLDedicatedMessageSegment_r16__criticalExtensions__Type) : (choice DLDedicatedMessageSegment_r16__criticalExtensions__list) :=
  match z with
   | DLDedicatedMessageSegment_r16__criticalExtensions__dlDedicatedMessageSegment_r16 t => existT _ 0 t
  | DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition DLDedicatedMessageSegment_r16__criticalExtensions__g := (fun n => typ_set (get_nth_typ DLDedicatedMessageSegment_r16__criticalExtensions__list n)).
Definition DLDedicatedMessageSegment_r16__criticalExtensions__F2 (y : choice DLDedicatedMessageSegment_r16__criticalExtensions__list) : DLDedicatedMessageSegment_r16__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DLDedicatedMessageSegment_r16__criticalExtensions__g n -> DLDedicatedMessageSegment_r16__criticalExtensions__Type) with
    | 0 => fun (t : DLDedicatedMessageSegment_r16_IEs__Type) => DLDedicatedMessageSegment_r16__criticalExtensions__dlDedicatedMessageSegment_r16 t 
    | 1 => fun (t : DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture__Type) => DLDedicatedMessageSegment_r16__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : DLDedicatedMessageSegment_r16__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ DLDedicatedMessageSegment_r16__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DLDedicatedMessageSegment_r16__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return DLDedicatedMessageSegment_r16__criticalExtensions__Type with end) n0
           end t0).

Lemma DLDedicatedMessageSegment_r16__criticalExtensions__helper2 :  forall (y : DLDedicatedMessageSegment_r16__criticalExtensions__Type), DLDedicatedMessageSegment_r16__criticalExtensions__cond y -> choice_cond DLDedicatedMessageSegment_r16__criticalExtensions__list (DLDedicatedMessageSegment_r16__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DLDedicatedMessageSegment_r16__criticalExtensions__helper3 :  forall (y : DLDedicatedMessageSegment_r16__criticalExtensions__Type), DLDedicatedMessageSegment_r16__criticalExtensions__F2 (DLDedicatedMessageSegment_r16__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DLDedicatedMessageSegment_r16__criticalExtensions__helper4 : (forall b : choice DLDedicatedMessageSegment_r16__criticalExtensions__list, choice_cond DLDedicatedMessageSegment_r16__criticalExtensions__list b -> DLDedicatedMessageSegment_r16__criticalExtensions__cond (DLDedicatedMessageSegment_r16__criticalExtensions__F2 b) /\ DLDedicatedMessageSegment_r16__criticalExtensions__F1 (DLDedicatedMessageSegment_r16__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DLDedicatedMessageSegment_r16__criticalExtensions__F1 DLDedicatedMessageSegment_r16__criticalExtensions__F2.
Definition DLDedicatedMessageSegment_r16__criticalExtensions__Format : T_Format DLDedicatedMessageSegment_r16__criticalExtensions__Type DLDedicatedMessageSegment_r16__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format DLDedicatedMessageSegment_r16__criticalExtensions__cond DLDedicatedMessageSegment_r16__criticalExtensions__list__Format DLDedicatedMessageSegment_r16__criticalExtensions__F1 DLDedicatedMessageSegment_r16__criticalExtensions__F2 DLDedicatedMessageSegment_r16__criticalExtensions__helper2 DLDedicatedMessageSegment_r16__criticalExtensions__helper3 DLDedicatedMessageSegment_r16__criticalExtensions__helper4.
Opaque DLDedicatedMessageSegment_r16__criticalExtensions__cond DLDedicatedMessageSegment_r16__criticalExtensions__Format.


Definition DLDedicatedMessageSegment_r16__Format_Type := Eval cbn in seq_format_prod DLDedicatedMessageSegment_r16__list.
Definition DLDedicatedMessageSegment_r16__Format_list : DLDedicatedMessageSegment_r16__Format_Type :=
  (DLDedicatedMessageSegment_r16__criticalExtensions__Format, unit_format).
Definition DLDedicatedMessageSegment_r16__list__Format := (*Eval compute in *) seq_format DLDedicatedMessageSegment_r16__list DLDedicatedMessageSegment_r16__Format_list.
Definition DLDedicatedMessageSegment_r16__F1 z :=
  (DLDedicatedMessageSegment_r16__criticalExtensions z, tt).
Definition DLDedicatedMessageSegment_r16__F2 (y : seq_type DLDedicatedMessageSegment_r16__list) :=
  match y with
  | (i0, _)=>
    make__DLDedicatedMessageSegment_r16__Type i0
  end.
Lemma DLDedicatedMessageSegment_r16__F1F2_cond (z : DLDedicatedMessageSegment_r16__Type)
  : DLDedicatedMessageSegment_r16__cond z ->
  (seq_cond DLDedicatedMessageSegment_r16__list (DLDedicatedMessageSegment_r16__F1 z)).
intro H. unfold DLDedicatedMessageSegment_r16__cond in H. simpl. auto. Qed.
Lemma DLDedicatedMessageSegment_r16__F1F2_cond2 (z : DLDedicatedMessageSegment_r16__Type)
 : DLDedicatedMessageSegment_r16__F2 (DLDedicatedMessageSegment_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DLDedicatedMessageSegment_r16__F2F1_cond (y : seq_type DLDedicatedMessageSegment_r16__list)
  : seq_cond DLDedicatedMessageSegment_r16__list y ->
 (DLDedicatedMessageSegment_r16__cond (DLDedicatedMessageSegment_r16__F2 y)) /\  DLDedicatedMessageSegment_r16__F1 (DLDedicatedMessageSegment_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DLDedicatedMessageSegment_r16__cond. simpl in *. auto.
 - simpl. unfold DLDedicatedMessageSegment_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DLDedicatedMessageSegment_r16__Format : T_Format DLDedicatedMessageSegment_r16__Type DLDedicatedMessageSegment_r16__cond :=
        proj2_format  DLDedicatedMessageSegment_r16__cond DLDedicatedMessageSegment_r16__list__Format
    DLDedicatedMessageSegment_r16__F1 DLDedicatedMessageSegment_r16__F2 DLDedicatedMessageSegment_r16__F1F2_cond  DLDedicatedMessageSegment_r16__F1F2_cond2 DLDedicatedMessageSegment_r16__F2F1_cond.
Opaque DLDedicatedMessageSegment_r16__cond DLDedicatedMessageSegment_r16__Format.

