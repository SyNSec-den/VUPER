Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DedicatedSIBRequest_r16_IEs.

Opaque DedicatedSIBRequest_r16_IEs__cond DedicatedSIBRequest_r16_IEs__Format.

Record DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type : Set := make__DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__cond (z : DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive DedicatedSIBRequest_r16__criticalExtensions__Type : Set :=
  | DedicatedSIBRequest_r16__criticalExtensions__dedicatedSIBRequest_r16 : DedicatedSIBRequest_r16_IEs__Type -> DedicatedSIBRequest_r16__criticalExtensions__Type
  | DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture : DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type -> DedicatedSIBRequest_r16__criticalExtensions__Type
.
Definition DedicatedSIBRequest_r16__criticalExtensions__list : list typ := (
typ_cons DedicatedSIBRequest_r16_IEs__Type DedicatedSIBRequest_r16_IEs__cond ::
typ_cons DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition DedicatedSIBRequest_r16__criticalExtensions__cond (c : DedicatedSIBRequest_r16__criticalExtensions__Type) := 
  match c with
  | DedicatedSIBRequest_r16__criticalExtensions__dedicatedSIBRequest_r16 t => DedicatedSIBRequest_r16_IEs__cond t 
  | DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture t => DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma DedicatedSIBRequest_r16__criticalExtensions__len_helper1 : to_bit_sz (length DedicatedSIBRequest_r16__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DedicatedSIBRequest_r16__criticalExtensions__len_helper2 : 2 <= length2 DedicatedSIBRequest_r16__criticalExtensions__list.
 simpl. lia. Qed.
Record DedicatedSIBRequest_r16__Type : Set :=
  make__DedicatedSIBRequest_r16__Type {
    DedicatedSIBRequest_r16__criticalExtensions : DedicatedSIBRequest_r16__criticalExtensions__Type ;
}.
Definition DedicatedSIBRequest_r16__list := (
 Nor DedicatedSIBRequest_r16__criticalExtensions__Type DedicatedSIBRequest_r16__criticalExtensions__cond ::
 nil).
Definition DedicatedSIBRequest_r16__cond z := 
  DedicatedSIBRequest_r16__criticalExtensions__cond (DedicatedSIBRequest_r16__criticalExtensions z) /\
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
Definition DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__helper : forall a : DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Format : T_Format DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type)
    DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__cond DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Format.


Definition DedicatedSIBRequest_r16__criticalExtensions__Format_Type := Eval cbn in get_formats DedicatedSIBRequest_r16__criticalExtensions__list.
Definition DedicatedSIBRequest_r16__criticalExtensions__Format_list : DedicatedSIBRequest_r16__criticalExtensions__Format_Type :=
  (DedicatedSIBRequest_r16_IEs__Format, (DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition DedicatedSIBRequest_r16__criticalExtensions__list__Format := Eval compute in choice_format DedicatedSIBRequest_r16__criticalExtensions__list DedicatedSIBRequest_r16__criticalExtensions__len_helper1 DedicatedSIBRequest_r16__criticalExtensions__len_helper2  DedicatedSIBRequest_r16__criticalExtensions__Format_list.
Definition DedicatedSIBRequest_r16__criticalExtensions__F1 (z : DedicatedSIBRequest_r16__criticalExtensions__Type) : (choice DedicatedSIBRequest_r16__criticalExtensions__list) :=
  match z with
   | DedicatedSIBRequest_r16__criticalExtensions__dedicatedSIBRequest_r16 t => existT _ 0 t
  | DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition DedicatedSIBRequest_r16__criticalExtensions__g := (fun n => typ_set (get_nth_typ DedicatedSIBRequest_r16__criticalExtensions__list n)).
Definition DedicatedSIBRequest_r16__criticalExtensions__F2 (y : choice DedicatedSIBRequest_r16__criticalExtensions__list) : DedicatedSIBRequest_r16__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DedicatedSIBRequest_r16__criticalExtensions__g n -> DedicatedSIBRequest_r16__criticalExtensions__Type) with
    | 0 => fun (t : DedicatedSIBRequest_r16_IEs__Type) => DedicatedSIBRequest_r16__criticalExtensions__dedicatedSIBRequest_r16 t 
    | 1 => fun (t : DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture__Type) => DedicatedSIBRequest_r16__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : DedicatedSIBRequest_r16__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ DedicatedSIBRequest_r16__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DedicatedSIBRequest_r16__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return DedicatedSIBRequest_r16__criticalExtensions__Type with end) n0
           end t0).

Lemma DedicatedSIBRequest_r16__criticalExtensions__helper2 :  forall (y : DedicatedSIBRequest_r16__criticalExtensions__Type), DedicatedSIBRequest_r16__criticalExtensions__cond y -> choice_cond DedicatedSIBRequest_r16__criticalExtensions__list (DedicatedSIBRequest_r16__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DedicatedSIBRequest_r16__criticalExtensions__helper3 :  forall (y : DedicatedSIBRequest_r16__criticalExtensions__Type), DedicatedSIBRequest_r16__criticalExtensions__F2 (DedicatedSIBRequest_r16__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DedicatedSIBRequest_r16__criticalExtensions__helper4 : (forall b : choice DedicatedSIBRequest_r16__criticalExtensions__list, choice_cond DedicatedSIBRequest_r16__criticalExtensions__list b -> DedicatedSIBRequest_r16__criticalExtensions__cond (DedicatedSIBRequest_r16__criticalExtensions__F2 b) /\ DedicatedSIBRequest_r16__criticalExtensions__F1 (DedicatedSIBRequest_r16__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DedicatedSIBRequest_r16__criticalExtensions__F1 DedicatedSIBRequest_r16__criticalExtensions__F2.
Definition DedicatedSIBRequest_r16__criticalExtensions__Format : T_Format DedicatedSIBRequest_r16__criticalExtensions__Type DedicatedSIBRequest_r16__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format DedicatedSIBRequest_r16__criticalExtensions__cond DedicatedSIBRequest_r16__criticalExtensions__list__Format DedicatedSIBRequest_r16__criticalExtensions__F1 DedicatedSIBRequest_r16__criticalExtensions__F2 DedicatedSIBRequest_r16__criticalExtensions__helper2 DedicatedSIBRequest_r16__criticalExtensions__helper3 DedicatedSIBRequest_r16__criticalExtensions__helper4.
Opaque DedicatedSIBRequest_r16__criticalExtensions__cond DedicatedSIBRequest_r16__criticalExtensions__Format.


Definition DedicatedSIBRequest_r16__Format_Type := Eval cbn in seq_format_prod DedicatedSIBRequest_r16__list.
Definition DedicatedSIBRequest_r16__Format_list : DedicatedSIBRequest_r16__Format_Type :=
  (DedicatedSIBRequest_r16__criticalExtensions__Format, unit_format).
Definition DedicatedSIBRequest_r16__list__Format := (*Eval compute in *) seq_format DedicatedSIBRequest_r16__list DedicatedSIBRequest_r16__Format_list.
Definition DedicatedSIBRequest_r16__F1 z :=
  (DedicatedSIBRequest_r16__criticalExtensions z, tt).
Definition DedicatedSIBRequest_r16__F2 (y : seq_type DedicatedSIBRequest_r16__list) :=
  match y with
  | (i0, _)=>
    make__DedicatedSIBRequest_r16__Type i0
  end.
Lemma DedicatedSIBRequest_r16__F1F2_cond (z : DedicatedSIBRequest_r16__Type)
  : DedicatedSIBRequest_r16__cond z ->
  (seq_cond DedicatedSIBRequest_r16__list (DedicatedSIBRequest_r16__F1 z)).
intro H. unfold DedicatedSIBRequest_r16__cond in H. simpl. auto. Qed.
Lemma DedicatedSIBRequest_r16__F1F2_cond2 (z : DedicatedSIBRequest_r16__Type)
 : DedicatedSIBRequest_r16__F2 (DedicatedSIBRequest_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DedicatedSIBRequest_r16__F2F1_cond (y : seq_type DedicatedSIBRequest_r16__list)
  : seq_cond DedicatedSIBRequest_r16__list y ->
 (DedicatedSIBRequest_r16__cond (DedicatedSIBRequest_r16__F2 y)) /\  DedicatedSIBRequest_r16__F1 (DedicatedSIBRequest_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DedicatedSIBRequest_r16__cond. simpl in *. auto.
 - simpl. unfold DedicatedSIBRequest_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DedicatedSIBRequest_r16__Format : T_Format DedicatedSIBRequest_r16__Type DedicatedSIBRequest_r16__cond :=
        proj2_format  DedicatedSIBRequest_r16__cond DedicatedSIBRequest_r16__list__Format
    DedicatedSIBRequest_r16__F1 DedicatedSIBRequest_r16__F2 DedicatedSIBRequest_r16__F1F2_cond  DedicatedSIBRequest_r16__F1F2_cond2 DedicatedSIBRequest_r16__F2F1_cond.
Opaque DedicatedSIBRequest_r16__cond DedicatedSIBRequest_r16__Format.

