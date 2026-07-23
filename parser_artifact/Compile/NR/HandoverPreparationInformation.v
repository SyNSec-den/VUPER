Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.HandoverPreparationInformation_IEs.

Opaque HandoverPreparationInformation_IEs__cond HandoverPreparationInformation_IEs__Format.


Inductive HandoverPreparationInformation__criticalExtensions__c1__Type : Set :=
  | HandoverPreparationInformation__criticalExtensions__c1__handoverPreparationInformation : HandoverPreparationInformation_IEs__Type -> HandoverPreparationInformation__criticalExtensions__c1__Type
  | HandoverPreparationInformation__criticalExtensions__c1__spare3 : unit -> HandoverPreparationInformation__criticalExtensions__c1__Type
  | HandoverPreparationInformation__criticalExtensions__c1__spare2 : unit -> HandoverPreparationInformation__criticalExtensions__c1__Type
  | HandoverPreparationInformation__criticalExtensions__c1__spare1 : unit -> HandoverPreparationInformation__criticalExtensions__c1__Type
.
Definition HandoverPreparationInformation__criticalExtensions__c1__list : list typ := (
typ_cons HandoverPreparationInformation_IEs__Type HandoverPreparationInformation_IEs__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition HandoverPreparationInformation__criticalExtensions__c1__cond (c : HandoverPreparationInformation__criticalExtensions__c1__Type) := 
  match c with
  | HandoverPreparationInformation__criticalExtensions__c1__handoverPreparationInformation t => HandoverPreparationInformation_IEs__cond t 
  | HandoverPreparationInformation__criticalExtensions__c1__spare3 t => (fun _ => True) t 
  | HandoverPreparationInformation__criticalExtensions__c1__spare2 t => (fun _ => True) t 
  | HandoverPreparationInformation__criticalExtensions__c1__spare1 t => (fun _ => True) t 
  end.

Lemma HandoverPreparationInformation__criticalExtensions__c1__len_helper1 : to_bit_sz (length HandoverPreparationInformation__criticalExtensions__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma HandoverPreparationInformation__criticalExtensions__c1__len_helper2 : 2 <= length2 HandoverPreparationInformation__criticalExtensions__c1__list.
 simpl. lia. Qed.
Record HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type : Set := make__HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__cond (z : HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive HandoverPreparationInformation__criticalExtensions__Type : Set :=
  | HandoverPreparationInformation__criticalExtensions__c1 : HandoverPreparationInformation__criticalExtensions__c1__Type -> HandoverPreparationInformation__criticalExtensions__Type
  | HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture : HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type -> HandoverPreparationInformation__criticalExtensions__Type
.
Definition HandoverPreparationInformation__criticalExtensions__list : list typ := (
typ_cons HandoverPreparationInformation__criticalExtensions__c1__Type HandoverPreparationInformation__criticalExtensions__c1__cond ::
typ_cons HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition HandoverPreparationInformation__criticalExtensions__cond (c : HandoverPreparationInformation__criticalExtensions__Type) := 
  match c with
  | HandoverPreparationInformation__criticalExtensions__c1 t => HandoverPreparationInformation__criticalExtensions__c1__cond t 
  | HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture t => HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma HandoverPreparationInformation__criticalExtensions__len_helper1 : to_bit_sz (length HandoverPreparationInformation__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma HandoverPreparationInformation__criticalExtensions__len_helper2 : 2 <= length2 HandoverPreparationInformation__criticalExtensions__list.
 simpl. lia. Qed.
Record HandoverPreparationInformation__Type : Set :=
  make__HandoverPreparationInformation__Type {
    HandoverPreparationInformation__criticalExtensions : HandoverPreparationInformation__criticalExtensions__Type ;
}.
Definition HandoverPreparationInformation__list := (
 Nor HandoverPreparationInformation__criticalExtensions__Type HandoverPreparationInformation__criticalExtensions__cond ::
 nil).
Definition HandoverPreparationInformation__cond z := 
  HandoverPreparationInformation__criticalExtensions__cond (HandoverPreparationInformation__criticalExtensions z) /\
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

Definition HandoverPreparationInformation__criticalExtensions__c1__Format_Type := Eval cbn in get_formats HandoverPreparationInformation__criticalExtensions__c1__list.
Definition HandoverPreparationInformation__criticalExtensions__c1__Format_list : HandoverPreparationInformation__criticalExtensions__c1__Format_Type :=
  (HandoverPreparationInformation_IEs__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))).
Definition HandoverPreparationInformation__criticalExtensions__c1__list__Format := Eval compute in choice_format HandoverPreparationInformation__criticalExtensions__c1__list HandoverPreparationInformation__criticalExtensions__c1__len_helper1 HandoverPreparationInformation__criticalExtensions__c1__len_helper2  HandoverPreparationInformation__criticalExtensions__c1__Format_list.
Definition HandoverPreparationInformation__criticalExtensions__c1__F1 (z : HandoverPreparationInformation__criticalExtensions__c1__Type) : (choice HandoverPreparationInformation__criticalExtensions__c1__list) :=
  match z with
   | HandoverPreparationInformation__criticalExtensions__c1__handoverPreparationInformation t => existT _ 0 t
  | HandoverPreparationInformation__criticalExtensions__c1__spare3 t => existT _ 1 t
  | HandoverPreparationInformation__criticalExtensions__c1__spare2 t => existT _ 2 t
  | HandoverPreparationInformation__criticalExtensions__c1__spare1 t => existT _ 3 t
  end.
Definition HandoverPreparationInformation__criticalExtensions__c1__g := (fun n => typ_set (get_nth_typ HandoverPreparationInformation__criticalExtensions__c1__list n)).
Definition HandoverPreparationInformation__criticalExtensions__c1__F2 (y : choice HandoverPreparationInformation__criticalExtensions__c1__list) : HandoverPreparationInformation__criticalExtensions__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (HandoverPreparationInformation__criticalExtensions__c1__g n -> HandoverPreparationInformation__criticalExtensions__c1__Type) with
    | 0 => fun (t : HandoverPreparationInformation_IEs__Type) => HandoverPreparationInformation__criticalExtensions__c1__handoverPreparationInformation t 
    | 1 => fun (t : unit) => HandoverPreparationInformation__criticalExtensions__c1__spare3 t 
    | 2 => fun (t : unit) => HandoverPreparationInformation__criticalExtensions__c1__spare2 t 
    | 3 => fun (t : unit) => HandoverPreparationInformation__criticalExtensions__c1__spare1 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : HandoverPreparationInformation__criticalExtensions__c1__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ HandoverPreparationInformation__criticalExtensions__c1__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len HandoverPreparationInformation__criticalExtensions__c1__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return HandoverPreparationInformation__criticalExtensions__c1__Type with end) n0
           end t0).

Lemma HandoverPreparationInformation__criticalExtensions__c1__helper2 :  forall (y : HandoverPreparationInformation__criticalExtensions__c1__Type), HandoverPreparationInformation__criticalExtensions__c1__cond y -> choice_cond HandoverPreparationInformation__criticalExtensions__c1__list (HandoverPreparationInformation__criticalExtensions__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma HandoverPreparationInformation__criticalExtensions__c1__helper3 :  forall (y : HandoverPreparationInformation__criticalExtensions__c1__Type), HandoverPreparationInformation__criticalExtensions__c1__F2 (HandoverPreparationInformation__criticalExtensions__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma HandoverPreparationInformation__criticalExtensions__c1__helper4 : (forall b : choice HandoverPreparationInformation__criticalExtensions__c1__list, choice_cond HandoverPreparationInformation__criticalExtensions__c1__list b -> HandoverPreparationInformation__criticalExtensions__c1__cond (HandoverPreparationInformation__criticalExtensions__c1__F2 b) /\ HandoverPreparationInformation__criticalExtensions__c1__F1 (HandoverPreparationInformation__criticalExtensions__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length HandoverPreparationInformation__criticalExtensions__c1__F1 HandoverPreparationInformation__criticalExtensions__c1__F2.
Definition HandoverPreparationInformation__criticalExtensions__c1__Format : T_Format HandoverPreparationInformation__criticalExtensions__c1__Type HandoverPreparationInformation__criticalExtensions__c1__cond :=
  (* Eval compute in *) proj2_format HandoverPreparationInformation__criticalExtensions__c1__cond HandoverPreparationInformation__criticalExtensions__c1__list__Format HandoverPreparationInformation__criticalExtensions__c1__F1 HandoverPreparationInformation__criticalExtensions__c1__F2 HandoverPreparationInformation__criticalExtensions__c1__helper2 HandoverPreparationInformation__criticalExtensions__c1__helper3 HandoverPreparationInformation__criticalExtensions__c1__helper4.
Opaque HandoverPreparationInformation__criticalExtensions__c1__cond HandoverPreparationInformation__criticalExtensions__c1__Format.

Definition HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__helper : forall a : HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Format : T_Format HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type)
    HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__cond HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Format.


Definition HandoverPreparationInformation__criticalExtensions__Format_Type := Eval cbn in get_formats HandoverPreparationInformation__criticalExtensions__list.
Definition HandoverPreparationInformation__criticalExtensions__Format_list : HandoverPreparationInformation__criticalExtensions__Format_Type :=
  (HandoverPreparationInformation__criticalExtensions__c1__Format, (HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition HandoverPreparationInformation__criticalExtensions__list__Format := Eval compute in choice_format HandoverPreparationInformation__criticalExtensions__list HandoverPreparationInformation__criticalExtensions__len_helper1 HandoverPreparationInformation__criticalExtensions__len_helper2  HandoverPreparationInformation__criticalExtensions__Format_list.
Definition HandoverPreparationInformation__criticalExtensions__F1 (z : HandoverPreparationInformation__criticalExtensions__Type) : (choice HandoverPreparationInformation__criticalExtensions__list) :=
  match z with
   | HandoverPreparationInformation__criticalExtensions__c1 t => existT _ 0 t
  | HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition HandoverPreparationInformation__criticalExtensions__g := (fun n => typ_set (get_nth_typ HandoverPreparationInformation__criticalExtensions__list n)).
Definition HandoverPreparationInformation__criticalExtensions__F2 (y : choice HandoverPreparationInformation__criticalExtensions__list) : HandoverPreparationInformation__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (HandoverPreparationInformation__criticalExtensions__g n -> HandoverPreparationInformation__criticalExtensions__Type) with
    | 0 => fun (t : HandoverPreparationInformation__criticalExtensions__c1__Type) => HandoverPreparationInformation__criticalExtensions__c1 t 
    | 1 => fun (t : HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture__Type) => HandoverPreparationInformation__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : HandoverPreparationInformation__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ HandoverPreparationInformation__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len HandoverPreparationInformation__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return HandoverPreparationInformation__criticalExtensions__Type with end) n0
           end t0).

Lemma HandoverPreparationInformation__criticalExtensions__helper2 :  forall (y : HandoverPreparationInformation__criticalExtensions__Type), HandoverPreparationInformation__criticalExtensions__cond y -> choice_cond HandoverPreparationInformation__criticalExtensions__list (HandoverPreparationInformation__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma HandoverPreparationInformation__criticalExtensions__helper3 :  forall (y : HandoverPreparationInformation__criticalExtensions__Type), HandoverPreparationInformation__criticalExtensions__F2 (HandoverPreparationInformation__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma HandoverPreparationInformation__criticalExtensions__helper4 : (forall b : choice HandoverPreparationInformation__criticalExtensions__list, choice_cond HandoverPreparationInformation__criticalExtensions__list b -> HandoverPreparationInformation__criticalExtensions__cond (HandoverPreparationInformation__criticalExtensions__F2 b) /\ HandoverPreparationInformation__criticalExtensions__F1 (HandoverPreparationInformation__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length HandoverPreparationInformation__criticalExtensions__F1 HandoverPreparationInformation__criticalExtensions__F2.
Definition HandoverPreparationInformation__criticalExtensions__Format : T_Format HandoverPreparationInformation__criticalExtensions__Type HandoverPreparationInformation__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format HandoverPreparationInformation__criticalExtensions__cond HandoverPreparationInformation__criticalExtensions__list__Format HandoverPreparationInformation__criticalExtensions__F1 HandoverPreparationInformation__criticalExtensions__F2 HandoverPreparationInformation__criticalExtensions__helper2 HandoverPreparationInformation__criticalExtensions__helper3 HandoverPreparationInformation__criticalExtensions__helper4.
Opaque HandoverPreparationInformation__criticalExtensions__cond HandoverPreparationInformation__criticalExtensions__Format.


Definition HandoverPreparationInformation__Format_Type := Eval cbn in seq_format_prod HandoverPreparationInformation__list.
Definition HandoverPreparationInformation__Format_list : HandoverPreparationInformation__Format_Type :=
  (HandoverPreparationInformation__criticalExtensions__Format, unit_format).
Definition HandoverPreparationInformation__list__Format := (*Eval compute in *) seq_format HandoverPreparationInformation__list HandoverPreparationInformation__Format_list.
Definition HandoverPreparationInformation__F1 z :=
  (HandoverPreparationInformation__criticalExtensions z, tt).
Definition HandoverPreparationInformation__F2 (y : seq_type HandoverPreparationInformation__list) :=
  match y with
  | (i0, _)=>
    make__HandoverPreparationInformation__Type i0
  end.
Lemma HandoverPreparationInformation__F1F2_cond (z : HandoverPreparationInformation__Type)
  : HandoverPreparationInformation__cond z ->
  (seq_cond HandoverPreparationInformation__list (HandoverPreparationInformation__F1 z)).
intro H. unfold HandoverPreparationInformation__cond in H. simpl. auto. Qed.
Lemma HandoverPreparationInformation__F1F2_cond2 (z : HandoverPreparationInformation__Type)
 : HandoverPreparationInformation__F2 (HandoverPreparationInformation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma HandoverPreparationInformation__F2F1_cond (y : seq_type HandoverPreparationInformation__list)
  : seq_cond HandoverPreparationInformation__list y ->
 (HandoverPreparationInformation__cond (HandoverPreparationInformation__F2 y)) /\  HandoverPreparationInformation__F1 (HandoverPreparationInformation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold HandoverPreparationInformation__cond. simpl in *. auto.
 - simpl. unfold HandoverPreparationInformation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition HandoverPreparationInformation__Format : T_Format HandoverPreparationInformation__Type HandoverPreparationInformation__cond :=
        proj2_format  HandoverPreparationInformation__cond HandoverPreparationInformation__list__Format
    HandoverPreparationInformation__F1 HandoverPreparationInformation__F2 HandoverPreparationInformation__F1F2_cond  HandoverPreparationInformation__F1F2_cond2 HandoverPreparationInformation__F2F1_cond.
Opaque HandoverPreparationInformation__cond HandoverPreparationInformation__Format.

