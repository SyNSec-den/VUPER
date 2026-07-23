Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.HandoverCommand_IEs.

Opaque HandoverCommand_IEs__cond HandoverCommand_IEs__Format.


Inductive HandoverCommand__criticalExtensions__c1__Type : Set :=
  | HandoverCommand__criticalExtensions__c1__handoverCommand : HandoverCommand_IEs__Type -> HandoverCommand__criticalExtensions__c1__Type
  | HandoverCommand__criticalExtensions__c1__spare3 : unit -> HandoverCommand__criticalExtensions__c1__Type
  | HandoverCommand__criticalExtensions__c1__spare2 : unit -> HandoverCommand__criticalExtensions__c1__Type
  | HandoverCommand__criticalExtensions__c1__spare1 : unit -> HandoverCommand__criticalExtensions__c1__Type
.
Definition HandoverCommand__criticalExtensions__c1__list : list typ := (
typ_cons HandoverCommand_IEs__Type HandoverCommand_IEs__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition HandoverCommand__criticalExtensions__c1__cond (c : HandoverCommand__criticalExtensions__c1__Type) := 
  match c with
  | HandoverCommand__criticalExtensions__c1__handoverCommand t => HandoverCommand_IEs__cond t 
  | HandoverCommand__criticalExtensions__c1__spare3 t => (fun _ => True) t 
  | HandoverCommand__criticalExtensions__c1__spare2 t => (fun _ => True) t 
  | HandoverCommand__criticalExtensions__c1__spare1 t => (fun _ => True) t 
  end.

Lemma HandoverCommand__criticalExtensions__c1__len_helper1 : to_bit_sz (length HandoverCommand__criticalExtensions__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma HandoverCommand__criticalExtensions__c1__len_helper2 : 2 <= length2 HandoverCommand__criticalExtensions__c1__list.
 simpl. lia. Qed.
Record HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type : Set := make__HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition HandoverCommand__criticalExtensions__criticalExtensionsFuture__cond (z : HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive HandoverCommand__criticalExtensions__Type : Set :=
  | HandoverCommand__criticalExtensions__c1 : HandoverCommand__criticalExtensions__c1__Type -> HandoverCommand__criticalExtensions__Type
  | HandoverCommand__criticalExtensions__criticalExtensionsFuture : HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type -> HandoverCommand__criticalExtensions__Type
.
Definition HandoverCommand__criticalExtensions__list : list typ := (
typ_cons HandoverCommand__criticalExtensions__c1__Type HandoverCommand__criticalExtensions__c1__cond ::
typ_cons HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type HandoverCommand__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition HandoverCommand__criticalExtensions__cond (c : HandoverCommand__criticalExtensions__Type) := 
  match c with
  | HandoverCommand__criticalExtensions__c1 t => HandoverCommand__criticalExtensions__c1__cond t 
  | HandoverCommand__criticalExtensions__criticalExtensionsFuture t => HandoverCommand__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma HandoverCommand__criticalExtensions__len_helper1 : to_bit_sz (length HandoverCommand__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma HandoverCommand__criticalExtensions__len_helper2 : 2 <= length2 HandoverCommand__criticalExtensions__list.
 simpl. lia. Qed.
Record HandoverCommand__Type : Set :=
  make__HandoverCommand__Type {
    HandoverCommand__criticalExtensions : HandoverCommand__criticalExtensions__Type ;
}.
Definition HandoverCommand__list := (
 Nor HandoverCommand__criticalExtensions__Type HandoverCommand__criticalExtensions__cond ::
 nil).
Definition HandoverCommand__cond z := 
  HandoverCommand__criticalExtensions__cond (HandoverCommand__criticalExtensions z) /\
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

Definition HandoverCommand__criticalExtensions__c1__Format_Type := Eval cbn in get_formats HandoverCommand__criticalExtensions__c1__list.
Definition HandoverCommand__criticalExtensions__c1__Format_list : HandoverCommand__criticalExtensions__c1__Format_Type :=
  (HandoverCommand_IEs__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))).
Definition HandoverCommand__criticalExtensions__c1__list__Format := Eval compute in choice_format HandoverCommand__criticalExtensions__c1__list HandoverCommand__criticalExtensions__c1__len_helper1 HandoverCommand__criticalExtensions__c1__len_helper2  HandoverCommand__criticalExtensions__c1__Format_list.
Definition HandoverCommand__criticalExtensions__c1__F1 (z : HandoverCommand__criticalExtensions__c1__Type) : (choice HandoverCommand__criticalExtensions__c1__list) :=
  match z with
   | HandoverCommand__criticalExtensions__c1__handoverCommand t => existT _ 0 t
  | HandoverCommand__criticalExtensions__c1__spare3 t => existT _ 1 t
  | HandoverCommand__criticalExtensions__c1__spare2 t => existT _ 2 t
  | HandoverCommand__criticalExtensions__c1__spare1 t => existT _ 3 t
  end.
Definition HandoverCommand__criticalExtensions__c1__g := (fun n => typ_set (get_nth_typ HandoverCommand__criticalExtensions__c1__list n)).
Definition HandoverCommand__criticalExtensions__c1__F2 (y : choice HandoverCommand__criticalExtensions__c1__list) : HandoverCommand__criticalExtensions__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (HandoverCommand__criticalExtensions__c1__g n -> HandoverCommand__criticalExtensions__c1__Type) with
    | 0 => fun (t : HandoverCommand_IEs__Type) => HandoverCommand__criticalExtensions__c1__handoverCommand t 
    | 1 => fun (t : unit) => HandoverCommand__criticalExtensions__c1__spare3 t 
    | 2 => fun (t : unit) => HandoverCommand__criticalExtensions__c1__spare2 t 
    | 3 => fun (t : unit) => HandoverCommand__criticalExtensions__c1__spare1 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : HandoverCommand__criticalExtensions__c1__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ HandoverCommand__criticalExtensions__c1__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len HandoverCommand__criticalExtensions__c1__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return HandoverCommand__criticalExtensions__c1__Type with end) n0
           end t0).

Lemma HandoverCommand__criticalExtensions__c1__helper2 :  forall (y : HandoverCommand__criticalExtensions__c1__Type), HandoverCommand__criticalExtensions__c1__cond y -> choice_cond HandoverCommand__criticalExtensions__c1__list (HandoverCommand__criticalExtensions__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma HandoverCommand__criticalExtensions__c1__helper3 :  forall (y : HandoverCommand__criticalExtensions__c1__Type), HandoverCommand__criticalExtensions__c1__F2 (HandoverCommand__criticalExtensions__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma HandoverCommand__criticalExtensions__c1__helper4 : (forall b : choice HandoverCommand__criticalExtensions__c1__list, choice_cond HandoverCommand__criticalExtensions__c1__list b -> HandoverCommand__criticalExtensions__c1__cond (HandoverCommand__criticalExtensions__c1__F2 b) /\ HandoverCommand__criticalExtensions__c1__F1 (HandoverCommand__criticalExtensions__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length HandoverCommand__criticalExtensions__c1__F1 HandoverCommand__criticalExtensions__c1__F2.
Definition HandoverCommand__criticalExtensions__c1__Format : T_Format HandoverCommand__criticalExtensions__c1__Type HandoverCommand__criticalExtensions__c1__cond :=
  (* Eval compute in *) proj2_format HandoverCommand__criticalExtensions__c1__cond HandoverCommand__criticalExtensions__c1__list__Format HandoverCommand__criticalExtensions__c1__F1 HandoverCommand__criticalExtensions__c1__F2 HandoverCommand__criticalExtensions__c1__helper2 HandoverCommand__criticalExtensions__c1__helper3 HandoverCommand__criticalExtensions__c1__helper4.
Opaque HandoverCommand__criticalExtensions__c1__cond HandoverCommand__criticalExtensions__c1__Format.

Definition HandoverCommand__criticalExtensions__criticalExtensionsFuture__helper : forall a : HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition HandoverCommand__criticalExtensions__criticalExtensionsFuture__Format : T_Format HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type HandoverCommand__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type)
    HandoverCommand__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque HandoverCommand__criticalExtensions__criticalExtensionsFuture__cond HandoverCommand__criticalExtensions__criticalExtensionsFuture__Format.


Definition HandoverCommand__criticalExtensions__Format_Type := Eval cbn in get_formats HandoverCommand__criticalExtensions__list.
Definition HandoverCommand__criticalExtensions__Format_list : HandoverCommand__criticalExtensions__Format_Type :=
  (HandoverCommand__criticalExtensions__c1__Format, (HandoverCommand__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition HandoverCommand__criticalExtensions__list__Format := Eval compute in choice_format HandoverCommand__criticalExtensions__list HandoverCommand__criticalExtensions__len_helper1 HandoverCommand__criticalExtensions__len_helper2  HandoverCommand__criticalExtensions__Format_list.
Definition HandoverCommand__criticalExtensions__F1 (z : HandoverCommand__criticalExtensions__Type) : (choice HandoverCommand__criticalExtensions__list) :=
  match z with
   | HandoverCommand__criticalExtensions__c1 t => existT _ 0 t
  | HandoverCommand__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition HandoverCommand__criticalExtensions__g := (fun n => typ_set (get_nth_typ HandoverCommand__criticalExtensions__list n)).
Definition HandoverCommand__criticalExtensions__F2 (y : choice HandoverCommand__criticalExtensions__list) : HandoverCommand__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (HandoverCommand__criticalExtensions__g n -> HandoverCommand__criticalExtensions__Type) with
    | 0 => fun (t : HandoverCommand__criticalExtensions__c1__Type) => HandoverCommand__criticalExtensions__c1 t 
    | 1 => fun (t : HandoverCommand__criticalExtensions__criticalExtensionsFuture__Type) => HandoverCommand__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : HandoverCommand__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ HandoverCommand__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len HandoverCommand__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return HandoverCommand__criticalExtensions__Type with end) n0
           end t0).

Lemma HandoverCommand__criticalExtensions__helper2 :  forall (y : HandoverCommand__criticalExtensions__Type), HandoverCommand__criticalExtensions__cond y -> choice_cond HandoverCommand__criticalExtensions__list (HandoverCommand__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma HandoverCommand__criticalExtensions__helper3 :  forall (y : HandoverCommand__criticalExtensions__Type), HandoverCommand__criticalExtensions__F2 (HandoverCommand__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma HandoverCommand__criticalExtensions__helper4 : (forall b : choice HandoverCommand__criticalExtensions__list, choice_cond HandoverCommand__criticalExtensions__list b -> HandoverCommand__criticalExtensions__cond (HandoverCommand__criticalExtensions__F2 b) /\ HandoverCommand__criticalExtensions__F1 (HandoverCommand__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length HandoverCommand__criticalExtensions__F1 HandoverCommand__criticalExtensions__F2.
Definition HandoverCommand__criticalExtensions__Format : T_Format HandoverCommand__criticalExtensions__Type HandoverCommand__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format HandoverCommand__criticalExtensions__cond HandoverCommand__criticalExtensions__list__Format HandoverCommand__criticalExtensions__F1 HandoverCommand__criticalExtensions__F2 HandoverCommand__criticalExtensions__helper2 HandoverCommand__criticalExtensions__helper3 HandoverCommand__criticalExtensions__helper4.
Opaque HandoverCommand__criticalExtensions__cond HandoverCommand__criticalExtensions__Format.


Definition HandoverCommand__Format_Type := Eval cbn in seq_format_prod HandoverCommand__list.
Definition HandoverCommand__Format_list : HandoverCommand__Format_Type :=
  (HandoverCommand__criticalExtensions__Format, unit_format).
Definition HandoverCommand__list__Format := (*Eval compute in *) seq_format HandoverCommand__list HandoverCommand__Format_list.
Definition HandoverCommand__F1 z :=
  (HandoverCommand__criticalExtensions z, tt).
Definition HandoverCommand__F2 (y : seq_type HandoverCommand__list) :=
  match y with
  | (i0, _)=>
    make__HandoverCommand__Type i0
  end.
Lemma HandoverCommand__F1F2_cond (z : HandoverCommand__Type)
  : HandoverCommand__cond z ->
  (seq_cond HandoverCommand__list (HandoverCommand__F1 z)).
intro H. unfold HandoverCommand__cond in H. simpl. auto. Qed.
Lemma HandoverCommand__F1F2_cond2 (z : HandoverCommand__Type)
 : HandoverCommand__F2 (HandoverCommand__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma HandoverCommand__F2F1_cond (y : seq_type HandoverCommand__list)
  : seq_cond HandoverCommand__list y ->
 (HandoverCommand__cond (HandoverCommand__F2 y)) /\  HandoverCommand__F1 (HandoverCommand__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold HandoverCommand__cond. simpl in *. auto.
 - simpl. unfold HandoverCommand__F1. simpl. destruct_all_unit. auto.   Qed.
Definition HandoverCommand__Format : T_Format HandoverCommand__Type HandoverCommand__cond :=
        proj2_format  HandoverCommand__cond HandoverCommand__list__Format
    HandoverCommand__F1 HandoverCommand__F2 HandoverCommand__F1F2_cond  HandoverCommand__F1F2_cond2 HandoverCommand__F2F1_cond.
Opaque HandoverCommand__cond HandoverCommand__Format.

