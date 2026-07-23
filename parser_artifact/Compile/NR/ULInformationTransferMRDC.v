Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ULInformationTransferMRDC_IEs.

Opaque ULInformationTransferMRDC_IEs__cond ULInformationTransferMRDC_IEs__Format.


Inductive ULInformationTransferMRDC__criticalExtensions__c1__Type : Set :=
  | ULInformationTransferMRDC__criticalExtensions__c1__ulInformationTransferMRDC : ULInformationTransferMRDC_IEs__Type -> ULInformationTransferMRDC__criticalExtensions__c1__Type
  | ULInformationTransferMRDC__criticalExtensions__c1__spare3 : unit -> ULInformationTransferMRDC__criticalExtensions__c1__Type
  | ULInformationTransferMRDC__criticalExtensions__c1__spare2 : unit -> ULInformationTransferMRDC__criticalExtensions__c1__Type
  | ULInformationTransferMRDC__criticalExtensions__c1__spare1 : unit -> ULInformationTransferMRDC__criticalExtensions__c1__Type
.
Definition ULInformationTransferMRDC__criticalExtensions__c1__list : list typ := (
typ_cons ULInformationTransferMRDC_IEs__Type ULInformationTransferMRDC_IEs__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition ULInformationTransferMRDC__criticalExtensions__c1__cond (c : ULInformationTransferMRDC__criticalExtensions__c1__Type) := 
  match c with
  | ULInformationTransferMRDC__criticalExtensions__c1__ulInformationTransferMRDC t => ULInformationTransferMRDC_IEs__cond t 
  | ULInformationTransferMRDC__criticalExtensions__c1__spare3 t => (fun _ => True) t 
  | ULInformationTransferMRDC__criticalExtensions__c1__spare2 t => (fun _ => True) t 
  | ULInformationTransferMRDC__criticalExtensions__c1__spare1 t => (fun _ => True) t 
  end.

Lemma ULInformationTransferMRDC__criticalExtensions__c1__len_helper1 : to_bit_sz (length ULInformationTransferMRDC__criticalExtensions__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ULInformationTransferMRDC__criticalExtensions__c1__len_helper2 : 2 <= length2 ULInformationTransferMRDC__criticalExtensions__c1__list.
 simpl. lia. Qed.
Record ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type : Set := make__ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__cond (z : ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive ULInformationTransferMRDC__criticalExtensions__Type : Set :=
  | ULInformationTransferMRDC__criticalExtensions__c1 : ULInformationTransferMRDC__criticalExtensions__c1__Type -> ULInformationTransferMRDC__criticalExtensions__Type
  | ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture : ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type -> ULInformationTransferMRDC__criticalExtensions__Type
.
Definition ULInformationTransferMRDC__criticalExtensions__list : list typ := (
typ_cons ULInformationTransferMRDC__criticalExtensions__c1__Type ULInformationTransferMRDC__criticalExtensions__c1__cond ::
typ_cons ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition ULInformationTransferMRDC__criticalExtensions__cond (c : ULInformationTransferMRDC__criticalExtensions__Type) := 
  match c with
  | ULInformationTransferMRDC__criticalExtensions__c1 t => ULInformationTransferMRDC__criticalExtensions__c1__cond t 
  | ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture t => ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma ULInformationTransferMRDC__criticalExtensions__len_helper1 : to_bit_sz (length ULInformationTransferMRDC__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ULInformationTransferMRDC__criticalExtensions__len_helper2 : 2 <= length2 ULInformationTransferMRDC__criticalExtensions__list.
 simpl. lia. Qed.
Record ULInformationTransferMRDC__Type : Set :=
  make__ULInformationTransferMRDC__Type {
    ULInformationTransferMRDC__criticalExtensions : ULInformationTransferMRDC__criticalExtensions__Type ;
}.
Definition ULInformationTransferMRDC__list := (
 Nor ULInformationTransferMRDC__criticalExtensions__Type ULInformationTransferMRDC__criticalExtensions__cond ::
 nil).
Definition ULInformationTransferMRDC__cond z := 
  ULInformationTransferMRDC__criticalExtensions__cond (ULInformationTransferMRDC__criticalExtensions z) /\
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

Definition ULInformationTransferMRDC__criticalExtensions__c1__Format_Type := Eval cbn in get_formats ULInformationTransferMRDC__criticalExtensions__c1__list.
Definition ULInformationTransferMRDC__criticalExtensions__c1__Format_list : ULInformationTransferMRDC__criticalExtensions__c1__Format_Type :=
  (ULInformationTransferMRDC_IEs__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))).
Definition ULInformationTransferMRDC__criticalExtensions__c1__list__Format := Eval compute in choice_format ULInformationTransferMRDC__criticalExtensions__c1__list ULInformationTransferMRDC__criticalExtensions__c1__len_helper1 ULInformationTransferMRDC__criticalExtensions__c1__len_helper2  ULInformationTransferMRDC__criticalExtensions__c1__Format_list.
Definition ULInformationTransferMRDC__criticalExtensions__c1__F1 (z : ULInformationTransferMRDC__criticalExtensions__c1__Type) : (choice ULInformationTransferMRDC__criticalExtensions__c1__list) :=
  match z with
   | ULInformationTransferMRDC__criticalExtensions__c1__ulInformationTransferMRDC t => existT _ 0 t
  | ULInformationTransferMRDC__criticalExtensions__c1__spare3 t => existT _ 1 t
  | ULInformationTransferMRDC__criticalExtensions__c1__spare2 t => existT _ 2 t
  | ULInformationTransferMRDC__criticalExtensions__c1__spare1 t => existT _ 3 t
  end.
Definition ULInformationTransferMRDC__criticalExtensions__c1__g := (fun n => typ_set (get_nth_typ ULInformationTransferMRDC__criticalExtensions__c1__list n)).
Definition ULInformationTransferMRDC__criticalExtensions__c1__F2 (y : choice ULInformationTransferMRDC__criticalExtensions__c1__list) : ULInformationTransferMRDC__criticalExtensions__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ULInformationTransferMRDC__criticalExtensions__c1__g n -> ULInformationTransferMRDC__criticalExtensions__c1__Type) with
    | 0 => fun (t : ULInformationTransferMRDC_IEs__Type) => ULInformationTransferMRDC__criticalExtensions__c1__ulInformationTransferMRDC t 
    | 1 => fun (t : unit) => ULInformationTransferMRDC__criticalExtensions__c1__spare3 t 
    | 2 => fun (t : unit) => ULInformationTransferMRDC__criticalExtensions__c1__spare2 t 
    | 3 => fun (t : unit) => ULInformationTransferMRDC__criticalExtensions__c1__spare1 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : ULInformationTransferMRDC__criticalExtensions__c1__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ ULInformationTransferMRDC__criticalExtensions__c1__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ULInformationTransferMRDC__criticalExtensions__c1__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return ULInformationTransferMRDC__criticalExtensions__c1__Type with end) n0
           end t0).

Lemma ULInformationTransferMRDC__criticalExtensions__c1__helper2 :  forall (y : ULInformationTransferMRDC__criticalExtensions__c1__Type), ULInformationTransferMRDC__criticalExtensions__c1__cond y -> choice_cond ULInformationTransferMRDC__criticalExtensions__c1__list (ULInformationTransferMRDC__criticalExtensions__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ULInformationTransferMRDC__criticalExtensions__c1__helper3 :  forall (y : ULInformationTransferMRDC__criticalExtensions__c1__Type), ULInformationTransferMRDC__criticalExtensions__c1__F2 (ULInformationTransferMRDC__criticalExtensions__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ULInformationTransferMRDC__criticalExtensions__c1__helper4 : (forall b : choice ULInformationTransferMRDC__criticalExtensions__c1__list, choice_cond ULInformationTransferMRDC__criticalExtensions__c1__list b -> ULInformationTransferMRDC__criticalExtensions__c1__cond (ULInformationTransferMRDC__criticalExtensions__c1__F2 b) /\ ULInformationTransferMRDC__criticalExtensions__c1__F1 (ULInformationTransferMRDC__criticalExtensions__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ULInformationTransferMRDC__criticalExtensions__c1__F1 ULInformationTransferMRDC__criticalExtensions__c1__F2.
Definition ULInformationTransferMRDC__criticalExtensions__c1__Format : T_Format ULInformationTransferMRDC__criticalExtensions__c1__Type ULInformationTransferMRDC__criticalExtensions__c1__cond :=
  (* Eval compute in *) proj2_format ULInformationTransferMRDC__criticalExtensions__c1__cond ULInformationTransferMRDC__criticalExtensions__c1__list__Format ULInformationTransferMRDC__criticalExtensions__c1__F1 ULInformationTransferMRDC__criticalExtensions__c1__F2 ULInformationTransferMRDC__criticalExtensions__c1__helper2 ULInformationTransferMRDC__criticalExtensions__c1__helper3 ULInformationTransferMRDC__criticalExtensions__c1__helper4.
Opaque ULInformationTransferMRDC__criticalExtensions__c1__cond ULInformationTransferMRDC__criticalExtensions__c1__Format.

Definition ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__helper : forall a : ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Format : T_Format ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type)
    ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__cond ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Format.


Definition ULInformationTransferMRDC__criticalExtensions__Format_Type := Eval cbn in get_formats ULInformationTransferMRDC__criticalExtensions__list.
Definition ULInformationTransferMRDC__criticalExtensions__Format_list : ULInformationTransferMRDC__criticalExtensions__Format_Type :=
  (ULInformationTransferMRDC__criticalExtensions__c1__Format, (ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition ULInformationTransferMRDC__criticalExtensions__list__Format := Eval compute in choice_format ULInformationTransferMRDC__criticalExtensions__list ULInformationTransferMRDC__criticalExtensions__len_helper1 ULInformationTransferMRDC__criticalExtensions__len_helper2  ULInformationTransferMRDC__criticalExtensions__Format_list.
Definition ULInformationTransferMRDC__criticalExtensions__F1 (z : ULInformationTransferMRDC__criticalExtensions__Type) : (choice ULInformationTransferMRDC__criticalExtensions__list) :=
  match z with
   | ULInformationTransferMRDC__criticalExtensions__c1 t => existT _ 0 t
  | ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition ULInformationTransferMRDC__criticalExtensions__g := (fun n => typ_set (get_nth_typ ULInformationTransferMRDC__criticalExtensions__list n)).
Definition ULInformationTransferMRDC__criticalExtensions__F2 (y : choice ULInformationTransferMRDC__criticalExtensions__list) : ULInformationTransferMRDC__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ULInformationTransferMRDC__criticalExtensions__g n -> ULInformationTransferMRDC__criticalExtensions__Type) with
    | 0 => fun (t : ULInformationTransferMRDC__criticalExtensions__c1__Type) => ULInformationTransferMRDC__criticalExtensions__c1 t 
    | 1 => fun (t : ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture__Type) => ULInformationTransferMRDC__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ULInformationTransferMRDC__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ULInformationTransferMRDC__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ULInformationTransferMRDC__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ULInformationTransferMRDC__criticalExtensions__Type with end) n0
           end t0).

Lemma ULInformationTransferMRDC__criticalExtensions__helper2 :  forall (y : ULInformationTransferMRDC__criticalExtensions__Type), ULInformationTransferMRDC__criticalExtensions__cond y -> choice_cond ULInformationTransferMRDC__criticalExtensions__list (ULInformationTransferMRDC__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ULInformationTransferMRDC__criticalExtensions__helper3 :  forall (y : ULInformationTransferMRDC__criticalExtensions__Type), ULInformationTransferMRDC__criticalExtensions__F2 (ULInformationTransferMRDC__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ULInformationTransferMRDC__criticalExtensions__helper4 : (forall b : choice ULInformationTransferMRDC__criticalExtensions__list, choice_cond ULInformationTransferMRDC__criticalExtensions__list b -> ULInformationTransferMRDC__criticalExtensions__cond (ULInformationTransferMRDC__criticalExtensions__F2 b) /\ ULInformationTransferMRDC__criticalExtensions__F1 (ULInformationTransferMRDC__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ULInformationTransferMRDC__criticalExtensions__F1 ULInformationTransferMRDC__criticalExtensions__F2.
Definition ULInformationTransferMRDC__criticalExtensions__Format : T_Format ULInformationTransferMRDC__criticalExtensions__Type ULInformationTransferMRDC__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format ULInformationTransferMRDC__criticalExtensions__cond ULInformationTransferMRDC__criticalExtensions__list__Format ULInformationTransferMRDC__criticalExtensions__F1 ULInformationTransferMRDC__criticalExtensions__F2 ULInformationTransferMRDC__criticalExtensions__helper2 ULInformationTransferMRDC__criticalExtensions__helper3 ULInformationTransferMRDC__criticalExtensions__helper4.
Opaque ULInformationTransferMRDC__criticalExtensions__cond ULInformationTransferMRDC__criticalExtensions__Format.


Definition ULInformationTransferMRDC__Format_Type := Eval cbn in seq_format_prod ULInformationTransferMRDC__list.
Definition ULInformationTransferMRDC__Format_list : ULInformationTransferMRDC__Format_Type :=
  (ULInformationTransferMRDC__criticalExtensions__Format, unit_format).
Definition ULInformationTransferMRDC__list__Format := (*Eval compute in *) seq_format ULInformationTransferMRDC__list ULInformationTransferMRDC__Format_list.
Definition ULInformationTransferMRDC__F1 z :=
  (ULInformationTransferMRDC__criticalExtensions z, tt).
Definition ULInformationTransferMRDC__F2 (y : seq_type ULInformationTransferMRDC__list) :=
  match y with
  | (i0, _)=>
    make__ULInformationTransferMRDC__Type i0
  end.
Lemma ULInformationTransferMRDC__F1F2_cond (z : ULInformationTransferMRDC__Type)
  : ULInformationTransferMRDC__cond z ->
  (seq_cond ULInformationTransferMRDC__list (ULInformationTransferMRDC__F1 z)).
intro H. unfold ULInformationTransferMRDC__cond in H. simpl. auto. Qed.
Lemma ULInformationTransferMRDC__F1F2_cond2 (z : ULInformationTransferMRDC__Type)
 : ULInformationTransferMRDC__F2 (ULInformationTransferMRDC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ULInformationTransferMRDC__F2F1_cond (y : seq_type ULInformationTransferMRDC__list)
  : seq_cond ULInformationTransferMRDC__list y ->
 (ULInformationTransferMRDC__cond (ULInformationTransferMRDC__F2 y)) /\  ULInformationTransferMRDC__F1 (ULInformationTransferMRDC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ULInformationTransferMRDC__cond. simpl in *. auto.
 - simpl. unfold ULInformationTransferMRDC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ULInformationTransferMRDC__Format : T_Format ULInformationTransferMRDC__Type ULInformationTransferMRDC__cond :=
        proj2_format  ULInformationTransferMRDC__cond ULInformationTransferMRDC__list__Format
    ULInformationTransferMRDC__F1 ULInformationTransferMRDC__F2 ULInformationTransferMRDC__F1F2_cond  ULInformationTransferMRDC__F1F2_cond2 ULInformationTransferMRDC__F2F1_cond.
Opaque ULInformationTransferMRDC__cond ULInformationTransferMRDC__Format.

