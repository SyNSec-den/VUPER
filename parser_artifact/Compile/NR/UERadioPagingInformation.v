Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.UERadioPagingInformation_IEs.

Opaque UERadioPagingInformation_IEs__cond UERadioPagingInformation_IEs__Format.


Inductive UERadioPagingInformation__criticalExtensions__c1__Type : Set :=
  | UERadioPagingInformation__criticalExtensions__c1__ueRadioPagingInformation : UERadioPagingInformation_IEs__Type -> UERadioPagingInformation__criticalExtensions__c1__Type
  | UERadioPagingInformation__criticalExtensions__c1__spare7 : unit -> UERadioPagingInformation__criticalExtensions__c1__Type
  | UERadioPagingInformation__criticalExtensions__c1__spare6 : unit -> UERadioPagingInformation__criticalExtensions__c1__Type
  | UERadioPagingInformation__criticalExtensions__c1__spare5 : unit -> UERadioPagingInformation__criticalExtensions__c1__Type
  | UERadioPagingInformation__criticalExtensions__c1__spare4 : unit -> UERadioPagingInformation__criticalExtensions__c1__Type
  | UERadioPagingInformation__criticalExtensions__c1__spare3 : unit -> UERadioPagingInformation__criticalExtensions__c1__Type
  | UERadioPagingInformation__criticalExtensions__c1__spare2 : unit -> UERadioPagingInformation__criticalExtensions__c1__Type
  | UERadioPagingInformation__criticalExtensions__c1__spare1 : unit -> UERadioPagingInformation__criticalExtensions__c1__Type
.
Definition UERadioPagingInformation__criticalExtensions__c1__list : list typ := (
typ_cons UERadioPagingInformation_IEs__Type UERadioPagingInformation_IEs__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition UERadioPagingInformation__criticalExtensions__c1__cond (c : UERadioPagingInformation__criticalExtensions__c1__Type) := 
  match c with
  | UERadioPagingInformation__criticalExtensions__c1__ueRadioPagingInformation t => UERadioPagingInformation_IEs__cond t 
  | UERadioPagingInformation__criticalExtensions__c1__spare7 t => (fun _ => True) t 
  | UERadioPagingInformation__criticalExtensions__c1__spare6 t => (fun _ => True) t 
  | UERadioPagingInformation__criticalExtensions__c1__spare5 t => (fun _ => True) t 
  | UERadioPagingInformation__criticalExtensions__c1__spare4 t => (fun _ => True) t 
  | UERadioPagingInformation__criticalExtensions__c1__spare3 t => (fun _ => True) t 
  | UERadioPagingInformation__criticalExtensions__c1__spare2 t => (fun _ => True) t 
  | UERadioPagingInformation__criticalExtensions__c1__spare1 t => (fun _ => True) t 
  end.

Lemma UERadioPagingInformation__criticalExtensions__c1__len_helper1 : to_bit_sz (length UERadioPagingInformation__criticalExtensions__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UERadioPagingInformation__criticalExtensions__c1__len_helper2 : 2 <= length2 UERadioPagingInformation__criticalExtensions__c1__list.
 simpl. lia. Qed.
Record UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__cond (z : UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UERadioPagingInformation__criticalExtensions__Type : Set :=
  | UERadioPagingInformation__criticalExtensions__c1 : UERadioPagingInformation__criticalExtensions__c1__Type -> UERadioPagingInformation__criticalExtensions__Type
  | UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture : UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type -> UERadioPagingInformation__criticalExtensions__Type
.
Definition UERadioPagingInformation__criticalExtensions__list : list typ := (
typ_cons UERadioPagingInformation__criticalExtensions__c1__Type UERadioPagingInformation__criticalExtensions__c1__cond ::
typ_cons UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UERadioPagingInformation__criticalExtensions__cond (c : UERadioPagingInformation__criticalExtensions__Type) := 
  match c with
  | UERadioPagingInformation__criticalExtensions__c1 t => UERadioPagingInformation__criticalExtensions__c1__cond t 
  | UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture t => UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UERadioPagingInformation__criticalExtensions__len_helper1 : to_bit_sz (length UERadioPagingInformation__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UERadioPagingInformation__criticalExtensions__len_helper2 : 2 <= length2 UERadioPagingInformation__criticalExtensions__list.
 simpl. lia. Qed.
Record UERadioPagingInformation__Type : Set :=
  make__UERadioPagingInformation__Type {
    UERadioPagingInformation__criticalExtensions : UERadioPagingInformation__criticalExtensions__Type ;
}.
Definition UERadioPagingInformation__list := (
 Nor UERadioPagingInformation__criticalExtensions__Type UERadioPagingInformation__criticalExtensions__cond ::
 nil).
Definition UERadioPagingInformation__cond z := 
  UERadioPagingInformation__criticalExtensions__cond (UERadioPagingInformation__criticalExtensions z) /\
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

Definition UERadioPagingInformation__criticalExtensions__c1__Format_Type := Eval cbn in get_formats UERadioPagingInformation__criticalExtensions__c1__list.
Definition UERadioPagingInformation__criticalExtensions__c1__Format_list : UERadioPagingInformation__criticalExtensions__c1__Format_Type :=
  (UERadioPagingInformation_IEs__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))))))).
Definition UERadioPagingInformation__criticalExtensions__c1__list__Format := Eval compute in choice_format UERadioPagingInformation__criticalExtensions__c1__list UERadioPagingInformation__criticalExtensions__c1__len_helper1 UERadioPagingInformation__criticalExtensions__c1__len_helper2  UERadioPagingInformation__criticalExtensions__c1__Format_list.
Definition UERadioPagingInformation__criticalExtensions__c1__F1 (z : UERadioPagingInformation__criticalExtensions__c1__Type) : (choice UERadioPagingInformation__criticalExtensions__c1__list) :=
  match z with
   | UERadioPagingInformation__criticalExtensions__c1__ueRadioPagingInformation t => existT _ 0 t
  | UERadioPagingInformation__criticalExtensions__c1__spare7 t => existT _ 1 t
  | UERadioPagingInformation__criticalExtensions__c1__spare6 t => existT _ 2 t
  | UERadioPagingInformation__criticalExtensions__c1__spare5 t => existT _ 3 t
  | UERadioPagingInformation__criticalExtensions__c1__spare4 t => existT _ 4 t
  | UERadioPagingInformation__criticalExtensions__c1__spare3 t => existT _ 5 t
  | UERadioPagingInformation__criticalExtensions__c1__spare2 t => existT _ 6 t
  | UERadioPagingInformation__criticalExtensions__c1__spare1 t => existT _ 7 t
  end.
Definition UERadioPagingInformation__criticalExtensions__c1__g := (fun n => typ_set (get_nth_typ UERadioPagingInformation__criticalExtensions__c1__list n)).
Definition UERadioPagingInformation__criticalExtensions__c1__F2 (y : choice UERadioPagingInformation__criticalExtensions__c1__list) : UERadioPagingInformation__criticalExtensions__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UERadioPagingInformation__criticalExtensions__c1__g n -> UERadioPagingInformation__criticalExtensions__c1__Type) with
    | 0 => fun (t : UERadioPagingInformation_IEs__Type) => UERadioPagingInformation__criticalExtensions__c1__ueRadioPagingInformation t 
    | 1 => fun (t : unit) => UERadioPagingInformation__criticalExtensions__c1__spare7 t 
    | 2 => fun (t : unit) => UERadioPagingInformation__criticalExtensions__c1__spare6 t 
    | 3 => fun (t : unit) => UERadioPagingInformation__criticalExtensions__c1__spare5 t 
    | 4 => fun (t : unit) => UERadioPagingInformation__criticalExtensions__c1__spare4 t 
    | 5 => fun (t : unit) => UERadioPagingInformation__criticalExtensions__c1__spare3 t 
    | 6 => fun (t : unit) => UERadioPagingInformation__criticalExtensions__c1__spare2 t 
    | 7 => fun (t : unit) => UERadioPagingInformation__criticalExtensions__c1__spare1 t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : UERadioPagingInformation__criticalExtensions__c1__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ UERadioPagingInformation__criticalExtensions__c1__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UERadioPagingInformation__criticalExtensions__c1__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return UERadioPagingInformation__criticalExtensions__c1__Type with end) n0
           end t0).

Lemma UERadioPagingInformation__criticalExtensions__c1__helper2 :  forall (y : UERadioPagingInformation__criticalExtensions__c1__Type), UERadioPagingInformation__criticalExtensions__c1__cond y -> choice_cond UERadioPagingInformation__criticalExtensions__c1__list (UERadioPagingInformation__criticalExtensions__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UERadioPagingInformation__criticalExtensions__c1__helper3 :  forall (y : UERadioPagingInformation__criticalExtensions__c1__Type), UERadioPagingInformation__criticalExtensions__c1__F2 (UERadioPagingInformation__criticalExtensions__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UERadioPagingInformation__criticalExtensions__c1__helper4 : (forall b : choice UERadioPagingInformation__criticalExtensions__c1__list, choice_cond UERadioPagingInformation__criticalExtensions__c1__list b -> UERadioPagingInformation__criticalExtensions__c1__cond (UERadioPagingInformation__criticalExtensions__c1__F2 b) /\ UERadioPagingInformation__criticalExtensions__c1__F1 (UERadioPagingInformation__criticalExtensions__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UERadioPagingInformation__criticalExtensions__c1__F1 UERadioPagingInformation__criticalExtensions__c1__F2.
Definition UERadioPagingInformation__criticalExtensions__c1__Format : T_Format UERadioPagingInformation__criticalExtensions__c1__Type UERadioPagingInformation__criticalExtensions__c1__cond :=
  (* Eval compute in *) proj2_format UERadioPagingInformation__criticalExtensions__c1__cond UERadioPagingInformation__criticalExtensions__c1__list__Format UERadioPagingInformation__criticalExtensions__c1__F1 UERadioPagingInformation__criticalExtensions__c1__F2 UERadioPagingInformation__criticalExtensions__c1__helper2 UERadioPagingInformation__criticalExtensions__c1__helper3 UERadioPagingInformation__criticalExtensions__c1__helper4.
Opaque UERadioPagingInformation__criticalExtensions__c1__cond UERadioPagingInformation__criticalExtensions__c1__Format.

Definition UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__helper : forall a : UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Format : T_Format UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type)
    UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__cond UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Format.


Definition UERadioPagingInformation__criticalExtensions__Format_Type := Eval cbn in get_formats UERadioPagingInformation__criticalExtensions__list.
Definition UERadioPagingInformation__criticalExtensions__Format_list : UERadioPagingInformation__criticalExtensions__Format_Type :=
  (UERadioPagingInformation__criticalExtensions__c1__Format, (UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UERadioPagingInformation__criticalExtensions__list__Format := Eval compute in choice_format UERadioPagingInformation__criticalExtensions__list UERadioPagingInformation__criticalExtensions__len_helper1 UERadioPagingInformation__criticalExtensions__len_helper2  UERadioPagingInformation__criticalExtensions__Format_list.
Definition UERadioPagingInformation__criticalExtensions__F1 (z : UERadioPagingInformation__criticalExtensions__Type) : (choice UERadioPagingInformation__criticalExtensions__list) :=
  match z with
   | UERadioPagingInformation__criticalExtensions__c1 t => existT _ 0 t
  | UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UERadioPagingInformation__criticalExtensions__g := (fun n => typ_set (get_nth_typ UERadioPagingInformation__criticalExtensions__list n)).
Definition UERadioPagingInformation__criticalExtensions__F2 (y : choice UERadioPagingInformation__criticalExtensions__list) : UERadioPagingInformation__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UERadioPagingInformation__criticalExtensions__g n -> UERadioPagingInformation__criticalExtensions__Type) with
    | 0 => fun (t : UERadioPagingInformation__criticalExtensions__c1__Type) => UERadioPagingInformation__criticalExtensions__c1 t 
    | 1 => fun (t : UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture__Type) => UERadioPagingInformation__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UERadioPagingInformation__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UERadioPagingInformation__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UERadioPagingInformation__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UERadioPagingInformation__criticalExtensions__Type with end) n0
           end t0).

Lemma UERadioPagingInformation__criticalExtensions__helper2 :  forall (y : UERadioPagingInformation__criticalExtensions__Type), UERadioPagingInformation__criticalExtensions__cond y -> choice_cond UERadioPagingInformation__criticalExtensions__list (UERadioPagingInformation__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UERadioPagingInformation__criticalExtensions__helper3 :  forall (y : UERadioPagingInformation__criticalExtensions__Type), UERadioPagingInformation__criticalExtensions__F2 (UERadioPagingInformation__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UERadioPagingInformation__criticalExtensions__helper4 : (forall b : choice UERadioPagingInformation__criticalExtensions__list, choice_cond UERadioPagingInformation__criticalExtensions__list b -> UERadioPagingInformation__criticalExtensions__cond (UERadioPagingInformation__criticalExtensions__F2 b) /\ UERadioPagingInformation__criticalExtensions__F1 (UERadioPagingInformation__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UERadioPagingInformation__criticalExtensions__F1 UERadioPagingInformation__criticalExtensions__F2.
Definition UERadioPagingInformation__criticalExtensions__Format : T_Format UERadioPagingInformation__criticalExtensions__Type UERadioPagingInformation__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UERadioPagingInformation__criticalExtensions__cond UERadioPagingInformation__criticalExtensions__list__Format UERadioPagingInformation__criticalExtensions__F1 UERadioPagingInformation__criticalExtensions__F2 UERadioPagingInformation__criticalExtensions__helper2 UERadioPagingInformation__criticalExtensions__helper3 UERadioPagingInformation__criticalExtensions__helper4.
Opaque UERadioPagingInformation__criticalExtensions__cond UERadioPagingInformation__criticalExtensions__Format.


Definition UERadioPagingInformation__Format_Type := Eval cbn in seq_format_prod UERadioPagingInformation__list.
Definition UERadioPagingInformation__Format_list : UERadioPagingInformation__Format_Type :=
  (UERadioPagingInformation__criticalExtensions__Format, unit_format).
Definition UERadioPagingInformation__list__Format := (*Eval compute in *) seq_format UERadioPagingInformation__list UERadioPagingInformation__Format_list.
Definition UERadioPagingInformation__F1 z :=
  (UERadioPagingInformation__criticalExtensions z, tt).
Definition UERadioPagingInformation__F2 (y : seq_type UERadioPagingInformation__list) :=
  match y with
  | (i0, _)=>
    make__UERadioPagingInformation__Type i0
  end.
Lemma UERadioPagingInformation__F1F2_cond (z : UERadioPagingInformation__Type)
  : UERadioPagingInformation__cond z ->
  (seq_cond UERadioPagingInformation__list (UERadioPagingInformation__F1 z)).
intro H. unfold UERadioPagingInformation__cond in H. simpl. auto. Qed.
Lemma UERadioPagingInformation__F1F2_cond2 (z : UERadioPagingInformation__Type)
 : UERadioPagingInformation__F2 (UERadioPagingInformation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UERadioPagingInformation__F2F1_cond (y : seq_type UERadioPagingInformation__list)
  : seq_cond UERadioPagingInformation__list y ->
 (UERadioPagingInformation__cond (UERadioPagingInformation__F2 y)) /\  UERadioPagingInformation__F1 (UERadioPagingInformation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UERadioPagingInformation__cond. simpl in *. auto.
 - simpl. unfold UERadioPagingInformation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UERadioPagingInformation__Format : T_Format UERadioPagingInformation__Type UERadioPagingInformation__cond :=
        proj2_format  UERadioPagingInformation__cond UERadioPagingInformation__list__Format
    UERadioPagingInformation__F1 UERadioPagingInformation__F2 UERadioPagingInformation__F1F2_cond  UERadioPagingInformation__F1F2_cond2 UERadioPagingInformation__F2F1_cond.
Opaque UERadioPagingInformation__cond UERadioPagingInformation__Format.

