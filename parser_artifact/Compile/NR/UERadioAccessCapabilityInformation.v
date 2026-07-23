Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.UERadioAccessCapabilityInformation_IEs.

Opaque UERadioAccessCapabilityInformation_IEs__cond UERadioAccessCapabilityInformation_IEs__Format.


Inductive UERadioAccessCapabilityInformation__criticalExtensions__c1__Type : Set :=
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__ueRadioAccessCapabilityInformation : UERadioAccessCapabilityInformation_IEs__Type -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare7 : unit -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare6 : unit -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare5 : unit -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare4 : unit -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare3 : unit -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare2 : unit -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare1 : unit -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type
.
Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__list : list typ := (
typ_cons UERadioAccessCapabilityInformation_IEs__Type UERadioAccessCapabilityInformation_IEs__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__cond (c : UERadioAccessCapabilityInformation__criticalExtensions__c1__Type) := 
  match c with
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__ueRadioAccessCapabilityInformation t => UERadioAccessCapabilityInformation_IEs__cond t 
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare7 t => (fun _ => True) t 
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare6 t => (fun _ => True) t 
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare5 t => (fun _ => True) t 
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare4 t => (fun _ => True) t 
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare3 t => (fun _ => True) t 
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare2 t => (fun _ => True) t 
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare1 t => (fun _ => True) t 
  end.

Lemma UERadioAccessCapabilityInformation__criticalExtensions__c1__len_helper1 : to_bit_sz (length UERadioAccessCapabilityInformation__criticalExtensions__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UERadioAccessCapabilityInformation__criticalExtensions__c1__len_helper2 : 2 <= length2 UERadioAccessCapabilityInformation__criticalExtensions__c1__list.
 simpl. lia. Qed.
Record UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type : Set := make__UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond (z : UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive UERadioAccessCapabilityInformation__criticalExtensions__Type : Set :=
  | UERadioAccessCapabilityInformation__criticalExtensions__c1 : UERadioAccessCapabilityInformation__criticalExtensions__c1__Type -> UERadioAccessCapabilityInformation__criticalExtensions__Type
  | UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture : UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type -> UERadioAccessCapabilityInformation__criticalExtensions__Type
.
Definition UERadioAccessCapabilityInformation__criticalExtensions__list : list typ := (
typ_cons UERadioAccessCapabilityInformation__criticalExtensions__c1__Type UERadioAccessCapabilityInformation__criticalExtensions__c1__cond ::
typ_cons UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition UERadioAccessCapabilityInformation__criticalExtensions__cond (c : UERadioAccessCapabilityInformation__criticalExtensions__Type) := 
  match c with
  | UERadioAccessCapabilityInformation__criticalExtensions__c1 t => UERadioAccessCapabilityInformation__criticalExtensions__c1__cond t 
  | UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture t => UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma UERadioAccessCapabilityInformation__criticalExtensions__len_helper1 : to_bit_sz (length UERadioAccessCapabilityInformation__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UERadioAccessCapabilityInformation__criticalExtensions__len_helper2 : 2 <= length2 UERadioAccessCapabilityInformation__criticalExtensions__list.
 simpl. lia. Qed.
Record UERadioAccessCapabilityInformation__Type : Set :=
  make__UERadioAccessCapabilityInformation__Type {
    UERadioAccessCapabilityInformation__criticalExtensions : UERadioAccessCapabilityInformation__criticalExtensions__Type ;
}.
Definition UERadioAccessCapabilityInformation__list := (
 Nor UERadioAccessCapabilityInformation__criticalExtensions__Type UERadioAccessCapabilityInformation__criticalExtensions__cond ::
 nil).
Definition UERadioAccessCapabilityInformation__cond z := 
  UERadioAccessCapabilityInformation__criticalExtensions__cond (UERadioAccessCapabilityInformation__criticalExtensions z) /\
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

Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__Format_Type := Eval cbn in get_formats UERadioAccessCapabilityInformation__criticalExtensions__c1__list.
Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__Format_list : UERadioAccessCapabilityInformation__criticalExtensions__c1__Format_Type :=
  (UERadioAccessCapabilityInformation_IEs__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))))))).
Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__list__Format := Eval compute in choice_format UERadioAccessCapabilityInformation__criticalExtensions__c1__list UERadioAccessCapabilityInformation__criticalExtensions__c1__len_helper1 UERadioAccessCapabilityInformation__criticalExtensions__c1__len_helper2  UERadioAccessCapabilityInformation__criticalExtensions__c1__Format_list.
Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__F1 (z : UERadioAccessCapabilityInformation__criticalExtensions__c1__Type) : (choice UERadioAccessCapabilityInformation__criticalExtensions__c1__list) :=
  match z with
   | UERadioAccessCapabilityInformation__criticalExtensions__c1__ueRadioAccessCapabilityInformation t => existT _ 0 t
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare7 t => existT _ 1 t
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare6 t => existT _ 2 t
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare5 t => existT _ 3 t
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare4 t => existT _ 4 t
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare3 t => existT _ 5 t
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare2 t => existT _ 6 t
  | UERadioAccessCapabilityInformation__criticalExtensions__c1__spare1 t => existT _ 7 t
  end.
Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__g := (fun n => typ_set (get_nth_typ UERadioAccessCapabilityInformation__criticalExtensions__c1__list n)).
Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__F2 (y : choice UERadioAccessCapabilityInformation__criticalExtensions__c1__list) : UERadioAccessCapabilityInformation__criticalExtensions__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UERadioAccessCapabilityInformation__criticalExtensions__c1__g n -> UERadioAccessCapabilityInformation__criticalExtensions__c1__Type) with
    | 0 => fun (t : UERadioAccessCapabilityInformation_IEs__Type) => UERadioAccessCapabilityInformation__criticalExtensions__c1__ueRadioAccessCapabilityInformation t 
    | 1 => fun (t : unit) => UERadioAccessCapabilityInformation__criticalExtensions__c1__spare7 t 
    | 2 => fun (t : unit) => UERadioAccessCapabilityInformation__criticalExtensions__c1__spare6 t 
    | 3 => fun (t : unit) => UERadioAccessCapabilityInformation__criticalExtensions__c1__spare5 t 
    | 4 => fun (t : unit) => UERadioAccessCapabilityInformation__criticalExtensions__c1__spare4 t 
    | 5 => fun (t : unit) => UERadioAccessCapabilityInformation__criticalExtensions__c1__spare3 t 
    | 6 => fun (t : unit) => UERadioAccessCapabilityInformation__criticalExtensions__c1__spare2 t 
    | 7 => fun (t : unit) => UERadioAccessCapabilityInformation__criticalExtensions__c1__spare1 t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : UERadioAccessCapabilityInformation__criticalExtensions__c1__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ UERadioAccessCapabilityInformation__criticalExtensions__c1__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UERadioAccessCapabilityInformation__criticalExtensions__c1__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return UERadioAccessCapabilityInformation__criticalExtensions__c1__Type with end) n0
           end t0).

Lemma UERadioAccessCapabilityInformation__criticalExtensions__c1__helper2 :  forall (y : UERadioAccessCapabilityInformation__criticalExtensions__c1__Type), UERadioAccessCapabilityInformation__criticalExtensions__c1__cond y -> choice_cond UERadioAccessCapabilityInformation__criticalExtensions__c1__list (UERadioAccessCapabilityInformation__criticalExtensions__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UERadioAccessCapabilityInformation__criticalExtensions__c1__helper3 :  forall (y : UERadioAccessCapabilityInformation__criticalExtensions__c1__Type), UERadioAccessCapabilityInformation__criticalExtensions__c1__F2 (UERadioAccessCapabilityInformation__criticalExtensions__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UERadioAccessCapabilityInformation__criticalExtensions__c1__helper4 : (forall b : choice UERadioAccessCapabilityInformation__criticalExtensions__c1__list, choice_cond UERadioAccessCapabilityInformation__criticalExtensions__c1__list b -> UERadioAccessCapabilityInformation__criticalExtensions__c1__cond (UERadioAccessCapabilityInformation__criticalExtensions__c1__F2 b) /\ UERadioAccessCapabilityInformation__criticalExtensions__c1__F1 (UERadioAccessCapabilityInformation__criticalExtensions__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UERadioAccessCapabilityInformation__criticalExtensions__c1__F1 UERadioAccessCapabilityInformation__criticalExtensions__c1__F2.
Definition UERadioAccessCapabilityInformation__criticalExtensions__c1__Format : T_Format UERadioAccessCapabilityInformation__criticalExtensions__c1__Type UERadioAccessCapabilityInformation__criticalExtensions__c1__cond :=
  (* Eval compute in *) proj2_format UERadioAccessCapabilityInformation__criticalExtensions__c1__cond UERadioAccessCapabilityInformation__criticalExtensions__c1__list__Format UERadioAccessCapabilityInformation__criticalExtensions__c1__F1 UERadioAccessCapabilityInformation__criticalExtensions__c1__F2 UERadioAccessCapabilityInformation__criticalExtensions__c1__helper2 UERadioAccessCapabilityInformation__criticalExtensions__c1__helper3 UERadioAccessCapabilityInformation__criticalExtensions__c1__helper4.
Opaque UERadioAccessCapabilityInformation__criticalExtensions__c1__cond UERadioAccessCapabilityInformation__criticalExtensions__c1__Format.

Definition UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__helper : forall a : UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Format : T_Format UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type)
    UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__cond UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Format.


Definition UERadioAccessCapabilityInformation__criticalExtensions__Format_Type := Eval cbn in get_formats UERadioAccessCapabilityInformation__criticalExtensions__list.
Definition UERadioAccessCapabilityInformation__criticalExtensions__Format_list : UERadioAccessCapabilityInformation__criticalExtensions__Format_Type :=
  (UERadioAccessCapabilityInformation__criticalExtensions__c1__Format, (UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition UERadioAccessCapabilityInformation__criticalExtensions__list__Format := Eval compute in choice_format UERadioAccessCapabilityInformation__criticalExtensions__list UERadioAccessCapabilityInformation__criticalExtensions__len_helper1 UERadioAccessCapabilityInformation__criticalExtensions__len_helper2  UERadioAccessCapabilityInformation__criticalExtensions__Format_list.
Definition UERadioAccessCapabilityInformation__criticalExtensions__F1 (z : UERadioAccessCapabilityInformation__criticalExtensions__Type) : (choice UERadioAccessCapabilityInformation__criticalExtensions__list) :=
  match z with
   | UERadioAccessCapabilityInformation__criticalExtensions__c1 t => existT _ 0 t
  | UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition UERadioAccessCapabilityInformation__criticalExtensions__g := (fun n => typ_set (get_nth_typ UERadioAccessCapabilityInformation__criticalExtensions__list n)).
Definition UERadioAccessCapabilityInformation__criticalExtensions__F2 (y : choice UERadioAccessCapabilityInformation__criticalExtensions__list) : UERadioAccessCapabilityInformation__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UERadioAccessCapabilityInformation__criticalExtensions__g n -> UERadioAccessCapabilityInformation__criticalExtensions__Type) with
    | 0 => fun (t : UERadioAccessCapabilityInformation__criticalExtensions__c1__Type) => UERadioAccessCapabilityInformation__criticalExtensions__c1 t 
    | 1 => fun (t : UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture__Type) => UERadioAccessCapabilityInformation__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UERadioAccessCapabilityInformation__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UERadioAccessCapabilityInformation__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UERadioAccessCapabilityInformation__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UERadioAccessCapabilityInformation__criticalExtensions__Type with end) n0
           end t0).

Lemma UERadioAccessCapabilityInformation__criticalExtensions__helper2 :  forall (y : UERadioAccessCapabilityInformation__criticalExtensions__Type), UERadioAccessCapabilityInformation__criticalExtensions__cond y -> choice_cond UERadioAccessCapabilityInformation__criticalExtensions__list (UERadioAccessCapabilityInformation__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UERadioAccessCapabilityInformation__criticalExtensions__helper3 :  forall (y : UERadioAccessCapabilityInformation__criticalExtensions__Type), UERadioAccessCapabilityInformation__criticalExtensions__F2 (UERadioAccessCapabilityInformation__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UERadioAccessCapabilityInformation__criticalExtensions__helper4 : (forall b : choice UERadioAccessCapabilityInformation__criticalExtensions__list, choice_cond UERadioAccessCapabilityInformation__criticalExtensions__list b -> UERadioAccessCapabilityInformation__criticalExtensions__cond (UERadioAccessCapabilityInformation__criticalExtensions__F2 b) /\ UERadioAccessCapabilityInformation__criticalExtensions__F1 (UERadioAccessCapabilityInformation__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UERadioAccessCapabilityInformation__criticalExtensions__F1 UERadioAccessCapabilityInformation__criticalExtensions__F2.
Definition UERadioAccessCapabilityInformation__criticalExtensions__Format : T_Format UERadioAccessCapabilityInformation__criticalExtensions__Type UERadioAccessCapabilityInformation__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format UERadioAccessCapabilityInformation__criticalExtensions__cond UERadioAccessCapabilityInformation__criticalExtensions__list__Format UERadioAccessCapabilityInformation__criticalExtensions__F1 UERadioAccessCapabilityInformation__criticalExtensions__F2 UERadioAccessCapabilityInformation__criticalExtensions__helper2 UERadioAccessCapabilityInformation__criticalExtensions__helper3 UERadioAccessCapabilityInformation__criticalExtensions__helper4.
Opaque UERadioAccessCapabilityInformation__criticalExtensions__cond UERadioAccessCapabilityInformation__criticalExtensions__Format.


Definition UERadioAccessCapabilityInformation__Format_Type := Eval cbn in seq_format_prod UERadioAccessCapabilityInformation__list.
Definition UERadioAccessCapabilityInformation__Format_list : UERadioAccessCapabilityInformation__Format_Type :=
  (UERadioAccessCapabilityInformation__criticalExtensions__Format, unit_format).
Definition UERadioAccessCapabilityInformation__list__Format := (*Eval compute in *) seq_format UERadioAccessCapabilityInformation__list UERadioAccessCapabilityInformation__Format_list.
Definition UERadioAccessCapabilityInformation__F1 z :=
  (UERadioAccessCapabilityInformation__criticalExtensions z, tt).
Definition UERadioAccessCapabilityInformation__F2 (y : seq_type UERadioAccessCapabilityInformation__list) :=
  match y with
  | (i0, _)=>
    make__UERadioAccessCapabilityInformation__Type i0
  end.
Lemma UERadioAccessCapabilityInformation__F1F2_cond (z : UERadioAccessCapabilityInformation__Type)
  : UERadioAccessCapabilityInformation__cond z ->
  (seq_cond UERadioAccessCapabilityInformation__list (UERadioAccessCapabilityInformation__F1 z)).
intro H. unfold UERadioAccessCapabilityInformation__cond in H. simpl. auto. Qed.
Lemma UERadioAccessCapabilityInformation__F1F2_cond2 (z : UERadioAccessCapabilityInformation__Type)
 : UERadioAccessCapabilityInformation__F2 (UERadioAccessCapabilityInformation__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UERadioAccessCapabilityInformation__F2F1_cond (y : seq_type UERadioAccessCapabilityInformation__list)
  : seq_cond UERadioAccessCapabilityInformation__list y ->
 (UERadioAccessCapabilityInformation__cond (UERadioAccessCapabilityInformation__F2 y)) /\  UERadioAccessCapabilityInformation__F1 (UERadioAccessCapabilityInformation__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UERadioAccessCapabilityInformation__cond. simpl in *. auto.
 - simpl. unfold UERadioAccessCapabilityInformation__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UERadioAccessCapabilityInformation__Format : T_Format UERadioAccessCapabilityInformation__Type UERadioAccessCapabilityInformation__cond :=
        proj2_format  UERadioAccessCapabilityInformation__cond UERadioAccessCapabilityInformation__list__Format
    UERadioAccessCapabilityInformation__F1 UERadioAccessCapabilityInformation__F2 UERadioAccessCapabilityInformation__F1F2_cond  UERadioAccessCapabilityInformation__F1F2_cond2 UERadioAccessCapabilityInformation__F2F1_cond.
Opaque UERadioAccessCapabilityInformation__cond UERadioAccessCapabilityInformation__Format.

