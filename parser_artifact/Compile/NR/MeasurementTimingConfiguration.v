Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.MeasurementTimingConfiguration_IEs.

Opaque MeasurementTimingConfiguration_IEs__cond MeasurementTimingConfiguration_IEs__Format.


Inductive MeasurementTimingConfiguration__criticalExtensions__c1__Type : Set :=
  | MeasurementTimingConfiguration__criticalExtensions__c1__measTimingConf : MeasurementTimingConfiguration_IEs__Type -> MeasurementTimingConfiguration__criticalExtensions__c1__Type
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare3 : unit -> MeasurementTimingConfiguration__criticalExtensions__c1__Type
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare2 : unit -> MeasurementTimingConfiguration__criticalExtensions__c1__Type
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare1 : unit -> MeasurementTimingConfiguration__criticalExtensions__c1__Type
.
Definition MeasurementTimingConfiguration__criticalExtensions__c1__list : list typ := (
typ_cons MeasurementTimingConfiguration_IEs__Type MeasurementTimingConfiguration_IEs__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition MeasurementTimingConfiguration__criticalExtensions__c1__cond (c : MeasurementTimingConfiguration__criticalExtensions__c1__Type) := 
  match c with
  | MeasurementTimingConfiguration__criticalExtensions__c1__measTimingConf t => MeasurementTimingConfiguration_IEs__cond t 
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare3 t => (fun _ => True) t 
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare2 t => (fun _ => True) t 
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare1 t => (fun _ => True) t 
  end.

Lemma MeasurementTimingConfiguration__criticalExtensions__c1__len_helper1 : to_bit_sz (length MeasurementTimingConfiguration__criticalExtensions__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasurementTimingConfiguration__criticalExtensions__c1__len_helper2 : 2 <= length2 MeasurementTimingConfiguration__criticalExtensions__c1__list.
 simpl. lia. Qed.
Record MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type : Set := make__MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__cond (z : MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive MeasurementTimingConfiguration__criticalExtensions__Type : Set :=
  | MeasurementTimingConfiguration__criticalExtensions__c1 : MeasurementTimingConfiguration__criticalExtensions__c1__Type -> MeasurementTimingConfiguration__criticalExtensions__Type
  | MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture : MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type -> MeasurementTimingConfiguration__criticalExtensions__Type
.
Definition MeasurementTimingConfiguration__criticalExtensions__list : list typ := (
typ_cons MeasurementTimingConfiguration__criticalExtensions__c1__Type MeasurementTimingConfiguration__criticalExtensions__c1__cond ::
typ_cons MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition MeasurementTimingConfiguration__criticalExtensions__cond (c : MeasurementTimingConfiguration__criticalExtensions__Type) := 
  match c with
  | MeasurementTimingConfiguration__criticalExtensions__c1 t => MeasurementTimingConfiguration__criticalExtensions__c1__cond t 
  | MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture t => MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma MeasurementTimingConfiguration__criticalExtensions__len_helper1 : to_bit_sz (length MeasurementTimingConfiguration__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasurementTimingConfiguration__criticalExtensions__len_helper2 : 2 <= length2 MeasurementTimingConfiguration__criticalExtensions__list.
 simpl. lia. Qed.
Record MeasurementTimingConfiguration__Type : Set :=
  make__MeasurementTimingConfiguration__Type {
    MeasurementTimingConfiguration__criticalExtensions : MeasurementTimingConfiguration__criticalExtensions__Type ;
}.
Definition MeasurementTimingConfiguration__list := (
 Nor MeasurementTimingConfiguration__criticalExtensions__Type MeasurementTimingConfiguration__criticalExtensions__cond ::
 nil).
Definition MeasurementTimingConfiguration__cond z := 
  MeasurementTimingConfiguration__criticalExtensions__cond (MeasurementTimingConfiguration__criticalExtensions z) /\
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

Definition MeasurementTimingConfiguration__criticalExtensions__c1__Format_Type := Eval cbn in get_formats MeasurementTimingConfiguration__criticalExtensions__c1__list.
Definition MeasurementTimingConfiguration__criticalExtensions__c1__Format_list : MeasurementTimingConfiguration__criticalExtensions__c1__Format_Type :=
  (MeasurementTimingConfiguration_IEs__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))).
Definition MeasurementTimingConfiguration__criticalExtensions__c1__list__Format := Eval compute in choice_format MeasurementTimingConfiguration__criticalExtensions__c1__list MeasurementTimingConfiguration__criticalExtensions__c1__len_helper1 MeasurementTimingConfiguration__criticalExtensions__c1__len_helper2  MeasurementTimingConfiguration__criticalExtensions__c1__Format_list.
Definition MeasurementTimingConfiguration__criticalExtensions__c1__F1 (z : MeasurementTimingConfiguration__criticalExtensions__c1__Type) : (choice MeasurementTimingConfiguration__criticalExtensions__c1__list) :=
  match z with
   | MeasurementTimingConfiguration__criticalExtensions__c1__measTimingConf t => existT _ 0 t
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare3 t => existT _ 1 t
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare2 t => existT _ 2 t
  | MeasurementTimingConfiguration__criticalExtensions__c1__spare1 t => existT _ 3 t
  end.
Definition MeasurementTimingConfiguration__criticalExtensions__c1__g := (fun n => typ_set (get_nth_typ MeasurementTimingConfiguration__criticalExtensions__c1__list n)).
Definition MeasurementTimingConfiguration__criticalExtensions__c1__F2 (y : choice MeasurementTimingConfiguration__criticalExtensions__c1__list) : MeasurementTimingConfiguration__criticalExtensions__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasurementTimingConfiguration__criticalExtensions__c1__g n -> MeasurementTimingConfiguration__criticalExtensions__c1__Type) with
    | 0 => fun (t : MeasurementTimingConfiguration_IEs__Type) => MeasurementTimingConfiguration__criticalExtensions__c1__measTimingConf t 
    | 1 => fun (t : unit) => MeasurementTimingConfiguration__criticalExtensions__c1__spare3 t 
    | 2 => fun (t : unit) => MeasurementTimingConfiguration__criticalExtensions__c1__spare2 t 
    | 3 => fun (t : unit) => MeasurementTimingConfiguration__criticalExtensions__c1__spare1 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : MeasurementTimingConfiguration__criticalExtensions__c1__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ MeasurementTimingConfiguration__criticalExtensions__c1__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasurementTimingConfiguration__criticalExtensions__c1__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return MeasurementTimingConfiguration__criticalExtensions__c1__Type with end) n0
           end t0).

Lemma MeasurementTimingConfiguration__criticalExtensions__c1__helper2 :  forall (y : MeasurementTimingConfiguration__criticalExtensions__c1__Type), MeasurementTimingConfiguration__criticalExtensions__c1__cond y -> choice_cond MeasurementTimingConfiguration__criticalExtensions__c1__list (MeasurementTimingConfiguration__criticalExtensions__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasurementTimingConfiguration__criticalExtensions__c1__helper3 :  forall (y : MeasurementTimingConfiguration__criticalExtensions__c1__Type), MeasurementTimingConfiguration__criticalExtensions__c1__F2 (MeasurementTimingConfiguration__criticalExtensions__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasurementTimingConfiguration__criticalExtensions__c1__helper4 : (forall b : choice MeasurementTimingConfiguration__criticalExtensions__c1__list, choice_cond MeasurementTimingConfiguration__criticalExtensions__c1__list b -> MeasurementTimingConfiguration__criticalExtensions__c1__cond (MeasurementTimingConfiguration__criticalExtensions__c1__F2 b) /\ MeasurementTimingConfiguration__criticalExtensions__c1__F1 (MeasurementTimingConfiguration__criticalExtensions__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasurementTimingConfiguration__criticalExtensions__c1__F1 MeasurementTimingConfiguration__criticalExtensions__c1__F2.
Definition MeasurementTimingConfiguration__criticalExtensions__c1__Format : T_Format MeasurementTimingConfiguration__criticalExtensions__c1__Type MeasurementTimingConfiguration__criticalExtensions__c1__cond :=
  (* Eval compute in *) proj2_format MeasurementTimingConfiguration__criticalExtensions__c1__cond MeasurementTimingConfiguration__criticalExtensions__c1__list__Format MeasurementTimingConfiguration__criticalExtensions__c1__F1 MeasurementTimingConfiguration__criticalExtensions__c1__F2 MeasurementTimingConfiguration__criticalExtensions__c1__helper2 MeasurementTimingConfiguration__criticalExtensions__c1__helper3 MeasurementTimingConfiguration__criticalExtensions__c1__helper4.
Opaque MeasurementTimingConfiguration__criticalExtensions__c1__cond MeasurementTimingConfiguration__criticalExtensions__c1__Format.

Definition MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__helper : forall a : MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Format : T_Format MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type)
    MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__cond MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Format.


Definition MeasurementTimingConfiguration__criticalExtensions__Format_Type := Eval cbn in get_formats MeasurementTimingConfiguration__criticalExtensions__list.
Definition MeasurementTimingConfiguration__criticalExtensions__Format_list : MeasurementTimingConfiguration__criticalExtensions__Format_Type :=
  (MeasurementTimingConfiguration__criticalExtensions__c1__Format, (MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition MeasurementTimingConfiguration__criticalExtensions__list__Format := Eval compute in choice_format MeasurementTimingConfiguration__criticalExtensions__list MeasurementTimingConfiguration__criticalExtensions__len_helper1 MeasurementTimingConfiguration__criticalExtensions__len_helper2  MeasurementTimingConfiguration__criticalExtensions__Format_list.
Definition MeasurementTimingConfiguration__criticalExtensions__F1 (z : MeasurementTimingConfiguration__criticalExtensions__Type) : (choice MeasurementTimingConfiguration__criticalExtensions__list) :=
  match z with
   | MeasurementTimingConfiguration__criticalExtensions__c1 t => existT _ 0 t
  | MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition MeasurementTimingConfiguration__criticalExtensions__g := (fun n => typ_set (get_nth_typ MeasurementTimingConfiguration__criticalExtensions__list n)).
Definition MeasurementTimingConfiguration__criticalExtensions__F2 (y : choice MeasurementTimingConfiguration__criticalExtensions__list) : MeasurementTimingConfiguration__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasurementTimingConfiguration__criticalExtensions__g n -> MeasurementTimingConfiguration__criticalExtensions__Type) with
    | 0 => fun (t : MeasurementTimingConfiguration__criticalExtensions__c1__Type) => MeasurementTimingConfiguration__criticalExtensions__c1 t 
    | 1 => fun (t : MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture__Type) => MeasurementTimingConfiguration__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MeasurementTimingConfiguration__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MeasurementTimingConfiguration__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasurementTimingConfiguration__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MeasurementTimingConfiguration__criticalExtensions__Type with end) n0
           end t0).

Lemma MeasurementTimingConfiguration__criticalExtensions__helper2 :  forall (y : MeasurementTimingConfiguration__criticalExtensions__Type), MeasurementTimingConfiguration__criticalExtensions__cond y -> choice_cond MeasurementTimingConfiguration__criticalExtensions__list (MeasurementTimingConfiguration__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasurementTimingConfiguration__criticalExtensions__helper3 :  forall (y : MeasurementTimingConfiguration__criticalExtensions__Type), MeasurementTimingConfiguration__criticalExtensions__F2 (MeasurementTimingConfiguration__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasurementTimingConfiguration__criticalExtensions__helper4 : (forall b : choice MeasurementTimingConfiguration__criticalExtensions__list, choice_cond MeasurementTimingConfiguration__criticalExtensions__list b -> MeasurementTimingConfiguration__criticalExtensions__cond (MeasurementTimingConfiguration__criticalExtensions__F2 b) /\ MeasurementTimingConfiguration__criticalExtensions__F1 (MeasurementTimingConfiguration__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasurementTimingConfiguration__criticalExtensions__F1 MeasurementTimingConfiguration__criticalExtensions__F2.
Definition MeasurementTimingConfiguration__criticalExtensions__Format : T_Format MeasurementTimingConfiguration__criticalExtensions__Type MeasurementTimingConfiguration__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format MeasurementTimingConfiguration__criticalExtensions__cond MeasurementTimingConfiguration__criticalExtensions__list__Format MeasurementTimingConfiguration__criticalExtensions__F1 MeasurementTimingConfiguration__criticalExtensions__F2 MeasurementTimingConfiguration__criticalExtensions__helper2 MeasurementTimingConfiguration__criticalExtensions__helper3 MeasurementTimingConfiguration__criticalExtensions__helper4.
Opaque MeasurementTimingConfiguration__criticalExtensions__cond MeasurementTimingConfiguration__criticalExtensions__Format.


Definition MeasurementTimingConfiguration__Format_Type := Eval cbn in seq_format_prod MeasurementTimingConfiguration__list.
Definition MeasurementTimingConfiguration__Format_list : MeasurementTimingConfiguration__Format_Type :=
  (MeasurementTimingConfiguration__criticalExtensions__Format, unit_format).
Definition MeasurementTimingConfiguration__list__Format := (*Eval compute in *) seq_format MeasurementTimingConfiguration__list MeasurementTimingConfiguration__Format_list.
Definition MeasurementTimingConfiguration__F1 z :=
  (MeasurementTimingConfiguration__criticalExtensions z, tt).
Definition MeasurementTimingConfiguration__F2 (y : seq_type MeasurementTimingConfiguration__list) :=
  match y with
  | (i0, _)=>
    make__MeasurementTimingConfiguration__Type i0
  end.
Lemma MeasurementTimingConfiguration__F1F2_cond (z : MeasurementTimingConfiguration__Type)
  : MeasurementTimingConfiguration__cond z ->
  (seq_cond MeasurementTimingConfiguration__list (MeasurementTimingConfiguration__F1 z)).
intro H. unfold MeasurementTimingConfiguration__cond in H. simpl. auto. Qed.
Lemma MeasurementTimingConfiguration__F1F2_cond2 (z : MeasurementTimingConfiguration__Type)
 : MeasurementTimingConfiguration__F2 (MeasurementTimingConfiguration__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasurementTimingConfiguration__F2F1_cond (y : seq_type MeasurementTimingConfiguration__list)
  : seq_cond MeasurementTimingConfiguration__list y ->
 (MeasurementTimingConfiguration__cond (MeasurementTimingConfiguration__F2 y)) /\  MeasurementTimingConfiguration__F1 (MeasurementTimingConfiguration__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasurementTimingConfiguration__cond. simpl in *. auto.
 - simpl. unfold MeasurementTimingConfiguration__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasurementTimingConfiguration__Format : T_Format MeasurementTimingConfiguration__Type MeasurementTimingConfiguration__cond :=
        proj2_format  MeasurementTimingConfiguration__cond MeasurementTimingConfiguration__list__Format
    MeasurementTimingConfiguration__F1 MeasurementTimingConfiguration__F2 MeasurementTimingConfiguration__F1F2_cond  MeasurementTimingConfiguration__F1F2_cond2 MeasurementTimingConfiguration__F2F1_cond.
Opaque MeasurementTimingConfiguration__cond MeasurementTimingConfiguration__Format.

