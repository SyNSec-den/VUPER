Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasurementReport_IEs.

Opaque MeasurementReport_IEs__cond MeasurementReport_IEs__Format.

Record MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type : Set := make__MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition MeasurementReport__criticalExtensions__criticalExtensionsFuture__cond (z : MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive MeasurementReport__criticalExtensions__Type : Set :=
  | MeasurementReport__criticalExtensions__measurementReport : MeasurementReport_IEs__Type -> MeasurementReport__criticalExtensions__Type
  | MeasurementReport__criticalExtensions__criticalExtensionsFuture : MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type -> MeasurementReport__criticalExtensions__Type
.
Definition MeasurementReport__criticalExtensions__list : list typ := (
typ_cons MeasurementReport_IEs__Type MeasurementReport_IEs__cond ::
typ_cons MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type MeasurementReport__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition MeasurementReport__criticalExtensions__cond (c : MeasurementReport__criticalExtensions__Type) := 
  match c with
  | MeasurementReport__criticalExtensions__measurementReport t => MeasurementReport_IEs__cond t 
  | MeasurementReport__criticalExtensions__criticalExtensionsFuture t => MeasurementReport__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma MeasurementReport__criticalExtensions__len_helper1 : to_bit_sz (length MeasurementReport__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasurementReport__criticalExtensions__len_helper2 : 2 <= length2 MeasurementReport__criticalExtensions__list.
 simpl. lia. Qed.
Record MeasurementReport__Type : Set :=
  make__MeasurementReport__Type {
    MeasurementReport__criticalExtensions : MeasurementReport__criticalExtensions__Type ;
}.
Definition MeasurementReport__list := (
 Nor MeasurementReport__criticalExtensions__Type MeasurementReport__criticalExtensions__cond ::
 nil).
Definition MeasurementReport__cond z := 
  MeasurementReport__criticalExtensions__cond (MeasurementReport__criticalExtensions z) /\
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
Definition MeasurementReport__criticalExtensions__criticalExtensionsFuture__helper : forall a : MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition MeasurementReport__criticalExtensions__criticalExtensionsFuture__Format : T_Format MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type MeasurementReport__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type)
    MeasurementReport__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque MeasurementReport__criticalExtensions__criticalExtensionsFuture__cond MeasurementReport__criticalExtensions__criticalExtensionsFuture__Format.


Definition MeasurementReport__criticalExtensions__Format_Type := Eval cbn in get_formats MeasurementReport__criticalExtensions__list.
Definition MeasurementReport__criticalExtensions__Format_list : MeasurementReport__criticalExtensions__Format_Type :=
  (MeasurementReport_IEs__Format, (MeasurementReport__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition MeasurementReport__criticalExtensions__list__Format := Eval compute in choice_format MeasurementReport__criticalExtensions__list MeasurementReport__criticalExtensions__len_helper1 MeasurementReport__criticalExtensions__len_helper2  MeasurementReport__criticalExtensions__Format_list.
Definition MeasurementReport__criticalExtensions__F1 (z : MeasurementReport__criticalExtensions__Type) : (choice MeasurementReport__criticalExtensions__list) :=
  match z with
   | MeasurementReport__criticalExtensions__measurementReport t => existT _ 0 t
  | MeasurementReport__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition MeasurementReport__criticalExtensions__g := (fun n => typ_set (get_nth_typ MeasurementReport__criticalExtensions__list n)).
Definition MeasurementReport__criticalExtensions__F2 (y : choice MeasurementReport__criticalExtensions__list) : MeasurementReport__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasurementReport__criticalExtensions__g n -> MeasurementReport__criticalExtensions__Type) with
    | 0 => fun (t : MeasurementReport_IEs__Type) => MeasurementReport__criticalExtensions__measurementReport t 
    | 1 => fun (t : MeasurementReport__criticalExtensions__criticalExtensionsFuture__Type) => MeasurementReport__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MeasurementReport__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MeasurementReport__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasurementReport__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MeasurementReport__criticalExtensions__Type with end) n0
           end t0).

Lemma MeasurementReport__criticalExtensions__helper2 :  forall (y : MeasurementReport__criticalExtensions__Type), MeasurementReport__criticalExtensions__cond y -> choice_cond MeasurementReport__criticalExtensions__list (MeasurementReport__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasurementReport__criticalExtensions__helper3 :  forall (y : MeasurementReport__criticalExtensions__Type), MeasurementReport__criticalExtensions__F2 (MeasurementReport__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasurementReport__criticalExtensions__helper4 : (forall b : choice MeasurementReport__criticalExtensions__list, choice_cond MeasurementReport__criticalExtensions__list b -> MeasurementReport__criticalExtensions__cond (MeasurementReport__criticalExtensions__F2 b) /\ MeasurementReport__criticalExtensions__F1 (MeasurementReport__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasurementReport__criticalExtensions__F1 MeasurementReport__criticalExtensions__F2.
Definition MeasurementReport__criticalExtensions__Format : T_Format MeasurementReport__criticalExtensions__Type MeasurementReport__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format MeasurementReport__criticalExtensions__cond MeasurementReport__criticalExtensions__list__Format MeasurementReport__criticalExtensions__F1 MeasurementReport__criticalExtensions__F2 MeasurementReport__criticalExtensions__helper2 MeasurementReport__criticalExtensions__helper3 MeasurementReport__criticalExtensions__helper4.
Opaque MeasurementReport__criticalExtensions__cond MeasurementReport__criticalExtensions__Format.


Definition MeasurementReport__Format_Type := Eval cbn in seq_format_prod MeasurementReport__list.
Definition MeasurementReport__Format_list : MeasurementReport__Format_Type :=
  (MeasurementReport__criticalExtensions__Format, unit_format).
Definition MeasurementReport__list__Format := (*Eval compute in *) seq_format MeasurementReport__list MeasurementReport__Format_list.
Definition MeasurementReport__F1 z :=
  (MeasurementReport__criticalExtensions z, tt).
Definition MeasurementReport__F2 (y : seq_type MeasurementReport__list) :=
  match y with
  | (i0, _)=>
    make__MeasurementReport__Type i0
  end.
Lemma MeasurementReport__F1F2_cond (z : MeasurementReport__Type)
  : MeasurementReport__cond z ->
  (seq_cond MeasurementReport__list (MeasurementReport__F1 z)).
intro H. unfold MeasurementReport__cond in H. simpl. auto. Qed.
Lemma MeasurementReport__F1F2_cond2 (z : MeasurementReport__Type)
 : MeasurementReport__F2 (MeasurementReport__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasurementReport__F2F1_cond (y : seq_type MeasurementReport__list)
  : seq_cond MeasurementReport__list y ->
 (MeasurementReport__cond (MeasurementReport__F2 y)) /\  MeasurementReport__F1 (MeasurementReport__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasurementReport__cond. simpl in *. auto.
 - simpl. unfold MeasurementReport__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasurementReport__Format : T_Format MeasurementReport__Type MeasurementReport__cond :=
        proj2_format  MeasurementReport__cond MeasurementReport__list__Format
    MeasurementReport__F1 MeasurementReport__F2 MeasurementReport__F1F2_cond  MeasurementReport__F1F2_cond2 MeasurementReport__F2F1_cond.
Opaque MeasurementReport__cond MeasurementReport__Format.

