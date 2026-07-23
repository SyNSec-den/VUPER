Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.MeasurementReportSidelink_r16_IEs.

Opaque MeasurementReportSidelink_r16_IEs__cond MeasurementReportSidelink_r16_IEs__Format.

Record MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type : Set := make__MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__cond (z : MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive MeasurementReportSidelink__criticalExtensions__Type : Set :=
  | MeasurementReportSidelink__criticalExtensions__measurementReportSidelink_r16 : MeasurementReportSidelink_r16_IEs__Type -> MeasurementReportSidelink__criticalExtensions__Type
  | MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture : MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type -> MeasurementReportSidelink__criticalExtensions__Type
.
Definition MeasurementReportSidelink__criticalExtensions__list : list typ := (
typ_cons MeasurementReportSidelink_r16_IEs__Type MeasurementReportSidelink_r16_IEs__cond ::
typ_cons MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition MeasurementReportSidelink__criticalExtensions__cond (c : MeasurementReportSidelink__criticalExtensions__Type) := 
  match c with
  | MeasurementReportSidelink__criticalExtensions__measurementReportSidelink_r16 t => MeasurementReportSidelink_r16_IEs__cond t 
  | MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture t => MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma MeasurementReportSidelink__criticalExtensions__len_helper1 : to_bit_sz (length MeasurementReportSidelink__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasurementReportSidelink__criticalExtensions__len_helper2 : 2 <= length2 MeasurementReportSidelink__criticalExtensions__list.
 simpl. lia. Qed.
Record MeasurementReportSidelink__Type : Set :=
  make__MeasurementReportSidelink__Type {
    MeasurementReportSidelink__criticalExtensions : MeasurementReportSidelink__criticalExtensions__Type ;
}.
Definition MeasurementReportSidelink__list := (
 Nor MeasurementReportSidelink__criticalExtensions__Type MeasurementReportSidelink__criticalExtensions__cond ::
 nil).
Definition MeasurementReportSidelink__cond z := 
  MeasurementReportSidelink__criticalExtensions__cond (MeasurementReportSidelink__criticalExtensions z) /\
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
Definition MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__helper : forall a : MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Format : T_Format MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type)
    MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__cond MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Format.


Definition MeasurementReportSidelink__criticalExtensions__Format_Type := Eval cbn in get_formats MeasurementReportSidelink__criticalExtensions__list.
Definition MeasurementReportSidelink__criticalExtensions__Format_list : MeasurementReportSidelink__criticalExtensions__Format_Type :=
  (MeasurementReportSidelink_r16_IEs__Format, (MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition MeasurementReportSidelink__criticalExtensions__list__Format := Eval compute in choice_format MeasurementReportSidelink__criticalExtensions__list MeasurementReportSidelink__criticalExtensions__len_helper1 MeasurementReportSidelink__criticalExtensions__len_helper2  MeasurementReportSidelink__criticalExtensions__Format_list.
Definition MeasurementReportSidelink__criticalExtensions__F1 (z : MeasurementReportSidelink__criticalExtensions__Type) : (choice MeasurementReportSidelink__criticalExtensions__list) :=
  match z with
   | MeasurementReportSidelink__criticalExtensions__measurementReportSidelink_r16 t => existT _ 0 t
  | MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition MeasurementReportSidelink__criticalExtensions__g := (fun n => typ_set (get_nth_typ MeasurementReportSidelink__criticalExtensions__list n)).
Definition MeasurementReportSidelink__criticalExtensions__F2 (y : choice MeasurementReportSidelink__criticalExtensions__list) : MeasurementReportSidelink__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasurementReportSidelink__criticalExtensions__g n -> MeasurementReportSidelink__criticalExtensions__Type) with
    | 0 => fun (t : MeasurementReportSidelink_r16_IEs__Type) => MeasurementReportSidelink__criticalExtensions__measurementReportSidelink_r16 t 
    | 1 => fun (t : MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture__Type) => MeasurementReportSidelink__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MeasurementReportSidelink__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MeasurementReportSidelink__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasurementReportSidelink__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MeasurementReportSidelink__criticalExtensions__Type with end) n0
           end t0).

Lemma MeasurementReportSidelink__criticalExtensions__helper2 :  forall (y : MeasurementReportSidelink__criticalExtensions__Type), MeasurementReportSidelink__criticalExtensions__cond y -> choice_cond MeasurementReportSidelink__criticalExtensions__list (MeasurementReportSidelink__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasurementReportSidelink__criticalExtensions__helper3 :  forall (y : MeasurementReportSidelink__criticalExtensions__Type), MeasurementReportSidelink__criticalExtensions__F2 (MeasurementReportSidelink__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasurementReportSidelink__criticalExtensions__helper4 : (forall b : choice MeasurementReportSidelink__criticalExtensions__list, choice_cond MeasurementReportSidelink__criticalExtensions__list b -> MeasurementReportSidelink__criticalExtensions__cond (MeasurementReportSidelink__criticalExtensions__F2 b) /\ MeasurementReportSidelink__criticalExtensions__F1 (MeasurementReportSidelink__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasurementReportSidelink__criticalExtensions__F1 MeasurementReportSidelink__criticalExtensions__F2.
Definition MeasurementReportSidelink__criticalExtensions__Format : T_Format MeasurementReportSidelink__criticalExtensions__Type MeasurementReportSidelink__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format MeasurementReportSidelink__criticalExtensions__cond MeasurementReportSidelink__criticalExtensions__list__Format MeasurementReportSidelink__criticalExtensions__F1 MeasurementReportSidelink__criticalExtensions__F2 MeasurementReportSidelink__criticalExtensions__helper2 MeasurementReportSidelink__criticalExtensions__helper3 MeasurementReportSidelink__criticalExtensions__helper4.
Opaque MeasurementReportSidelink__criticalExtensions__cond MeasurementReportSidelink__criticalExtensions__Format.


Definition MeasurementReportSidelink__Format_Type := Eval cbn in seq_format_prod MeasurementReportSidelink__list.
Definition MeasurementReportSidelink__Format_list : MeasurementReportSidelink__Format_Type :=
  (MeasurementReportSidelink__criticalExtensions__Format, unit_format).
Definition MeasurementReportSidelink__list__Format := (*Eval compute in *) seq_format MeasurementReportSidelink__list MeasurementReportSidelink__Format_list.
Definition MeasurementReportSidelink__F1 z :=
  (MeasurementReportSidelink__criticalExtensions z, tt).
Definition MeasurementReportSidelink__F2 (y : seq_type MeasurementReportSidelink__list) :=
  match y with
  | (i0, _)=>
    make__MeasurementReportSidelink__Type i0
  end.
Lemma MeasurementReportSidelink__F1F2_cond (z : MeasurementReportSidelink__Type)
  : MeasurementReportSidelink__cond z ->
  (seq_cond MeasurementReportSidelink__list (MeasurementReportSidelink__F1 z)).
intro H. unfold MeasurementReportSidelink__cond in H. simpl. auto. Qed.
Lemma MeasurementReportSidelink__F1F2_cond2 (z : MeasurementReportSidelink__Type)
 : MeasurementReportSidelink__F2 (MeasurementReportSidelink__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasurementReportSidelink__F2F1_cond (y : seq_type MeasurementReportSidelink__list)
  : seq_cond MeasurementReportSidelink__list y ->
 (MeasurementReportSidelink__cond (MeasurementReportSidelink__F2 y)) /\  MeasurementReportSidelink__F1 (MeasurementReportSidelink__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasurementReportSidelink__cond. simpl in *. auto.
 - simpl. unfold MeasurementReportSidelink__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasurementReportSidelink__Format : T_Format MeasurementReportSidelink__Type MeasurementReportSidelink__cond :=
        proj2_format  MeasurementReportSidelink__cond MeasurementReportSidelink__list__Format
    MeasurementReportSidelink__F1 MeasurementReportSidelink__F2 MeasurementReportSidelink__F1F2_cond  MeasurementReportSidelink__F1F2_cond2 MeasurementReportSidelink__F2F1_cond.
Opaque MeasurementReportSidelink__cond MeasurementReportSidelink__Format.

