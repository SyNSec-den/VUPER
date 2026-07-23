Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasConfigAppLayerId_r17.

Opaque MeasConfigAppLayerId_r17__cond MeasConfigAppLayerId_r17__Format.

Inductive MeasReportAppLayer_r17__appLayerSessionStatus_r17__Type : Set :=
 | MeasReportAppLayer_r17__appLayerSessionStatus_r17__started
 | MeasReportAppLayer_r17__appLayerSessionStatus_r17__stopped
.
Definition MeasReportAppLayer_r17__appLayerSessionStatus_r17__cond := (fun (_ : MeasReportAppLayer_r17__appLayerSessionStatus_r17__Type) => True).
Lemma MeasReportAppLayer_r17__appLayerSessionStatus_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasReportAppLayer_r17__appLayerSessionStatus_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MeasReportAppLayer_r17__appLayerSessionStatus_r17__nat__helper.

Definition MeasReportAppLayer_r17__appLayerSessionStatus_r17__F1 t :=
  match t with
  | MeasReportAppLayer_r17__appLayerSessionStatus_r17__started => 0
  | MeasReportAppLayer_r17__appLayerSessionStatus_r17__stopped => 1
  end.
Definition MeasReportAppLayer_r17__appLayerSessionStatus_r17__F2 n :=
  match n with
  | 0 => MeasReportAppLayer_r17__appLayerSessionStatus_r17__started
  | 1 => MeasReportAppLayer_r17__appLayerSessionStatus_r17__stopped
  | _ => MeasReportAppLayer_r17__appLayerSessionStatus_r17__started
  end.
Lemma MeasReportAppLayer_r17__appLayerSessionStatus_r17__F1F2 : forall x : MeasReportAppLayer_r17__appLayerSessionStatus_r17__Type, (MeasReportAppLayer_r17__appLayerSessionStatus_r17__F1 x <= 1) /\ MeasReportAppLayer_r17__appLayerSessionStatus_r17__F2 (MeasReportAppLayer_r17__appLayerSessionStatus_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasReportAppLayer_r17__appLayerSessionStatus_r17__F2F1 : forall (y : nat) (H : y <= 1), MeasReportAppLayer_r17__appLayerSessionStatus_r17__F1 (MeasReportAppLayer_r17__appLayerSessionStatus_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RAN_VisibleMeasurements_r17.

Opaque RAN_VisibleMeasurements_r17__cond RAN_VisibleMeasurements_r17__Format.

Record MeasReportAppLayer_r17__Type : Set :=
  make__MeasReportAppLayer_r17__Type {
    MeasReportAppLayer_r17__measConfigAppLayerId_r17 : MeasConfigAppLayerId_r17__Type ;
    MeasReportAppLayer_r17__measReportAppLayerContainer_r17 : option octet_string ;
    MeasReportAppLayer_r17__appLayerSessionStatus_r17 : option MeasReportAppLayer_r17__appLayerSessionStatus_r17__Type ;
    MeasReportAppLayer_r17__ran_VisibleMeasurements_r17 : option RAN_VisibleMeasurements_r17__Type ;
}.
Definition MeasReportAppLayer_r17__list := (
 Nor MeasConfigAppLayerId_r17__Type MeasConfigAppLayerId_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MeasReportAppLayer_r17__appLayerSessionStatus_r17__Type MeasReportAppLayer_r17__appLayerSessionStatus_r17__cond ::
 Opt RAN_VisibleMeasurements_r17__Type RAN_VisibleMeasurements_r17__cond ::
 nil).
Definition MeasReportAppLayer_r17__cond z := 
  MeasConfigAppLayerId_r17__cond (MeasReportAppLayer_r17__measConfigAppLayerId_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (MeasReportAppLayer_r17__measReportAppLayerContainer_r17 z) /\
  opt_cond MeasReportAppLayer_r17__appLayerSessionStatus_r17__cond (MeasReportAppLayer_r17__appLayerSessionStatus_r17 z) /\
  opt_cond RAN_VisibleMeasurements_r17__cond (MeasReportAppLayer_r17__ran_VisibleMeasurements_r17 z) /\
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
Definition MeasReportAppLayer_r17__appLayerSessionStatus_r17__Format : T_Format MeasReportAppLayer_r17__appLayerSessionStatus_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasReportAppLayer_r17__appLayerSessionStatus_r17__nat__Format MeasReportAppLayer_r17__appLayerSessionStatus_r17__F1 MeasReportAppLayer_r17__appLayerSessionStatus_r17__F2 MeasReportAppLayer_r17__appLayerSessionStatus_r17__F1F2 MeasReportAppLayer_r17__appLayerSessionStatus_r17__F2F1.

Opaque MeasReportAppLayer_r17__appLayerSessionStatus_r17__cond MeasReportAppLayer_r17__appLayerSessionStatus_r17__Format.


Definition MeasReportAppLayer_r17__Format_Type := Eval cbn in seq_format_prod MeasReportAppLayer_r17__list.
Definition MeasReportAppLayer_r17__Format_list : MeasReportAppLayer_r17__Format_Type :=
  (MeasConfigAppLayerId_r17__Format, (octet_string_nc__Format, (MeasReportAppLayer_r17__appLayerSessionStatus_r17__Format, (RAN_VisibleMeasurements_r17__Format, unit_format)))).
Definition MeasReportAppLayer_r17__list__Format := (*Eval compute in *) seq_format MeasReportAppLayer_r17__list MeasReportAppLayer_r17__Format_list.
Definition MeasReportAppLayer_r17__F1 z :=
  (MeasReportAppLayer_r17__measConfigAppLayerId_r17 z, (MeasReportAppLayer_r17__measReportAppLayerContainer_r17 z, (MeasReportAppLayer_r17__appLayerSessionStatus_r17 z, (MeasReportAppLayer_r17__ran_VisibleMeasurements_r17 z, tt)))).
Definition MeasReportAppLayer_r17__F2 (y : seq_type MeasReportAppLayer_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasReportAppLayer_r17__Type i0 i1 i2 i3
  end.
Lemma MeasReportAppLayer_r17__F1F2_cond (z : MeasReportAppLayer_r17__Type)
  : MeasReportAppLayer_r17__cond z ->
  (seq_cond MeasReportAppLayer_r17__list (MeasReportAppLayer_r17__F1 z)).
intro H. unfold MeasReportAppLayer_r17__cond in H. simpl. auto. Qed.
Lemma MeasReportAppLayer_r17__F1F2_cond2 (z : MeasReportAppLayer_r17__Type)
 : MeasReportAppLayer_r17__F2 (MeasReportAppLayer_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasReportAppLayer_r17__F2F1_cond (y : seq_type MeasReportAppLayer_r17__list)
  : seq_cond MeasReportAppLayer_r17__list y ->
 (MeasReportAppLayer_r17__cond (MeasReportAppLayer_r17__F2 y)) /\  MeasReportAppLayer_r17__F1 (MeasReportAppLayer_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasReportAppLayer_r17__cond. simpl in *. auto.
 - simpl. unfold MeasReportAppLayer_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasReportAppLayer_r17__Format : T_Format MeasReportAppLayer_r17__Type MeasReportAppLayer_r17__cond :=
        proj2_format  MeasReportAppLayer_r17__cond MeasReportAppLayer_r17__list__Format
    MeasReportAppLayer_r17__F1 MeasReportAppLayer_r17__F2 MeasReportAppLayer_r17__F1F2_cond  MeasReportAppLayer_r17__F1F2_cond2 MeasReportAppLayer_r17__F2F1_cond.
Opaque MeasReportAppLayer_r17__cond MeasReportAppLayer_r17__Format.

