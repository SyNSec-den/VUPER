Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Require Import NR.EUTRA_AllowedMeasBandwidth.

Opaque EUTRA_AllowedMeasBandwidth__cond EUTRA_AllowedMeasBandwidth__Format.

Require Import NR.CellListEUTRA_r16.

Opaque CellListEUTRA_r16__cond CellListEUTRA_r16__Format.

Inductive MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Type : Set :=
 | MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__rsrp
 | MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__rsrq
 | MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__both
.
Definition MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__cond := (fun (_ : MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Type) => True).
Lemma MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__nat__helper.

Definition MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F1 t :=
  match t with
  | MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__rsrp => 0
  | MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__rsrq => 1
  | MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__both => 2
  end.
Definition MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F2 n :=
  match n with
  | 0 => MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__rsrp
  | 1 => MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__rsrq
  | 2 => MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__both
  | _ => MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__rsrp
  end.
Lemma MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F1F2 : forall x : MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Type, (MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F1 x <= 2) /\ MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F2 (MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F1 x) = x. imp_solve. Qed.
Lemma MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F2F1 : forall (y : nat) (H : y <= 2), MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F1 (MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RSRP_RangeEUTRA.

Opaque RSRP_RangeEUTRA__cond RSRP_RangeEUTRA__Format.

Require Import NR.RSRQ_RangeEUTRA_r16.

Opaque RSRQ_RangeEUTRA_r16__cond RSRQ_RangeEUTRA_r16__Format.

Record MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Type : Set :=
  make__MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Type {
    MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__idleRSRP_Threshold_EUTRA_r16 : option RSRP_RangeEUTRA__Type ;
    MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__idleRSRQ_Threshold_EUTRA_r16 : option RSRQ_RangeEUTRA_r16__Type ;
}.
Definition MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list := (
 Opt RSRP_RangeEUTRA__Type RSRP_RangeEUTRA__cond ::
 Opt RSRQ_RangeEUTRA_r16__Type RSRQ_RangeEUTRA_r16__cond ::
 nil).
Definition MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond z := 
  opt_cond RSRP_RangeEUTRA__cond (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__idleRSRP_Threshold_EUTRA_r16 z) /\
  opt_cond RSRQ_RangeEUTRA_r16__cond (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__idleRSRQ_Threshold_EUTRA_r16 z) /\
  True.

Record MeasIdleCarrierEUTRA_r16__Type : Set :=
  make__MeasIdleCarrierEUTRA_r16__Type {
    MeasIdleCarrierEUTRA_r16__carrierFreqEUTRA_r16 : ARFCN_ValueEUTRA__Type ;
    MeasIdleCarrierEUTRA_r16__allowedMeasBandwidth_r16 : EUTRA_AllowedMeasBandwidth__Type ;
    MeasIdleCarrierEUTRA_r16__measCellListEUTRA_r16 : option CellListEUTRA_r16__Type ;
    MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16 : MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Type ;
    MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16 : option MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Type ;
}.
Definition MeasIdleCarrierEUTRA_r16__root_list : list seq_elem := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Nor EUTRA_AllowedMeasBandwidth__Type EUTRA_AllowedMeasBandwidth__cond ::
 Opt CellListEUTRA_r16__Type CellListEUTRA_r16__cond ::
 Nor MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Type MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__cond ::
 Opt MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Type MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond ::
 nil).
Definition MeasIdleCarrierEUTRA_r16__ext_list : list typ := (
  nil).
Definition MeasIdleCarrierEUTRA_r16__cond (z : MeasIdleCarrierEUTRA_r16__Type) := 
(  ARFCN_ValueEUTRA__cond (MeasIdleCarrierEUTRA_r16__carrierFreqEUTRA_r16 z) /\
  EUTRA_AllowedMeasBandwidth__cond (MeasIdleCarrierEUTRA_r16__allowedMeasBandwidth_r16 z) /\
  opt_cond CellListEUTRA_r16__cond (MeasIdleCarrierEUTRA_r16__measCellListEUTRA_r16 z) /\
  MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__cond (MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16 z) /\
  opt_cond MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16 z) /\
  True) /\ 
(  True).


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
Definition MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Format : T_Format MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__nat__Format MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F1 MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F2 MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F1F2 MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__F2F1.

Opaque MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__cond MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Format.


Definition MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Format_Type := Eval cbn in seq_format_prod MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list.
Definition MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Format_list : MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Format_Type :=
  (RSRP_RangeEUTRA__Format, (RSRQ_RangeEUTRA_r16__Format, unit_format)).
Definition MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list__Format := (*Eval compute in *) seq_format MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Format_list.
Definition MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1 z :=
  (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__idleRSRP_Threshold_EUTRA_r16 z, (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__idleRSRQ_Threshold_EUTRA_r16 z, tt)).
Definition MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F2 (y : seq_type MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Type i0 i1
  end.
Lemma MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1F2_cond (z : MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Type)
  : MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond z ->
  (seq_cond MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1 z)).
intro H. unfold MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond in H. simpl. auto. Qed.
Lemma MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1F2_cond2 (z : MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Type)
 : MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F2 (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F2F1_cond (y : seq_type MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list)
  : seq_cond MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list y ->
 (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F2 y)) /\  MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1 (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond. simpl in *. auto.
 - simpl. unfold MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Format : T_Format MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Type MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond :=
        proj2_format  MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__list__Format
    MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1 MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F2 MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1F2_cond  MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F1F2_cond2 MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__F2F1_cond.
Opaque MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__cond MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Format.


Definition MeasIdleCarrierEUTRA_r16__root_Format_Type := Eval cbn in seq_format_prod MeasIdleCarrierEUTRA_r16__root_list.
Definition MeasIdleCarrierEUTRA_r16__root_Format_list : MeasIdleCarrierEUTRA_r16__root_Format_Type :=
  (ARFCN_ValueEUTRA__Format, (EUTRA_AllowedMeasBandwidth__Format, (CellListEUTRA_r16__Format, (MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16__Format, (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16__Format, unit_format))))).

Definition MeasIdleCarrierEUTRA_r16__ext_Format_Type := Eval cbn in get_formats MeasIdleCarrierEUTRA_r16__ext_list.
Definition MeasIdleCarrierEUTRA_r16__ext_Format_list : MeasIdleCarrierEUTRA_r16__ext_Format_Type :=
  unit__Format.

Definition MeasIdleCarrierEUTRA_r16__list_type : Set := (seq_type MeasIdleCarrierEUTRA_r16__root_list) * (seq_ext_type MeasIdleCarrierEUTRA_r16__ext_list).
Definition MeasIdleCarrierEUTRA_r16__list_cond (z : MeasIdleCarrierEUTRA_r16__list_type) : Prop :=
        (seq_cond MeasIdleCarrierEUTRA_r16__root_list (fst z)) /\ (seq_ext_cond MeasIdleCarrierEUTRA_r16__ext_list (snd z)).
Definition MeasIdleCarrierEUTRA_r16__list_format : T_Format MeasIdleCarrierEUTRA_r16__list_type MeasIdleCarrierEUTRA_r16__list_cond :=
 (* Eval compute in *) seq_ext_format MeasIdleCarrierEUTRA_r16__root_list MeasIdleCarrierEUTRA_r16__root_Format_list MeasIdleCarrierEUTRA_r16__ext_list MeasIdleCarrierEUTRA_r16__ext_Format_list.

Opaque MeasIdleCarrierEUTRA_r16__list_format.
Definition MeasIdleCarrierEUTRA_r16__F1 (z : MeasIdleCarrierEUTRA_r16__Type) : MeasIdleCarrierEUTRA_r16__list_type :=
  (((MeasIdleCarrierEUTRA_r16__carrierFreqEUTRA_r16 z, (MeasIdleCarrierEUTRA_r16__allowedMeasBandwidth_r16 z, (MeasIdleCarrierEUTRA_r16__measCellListEUTRA_r16 z, (MeasIdleCarrierEUTRA_r16__reportQuantitiesEUTRA_r16 z, (MeasIdleCarrierEUTRA_r16__qualityThresholdEUTRA_r16 z, tt)))))), (
tt)).
Definition MeasIdleCarrierEUTRA_r16__F2 (y : MeasIdleCarrierEUTRA_r16__list_type) : MeasIdleCarrierEUTRA_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__MeasIdleCarrierEUTRA_r16__Type j0 j1 j2 j3 j4
  end.
Definition MeasIdleCarrierEUTRA_r16__helper1 : (forall a : MeasIdleCarrierEUTRA_r16__Type, MeasIdleCarrierEUTRA_r16__cond a -> MeasIdleCarrierEUTRA_r16__list_cond (MeasIdleCarrierEUTRA_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasIdleCarrierEUTRA_r16__helper2 : (forall a : MeasIdleCarrierEUTRA_r16__Type, MeasIdleCarrierEUTRA_r16__F2 (MeasIdleCarrierEUTRA_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasIdleCarrierEUTRA_r16__helper3 : (forall b : MeasIdleCarrierEUTRA_r16__list_type, MeasIdleCarrierEUTRA_r16__list_cond b -> MeasIdleCarrierEUTRA_r16__cond (MeasIdleCarrierEUTRA_r16__F2 b) /\ MeasIdleCarrierEUTRA_r16__F1 (MeasIdleCarrierEUTRA_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasIdleCarrierEUTRA_r16__cond, MeasIdleCarrierEUTRA_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasIdleCarrierEUTRA_r16__Format : T_Format MeasIdleCarrierEUTRA_r16__Type MeasIdleCarrierEUTRA_r16__cond :=
 proj2_format MeasIdleCarrierEUTRA_r16__cond MeasIdleCarrierEUTRA_r16__list_format  MeasIdleCarrierEUTRA_r16__F1 MeasIdleCarrierEUTRA_r16__F2 MeasIdleCarrierEUTRA_r16__helper1 MeasIdleCarrierEUTRA_r16__helper2 MeasIdleCarrierEUTRA_r16__helper3.

Opaque MeasIdleCarrierEUTRA_r16__cond MeasIdleCarrierEUTRA_r16__Format.

