Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Require Import NR.SS_RSSI_Measurement.

Opaque SS_RSSI_Measurement__cond SS_RSSI_Measurement__Format.

Record MeasTiming__frequencyAndTiming__Type : Set :=
  make__MeasTiming__frequencyAndTiming__Type {
    MeasTiming__frequencyAndTiming__carrierFreq : ARFCN_ValueNR__Type ;
    MeasTiming__frequencyAndTiming__ssbSubcarrierSpacing : SubcarrierSpacing__Type ;
    MeasTiming__frequencyAndTiming__ssb_MeasurementTimingConfiguration : SSB_MTC__Type ;
    MeasTiming__frequencyAndTiming__ss_RSSI_Measurement : option SS_RSSI_Measurement__Type ;
}.
Definition MeasTiming__frequencyAndTiming__list := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Nor SSB_MTC__Type SSB_MTC__cond ::
 Opt SS_RSSI_Measurement__Type SS_RSSI_Measurement__cond ::
 nil).
Definition MeasTiming__frequencyAndTiming__cond z := 
  ARFCN_ValueNR__cond (MeasTiming__frequencyAndTiming__carrierFreq z) /\
  SubcarrierSpacing__cond (MeasTiming__frequencyAndTiming__ssbSubcarrierSpacing z) /\
  SSB_MTC__cond (MeasTiming__frequencyAndTiming__ssb_MeasurementTimingConfiguration z) /\
  opt_cond SS_RSSI_Measurement__cond (MeasTiming__frequencyAndTiming__ss_RSSI_Measurement z) /\
  True.

Require Import NR.SSB_ToMeasure.

Opaque SSB_ToMeasure__cond SSB_ToMeasure__Format.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Record MeasTiming__ext0O__Type : Set :=
  make__MeasTiming__ext0O__Type {
    MeasTiming__ext0O__ssb_ToMeasure : option SSB_ToMeasure__Type ;
    MeasTiming__ext0O__physCellId : option PhysCellId__Type ;
}.
Definition MeasTiming__ext0O__list := (
 Opt SSB_ToMeasure__Type SSB_ToMeasure__cond ::
 Opt PhysCellId__Type PhysCellId__cond ::
 nil).
Definition MeasTiming__ext0O__cond z := 
  opt_cond SSB_ToMeasure__cond (MeasTiming__ext0O__ssb_ToMeasure z) /\
  opt_cond PhysCellId__cond (MeasTiming__ext0O__physCellId z) /\
  True.

Definition MeasTiming__ext0__Type := MeasTiming__ext0O__Type.
Definition MeasTiming__ext0__cond := MeasTiming__ext0O__cond.

Record MeasTiming__Type : Set :=
  make__MeasTiming__Type {
    MeasTiming__frequencyAndTiming : option MeasTiming__frequencyAndTiming__Type ;
    MeasTiming__ext0 : option MeasTiming__ext0__Type ;
}.
Definition MeasTiming__root_list : list seq_elem := (
 Opt MeasTiming__frequencyAndTiming__Type MeasTiming__frequencyAndTiming__cond ::
 nil).
Definition MeasTiming__ext_list : list typ := (
  typ_cons MeasTiming__ext0__Type MeasTiming__ext0__cond ::
  nil).
Definition MeasTiming__cond (z : MeasTiming__Type) := 
(  opt_cond MeasTiming__frequencyAndTiming__cond (MeasTiming__frequencyAndTiming z) /\
  True) /\ 
(  opt_cond MeasTiming__ext0__cond (MeasTiming__ext0 z) /\
  True).


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

Definition MeasTiming__frequencyAndTiming__Format_Type := Eval cbn in seq_format_prod MeasTiming__frequencyAndTiming__list.
Definition MeasTiming__frequencyAndTiming__Format_list : MeasTiming__frequencyAndTiming__Format_Type :=
  (ARFCN_ValueNR__Format, (SubcarrierSpacing__Format, (SSB_MTC__Format, (SS_RSSI_Measurement__Format, unit_format)))).
Definition MeasTiming__frequencyAndTiming__list__Format := (*Eval compute in *) seq_format MeasTiming__frequencyAndTiming__list MeasTiming__frequencyAndTiming__Format_list.
Definition MeasTiming__frequencyAndTiming__F1 z :=
  (MeasTiming__frequencyAndTiming__carrierFreq z, (MeasTiming__frequencyAndTiming__ssbSubcarrierSpacing z, (MeasTiming__frequencyAndTiming__ssb_MeasurementTimingConfiguration z, (MeasTiming__frequencyAndTiming__ss_RSSI_Measurement z, tt)))).
Definition MeasTiming__frequencyAndTiming__F2 (y : seq_type MeasTiming__frequencyAndTiming__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MeasTiming__frequencyAndTiming__Type i0 i1 i2 i3
  end.
Lemma MeasTiming__frequencyAndTiming__F1F2_cond (z : MeasTiming__frequencyAndTiming__Type)
  : MeasTiming__frequencyAndTiming__cond z ->
  (seq_cond MeasTiming__frequencyAndTiming__list (MeasTiming__frequencyAndTiming__F1 z)).
intro H. unfold MeasTiming__frequencyAndTiming__cond in H. simpl. auto. Qed.
Lemma MeasTiming__frequencyAndTiming__F1F2_cond2 (z : MeasTiming__frequencyAndTiming__Type)
 : MeasTiming__frequencyAndTiming__F2 (MeasTiming__frequencyAndTiming__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasTiming__frequencyAndTiming__F2F1_cond (y : seq_type MeasTiming__frequencyAndTiming__list)
  : seq_cond MeasTiming__frequencyAndTiming__list y ->
 (MeasTiming__frequencyAndTiming__cond (MeasTiming__frequencyAndTiming__F2 y)) /\  MeasTiming__frequencyAndTiming__F1 (MeasTiming__frequencyAndTiming__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasTiming__frequencyAndTiming__cond. simpl in *. auto.
 - simpl. unfold MeasTiming__frequencyAndTiming__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasTiming__frequencyAndTiming__Format : T_Format MeasTiming__frequencyAndTiming__Type MeasTiming__frequencyAndTiming__cond :=
        proj2_format  MeasTiming__frequencyAndTiming__cond MeasTiming__frequencyAndTiming__list__Format
    MeasTiming__frequencyAndTiming__F1 MeasTiming__frequencyAndTiming__F2 MeasTiming__frequencyAndTiming__F1F2_cond  MeasTiming__frequencyAndTiming__F1F2_cond2 MeasTiming__frequencyAndTiming__F2F1_cond.
Opaque MeasTiming__frequencyAndTiming__cond MeasTiming__frequencyAndTiming__Format.


Definition MeasTiming__ext0O__Format_Type := Eval cbn in seq_format_prod MeasTiming__ext0O__list.
Definition MeasTiming__ext0O__Format_list : MeasTiming__ext0O__Format_Type :=
  (SSB_ToMeasure__Format, (PhysCellId__Format, unit_format)).
Definition MeasTiming__ext0O__list__Format := (*Eval compute in *) seq_format MeasTiming__ext0O__list MeasTiming__ext0O__Format_list.
Definition MeasTiming__ext0O__F1 z :=
  (MeasTiming__ext0O__ssb_ToMeasure z, (MeasTiming__ext0O__physCellId z, tt)).
Definition MeasTiming__ext0O__F2 (y : seq_type MeasTiming__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MeasTiming__ext0O__Type i0 i1
  end.
Lemma MeasTiming__ext0O__F1F2_cond (z : MeasTiming__ext0O__Type)
  : MeasTiming__ext0O__cond z ->
  (seq_cond MeasTiming__ext0O__list (MeasTiming__ext0O__F1 z)).
intro H. unfold MeasTiming__ext0O__cond in H. simpl. auto. Qed.
Lemma MeasTiming__ext0O__F1F2_cond2 (z : MeasTiming__ext0O__Type)
 : MeasTiming__ext0O__F2 (MeasTiming__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MeasTiming__ext0O__F2F1_cond (y : seq_type MeasTiming__ext0O__list)
  : seq_cond MeasTiming__ext0O__list y ->
 (MeasTiming__ext0O__cond (MeasTiming__ext0O__F2 y)) /\  MeasTiming__ext0O__F1 (MeasTiming__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MeasTiming__ext0O__cond. simpl in *. auto.
 - simpl. unfold MeasTiming__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MeasTiming__ext0O__Format : T_Format MeasTiming__ext0O__Type MeasTiming__ext0O__cond :=
        proj2_format  MeasTiming__ext0O__cond MeasTiming__ext0O__list__Format
    MeasTiming__ext0O__F1 MeasTiming__ext0O__F2 MeasTiming__ext0O__F1F2_cond  MeasTiming__ext0O__F1F2_cond2 MeasTiming__ext0O__F2F1_cond.
Opaque MeasTiming__ext0O__cond MeasTiming__ext0O__Format.

Definition MeasTiming__ext0__check_all_none (b : MeasTiming__ext0O__Type) : bool :=
match b with 
  | make__MeasTiming__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition MeasTiming__ext0__Format : T_Format MeasTiming__ext0__Type MeasTiming__ext0__cond :=
  restrict_add_format MeasTiming__ext0__check_all_none MeasTiming__ext0O__Format.

Opaque MeasTiming__ext0__cond MeasTiming__ext0__Format.


Definition MeasTiming__root_Format_Type := Eval cbn in seq_format_prod MeasTiming__root_list.
Definition MeasTiming__root_Format_list : MeasTiming__root_Format_Type :=
  (MeasTiming__frequencyAndTiming__Format, unit_format).

Definition MeasTiming__ext_Format_Type := Eval cbn in get_formats MeasTiming__ext_list.
Definition MeasTiming__ext_Format_list : MeasTiming__ext_Format_Type :=
  (MeasTiming__ext0__Format, unit__Format).

Definition MeasTiming__list_type : Set := (seq_type MeasTiming__root_list) * (seq_ext_type MeasTiming__ext_list).
Definition MeasTiming__list_cond (z : MeasTiming__list_type) : Prop :=
        (seq_cond MeasTiming__root_list (fst z)) /\ (seq_ext_cond MeasTiming__ext_list (snd z)).
Definition MeasTiming__list_format : T_Format MeasTiming__list_type MeasTiming__list_cond :=
 (* Eval compute in *) seq_ext_format MeasTiming__root_list MeasTiming__root_Format_list MeasTiming__ext_list MeasTiming__ext_Format_list.

Opaque MeasTiming__list_format.
Definition MeasTiming__F1 (z : MeasTiming__Type) : MeasTiming__list_type :=
  (((MeasTiming__frequencyAndTiming z, tt)), (
(MeasTiming__ext0 z, tt))).
Definition MeasTiming__F2 (y : MeasTiming__list_type) : MeasTiming__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__MeasTiming__Type j0 i0
  end.
Definition MeasTiming__helper1 : (forall a : MeasTiming__Type, MeasTiming__cond a -> MeasTiming__list_cond (MeasTiming__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasTiming__helper2 : (forall a : MeasTiming__Type, MeasTiming__F2 (MeasTiming__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasTiming__helper3 : (forall b : MeasTiming__list_type, MeasTiming__list_cond b -> MeasTiming__cond (MeasTiming__F2 b) /\ MeasTiming__F1 (MeasTiming__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasTiming__cond, MeasTiming__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasTiming__Format : T_Format MeasTiming__Type MeasTiming__cond :=
 proj2_format MeasTiming__cond MeasTiming__list_format  MeasTiming__F1 MeasTiming__F2 MeasTiming__helper1 MeasTiming__helper2 MeasTiming__helper3.

Opaque MeasTiming__cond MeasTiming__Format.

