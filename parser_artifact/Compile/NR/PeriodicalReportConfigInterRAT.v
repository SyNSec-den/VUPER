Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ReportInterval.

Opaque ReportInterval__cond ReportInterval__Format.

Inductive PeriodicalReportConfigInterRAT__reportAmount__Type : Set :=
 | PeriodicalReportConfigInterRAT__reportAmount__r1
 | PeriodicalReportConfigInterRAT__reportAmount__r2
 | PeriodicalReportConfigInterRAT__reportAmount__r4
 | PeriodicalReportConfigInterRAT__reportAmount__r8
 | PeriodicalReportConfigInterRAT__reportAmount__r16
 | PeriodicalReportConfigInterRAT__reportAmount__r32
 | PeriodicalReportConfigInterRAT__reportAmount__r64
 | PeriodicalReportConfigInterRAT__reportAmount__infinity
.
Definition PeriodicalReportConfigInterRAT__reportAmount__cond := (fun (_ : PeriodicalReportConfigInterRAT__reportAmount__Type) => True).
Lemma PeriodicalReportConfigInterRAT__reportAmount__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PeriodicalReportConfigInterRAT__reportAmount__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 PeriodicalReportConfigInterRAT__reportAmount__nat__helper.

Definition PeriodicalReportConfigInterRAT__reportAmount__F1 t :=
  match t with
  | PeriodicalReportConfigInterRAT__reportAmount__r1 => 0
  | PeriodicalReportConfigInterRAT__reportAmount__r2 => 1
  | PeriodicalReportConfigInterRAT__reportAmount__r4 => 2
  | PeriodicalReportConfigInterRAT__reportAmount__r8 => 3
  | PeriodicalReportConfigInterRAT__reportAmount__r16 => 4
  | PeriodicalReportConfigInterRAT__reportAmount__r32 => 5
  | PeriodicalReportConfigInterRAT__reportAmount__r64 => 6
  | PeriodicalReportConfigInterRAT__reportAmount__infinity => 7
  end.
Definition PeriodicalReportConfigInterRAT__reportAmount__F2 n :=
  match n with
  | 0 => PeriodicalReportConfigInterRAT__reportAmount__r1
  | 1 => PeriodicalReportConfigInterRAT__reportAmount__r2
  | 2 => PeriodicalReportConfigInterRAT__reportAmount__r4
  | 3 => PeriodicalReportConfigInterRAT__reportAmount__r8
  | 4 => PeriodicalReportConfigInterRAT__reportAmount__r16
  | 5 => PeriodicalReportConfigInterRAT__reportAmount__r32
  | 6 => PeriodicalReportConfigInterRAT__reportAmount__r64
  | 7 => PeriodicalReportConfigInterRAT__reportAmount__infinity
  | _ => PeriodicalReportConfigInterRAT__reportAmount__r1
  end.
Lemma PeriodicalReportConfigInterRAT__reportAmount__F1F2 : forall x : PeriodicalReportConfigInterRAT__reportAmount__Type, (PeriodicalReportConfigInterRAT__reportAmount__F1 x <= 7) /\ PeriodicalReportConfigInterRAT__reportAmount__F2 (PeriodicalReportConfigInterRAT__reportAmount__F1 x) = x. imp_solve. Qed.
Lemma PeriodicalReportConfigInterRAT__reportAmount__F2F1 : forall (y : nat) (H : y <= 7), PeriodicalReportConfigInterRAT__reportAmount__F1 (PeriodicalReportConfigInterRAT__reportAmount__F2 y) = y. enum_solve H y. Qed.

Require Import NR.MeasReportQuantity.

Opaque MeasReportQuantity__cond MeasReportQuantity__Format.

Lemma PeriodicalReportConfigInterRAT__maxReportCells__helper1 : (1 <= maxCellReport)%Z. unfold maxCellReport.
 lia. Qed.
Lemma PeriodicalReportConfigInterRAT__maxReportCells__helper2 : to_bit_sz (Z.to_nat (maxCellReport - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellReport - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PeriodicalReportConfigInterRAT__maxReportCells__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PeriodicalReportConfigInterRAT__maxReportCells__Type := Z.
Definition PeriodicalReportConfigInterRAT__maxReportCells__cond := (fun z => (1 <= z <= maxCellReport)%Z).
Require Import NR.MeasReportQuantityUTRA_FDD_r16.

Opaque MeasReportQuantityUTRA_FDD_r16__cond MeasReportQuantityUTRA_FDD_r16__Format.

Record PeriodicalReportConfigInterRAT__ext0O__Type : Set :=
  make__PeriodicalReportConfigInterRAT__ext0O__Type {
    PeriodicalReportConfigInterRAT__ext0O__reportQuantityUTRA_FDD_r16 : option MeasReportQuantityUTRA_FDD_r16__Type ;
}.
Definition PeriodicalReportConfigInterRAT__ext0O__list := (
 Opt MeasReportQuantityUTRA_FDD_r16__Type MeasReportQuantityUTRA_FDD_r16__cond ::
 nil).
Definition PeriodicalReportConfigInterRAT__ext0O__cond z := 
  opt_cond MeasReportQuantityUTRA_FDD_r16__cond (PeriodicalReportConfigInterRAT__ext0O__reportQuantityUTRA_FDD_r16 z) /\
  True.

Definition PeriodicalReportConfigInterRAT__ext0__Type := PeriodicalReportConfigInterRAT__ext0O__Type.
Definition PeriodicalReportConfigInterRAT__ext0__cond := PeriodicalReportConfigInterRAT__ext0O__cond.

Inductive PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type : Set :=
 | PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__true
.
Definition PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__cond := (fun (_ : PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type) => True).
Lemma PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__nat__helper.

Definition PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 t :=
  match t with
  | PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__true => 0
  end.
Definition PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2 n :=
  match n with
  | 0 => PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__true
  | _ => PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__true
  end.
Lemma PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1F2 : forall x : PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type, (PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 x <= 0) /\ PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2 (PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 x) = x. imp_solve. Qed.
Lemma PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2F1 : forall (y : nat) (H : y <= 0), PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 (PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.BT_NameList_r16.
Definition PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__Type := SetupRelease__Type BT_NameList_r16__Type.
Definition PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__cond := SetupRelease__cond _ BT_NameList_r16__cond.
Definition PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__Format : T_Format PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__Type PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__cond := SetupRelease__Format _ _ BT_NameList_r16__Format.
Opaque PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__cond PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.WLAN_NameList_r16.
Definition PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__Type := SetupRelease__Type WLAN_NameList_r16__Type.
Definition PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond := SetupRelease__cond _ WLAN_NameList_r16__cond.
Definition PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__Format : T_Format PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__Type PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond := SetupRelease__Format _ _ WLAN_NameList_r16__Format.
Opaque PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.Sensor_NameList_r16.
Definition PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__Type := SetupRelease__Type Sensor_NameList_r16__Type.
Definition PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__cond := SetupRelease__cond _ Sensor_NameList_r16__cond.
Definition PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__Format : T_Format PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__Type PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__cond := SetupRelease__Format _ _ Sensor_NameList_r16__Format.
Opaque PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__cond PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__Format.

Record PeriodicalReportConfigInterRAT__ext1O__Type : Set :=
  make__PeriodicalReportConfigInterRAT__ext1O__Type {
    PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16 : option PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type ;
    PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16 : option PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__Type ;
    PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16 : option PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__Type ;
    PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16 : option PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__Type ;
}.
Definition PeriodicalReportConfigInterRAT__ext1O__list := (
 Opt PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__cond ::
 Opt PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__Type PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__cond ::
 Opt PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__Type PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond ::
 Opt PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__Type PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__cond ::
 nil).
Definition PeriodicalReportConfigInterRAT__ext1O__cond z := 
  opt_cond PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__cond (PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16 z) /\
  opt_cond PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__cond (PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16 z) /\
  opt_cond PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond (PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16 z) /\
  opt_cond PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__cond (PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16 z) /\
  True.

Definition PeriodicalReportConfigInterRAT__ext1__Type := PeriodicalReportConfigInterRAT__ext1O__Type.
Definition PeriodicalReportConfigInterRAT__ext1__cond := PeriodicalReportConfigInterRAT__ext1O__cond.

Require Import NR.SL_MeasReportQuantity_r16.

Opaque SL_MeasReportQuantity_r16__cond SL_MeasReportQuantity_r16__Format.

Record PeriodicalReportConfigInterRAT__ext2O__Type : Set :=
  make__PeriodicalReportConfigInterRAT__ext2O__Type {
    PeriodicalReportConfigInterRAT__ext2O__reportQuantityRelay_r17 : option SL_MeasReportQuantity_r16__Type ;
}.
Definition PeriodicalReportConfigInterRAT__ext2O__list := (
 Opt SL_MeasReportQuantity_r16__Type SL_MeasReportQuantity_r16__cond ::
 nil).
Definition PeriodicalReportConfigInterRAT__ext2O__cond z := 
  opt_cond SL_MeasReportQuantity_r16__cond (PeriodicalReportConfigInterRAT__ext2O__reportQuantityRelay_r17 z) /\
  True.

Definition PeriodicalReportConfigInterRAT__ext2__Type := PeriodicalReportConfigInterRAT__ext2O__Type.
Definition PeriodicalReportConfigInterRAT__ext2__cond := PeriodicalReportConfigInterRAT__ext2O__cond.

Record PeriodicalReportConfigInterRAT__Type : Set :=
  make__PeriodicalReportConfigInterRAT__Type {
    PeriodicalReportConfigInterRAT__reportInterval : ReportInterval__Type ;
    PeriodicalReportConfigInterRAT__reportAmount : PeriodicalReportConfigInterRAT__reportAmount__Type ;
    PeriodicalReportConfigInterRAT__reportQuantity : MeasReportQuantity__Type ;
    PeriodicalReportConfigInterRAT__maxReportCells : Z ;
    PeriodicalReportConfigInterRAT__ext0 : option PeriodicalReportConfigInterRAT__ext0__Type ;
    PeriodicalReportConfigInterRAT__ext1 : option PeriodicalReportConfigInterRAT__ext1__Type ;
    PeriodicalReportConfigInterRAT__ext2 : option PeriodicalReportConfigInterRAT__ext2__Type ;
}.
Definition PeriodicalReportConfigInterRAT__root_list : list seq_elem := (
 Nor ReportInterval__Type ReportInterval__cond ::
 Nor PeriodicalReportConfigInterRAT__reportAmount__Type PeriodicalReportConfigInterRAT__reportAmount__cond ::
 Nor MeasReportQuantity__Type MeasReportQuantity__cond ::
 Nor Z PeriodicalReportConfigInterRAT__maxReportCells__cond ::
 nil).
Definition PeriodicalReportConfigInterRAT__ext_list : list typ := (
  typ_cons PeriodicalReportConfigInterRAT__ext0__Type PeriodicalReportConfigInterRAT__ext0__cond ::
  typ_cons PeriodicalReportConfigInterRAT__ext1__Type PeriodicalReportConfigInterRAT__ext1__cond ::
  typ_cons PeriodicalReportConfigInterRAT__ext2__Type PeriodicalReportConfigInterRAT__ext2__cond ::
  nil).
Definition PeriodicalReportConfigInterRAT__cond (z : PeriodicalReportConfigInterRAT__Type) := 
(  ReportInterval__cond (PeriodicalReportConfigInterRAT__reportInterval z) /\
  PeriodicalReportConfigInterRAT__reportAmount__cond (PeriodicalReportConfigInterRAT__reportAmount z) /\
  MeasReportQuantity__cond (PeriodicalReportConfigInterRAT__reportQuantity z) /\
  PeriodicalReportConfigInterRAT__maxReportCells__cond (PeriodicalReportConfigInterRAT__maxReportCells z) /\
  True) /\ 
(  opt_cond PeriodicalReportConfigInterRAT__ext0__cond (PeriodicalReportConfigInterRAT__ext0 z) /\
  opt_cond PeriodicalReportConfigInterRAT__ext1__cond (PeriodicalReportConfigInterRAT__ext1 z) /\
  opt_cond PeriodicalReportConfigInterRAT__ext2__cond (PeriodicalReportConfigInterRAT__ext2 z) /\
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
Definition PeriodicalReportConfigInterRAT__reportAmount__Format : T_Format PeriodicalReportConfigInterRAT__reportAmount__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PeriodicalReportConfigInterRAT__reportAmount__nat__Format PeriodicalReportConfigInterRAT__reportAmount__F1 PeriodicalReportConfigInterRAT__reportAmount__F2 PeriodicalReportConfigInterRAT__reportAmount__F1F2 PeriodicalReportConfigInterRAT__reportAmount__F2F1.

Opaque PeriodicalReportConfigInterRAT__reportAmount__cond PeriodicalReportConfigInterRAT__reportAmount__Format.

Definition PeriodicalReportConfigInterRAT__maxReportCells__Format : T_Format Z PeriodicalReportConfigInterRAT__maxReportCells__cond :=
 ranged_int_format (1) (maxCellReport) PeriodicalReportConfigInterRAT__maxReportCells__helper1 PeriodicalReportConfigInterRAT__maxReportCells__helper2.

Opaque PeriodicalReportConfigInterRAT__maxReportCells__cond PeriodicalReportConfigInterRAT__maxReportCells__Format.


Definition PeriodicalReportConfigInterRAT__ext0O__Format_Type := Eval cbn in seq_format_prod PeriodicalReportConfigInterRAT__ext0O__list.
Definition PeriodicalReportConfigInterRAT__ext0O__Format_list : PeriodicalReportConfigInterRAT__ext0O__Format_Type :=
  (MeasReportQuantityUTRA_FDD_r16__Format, unit_format).
Definition PeriodicalReportConfigInterRAT__ext0O__list__Format := (*Eval compute in *) seq_format PeriodicalReportConfigInterRAT__ext0O__list PeriodicalReportConfigInterRAT__ext0O__Format_list.
Definition PeriodicalReportConfigInterRAT__ext0O__F1 z :=
  (PeriodicalReportConfigInterRAT__ext0O__reportQuantityUTRA_FDD_r16 z, tt).
Definition PeriodicalReportConfigInterRAT__ext0O__F2 (y : seq_type PeriodicalReportConfigInterRAT__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PeriodicalReportConfigInterRAT__ext0O__Type i0
  end.
Lemma PeriodicalReportConfigInterRAT__ext0O__F1F2_cond (z : PeriodicalReportConfigInterRAT__ext0O__Type)
  : PeriodicalReportConfigInterRAT__ext0O__cond z ->
  (seq_cond PeriodicalReportConfigInterRAT__ext0O__list (PeriodicalReportConfigInterRAT__ext0O__F1 z)).
intro H. unfold PeriodicalReportConfigInterRAT__ext0O__cond in H. simpl. auto. Qed.
Lemma PeriodicalReportConfigInterRAT__ext0O__F1F2_cond2 (z : PeriodicalReportConfigInterRAT__ext0O__Type)
 : PeriodicalReportConfigInterRAT__ext0O__F2 (PeriodicalReportConfigInterRAT__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PeriodicalReportConfigInterRAT__ext0O__F2F1_cond (y : seq_type PeriodicalReportConfigInterRAT__ext0O__list)
  : seq_cond PeriodicalReportConfigInterRAT__ext0O__list y ->
 (PeriodicalReportConfigInterRAT__ext0O__cond (PeriodicalReportConfigInterRAT__ext0O__F2 y)) /\  PeriodicalReportConfigInterRAT__ext0O__F1 (PeriodicalReportConfigInterRAT__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PeriodicalReportConfigInterRAT__ext0O__cond. simpl in *. auto.
 - simpl. unfold PeriodicalReportConfigInterRAT__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PeriodicalReportConfigInterRAT__ext0O__Format : T_Format PeriodicalReportConfigInterRAT__ext0O__Type PeriodicalReportConfigInterRAT__ext0O__cond :=
        proj2_format  PeriodicalReportConfigInterRAT__ext0O__cond PeriodicalReportConfigInterRAT__ext0O__list__Format
    PeriodicalReportConfigInterRAT__ext0O__F1 PeriodicalReportConfigInterRAT__ext0O__F2 PeriodicalReportConfigInterRAT__ext0O__F1F2_cond  PeriodicalReportConfigInterRAT__ext0O__F1F2_cond2 PeriodicalReportConfigInterRAT__ext0O__F2F1_cond.
Opaque PeriodicalReportConfigInterRAT__ext0O__cond PeriodicalReportConfigInterRAT__ext0O__Format.

Definition PeriodicalReportConfigInterRAT__ext0__check_all_none (b : PeriodicalReportConfigInterRAT__ext0O__Type) : bool :=
match b with 
  | make__PeriodicalReportConfigInterRAT__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PeriodicalReportConfigInterRAT__ext0__Format : T_Format PeriodicalReportConfigInterRAT__ext0__Type PeriodicalReportConfigInterRAT__ext0__cond :=
  restrict_add_format PeriodicalReportConfigInterRAT__ext0__check_all_none PeriodicalReportConfigInterRAT__ext0O__Format.

Opaque PeriodicalReportConfigInterRAT__ext0__cond PeriodicalReportConfigInterRAT__ext0__Format.

Definition PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Format : T_Format PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__nat__Format PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1 PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2 PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F1F2 PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__F2F1.

Opaque PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__cond PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Format.

Opaque PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__cond PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__Format.

Opaque PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__cond PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__Format.

Opaque PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__cond PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__Format.


Definition PeriodicalReportConfigInterRAT__ext1O__Format_Type := Eval cbn in seq_format_prod PeriodicalReportConfigInterRAT__ext1O__list.
Definition PeriodicalReportConfigInterRAT__ext1O__Format_list : PeriodicalReportConfigInterRAT__ext1O__Format_Type :=
  (PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16__Format, (PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16__Format, (PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16__Format, (PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16__Format, unit_format)))).
Definition PeriodicalReportConfigInterRAT__ext1O__list__Format := (*Eval compute in *) seq_format PeriodicalReportConfigInterRAT__ext1O__list PeriodicalReportConfigInterRAT__ext1O__Format_list.
Definition PeriodicalReportConfigInterRAT__ext1O__F1 z :=
  (PeriodicalReportConfigInterRAT__ext1O__includeCommonLocationInfo_r16 z, (PeriodicalReportConfigInterRAT__ext1O__includeBT_Meas_r16 z, (PeriodicalReportConfigInterRAT__ext1O__includeWLAN_Meas_r16 z, (PeriodicalReportConfigInterRAT__ext1O__includeSensor_Meas_r16 z, tt)))).
Definition PeriodicalReportConfigInterRAT__ext1O__F2 (y : seq_type PeriodicalReportConfigInterRAT__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__PeriodicalReportConfigInterRAT__ext1O__Type i0 i1 i2 i3
  end.
Lemma PeriodicalReportConfigInterRAT__ext1O__F1F2_cond (z : PeriodicalReportConfigInterRAT__ext1O__Type)
  : PeriodicalReportConfigInterRAT__ext1O__cond z ->
  (seq_cond PeriodicalReportConfigInterRAT__ext1O__list (PeriodicalReportConfigInterRAT__ext1O__F1 z)).
intro H. unfold PeriodicalReportConfigInterRAT__ext1O__cond in H. simpl. auto. Qed.
Lemma PeriodicalReportConfigInterRAT__ext1O__F1F2_cond2 (z : PeriodicalReportConfigInterRAT__ext1O__Type)
 : PeriodicalReportConfigInterRAT__ext1O__F2 (PeriodicalReportConfigInterRAT__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PeriodicalReportConfigInterRAT__ext1O__F2F1_cond (y : seq_type PeriodicalReportConfigInterRAT__ext1O__list)
  : seq_cond PeriodicalReportConfigInterRAT__ext1O__list y ->
 (PeriodicalReportConfigInterRAT__ext1O__cond (PeriodicalReportConfigInterRAT__ext1O__F2 y)) /\  PeriodicalReportConfigInterRAT__ext1O__F1 (PeriodicalReportConfigInterRAT__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PeriodicalReportConfigInterRAT__ext1O__cond. simpl in *. auto.
 - simpl. unfold PeriodicalReportConfigInterRAT__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PeriodicalReportConfigInterRAT__ext1O__Format : T_Format PeriodicalReportConfigInterRAT__ext1O__Type PeriodicalReportConfigInterRAT__ext1O__cond :=
        proj2_format  PeriodicalReportConfigInterRAT__ext1O__cond PeriodicalReportConfigInterRAT__ext1O__list__Format
    PeriodicalReportConfigInterRAT__ext1O__F1 PeriodicalReportConfigInterRAT__ext1O__F2 PeriodicalReportConfigInterRAT__ext1O__F1F2_cond  PeriodicalReportConfigInterRAT__ext1O__F1F2_cond2 PeriodicalReportConfigInterRAT__ext1O__F2F1_cond.
Opaque PeriodicalReportConfigInterRAT__ext1O__cond PeriodicalReportConfigInterRAT__ext1O__Format.

Definition PeriodicalReportConfigInterRAT__ext1__check_all_none (b : PeriodicalReportConfigInterRAT__ext1O__Type) : bool :=
match b with 
  | make__PeriodicalReportConfigInterRAT__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition PeriodicalReportConfigInterRAT__ext1__Format : T_Format PeriodicalReportConfigInterRAT__ext1__Type PeriodicalReportConfigInterRAT__ext1__cond :=
  restrict_add_format PeriodicalReportConfigInterRAT__ext1__check_all_none PeriodicalReportConfigInterRAT__ext1O__Format.

Opaque PeriodicalReportConfigInterRAT__ext1__cond PeriodicalReportConfigInterRAT__ext1__Format.


Definition PeriodicalReportConfigInterRAT__ext2O__Format_Type := Eval cbn in seq_format_prod PeriodicalReportConfigInterRAT__ext2O__list.
Definition PeriodicalReportConfigInterRAT__ext2O__Format_list : PeriodicalReportConfigInterRAT__ext2O__Format_Type :=
  (SL_MeasReportQuantity_r16__Format, unit_format).
Definition PeriodicalReportConfigInterRAT__ext2O__list__Format := (*Eval compute in *) seq_format PeriodicalReportConfigInterRAT__ext2O__list PeriodicalReportConfigInterRAT__ext2O__Format_list.
Definition PeriodicalReportConfigInterRAT__ext2O__F1 z :=
  (PeriodicalReportConfigInterRAT__ext2O__reportQuantityRelay_r17 z, tt).
Definition PeriodicalReportConfigInterRAT__ext2O__F2 (y : seq_type PeriodicalReportConfigInterRAT__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__PeriodicalReportConfigInterRAT__ext2O__Type i0
  end.
Lemma PeriodicalReportConfigInterRAT__ext2O__F1F2_cond (z : PeriodicalReportConfigInterRAT__ext2O__Type)
  : PeriodicalReportConfigInterRAT__ext2O__cond z ->
  (seq_cond PeriodicalReportConfigInterRAT__ext2O__list (PeriodicalReportConfigInterRAT__ext2O__F1 z)).
intro H. unfold PeriodicalReportConfigInterRAT__ext2O__cond in H. simpl. auto. Qed.
Lemma PeriodicalReportConfigInterRAT__ext2O__F1F2_cond2 (z : PeriodicalReportConfigInterRAT__ext2O__Type)
 : PeriodicalReportConfigInterRAT__ext2O__F2 (PeriodicalReportConfigInterRAT__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PeriodicalReportConfigInterRAT__ext2O__F2F1_cond (y : seq_type PeriodicalReportConfigInterRAT__ext2O__list)
  : seq_cond PeriodicalReportConfigInterRAT__ext2O__list y ->
 (PeriodicalReportConfigInterRAT__ext2O__cond (PeriodicalReportConfigInterRAT__ext2O__F2 y)) /\  PeriodicalReportConfigInterRAT__ext2O__F1 (PeriodicalReportConfigInterRAT__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PeriodicalReportConfigInterRAT__ext2O__cond. simpl in *. auto.
 - simpl. unfold PeriodicalReportConfigInterRAT__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PeriodicalReportConfigInterRAT__ext2O__Format : T_Format PeriodicalReportConfigInterRAT__ext2O__Type PeriodicalReportConfigInterRAT__ext2O__cond :=
        proj2_format  PeriodicalReportConfigInterRAT__ext2O__cond PeriodicalReportConfigInterRAT__ext2O__list__Format
    PeriodicalReportConfigInterRAT__ext2O__F1 PeriodicalReportConfigInterRAT__ext2O__F2 PeriodicalReportConfigInterRAT__ext2O__F1F2_cond  PeriodicalReportConfigInterRAT__ext2O__F1F2_cond2 PeriodicalReportConfigInterRAT__ext2O__F2F1_cond.
Opaque PeriodicalReportConfigInterRAT__ext2O__cond PeriodicalReportConfigInterRAT__ext2O__Format.

Definition PeriodicalReportConfigInterRAT__ext2__check_all_none (b : PeriodicalReportConfigInterRAT__ext2O__Type) : bool :=
match b with 
  | make__PeriodicalReportConfigInterRAT__ext2O__Type None  => false 
  | _ => true 
 end.
Definition PeriodicalReportConfigInterRAT__ext2__Format : T_Format PeriodicalReportConfigInterRAT__ext2__Type PeriodicalReportConfigInterRAT__ext2__cond :=
  restrict_add_format PeriodicalReportConfigInterRAT__ext2__check_all_none PeriodicalReportConfigInterRAT__ext2O__Format.

Opaque PeriodicalReportConfigInterRAT__ext2__cond PeriodicalReportConfigInterRAT__ext2__Format.


Definition PeriodicalReportConfigInterRAT__root_Format_Type := Eval cbn in seq_format_prod PeriodicalReportConfigInterRAT__root_list.
Definition PeriodicalReportConfigInterRAT__root_Format_list : PeriodicalReportConfigInterRAT__root_Format_Type :=
  (ReportInterval__Format, (PeriodicalReportConfigInterRAT__reportAmount__Format, (MeasReportQuantity__Format, (PeriodicalReportConfigInterRAT__maxReportCells__Format, unit_format)))).

Definition PeriodicalReportConfigInterRAT__ext_Format_Type := Eval cbn in get_formats PeriodicalReportConfigInterRAT__ext_list.
Definition PeriodicalReportConfigInterRAT__ext_Format_list : PeriodicalReportConfigInterRAT__ext_Format_Type :=
  (PeriodicalReportConfigInterRAT__ext0__Format, (PeriodicalReportConfigInterRAT__ext1__Format, (PeriodicalReportConfigInterRAT__ext2__Format, unit__Format))).

Definition PeriodicalReportConfigInterRAT__list_type : Set := (seq_type PeriodicalReportConfigInterRAT__root_list) * (seq_ext_type PeriodicalReportConfigInterRAT__ext_list).
Definition PeriodicalReportConfigInterRAT__list_cond (z : PeriodicalReportConfigInterRAT__list_type) : Prop :=
        (seq_cond PeriodicalReportConfigInterRAT__root_list (fst z)) /\ (seq_ext_cond PeriodicalReportConfigInterRAT__ext_list (snd z)).
Definition PeriodicalReportConfigInterRAT__list_format : T_Format PeriodicalReportConfigInterRAT__list_type PeriodicalReportConfigInterRAT__list_cond :=
 (* Eval compute in *) seq_ext_format PeriodicalReportConfigInterRAT__root_list PeriodicalReportConfigInterRAT__root_Format_list PeriodicalReportConfigInterRAT__ext_list PeriodicalReportConfigInterRAT__ext_Format_list.

Opaque PeriodicalReportConfigInterRAT__list_format.
Definition PeriodicalReportConfigInterRAT__F1 (z : PeriodicalReportConfigInterRAT__Type) : PeriodicalReportConfigInterRAT__list_type :=
  (((PeriodicalReportConfigInterRAT__reportInterval z, (PeriodicalReportConfigInterRAT__reportAmount z, (PeriodicalReportConfigInterRAT__reportQuantity z, (PeriodicalReportConfigInterRAT__maxReportCells z, tt))))), (
(PeriodicalReportConfigInterRAT__ext0 z, (PeriodicalReportConfigInterRAT__ext1 z, (PeriodicalReportConfigInterRAT__ext2 z, tt))))).
Definition PeriodicalReportConfigInterRAT__F2 (y : PeriodicalReportConfigInterRAT__list_type) : PeriodicalReportConfigInterRAT__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, (i2, _))))=>
    make__PeriodicalReportConfigInterRAT__Type j0 j1 j2 j3 i0 i1 i2
  end.
Definition PeriodicalReportConfigInterRAT__helper1 : (forall a : PeriodicalReportConfigInterRAT__Type, PeriodicalReportConfigInterRAT__cond a -> PeriodicalReportConfigInterRAT__list_cond (PeriodicalReportConfigInterRAT__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PeriodicalReportConfigInterRAT__helper2 : (forall a : PeriodicalReportConfigInterRAT__Type, PeriodicalReportConfigInterRAT__F2 (PeriodicalReportConfigInterRAT__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PeriodicalReportConfigInterRAT__helper3 : (forall b : PeriodicalReportConfigInterRAT__list_type, PeriodicalReportConfigInterRAT__list_cond b -> PeriodicalReportConfigInterRAT__cond (PeriodicalReportConfigInterRAT__F2 b) /\ PeriodicalReportConfigInterRAT__F1 (PeriodicalReportConfigInterRAT__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PeriodicalReportConfigInterRAT__cond, PeriodicalReportConfigInterRAT__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PeriodicalReportConfigInterRAT__Format : T_Format PeriodicalReportConfigInterRAT__Type PeriodicalReportConfigInterRAT__cond :=
 proj2_format PeriodicalReportConfigInterRAT__cond PeriodicalReportConfigInterRAT__list_format  PeriodicalReportConfigInterRAT__F1 PeriodicalReportConfigInterRAT__F2 PeriodicalReportConfigInterRAT__helper1 PeriodicalReportConfigInterRAT__helper2 PeriodicalReportConfigInterRAT__helper3.

Opaque PeriodicalReportConfigInterRAT__cond PeriodicalReportConfigInterRAT__Format.

