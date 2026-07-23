Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.MeasResultSuccessHONR_r17.

Opaque MeasResultSuccessHONR_r17__cond MeasResultSuccessHONR_r17__Format.

Inductive SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type : Set :=
 | SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__true
.
Definition SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__cond := (fun (_ : SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type) => True).
Lemma SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__nat__helper.

Definition SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F1 t :=
  match t with
  | SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__true => 0
  end.
Definition SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F2 n :=
  match n with
  | 0 => SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__true
  | _ => SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__true
  end.
Lemma SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F1F2 : forall x : SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type, (SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F1 x <= 0) /\ SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F2 (SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F1 x) = x. imp_solve. Qed.
Lemma SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F2F1 : forall (y : nat) (H : y <= 0), SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F1 (SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F2 y) = y. enum_solve H y. Qed.

Record SuccessHO_Report_r17__sourceCellInfo_r17__Type : Set :=
  make__SuccessHO_Report_r17__sourceCellInfo_r17__Type {
    SuccessHO_Report_r17__sourceCellInfo_r17__sourcePCellId_r17 : CGI_Info_Logging_r16__Type ;
    SuccessHO_Report_r17__sourceCellInfo_r17__sourceCellMeas_r17 : option MeasResultSuccessHONR_r17__Type ;
    SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17 : option SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type ;
}.
Definition SuccessHO_Report_r17__sourceCellInfo_r17__list := (
 Nor CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
 Opt MeasResultSuccessHONR_r17__Type MeasResultSuccessHONR_r17__cond ::
 Opt SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__cond ::
 nil).
Definition SuccessHO_Report_r17__sourceCellInfo_r17__cond z := 
  CGI_Info_Logging_r16__cond (SuccessHO_Report_r17__sourceCellInfo_r17__sourcePCellId_r17 z) /\
  opt_cond MeasResultSuccessHONR_r17__cond (SuccessHO_Report_r17__sourceCellInfo_r17__sourceCellMeas_r17 z) /\
  opt_cond SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__cond (SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17 z) /\
  True.

Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.MeasResultSuccessHONR_r17.

Opaque MeasResultSuccessHONR_r17__cond MeasResultSuccessHONR_r17__Format.

Record SuccessHO_Report_r17__targetCellInfo_r17__Type : Set :=
  make__SuccessHO_Report_r17__targetCellInfo_r17__Type {
    SuccessHO_Report_r17__targetCellInfo_r17__targetPCellId_r17 : CGI_Info_Logging_r16__Type ;
    SuccessHO_Report_r17__targetCellInfo_r17__targetCellMeas_r17 : option MeasResultSuccessHONR_r17__Type ;
}.
Definition SuccessHO_Report_r17__targetCellInfo_r17__list := (
 Nor CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
 Opt MeasResultSuccessHONR_r17__Type MeasResultSuccessHONR_r17__cond ::
 nil).
Definition SuccessHO_Report_r17__targetCellInfo_r17__cond z := 
  CGI_Info_Logging_r16__cond (SuccessHO_Report_r17__targetCellInfo_r17__targetPCellId_r17 z) /\
  opt_cond MeasResultSuccessHONR_r17__cond (SuccessHO_Report_r17__targetCellInfo_r17__targetCellMeas_r17 z) /\
  True.

Require Import NR.MeasResultList2NR_r16.

Opaque MeasResultList2NR_r16__cond MeasResultList2NR_r16__Format.

Require Import NR.MeasResultList2EUTRA_r16.

Opaque MeasResultList2EUTRA_r16__cond MeasResultList2EUTRA_r16__Format.

Record SuccessHO_Report_r17__measResultNeighCells_r17__Type : Set :=
  make__SuccessHO_Report_r17__measResultNeighCells_r17__Type {
    SuccessHO_Report_r17__measResultNeighCells_r17__measResultListNR_r17 : option MeasResultList2NR_r16__Type ;
    SuccessHO_Report_r17__measResultNeighCells_r17__measResultListEUTRA_r17 : option MeasResultList2EUTRA_r16__Type ;
}.
Definition SuccessHO_Report_r17__measResultNeighCells_r17__list := (
 Opt MeasResultList2NR_r16__Type MeasResultList2NR_r16__cond ::
 Opt MeasResultList2EUTRA_r16__Type MeasResultList2EUTRA_r16__cond ::
 nil).
Definition SuccessHO_Report_r17__measResultNeighCells_r17__cond z := 
  opt_cond MeasResultList2NR_r16__cond (SuccessHO_Report_r17__measResultNeighCells_r17__measResultListNR_r17 z) /\
  opt_cond MeasResultList2EUTRA_r16__cond (SuccessHO_Report_r17__measResultNeighCells_r17__measResultListEUTRA_r17 z) /\
  True.

Require Import NR.LocationInfo_r16.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

Require Import NR.TimeSinceCHO_Reconfig_r17.

Opaque TimeSinceCHO_Reconfig_r17__cond TimeSinceCHO_Reconfig_r17__Format.

Require Import NR.SHR_Cause_r17.

Opaque SHR_Cause_r17__cond SHR_Cause_r17__Format.

Require Import NR.RA_InformationCommon_r16.

Opaque RA_InformationCommon_r16__cond RA_InformationCommon_r16__Format.

Require Import NR.UPInterruptionTimeAtHO_r17.

Opaque UPInterruptionTimeAtHO_r17__cond UPInterruptionTimeAtHO_r17__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Record SuccessHO_Report_r17__Type : Set :=
  make__SuccessHO_Report_r17__Type {
    SuccessHO_Report_r17__sourceCellInfo_r17 : SuccessHO_Report_r17__sourceCellInfo_r17__Type ;
    SuccessHO_Report_r17__targetCellInfo_r17 : SuccessHO_Report_r17__targetCellInfo_r17__Type ;
    SuccessHO_Report_r17__measResultNeighCells_r17 : option SuccessHO_Report_r17__measResultNeighCells_r17__Type ;
    SuccessHO_Report_r17__locationInfo_r17 : option LocationInfo_r16__Type ;
    SuccessHO_Report_r17__timeSinceCHO_Reconfig_r17 : option TimeSinceCHO_Reconfig_r17__Type ;
    SuccessHO_Report_r17__shr_Cause_r17 : option SHR_Cause_r17__Type ;
    SuccessHO_Report_r17__ra_InformationCommon_r17 : option RA_InformationCommon_r16__Type ;
    SuccessHO_Report_r17__upInterruptionTimeAtHO_r17 : option UPInterruptionTimeAtHO_r17__Type ;
    SuccessHO_Report_r17__c_RNTI_r17 : option RNTI_Value__Type ;
}.
Definition SuccessHO_Report_r17__root_list : list seq_elem := (
 Nor SuccessHO_Report_r17__sourceCellInfo_r17__Type SuccessHO_Report_r17__sourceCellInfo_r17__cond ::
 Nor SuccessHO_Report_r17__targetCellInfo_r17__Type SuccessHO_Report_r17__targetCellInfo_r17__cond ::
 Opt SuccessHO_Report_r17__measResultNeighCells_r17__Type SuccessHO_Report_r17__measResultNeighCells_r17__cond ::
 Opt LocationInfo_r16__Type LocationInfo_r16__cond ::
 Opt TimeSinceCHO_Reconfig_r17__Type TimeSinceCHO_Reconfig_r17__cond ::
 Opt SHR_Cause_r17__Type SHR_Cause_r17__cond ::
 Opt RA_InformationCommon_r16__Type RA_InformationCommon_r16__cond ::
 Opt UPInterruptionTimeAtHO_r17__Type UPInterruptionTimeAtHO_r17__cond ::
 Opt RNTI_Value__Type RNTI_Value__cond ::
 nil).
Definition SuccessHO_Report_r17__ext_list : list typ := (
  nil).
Definition SuccessHO_Report_r17__cond (z : SuccessHO_Report_r17__Type) := 
(  SuccessHO_Report_r17__sourceCellInfo_r17__cond (SuccessHO_Report_r17__sourceCellInfo_r17 z) /\
  SuccessHO_Report_r17__targetCellInfo_r17__cond (SuccessHO_Report_r17__targetCellInfo_r17 z) /\
  opt_cond SuccessHO_Report_r17__measResultNeighCells_r17__cond (SuccessHO_Report_r17__measResultNeighCells_r17 z) /\
  opt_cond LocationInfo_r16__cond (SuccessHO_Report_r17__locationInfo_r17 z) /\
  opt_cond TimeSinceCHO_Reconfig_r17__cond (SuccessHO_Report_r17__timeSinceCHO_Reconfig_r17 z) /\
  opt_cond SHR_Cause_r17__cond (SuccessHO_Report_r17__shr_Cause_r17 z) /\
  opt_cond RA_InformationCommon_r16__cond (SuccessHO_Report_r17__ra_InformationCommon_r17 z) /\
  opt_cond UPInterruptionTimeAtHO_r17__cond (SuccessHO_Report_r17__upInterruptionTimeAtHO_r17 z) /\
  opt_cond RNTI_Value__cond (SuccessHO_Report_r17__c_RNTI_r17 z) /\
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
Definition SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Format : T_Format SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__nat__Format SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F1 SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F2 SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F1F2 SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__F2F1.

Opaque SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__cond SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Format.


Definition SuccessHO_Report_r17__sourceCellInfo_r17__Format_Type := Eval cbn in seq_format_prod SuccessHO_Report_r17__sourceCellInfo_r17__list.
Definition SuccessHO_Report_r17__sourceCellInfo_r17__Format_list : SuccessHO_Report_r17__sourceCellInfo_r17__Format_Type :=
  (CGI_Info_Logging_r16__Format, (MeasResultSuccessHONR_r17__Format, (SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17__Format, unit_format))).
Definition SuccessHO_Report_r17__sourceCellInfo_r17__list__Format := (*Eval compute in *) seq_format SuccessHO_Report_r17__sourceCellInfo_r17__list SuccessHO_Report_r17__sourceCellInfo_r17__Format_list.
Definition SuccessHO_Report_r17__sourceCellInfo_r17__F1 z :=
  (SuccessHO_Report_r17__sourceCellInfo_r17__sourcePCellId_r17 z, (SuccessHO_Report_r17__sourceCellInfo_r17__sourceCellMeas_r17 z, (SuccessHO_Report_r17__sourceCellInfo_r17__rlf_InSourceDAPS_r17 z, tt))).
Definition SuccessHO_Report_r17__sourceCellInfo_r17__F2 (y : seq_type SuccessHO_Report_r17__sourceCellInfo_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SuccessHO_Report_r17__sourceCellInfo_r17__Type i0 i1 i2
  end.
Lemma SuccessHO_Report_r17__sourceCellInfo_r17__F1F2_cond (z : SuccessHO_Report_r17__sourceCellInfo_r17__Type)
  : SuccessHO_Report_r17__sourceCellInfo_r17__cond z ->
  (seq_cond SuccessHO_Report_r17__sourceCellInfo_r17__list (SuccessHO_Report_r17__sourceCellInfo_r17__F1 z)).
intro H. unfold SuccessHO_Report_r17__sourceCellInfo_r17__cond in H. simpl. auto. Qed.
Lemma SuccessHO_Report_r17__sourceCellInfo_r17__F1F2_cond2 (z : SuccessHO_Report_r17__sourceCellInfo_r17__Type)
 : SuccessHO_Report_r17__sourceCellInfo_r17__F2 (SuccessHO_Report_r17__sourceCellInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SuccessHO_Report_r17__sourceCellInfo_r17__F2F1_cond (y : seq_type SuccessHO_Report_r17__sourceCellInfo_r17__list)
  : seq_cond SuccessHO_Report_r17__sourceCellInfo_r17__list y ->
 (SuccessHO_Report_r17__sourceCellInfo_r17__cond (SuccessHO_Report_r17__sourceCellInfo_r17__F2 y)) /\  SuccessHO_Report_r17__sourceCellInfo_r17__F1 (SuccessHO_Report_r17__sourceCellInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SuccessHO_Report_r17__sourceCellInfo_r17__cond. simpl in *. auto.
 - simpl. unfold SuccessHO_Report_r17__sourceCellInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SuccessHO_Report_r17__sourceCellInfo_r17__Format : T_Format SuccessHO_Report_r17__sourceCellInfo_r17__Type SuccessHO_Report_r17__sourceCellInfo_r17__cond :=
        proj2_format  SuccessHO_Report_r17__sourceCellInfo_r17__cond SuccessHO_Report_r17__sourceCellInfo_r17__list__Format
    SuccessHO_Report_r17__sourceCellInfo_r17__F1 SuccessHO_Report_r17__sourceCellInfo_r17__F2 SuccessHO_Report_r17__sourceCellInfo_r17__F1F2_cond  SuccessHO_Report_r17__sourceCellInfo_r17__F1F2_cond2 SuccessHO_Report_r17__sourceCellInfo_r17__F2F1_cond.
Opaque SuccessHO_Report_r17__sourceCellInfo_r17__cond SuccessHO_Report_r17__sourceCellInfo_r17__Format.


Definition SuccessHO_Report_r17__targetCellInfo_r17__Format_Type := Eval cbn in seq_format_prod SuccessHO_Report_r17__targetCellInfo_r17__list.
Definition SuccessHO_Report_r17__targetCellInfo_r17__Format_list : SuccessHO_Report_r17__targetCellInfo_r17__Format_Type :=
  (CGI_Info_Logging_r16__Format, (MeasResultSuccessHONR_r17__Format, unit_format)).
Definition SuccessHO_Report_r17__targetCellInfo_r17__list__Format := (*Eval compute in *) seq_format SuccessHO_Report_r17__targetCellInfo_r17__list SuccessHO_Report_r17__targetCellInfo_r17__Format_list.
Definition SuccessHO_Report_r17__targetCellInfo_r17__F1 z :=
  (SuccessHO_Report_r17__targetCellInfo_r17__targetPCellId_r17 z, (SuccessHO_Report_r17__targetCellInfo_r17__targetCellMeas_r17 z, tt)).
Definition SuccessHO_Report_r17__targetCellInfo_r17__F2 (y : seq_type SuccessHO_Report_r17__targetCellInfo_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SuccessHO_Report_r17__targetCellInfo_r17__Type i0 i1
  end.
Lemma SuccessHO_Report_r17__targetCellInfo_r17__F1F2_cond (z : SuccessHO_Report_r17__targetCellInfo_r17__Type)
  : SuccessHO_Report_r17__targetCellInfo_r17__cond z ->
  (seq_cond SuccessHO_Report_r17__targetCellInfo_r17__list (SuccessHO_Report_r17__targetCellInfo_r17__F1 z)).
intro H. unfold SuccessHO_Report_r17__targetCellInfo_r17__cond in H. simpl. auto. Qed.
Lemma SuccessHO_Report_r17__targetCellInfo_r17__F1F2_cond2 (z : SuccessHO_Report_r17__targetCellInfo_r17__Type)
 : SuccessHO_Report_r17__targetCellInfo_r17__F2 (SuccessHO_Report_r17__targetCellInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SuccessHO_Report_r17__targetCellInfo_r17__F2F1_cond (y : seq_type SuccessHO_Report_r17__targetCellInfo_r17__list)
  : seq_cond SuccessHO_Report_r17__targetCellInfo_r17__list y ->
 (SuccessHO_Report_r17__targetCellInfo_r17__cond (SuccessHO_Report_r17__targetCellInfo_r17__F2 y)) /\  SuccessHO_Report_r17__targetCellInfo_r17__F1 (SuccessHO_Report_r17__targetCellInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SuccessHO_Report_r17__targetCellInfo_r17__cond. simpl in *. auto.
 - simpl. unfold SuccessHO_Report_r17__targetCellInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SuccessHO_Report_r17__targetCellInfo_r17__Format : T_Format SuccessHO_Report_r17__targetCellInfo_r17__Type SuccessHO_Report_r17__targetCellInfo_r17__cond :=
        proj2_format  SuccessHO_Report_r17__targetCellInfo_r17__cond SuccessHO_Report_r17__targetCellInfo_r17__list__Format
    SuccessHO_Report_r17__targetCellInfo_r17__F1 SuccessHO_Report_r17__targetCellInfo_r17__F2 SuccessHO_Report_r17__targetCellInfo_r17__F1F2_cond  SuccessHO_Report_r17__targetCellInfo_r17__F1F2_cond2 SuccessHO_Report_r17__targetCellInfo_r17__F2F1_cond.
Opaque SuccessHO_Report_r17__targetCellInfo_r17__cond SuccessHO_Report_r17__targetCellInfo_r17__Format.


Definition SuccessHO_Report_r17__measResultNeighCells_r17__Format_Type := Eval cbn in seq_format_prod SuccessHO_Report_r17__measResultNeighCells_r17__list.
Definition SuccessHO_Report_r17__measResultNeighCells_r17__Format_list : SuccessHO_Report_r17__measResultNeighCells_r17__Format_Type :=
  (MeasResultList2NR_r16__Format, (MeasResultList2EUTRA_r16__Format, unit_format)).
Definition SuccessHO_Report_r17__measResultNeighCells_r17__list__Format := (*Eval compute in *) seq_format SuccessHO_Report_r17__measResultNeighCells_r17__list SuccessHO_Report_r17__measResultNeighCells_r17__Format_list.
Definition SuccessHO_Report_r17__measResultNeighCells_r17__F1 z :=
  (SuccessHO_Report_r17__measResultNeighCells_r17__measResultListNR_r17 z, (SuccessHO_Report_r17__measResultNeighCells_r17__measResultListEUTRA_r17 z, tt)).
Definition SuccessHO_Report_r17__measResultNeighCells_r17__F2 (y : seq_type SuccessHO_Report_r17__measResultNeighCells_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SuccessHO_Report_r17__measResultNeighCells_r17__Type i0 i1
  end.
Lemma SuccessHO_Report_r17__measResultNeighCells_r17__F1F2_cond (z : SuccessHO_Report_r17__measResultNeighCells_r17__Type)
  : SuccessHO_Report_r17__measResultNeighCells_r17__cond z ->
  (seq_cond SuccessHO_Report_r17__measResultNeighCells_r17__list (SuccessHO_Report_r17__measResultNeighCells_r17__F1 z)).
intro H. unfold SuccessHO_Report_r17__measResultNeighCells_r17__cond in H. simpl. auto. Qed.
Lemma SuccessHO_Report_r17__measResultNeighCells_r17__F1F2_cond2 (z : SuccessHO_Report_r17__measResultNeighCells_r17__Type)
 : SuccessHO_Report_r17__measResultNeighCells_r17__F2 (SuccessHO_Report_r17__measResultNeighCells_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SuccessHO_Report_r17__measResultNeighCells_r17__F2F1_cond (y : seq_type SuccessHO_Report_r17__measResultNeighCells_r17__list)
  : seq_cond SuccessHO_Report_r17__measResultNeighCells_r17__list y ->
 (SuccessHO_Report_r17__measResultNeighCells_r17__cond (SuccessHO_Report_r17__measResultNeighCells_r17__F2 y)) /\  SuccessHO_Report_r17__measResultNeighCells_r17__F1 (SuccessHO_Report_r17__measResultNeighCells_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SuccessHO_Report_r17__measResultNeighCells_r17__cond. simpl in *. auto.
 - simpl. unfold SuccessHO_Report_r17__measResultNeighCells_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SuccessHO_Report_r17__measResultNeighCells_r17__Format : T_Format SuccessHO_Report_r17__measResultNeighCells_r17__Type SuccessHO_Report_r17__measResultNeighCells_r17__cond :=
        proj2_format  SuccessHO_Report_r17__measResultNeighCells_r17__cond SuccessHO_Report_r17__measResultNeighCells_r17__list__Format
    SuccessHO_Report_r17__measResultNeighCells_r17__F1 SuccessHO_Report_r17__measResultNeighCells_r17__F2 SuccessHO_Report_r17__measResultNeighCells_r17__F1F2_cond  SuccessHO_Report_r17__measResultNeighCells_r17__F1F2_cond2 SuccessHO_Report_r17__measResultNeighCells_r17__F2F1_cond.
Opaque SuccessHO_Report_r17__measResultNeighCells_r17__cond SuccessHO_Report_r17__measResultNeighCells_r17__Format.


Definition SuccessHO_Report_r17__root_Format_Type := Eval cbn in seq_format_prod SuccessHO_Report_r17__root_list.
Definition SuccessHO_Report_r17__root_Format_list : SuccessHO_Report_r17__root_Format_Type :=
  (SuccessHO_Report_r17__sourceCellInfo_r17__Format, (SuccessHO_Report_r17__targetCellInfo_r17__Format, (SuccessHO_Report_r17__measResultNeighCells_r17__Format, (LocationInfo_r16__Format, (TimeSinceCHO_Reconfig_r17__Format, (SHR_Cause_r17__Format, (RA_InformationCommon_r16__Format, (UPInterruptionTimeAtHO_r17__Format, (RNTI_Value__Format, unit_format))))))))).

Definition SuccessHO_Report_r17__ext_Format_Type := Eval cbn in get_formats SuccessHO_Report_r17__ext_list.
Definition SuccessHO_Report_r17__ext_Format_list : SuccessHO_Report_r17__ext_Format_Type :=
  unit__Format.

Definition SuccessHO_Report_r17__list_type : Set := (seq_type SuccessHO_Report_r17__root_list) * (seq_ext_type SuccessHO_Report_r17__ext_list).
Definition SuccessHO_Report_r17__list_cond (z : SuccessHO_Report_r17__list_type) : Prop :=
        (seq_cond SuccessHO_Report_r17__root_list (fst z)) /\ (seq_ext_cond SuccessHO_Report_r17__ext_list (snd z)).
Definition SuccessHO_Report_r17__list_format : T_Format SuccessHO_Report_r17__list_type SuccessHO_Report_r17__list_cond :=
 (* Eval compute in *) seq_ext_format SuccessHO_Report_r17__root_list SuccessHO_Report_r17__root_Format_list SuccessHO_Report_r17__ext_list SuccessHO_Report_r17__ext_Format_list.

Opaque SuccessHO_Report_r17__list_format.
Definition SuccessHO_Report_r17__F1 (z : SuccessHO_Report_r17__Type) : SuccessHO_Report_r17__list_type :=
  (((SuccessHO_Report_r17__sourceCellInfo_r17 z, (SuccessHO_Report_r17__targetCellInfo_r17 z, (SuccessHO_Report_r17__measResultNeighCells_r17 z, (SuccessHO_Report_r17__locationInfo_r17 z, (SuccessHO_Report_r17__timeSinceCHO_Reconfig_r17 z, (SuccessHO_Report_r17__shr_Cause_r17 z, (SuccessHO_Report_r17__ra_InformationCommon_r17 z, (SuccessHO_Report_r17__upInterruptionTimeAtHO_r17 z, (SuccessHO_Report_r17__c_RNTI_r17 z, tt)))))))))), (
tt)).
Definition SuccessHO_Report_r17__F2 (y : SuccessHO_Report_r17__list_type) : SuccessHO_Report_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), _)=>
    make__SuccessHO_Report_r17__Type j0 j1 j2 j3 j4 j5 j6 j7 j8
  end.
Definition SuccessHO_Report_r17__helper1 : (forall a : SuccessHO_Report_r17__Type, SuccessHO_Report_r17__cond a -> SuccessHO_Report_r17__list_cond (SuccessHO_Report_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SuccessHO_Report_r17__helper2 : (forall a : SuccessHO_Report_r17__Type, SuccessHO_Report_r17__F2 (SuccessHO_Report_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SuccessHO_Report_r17__helper3 : (forall b : SuccessHO_Report_r17__list_type, SuccessHO_Report_r17__list_cond b -> SuccessHO_Report_r17__cond (SuccessHO_Report_r17__F2 b) /\ SuccessHO_Report_r17__F1 (SuccessHO_Report_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SuccessHO_Report_r17__cond, SuccessHO_Report_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SuccessHO_Report_r17__Format : T_Format SuccessHO_Report_r17__Type SuccessHO_Report_r17__cond :=
 proj2_format SuccessHO_Report_r17__cond SuccessHO_Report_r17__list_format  SuccessHO_Report_r17__F1 SuccessHO_Report_r17__F2 SuccessHO_Report_r17__helper1 SuccessHO_Report_r17__helper2 SuccessHO_Report_r17__helper3.

Opaque SuccessHO_Report_r17__cond SuccessHO_Report_r17__Format.

