Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasResultIdleEUTRA_r16.

Opaque MeasResultIdleEUTRA_r16__cond MeasResultIdleEUTRA_r16__Format.

Require Import NR.MeasResultIdleNR_r16.

Opaque MeasResultIdleNR_r16__cond MeasResultIdleNR_r16__Format.

Require Import NR.LogMeasReport_r16.

Opaque LogMeasReport_r16__cond LogMeasReport_r16__Format.

Require Import NR.ConnEstFailReport_r16.

Opaque ConnEstFailReport_r16__cond ConnEstFailReport_r16__Format.

Require Import NR.RA_ReportList_r16.

Opaque RA_ReportList_r16__cond RA_ReportList_r16__Format.

Require Import NR.RLF_Report_r16.

Opaque RLF_Report_r16__cond RLF_Report_r16__Format.

Require Import NR.MobilityHistoryReport_r16.

Opaque MobilityHistoryReport_r16__cond MobilityHistoryReport_r16__Format.

Require Import NR.UEInformationResponse_v1700_IEs.

Opaque UEInformationResponse_v1700_IEs__cond UEInformationResponse_v1700_IEs__Format.

Record UEInformationResponse_r16_IEs__Type : Set :=
  make__UEInformationResponse_r16_IEs__Type {
    UEInformationResponse_r16_IEs__measResultIdleEUTRA_r16 : option MeasResultIdleEUTRA_r16__Type ;
    UEInformationResponse_r16_IEs__measResultIdleNR_r16 : option MeasResultIdleNR_r16__Type ;
    UEInformationResponse_r16_IEs__logMeasReport_r16 : option LogMeasReport_r16__Type ;
    UEInformationResponse_r16_IEs__connEstFailReport_r16 : option ConnEstFailReport_r16__Type ;
    UEInformationResponse_r16_IEs__ra_ReportList_r16 : option RA_ReportList_r16__Type ;
    UEInformationResponse_r16_IEs__rlf_Report_r16 : option RLF_Report_r16__Type ;
    UEInformationResponse_r16_IEs__mobilityHistoryReport_r16 : option MobilityHistoryReport_r16__Type ;
    UEInformationResponse_r16_IEs__lateNonCriticalExtension : option octet_string ;
    UEInformationResponse_r16_IEs__nonCriticalExtension : option UEInformationResponse_v1700_IEs__Type ;
}.
Definition UEInformationResponse_r16_IEs__list := (
 Opt MeasResultIdleEUTRA_r16__Type MeasResultIdleEUTRA_r16__cond ::
 Opt MeasResultIdleNR_r16__Type MeasResultIdleNR_r16__cond ::
 Opt LogMeasReport_r16__Type LogMeasReport_r16__cond ::
 Opt ConnEstFailReport_r16__Type ConnEstFailReport_r16__cond ::
 Opt RA_ReportList_r16__Type RA_ReportList_r16__cond ::
 Opt RLF_Report_r16__Type RLF_Report_r16__cond ::
 Opt MobilityHistoryReport_r16__Type MobilityHistoryReport_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UEInformationResponse_v1700_IEs__Type UEInformationResponse_v1700_IEs__cond ::
 nil).
Definition UEInformationResponse_r16_IEs__cond z := 
  opt_cond MeasResultIdleEUTRA_r16__cond (UEInformationResponse_r16_IEs__measResultIdleEUTRA_r16 z) /\
  opt_cond MeasResultIdleNR_r16__cond (UEInformationResponse_r16_IEs__measResultIdleNR_r16 z) /\
  opt_cond LogMeasReport_r16__cond (UEInformationResponse_r16_IEs__logMeasReport_r16 z) /\
  opt_cond ConnEstFailReport_r16__cond (UEInformationResponse_r16_IEs__connEstFailReport_r16 z) /\
  opt_cond RA_ReportList_r16__cond (UEInformationResponse_r16_IEs__ra_ReportList_r16 z) /\
  opt_cond RLF_Report_r16__cond (UEInformationResponse_r16_IEs__rlf_Report_r16 z) /\
  opt_cond MobilityHistoryReport_r16__cond (UEInformationResponse_r16_IEs__mobilityHistoryReport_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UEInformationResponse_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond UEInformationResponse_v1700_IEs__cond (UEInformationResponse_r16_IEs__nonCriticalExtension z) /\
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

Definition UEInformationResponse_r16_IEs__Format_Type := Eval cbn in seq_format_prod UEInformationResponse_r16_IEs__list.
Definition UEInformationResponse_r16_IEs__Format_list : UEInformationResponse_r16_IEs__Format_Type :=
  (MeasResultIdleEUTRA_r16__Format, (MeasResultIdleNR_r16__Format, (LogMeasReport_r16__Format, (ConnEstFailReport_r16__Format, (RA_ReportList_r16__Format, (RLF_Report_r16__Format, (MobilityHistoryReport_r16__Format, (octet_string_nc__Format, (UEInformationResponse_v1700_IEs__Format, unit_format))))))))).
Definition UEInformationResponse_r16_IEs__list__Format := (*Eval compute in *) seq_format UEInformationResponse_r16_IEs__list UEInformationResponse_r16_IEs__Format_list.
Definition UEInformationResponse_r16_IEs__F1 z :=
  (UEInformationResponse_r16_IEs__measResultIdleEUTRA_r16 z, (UEInformationResponse_r16_IEs__measResultIdleNR_r16 z, (UEInformationResponse_r16_IEs__logMeasReport_r16 z, (UEInformationResponse_r16_IEs__connEstFailReport_r16 z, (UEInformationResponse_r16_IEs__ra_ReportList_r16 z, (UEInformationResponse_r16_IEs__rlf_Report_r16 z, (UEInformationResponse_r16_IEs__mobilityHistoryReport_r16 z, (UEInformationResponse_r16_IEs__lateNonCriticalExtension z, (UEInformationResponse_r16_IEs__nonCriticalExtension z, tt))))))))).
Definition UEInformationResponse_r16_IEs__F2 (y : seq_type UEInformationResponse_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _)))))))))=>
    make__UEInformationResponse_r16_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Lemma UEInformationResponse_r16_IEs__F1F2_cond (z : UEInformationResponse_r16_IEs__Type)
  : UEInformationResponse_r16_IEs__cond z ->
  (seq_cond UEInformationResponse_r16_IEs__list (UEInformationResponse_r16_IEs__F1 z)).
intro H. unfold UEInformationResponse_r16_IEs__cond in H. simpl. auto. Qed.
Lemma UEInformationResponse_r16_IEs__F1F2_cond2 (z : UEInformationResponse_r16_IEs__Type)
 : UEInformationResponse_r16_IEs__F2 (UEInformationResponse_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEInformationResponse_r16_IEs__F2F1_cond (y : seq_type UEInformationResponse_r16_IEs__list)
  : seq_cond UEInformationResponse_r16_IEs__list y ->
 (UEInformationResponse_r16_IEs__cond (UEInformationResponse_r16_IEs__F2 y)) /\  UEInformationResponse_r16_IEs__F1 (UEInformationResponse_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEInformationResponse_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold UEInformationResponse_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEInformationResponse_r16_IEs__Format : T_Format UEInformationResponse_r16_IEs__Type UEInformationResponse_r16_IEs__cond :=
        proj2_format  UEInformationResponse_r16_IEs__cond UEInformationResponse_r16_IEs__list__Format
    UEInformationResponse_r16_IEs__F1 UEInformationResponse_r16_IEs__F2 UEInformationResponse_r16_IEs__F1F2_cond  UEInformationResponse_r16_IEs__F1F2_cond2 UEInformationResponse_r16_IEs__F2F1_cond.
Opaque UEInformationResponse_r16_IEs__cond UEInformationResponse_r16_IEs__Format.

