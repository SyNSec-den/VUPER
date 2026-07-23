Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Type : Set :=
 | UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__true
.
Definition UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__cond := (fun (_ : UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Type) => True).
Lemma UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__nat__helper.

Definition UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F1 t :=
  match t with
  | UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__true => 0
  end.
Definition UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F2 n :=
  match n with
  | 0 => UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__true
  | _ => UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__true
  end.
Lemma UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F1F2 : forall x : UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Type, (UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F1 x <= 0) /\ UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F2 (UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F1 x) = x. imp_solve. Qed.
Lemma UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F2F1 : forall (y : nat) (H : y <= 0), UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F1 (UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UEInformationRequest_r16_IEs__logMeasReportReq_r16__Type : Set :=
 | UEInformationRequest_r16_IEs__logMeasReportReq_r16__true
.
Definition UEInformationRequest_r16_IEs__logMeasReportReq_r16__cond := (fun (_ : UEInformationRequest_r16_IEs__logMeasReportReq_r16__Type) => True).
Lemma UEInformationRequest_r16_IEs__logMeasReportReq_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEInformationRequest_r16_IEs__logMeasReportReq_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEInformationRequest_r16_IEs__logMeasReportReq_r16__nat__helper.

Definition UEInformationRequest_r16_IEs__logMeasReportReq_r16__F1 t :=
  match t with
  | UEInformationRequest_r16_IEs__logMeasReportReq_r16__true => 0
  end.
Definition UEInformationRequest_r16_IEs__logMeasReportReq_r16__F2 n :=
  match n with
  | 0 => UEInformationRequest_r16_IEs__logMeasReportReq_r16__true
  | _ => UEInformationRequest_r16_IEs__logMeasReportReq_r16__true
  end.
Lemma UEInformationRequest_r16_IEs__logMeasReportReq_r16__F1F2 : forall x : UEInformationRequest_r16_IEs__logMeasReportReq_r16__Type, (UEInformationRequest_r16_IEs__logMeasReportReq_r16__F1 x <= 0) /\ UEInformationRequest_r16_IEs__logMeasReportReq_r16__F2 (UEInformationRequest_r16_IEs__logMeasReportReq_r16__F1 x) = x. imp_solve. Qed.
Lemma UEInformationRequest_r16_IEs__logMeasReportReq_r16__F2F1 : forall (y : nat) (H : y <= 0), UEInformationRequest_r16_IEs__logMeasReportReq_r16__F1 (UEInformationRequest_r16_IEs__logMeasReportReq_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Type : Set :=
 | UEInformationRequest_r16_IEs__connEstFailReportReq_r16__true
.
Definition UEInformationRequest_r16_IEs__connEstFailReportReq_r16__cond := (fun (_ : UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Type) => True).
Lemma UEInformationRequest_r16_IEs__connEstFailReportReq_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEInformationRequest_r16_IEs__connEstFailReportReq_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEInformationRequest_r16_IEs__connEstFailReportReq_r16__nat__helper.

Definition UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F1 t :=
  match t with
  | UEInformationRequest_r16_IEs__connEstFailReportReq_r16__true => 0
  end.
Definition UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F2 n :=
  match n with
  | 0 => UEInformationRequest_r16_IEs__connEstFailReportReq_r16__true
  | _ => UEInformationRequest_r16_IEs__connEstFailReportReq_r16__true
  end.
Lemma UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F1F2 : forall x : UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Type, (UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F1 x <= 0) /\ UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F2 (UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F1 x) = x. imp_solve. Qed.
Lemma UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F2F1 : forall (y : nat) (H : y <= 0), UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F1 (UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UEInformationRequest_r16_IEs__ra_ReportReq_r16__Type : Set :=
 | UEInformationRequest_r16_IEs__ra_ReportReq_r16__true
.
Definition UEInformationRequest_r16_IEs__ra_ReportReq_r16__cond := (fun (_ : UEInformationRequest_r16_IEs__ra_ReportReq_r16__Type) => True).
Lemma UEInformationRequest_r16_IEs__ra_ReportReq_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEInformationRequest_r16_IEs__ra_ReportReq_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEInformationRequest_r16_IEs__ra_ReportReq_r16__nat__helper.

Definition UEInformationRequest_r16_IEs__ra_ReportReq_r16__F1 t :=
  match t with
  | UEInformationRequest_r16_IEs__ra_ReportReq_r16__true => 0
  end.
Definition UEInformationRequest_r16_IEs__ra_ReportReq_r16__F2 n :=
  match n with
  | 0 => UEInformationRequest_r16_IEs__ra_ReportReq_r16__true
  | _ => UEInformationRequest_r16_IEs__ra_ReportReq_r16__true
  end.
Lemma UEInformationRequest_r16_IEs__ra_ReportReq_r16__F1F2 : forall x : UEInformationRequest_r16_IEs__ra_ReportReq_r16__Type, (UEInformationRequest_r16_IEs__ra_ReportReq_r16__F1 x <= 0) /\ UEInformationRequest_r16_IEs__ra_ReportReq_r16__F2 (UEInformationRequest_r16_IEs__ra_ReportReq_r16__F1 x) = x. imp_solve. Qed.
Lemma UEInformationRequest_r16_IEs__ra_ReportReq_r16__F2F1 : forall (y : nat) (H : y <= 0), UEInformationRequest_r16_IEs__ra_ReportReq_r16__F1 (UEInformationRequest_r16_IEs__ra_ReportReq_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Type : Set :=
 | UEInformationRequest_r16_IEs__rlf_ReportReq_r16__true
.
Definition UEInformationRequest_r16_IEs__rlf_ReportReq_r16__cond := (fun (_ : UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Type) => True).
Lemma UEInformationRequest_r16_IEs__rlf_ReportReq_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEInformationRequest_r16_IEs__rlf_ReportReq_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEInformationRequest_r16_IEs__rlf_ReportReq_r16__nat__helper.

Definition UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F1 t :=
  match t with
  | UEInformationRequest_r16_IEs__rlf_ReportReq_r16__true => 0
  end.
Definition UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F2 n :=
  match n with
  | 0 => UEInformationRequest_r16_IEs__rlf_ReportReq_r16__true
  | _ => UEInformationRequest_r16_IEs__rlf_ReportReq_r16__true
  end.
Lemma UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F1F2 : forall x : UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Type, (UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F1 x <= 0) /\ UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F2 (UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F1 x) = x. imp_solve. Qed.
Lemma UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F2F1 : forall (y : nat) (H : y <= 0), UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F1 (UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F2 y) = y. enum_solve H y. Qed.

Inductive UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Type : Set :=
 | UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__true
.
Definition UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__cond := (fun (_ : UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Type) => True).
Lemma UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__nat__helper.

Definition UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F1 t :=
  match t with
  | UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__true => 0
  end.
Definition UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F2 n :=
  match n with
  | 0 => UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__true
  | _ => UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__true
  end.
Lemma UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F1F2 : forall x : UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Type, (UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F1 x <= 0) /\ UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F2 (UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F1 x) = x. imp_solve. Qed.
Lemma UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F2F1 : forall (y : nat) (H : y <= 0), UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F1 (UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UEInformationRequest_v1700_IEs.

Opaque UEInformationRequest_v1700_IEs__cond UEInformationRequest_v1700_IEs__Format.

Record UEInformationRequest_r16_IEs__Type : Set :=
  make__UEInformationRequest_r16_IEs__Type {
    UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16 : option UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Type ;
    UEInformationRequest_r16_IEs__logMeasReportReq_r16 : option UEInformationRequest_r16_IEs__logMeasReportReq_r16__Type ;
    UEInformationRequest_r16_IEs__connEstFailReportReq_r16 : option UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Type ;
    UEInformationRequest_r16_IEs__ra_ReportReq_r16 : option UEInformationRequest_r16_IEs__ra_ReportReq_r16__Type ;
    UEInformationRequest_r16_IEs__rlf_ReportReq_r16 : option UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Type ;
    UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16 : option UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Type ;
    UEInformationRequest_r16_IEs__lateNonCriticalExtension : option octet_string ;
    UEInformationRequest_r16_IEs__nonCriticalExtension : option UEInformationRequest_v1700_IEs__Type ;
}.
Definition UEInformationRequest_r16_IEs__list := (
 Opt UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Type UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__cond ::
 Opt UEInformationRequest_r16_IEs__logMeasReportReq_r16__Type UEInformationRequest_r16_IEs__logMeasReportReq_r16__cond ::
 Opt UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Type UEInformationRequest_r16_IEs__connEstFailReportReq_r16__cond ::
 Opt UEInformationRequest_r16_IEs__ra_ReportReq_r16__Type UEInformationRequest_r16_IEs__ra_ReportReq_r16__cond ::
 Opt UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Type UEInformationRequest_r16_IEs__rlf_ReportReq_r16__cond ::
 Opt UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Type UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt UEInformationRequest_v1700_IEs__Type UEInformationRequest_v1700_IEs__cond ::
 nil).
Definition UEInformationRequest_r16_IEs__cond z := 
  opt_cond UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__cond (UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16 z) /\
  opt_cond UEInformationRequest_r16_IEs__logMeasReportReq_r16__cond (UEInformationRequest_r16_IEs__logMeasReportReq_r16 z) /\
  opt_cond UEInformationRequest_r16_IEs__connEstFailReportReq_r16__cond (UEInformationRequest_r16_IEs__connEstFailReportReq_r16 z) /\
  opt_cond UEInformationRequest_r16_IEs__ra_ReportReq_r16__cond (UEInformationRequest_r16_IEs__ra_ReportReq_r16 z) /\
  opt_cond UEInformationRequest_r16_IEs__rlf_ReportReq_r16__cond (UEInformationRequest_r16_IEs__rlf_ReportReq_r16 z) /\
  opt_cond UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__cond (UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (UEInformationRequest_r16_IEs__lateNonCriticalExtension z) /\
  opt_cond UEInformationRequest_v1700_IEs__cond (UEInformationRequest_r16_IEs__nonCriticalExtension z) /\
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
Definition UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Format : T_Format UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__nat__Format UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F1 UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F2 UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F1F2 UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__F2F1.

Opaque UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__cond UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Format.

Definition UEInformationRequest_r16_IEs__logMeasReportReq_r16__Format : T_Format UEInformationRequest_r16_IEs__logMeasReportReq_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEInformationRequest_r16_IEs__logMeasReportReq_r16__nat__Format UEInformationRequest_r16_IEs__logMeasReportReq_r16__F1 UEInformationRequest_r16_IEs__logMeasReportReq_r16__F2 UEInformationRequest_r16_IEs__logMeasReportReq_r16__F1F2 UEInformationRequest_r16_IEs__logMeasReportReq_r16__F2F1.

Opaque UEInformationRequest_r16_IEs__logMeasReportReq_r16__cond UEInformationRequest_r16_IEs__logMeasReportReq_r16__Format.

Definition UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Format : T_Format UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEInformationRequest_r16_IEs__connEstFailReportReq_r16__nat__Format UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F1 UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F2 UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F1F2 UEInformationRequest_r16_IEs__connEstFailReportReq_r16__F2F1.

Opaque UEInformationRequest_r16_IEs__connEstFailReportReq_r16__cond UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Format.

Definition UEInformationRequest_r16_IEs__ra_ReportReq_r16__Format : T_Format UEInformationRequest_r16_IEs__ra_ReportReq_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEInformationRequest_r16_IEs__ra_ReportReq_r16__nat__Format UEInformationRequest_r16_IEs__ra_ReportReq_r16__F1 UEInformationRequest_r16_IEs__ra_ReportReq_r16__F2 UEInformationRequest_r16_IEs__ra_ReportReq_r16__F1F2 UEInformationRequest_r16_IEs__ra_ReportReq_r16__F2F1.

Opaque UEInformationRequest_r16_IEs__ra_ReportReq_r16__cond UEInformationRequest_r16_IEs__ra_ReportReq_r16__Format.

Definition UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Format : T_Format UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEInformationRequest_r16_IEs__rlf_ReportReq_r16__nat__Format UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F1 UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F2 UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F1F2 UEInformationRequest_r16_IEs__rlf_ReportReq_r16__F2F1.

Opaque UEInformationRequest_r16_IEs__rlf_ReportReq_r16__cond UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Format.

Definition UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Format : T_Format UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__nat__Format UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F1 UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F2 UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F1F2 UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__F2F1.

Opaque UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__cond UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Format.


Definition UEInformationRequest_r16_IEs__Format_Type := Eval cbn in seq_format_prod UEInformationRequest_r16_IEs__list.
Definition UEInformationRequest_r16_IEs__Format_list : UEInformationRequest_r16_IEs__Format_Type :=
  (UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16__Format, (UEInformationRequest_r16_IEs__logMeasReportReq_r16__Format, (UEInformationRequest_r16_IEs__connEstFailReportReq_r16__Format, (UEInformationRequest_r16_IEs__ra_ReportReq_r16__Format, (UEInformationRequest_r16_IEs__rlf_ReportReq_r16__Format, (UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16__Format, (octet_string_nc__Format, (UEInformationRequest_v1700_IEs__Format, unit_format)))))))).
Definition UEInformationRequest_r16_IEs__list__Format := (*Eval compute in *) seq_format UEInformationRequest_r16_IEs__list UEInformationRequest_r16_IEs__Format_list.
Definition UEInformationRequest_r16_IEs__F1 z :=
  (UEInformationRequest_r16_IEs__idleModeMeasurementReq_r16 z, (UEInformationRequest_r16_IEs__logMeasReportReq_r16 z, (UEInformationRequest_r16_IEs__connEstFailReportReq_r16 z, (UEInformationRequest_r16_IEs__ra_ReportReq_r16 z, (UEInformationRequest_r16_IEs__rlf_ReportReq_r16 z, (UEInformationRequest_r16_IEs__mobilityHistoryReportReq_r16 z, (UEInformationRequest_r16_IEs__lateNonCriticalExtension z, (UEInformationRequest_r16_IEs__nonCriticalExtension z, tt)))))))).
Definition UEInformationRequest_r16_IEs__F2 (y : seq_type UEInformationRequest_r16_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__UEInformationRequest_r16_IEs__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma UEInformationRequest_r16_IEs__F1F2_cond (z : UEInformationRequest_r16_IEs__Type)
  : UEInformationRequest_r16_IEs__cond z ->
  (seq_cond UEInformationRequest_r16_IEs__list (UEInformationRequest_r16_IEs__F1 z)).
intro H. unfold UEInformationRequest_r16_IEs__cond in H. simpl. auto. Qed.
Lemma UEInformationRequest_r16_IEs__F1F2_cond2 (z : UEInformationRequest_r16_IEs__Type)
 : UEInformationRequest_r16_IEs__F2 (UEInformationRequest_r16_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UEInformationRequest_r16_IEs__F2F1_cond (y : seq_type UEInformationRequest_r16_IEs__list)
  : seq_cond UEInformationRequest_r16_IEs__list y ->
 (UEInformationRequest_r16_IEs__cond (UEInformationRequest_r16_IEs__F2 y)) /\  UEInformationRequest_r16_IEs__F1 (UEInformationRequest_r16_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UEInformationRequest_r16_IEs__cond. simpl in *. auto.
 - simpl. unfold UEInformationRequest_r16_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UEInformationRequest_r16_IEs__Format : T_Format UEInformationRequest_r16_IEs__Type UEInformationRequest_r16_IEs__cond :=
        proj2_format  UEInformationRequest_r16_IEs__cond UEInformationRequest_r16_IEs__list__Format
    UEInformationRequest_r16_IEs__F1 UEInformationRequest_r16_IEs__F2 UEInformationRequest_r16_IEs__F1F2_cond  UEInformationRequest_r16_IEs__F1F2_cond2 UEInformationRequest_r16_IEs__F2F1_cond.
Opaque UEInformationRequest_r16_IEs__cond UEInformationRequest_r16_IEs__Format.

