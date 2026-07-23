Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasurementReport.

Opaque MeasurementReport__cond MeasurementReport__Format.

Require Import NR.RRCReconfigurationComplete.

Opaque RRCReconfigurationComplete__cond RRCReconfigurationComplete__Format.

Require Import NR.RRCSetupComplete.

Opaque RRCSetupComplete__cond RRCSetupComplete__Format.

Require Import NR.RRCReestablishmentComplete.

Opaque RRCReestablishmentComplete__cond RRCReestablishmentComplete__Format.

Require Import NR.RRCResumeComplete.

Opaque RRCResumeComplete__cond RRCResumeComplete__Format.

Require Import NR.SecurityModeComplete.

Opaque SecurityModeComplete__cond SecurityModeComplete__Format.

Require Import NR.SecurityModeFailure.

Opaque SecurityModeFailure__cond SecurityModeFailure__Format.

Require Import NR.ULInformationTransfer.

Opaque ULInformationTransfer__cond ULInformationTransfer__Format.

Require Import NR.LocationMeasurementIndication.

Opaque LocationMeasurementIndication__cond LocationMeasurementIndication__Format.

Require Import NR.UECapabilityInformation.

Opaque UECapabilityInformation__cond UECapabilityInformation__Format.

Require Import NR.CounterCheckResponse.

Opaque CounterCheckResponse__cond CounterCheckResponse__Format.

Require Import NR.UEAssistanceInformation.

Opaque UEAssistanceInformation__cond UEAssistanceInformation__Format.

Require Import NR.FailureInformation.

Opaque FailureInformation__cond FailureInformation__Format.

Require Import NR.ULInformationTransferMRDC.

Opaque ULInformationTransferMRDC__cond ULInformationTransferMRDC__Format.

Require Import NR.SCGFailureInformation.

Opaque SCGFailureInformation__cond SCGFailureInformation__Format.

Require Import NR.SCGFailureInformationEUTRA.

Opaque SCGFailureInformationEUTRA__cond SCGFailureInformationEUTRA__Format.


Inductive UL_DCCH_MessageType__c1__Type : Set :=
  | UL_DCCH_MessageType__c1__measurementReport : MeasurementReport__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__rrcReconfigurationComplete : RRCReconfigurationComplete__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__rrcSetupComplete : RRCSetupComplete__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__rrcReestablishmentComplete : RRCReestablishmentComplete__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__rrcResumeComplete : RRCResumeComplete__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__securityModeComplete : SecurityModeComplete__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__securityModeFailure : SecurityModeFailure__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__ulInformationTransfer : ULInformationTransfer__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__locationMeasurementIndication : LocationMeasurementIndication__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__ueCapabilityInformation : UECapabilityInformation__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__counterCheckResponse : CounterCheckResponse__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__ueAssistanceInformation : UEAssistanceInformation__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__failureInformation : FailureInformation__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__ulInformationTransferMRDC : ULInformationTransferMRDC__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__scgFailureInformation : SCGFailureInformation__Type -> UL_DCCH_MessageType__c1__Type
  | UL_DCCH_MessageType__c1__scgFailureInformationEUTRA : SCGFailureInformationEUTRA__Type -> UL_DCCH_MessageType__c1__Type
.
Definition UL_DCCH_MessageType__c1__list : list typ := (
typ_cons MeasurementReport__Type MeasurementReport__cond ::
typ_cons RRCReconfigurationComplete__Type RRCReconfigurationComplete__cond ::
typ_cons RRCSetupComplete__Type RRCSetupComplete__cond ::
typ_cons RRCReestablishmentComplete__Type RRCReestablishmentComplete__cond ::
typ_cons RRCResumeComplete__Type RRCResumeComplete__cond ::
typ_cons SecurityModeComplete__Type SecurityModeComplete__cond ::
typ_cons SecurityModeFailure__Type SecurityModeFailure__cond ::
typ_cons ULInformationTransfer__Type ULInformationTransfer__cond ::
typ_cons LocationMeasurementIndication__Type LocationMeasurementIndication__cond ::
typ_cons UECapabilityInformation__Type UECapabilityInformation__cond ::
typ_cons CounterCheckResponse__Type CounterCheckResponse__cond ::
typ_cons UEAssistanceInformation__Type UEAssistanceInformation__cond ::
typ_cons FailureInformation__Type FailureInformation__cond ::
typ_cons ULInformationTransferMRDC__Type ULInformationTransferMRDC__cond ::
typ_cons SCGFailureInformation__Type SCGFailureInformation__cond ::
typ_cons SCGFailureInformationEUTRA__Type SCGFailureInformationEUTRA__cond ::
 nil).
Definition UL_DCCH_MessageType__c1__cond (c : UL_DCCH_MessageType__c1__Type) := 
  match c with
  | UL_DCCH_MessageType__c1__measurementReport t => MeasurementReport__cond t 
  | UL_DCCH_MessageType__c1__rrcReconfigurationComplete t => RRCReconfigurationComplete__cond t 
  | UL_DCCH_MessageType__c1__rrcSetupComplete t => RRCSetupComplete__cond t 
  | UL_DCCH_MessageType__c1__rrcReestablishmentComplete t => RRCReestablishmentComplete__cond t 
  | UL_DCCH_MessageType__c1__rrcResumeComplete t => RRCResumeComplete__cond t 
  | UL_DCCH_MessageType__c1__securityModeComplete t => SecurityModeComplete__cond t 
  | UL_DCCH_MessageType__c1__securityModeFailure t => SecurityModeFailure__cond t 
  | UL_DCCH_MessageType__c1__ulInformationTransfer t => ULInformationTransfer__cond t 
  | UL_DCCH_MessageType__c1__locationMeasurementIndication t => LocationMeasurementIndication__cond t 
  | UL_DCCH_MessageType__c1__ueCapabilityInformation t => UECapabilityInformation__cond t 
  | UL_DCCH_MessageType__c1__counterCheckResponse t => CounterCheckResponse__cond t 
  | UL_DCCH_MessageType__c1__ueAssistanceInformation t => UEAssistanceInformation__cond t 
  | UL_DCCH_MessageType__c1__failureInformation t => FailureInformation__cond t 
  | UL_DCCH_MessageType__c1__ulInformationTransferMRDC t => ULInformationTransferMRDC__cond t 
  | UL_DCCH_MessageType__c1__scgFailureInformation t => SCGFailureInformation__cond t 
  | UL_DCCH_MessageType__c1__scgFailureInformationEUTRA t => SCGFailureInformationEUTRA__cond t 
  end.

Lemma UL_DCCH_MessageType__c1__len_helper1 : to_bit_sz (length UL_DCCH_MessageType__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UL_DCCH_MessageType__c1__len_helper2 : 2 <= length2 UL_DCCH_MessageType__c1__list.
 simpl. lia. Qed.
Require Import NR.ULDedicatedMessageSegment_r16.

Opaque ULDedicatedMessageSegment_r16__cond ULDedicatedMessageSegment_r16__Format.

Require Import NR.DedicatedSIBRequest_r16.

Opaque DedicatedSIBRequest_r16__cond DedicatedSIBRequest_r16__Format.

Require Import NR.MCGFailureInformation_r16.

Opaque MCGFailureInformation_r16__cond MCGFailureInformation_r16__Format.

Require Import NR.UEInformationResponse_r16.

Opaque UEInformationResponse_r16__cond UEInformationResponse_r16__Format.

Require Import NR.SidelinkUEInformationNR_r16.

Opaque SidelinkUEInformationNR_r16__cond SidelinkUEInformationNR_r16__Format.

Require Import NR.ULInformationTransferIRAT_r16.

Opaque ULInformationTransferIRAT_r16__cond ULInformationTransferIRAT_r16__Format.

Require Import NR.IABOtherInformation_r16.

Opaque IABOtherInformation_r16__cond IABOtherInformation_r16__Format.

Require Import NR.MBSInterestIndication_r17.

Opaque MBSInterestIndication_r17__cond MBSInterestIndication_r17__Format.

Require Import NR.UEPositioningAssistanceInfo_r17.

Opaque UEPositioningAssistanceInfo_r17__cond UEPositioningAssistanceInfo_r17__Format.

Require Import NR.MeasurementReportAppLayer_r17.

Opaque MeasurementReportAppLayer_r17__cond MeasurementReportAppLayer_r17__Format.


Inductive UL_DCCH_MessageType__messageClassExtension__c2__Type : Set :=
  | UL_DCCH_MessageType__messageClassExtension__c2__ulDedicatedMessageSegment_r16 : ULDedicatedMessageSegment_r16__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__dedicatedSIBRequest_r16 : DedicatedSIBRequest_r16__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__mcgFailureInformation_r16 : MCGFailureInformation_r16__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__ueInformationResponse_r16 : UEInformationResponse_r16__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__sidelinkUEInformationNR_r16 : SidelinkUEInformationNR_r16__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__ulInformationTransferIRAT_r16 : ULInformationTransferIRAT_r16__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__iabOtherInformation_r16 : IABOtherInformation_r16__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__mbsInterestIndication_r17 : MBSInterestIndication_r17__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__uePositioningAssistanceInfo_r17 : UEPositioningAssistanceInfo_r17__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__measurementReportAppLayer_r17 : MeasurementReportAppLayer_r17__Type -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__spare6 : unit -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__spare5 : unit -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__spare4 : unit -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__spare3 : unit -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__spare2 : unit -> UL_DCCH_MessageType__messageClassExtension__c2__Type
  | UL_DCCH_MessageType__messageClassExtension__c2__spare1 : unit -> UL_DCCH_MessageType__messageClassExtension__c2__Type
.
Definition UL_DCCH_MessageType__messageClassExtension__c2__list : list typ := (
typ_cons ULDedicatedMessageSegment_r16__Type ULDedicatedMessageSegment_r16__cond ::
typ_cons DedicatedSIBRequest_r16__Type DedicatedSIBRequest_r16__cond ::
typ_cons MCGFailureInformation_r16__Type MCGFailureInformation_r16__cond ::
typ_cons UEInformationResponse_r16__Type UEInformationResponse_r16__cond ::
typ_cons SidelinkUEInformationNR_r16__Type SidelinkUEInformationNR_r16__cond ::
typ_cons ULInformationTransferIRAT_r16__Type ULInformationTransferIRAT_r16__cond ::
typ_cons IABOtherInformation_r16__Type IABOtherInformation_r16__cond ::
typ_cons MBSInterestIndication_r17__Type MBSInterestIndication_r17__cond ::
typ_cons UEPositioningAssistanceInfo_r17__Type UEPositioningAssistanceInfo_r17__cond ::
typ_cons MeasurementReportAppLayer_r17__Type MeasurementReportAppLayer_r17__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition UL_DCCH_MessageType__messageClassExtension__c2__cond (c : UL_DCCH_MessageType__messageClassExtension__c2__Type) := 
  match c with
  | UL_DCCH_MessageType__messageClassExtension__c2__ulDedicatedMessageSegment_r16 t => ULDedicatedMessageSegment_r16__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__dedicatedSIBRequest_r16 t => DedicatedSIBRequest_r16__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__mcgFailureInformation_r16 t => MCGFailureInformation_r16__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__ueInformationResponse_r16 t => UEInformationResponse_r16__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__sidelinkUEInformationNR_r16 t => SidelinkUEInformationNR_r16__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__ulInformationTransferIRAT_r16 t => ULInformationTransferIRAT_r16__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__iabOtherInformation_r16 t => IABOtherInformation_r16__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__mbsInterestIndication_r17 t => MBSInterestIndication_r17__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__uePositioningAssistanceInfo_r17 t => UEPositioningAssistanceInfo_r17__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__measurementReportAppLayer_r17 t => MeasurementReportAppLayer_r17__cond t 
  | UL_DCCH_MessageType__messageClassExtension__c2__spare6 t => (fun _ => True) t 
  | UL_DCCH_MessageType__messageClassExtension__c2__spare5 t => (fun _ => True) t 
  | UL_DCCH_MessageType__messageClassExtension__c2__spare4 t => (fun _ => True) t 
  | UL_DCCH_MessageType__messageClassExtension__c2__spare3 t => (fun _ => True) t 
  | UL_DCCH_MessageType__messageClassExtension__c2__spare2 t => (fun _ => True) t 
  | UL_DCCH_MessageType__messageClassExtension__c2__spare1 t => (fun _ => True) t 
  end.

Lemma UL_DCCH_MessageType__messageClassExtension__c2__len_helper1 : to_bit_sz (length UL_DCCH_MessageType__messageClassExtension__c2__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UL_DCCH_MessageType__messageClassExtension__c2__len_helper2 : 2 <= length2 UL_DCCH_MessageType__messageClassExtension__c2__list.
 simpl. lia. Qed.
Record UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type : Set := make__UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type {}.
Definition UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__cond (z : UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type) := True.

Inductive UL_DCCH_MessageType__messageClassExtension__Type : Set :=
  | UL_DCCH_MessageType__messageClassExtension__c2 : UL_DCCH_MessageType__messageClassExtension__c2__Type -> UL_DCCH_MessageType__messageClassExtension__Type
  | UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16 : UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type -> UL_DCCH_MessageType__messageClassExtension__Type
.
Definition UL_DCCH_MessageType__messageClassExtension__list : list typ := (
typ_cons UL_DCCH_MessageType__messageClassExtension__c2__Type UL_DCCH_MessageType__messageClassExtension__c2__cond ::
typ_cons UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__cond ::
 nil).
Definition UL_DCCH_MessageType__messageClassExtension__cond (c : UL_DCCH_MessageType__messageClassExtension__Type) := 
  match c with
  | UL_DCCH_MessageType__messageClassExtension__c2 t => UL_DCCH_MessageType__messageClassExtension__c2__cond t 
  | UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16 t => UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__cond t 
  end.

Lemma UL_DCCH_MessageType__messageClassExtension__len_helper1 : to_bit_sz (length UL_DCCH_MessageType__messageClassExtension__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UL_DCCH_MessageType__messageClassExtension__len_helper2 : 2 <= length2 UL_DCCH_MessageType__messageClassExtension__list.
 simpl. lia. Qed.

Inductive UL_DCCH_MessageType__Type : Set :=
  | UL_DCCH_MessageType__c1 : UL_DCCH_MessageType__c1__Type -> UL_DCCH_MessageType__Type
  | UL_DCCH_MessageType__messageClassExtension : UL_DCCH_MessageType__messageClassExtension__Type -> UL_DCCH_MessageType__Type
.
Definition UL_DCCH_MessageType__list : list typ := (
typ_cons UL_DCCH_MessageType__c1__Type UL_DCCH_MessageType__c1__cond ::
typ_cons UL_DCCH_MessageType__messageClassExtension__Type UL_DCCH_MessageType__messageClassExtension__cond ::
 nil).
Definition UL_DCCH_MessageType__cond (c : UL_DCCH_MessageType__Type) := 
  match c with
  | UL_DCCH_MessageType__c1 t => UL_DCCH_MessageType__c1__cond t 
  | UL_DCCH_MessageType__messageClassExtension t => UL_DCCH_MessageType__messageClassExtension__cond t 
  end.

Lemma UL_DCCH_MessageType__len_helper1 : to_bit_sz (length UL_DCCH_MessageType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma UL_DCCH_MessageType__len_helper2 : 2 <= length2 UL_DCCH_MessageType__list.
 simpl. lia. Qed.

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

Definition UL_DCCH_MessageType__c1__Format_Type := Eval cbn in get_formats UL_DCCH_MessageType__c1__list.
Definition UL_DCCH_MessageType__c1__Format_list : UL_DCCH_MessageType__c1__Format_Type :=
  (MeasurementReport__Format, (RRCReconfigurationComplete__Format, (RRCSetupComplete__Format, (RRCReestablishmentComplete__Format, (RRCResumeComplete__Format, (SecurityModeComplete__Format, (SecurityModeFailure__Format, (ULInformationTransfer__Format, (LocationMeasurementIndication__Format, (UECapabilityInformation__Format, (CounterCheckResponse__Format, (UEAssistanceInformation__Format, (FailureInformation__Format, (ULInformationTransferMRDC__Format, (SCGFailureInformation__Format, (SCGFailureInformationEUTRA__Format, unit__Format)))))))))))))))).
Definition UL_DCCH_MessageType__c1__list__Format := Eval compute in choice_format UL_DCCH_MessageType__c1__list UL_DCCH_MessageType__c1__len_helper1 UL_DCCH_MessageType__c1__len_helper2  UL_DCCH_MessageType__c1__Format_list.
Definition UL_DCCH_MessageType__c1__F1 (z : UL_DCCH_MessageType__c1__Type) : (choice UL_DCCH_MessageType__c1__list) :=
  match z with
   | UL_DCCH_MessageType__c1__measurementReport t => existT _ 0 t
  | UL_DCCH_MessageType__c1__rrcReconfigurationComplete t => existT _ 1 t
  | UL_DCCH_MessageType__c1__rrcSetupComplete t => existT _ 2 t
  | UL_DCCH_MessageType__c1__rrcReestablishmentComplete t => existT _ 3 t
  | UL_DCCH_MessageType__c1__rrcResumeComplete t => existT _ 4 t
  | UL_DCCH_MessageType__c1__securityModeComplete t => existT _ 5 t
  | UL_DCCH_MessageType__c1__securityModeFailure t => existT _ 6 t
  | UL_DCCH_MessageType__c1__ulInformationTransfer t => existT _ 7 t
  | UL_DCCH_MessageType__c1__locationMeasurementIndication t => existT _ 8 t
  | UL_DCCH_MessageType__c1__ueCapabilityInformation t => existT _ 9 t
  | UL_DCCH_MessageType__c1__counterCheckResponse t => existT _ 10 t
  | UL_DCCH_MessageType__c1__ueAssistanceInformation t => existT _ 11 t
  | UL_DCCH_MessageType__c1__failureInformation t => existT _ 12 t
  | UL_DCCH_MessageType__c1__ulInformationTransferMRDC t => existT _ 13 t
  | UL_DCCH_MessageType__c1__scgFailureInformation t => existT _ 14 t
  | UL_DCCH_MessageType__c1__scgFailureInformationEUTRA t => existT _ 15 t
  end.
Definition UL_DCCH_MessageType__c1__g := (fun n => typ_set (get_nth_typ UL_DCCH_MessageType__c1__list n)).
Definition UL_DCCH_MessageType__c1__F2 (y : choice UL_DCCH_MessageType__c1__list) : UL_DCCH_MessageType__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UL_DCCH_MessageType__c1__g n -> UL_DCCH_MessageType__c1__Type) with
    | 0 => fun (t : MeasurementReport__Type) => UL_DCCH_MessageType__c1__measurementReport t 
    | 1 => fun (t : RRCReconfigurationComplete__Type) => UL_DCCH_MessageType__c1__rrcReconfigurationComplete t 
    | 2 => fun (t : RRCSetupComplete__Type) => UL_DCCH_MessageType__c1__rrcSetupComplete t 
    | 3 => fun (t : RRCReestablishmentComplete__Type) => UL_DCCH_MessageType__c1__rrcReestablishmentComplete t 
    | 4 => fun (t : RRCResumeComplete__Type) => UL_DCCH_MessageType__c1__rrcResumeComplete t 
    | 5 => fun (t : SecurityModeComplete__Type) => UL_DCCH_MessageType__c1__securityModeComplete t 
    | 6 => fun (t : SecurityModeFailure__Type) => UL_DCCH_MessageType__c1__securityModeFailure t 
    | 7 => fun (t : ULInformationTransfer__Type) => UL_DCCH_MessageType__c1__ulInformationTransfer t 
    | 8 => fun (t : LocationMeasurementIndication__Type) => UL_DCCH_MessageType__c1__locationMeasurementIndication t 
    | 9 => fun (t : UECapabilityInformation__Type) => UL_DCCH_MessageType__c1__ueCapabilityInformation t 
    | 10 => fun (t : CounterCheckResponse__Type) => UL_DCCH_MessageType__c1__counterCheckResponse t 
    | 11 => fun (t : UEAssistanceInformation__Type) => UL_DCCH_MessageType__c1__ueAssistanceInformation t 
    | 12 => fun (t : FailureInformation__Type) => UL_DCCH_MessageType__c1__failureInformation t 
    | 13 => fun (t : ULInformationTransferMRDC__Type) => UL_DCCH_MessageType__c1__ulInformationTransferMRDC t 
    | 14 => fun (t : SCGFailureInformation__Type) => UL_DCCH_MessageType__c1__scgFailureInformation t 
    | 15 => fun (t : SCGFailureInformationEUTRA__Type) => UL_DCCH_MessageType__c1__scgFailureInformationEUTRA t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0)))))))))))))))) => (fun (x' : nat) (t'' : UL_DCCH_MessageType__c1__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ UL_DCCH_MessageType__c1__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UL_DCCH_MessageType__c1__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))))))))) in match t' return UL_DCCH_MessageType__c1__Type with end) n0
           end t0).

Lemma UL_DCCH_MessageType__c1__helper2 :  forall (y : UL_DCCH_MessageType__c1__Type), UL_DCCH_MessageType__c1__cond y -> choice_cond UL_DCCH_MessageType__c1__list (UL_DCCH_MessageType__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UL_DCCH_MessageType__c1__helper3 :  forall (y : UL_DCCH_MessageType__c1__Type), UL_DCCH_MessageType__c1__F2 (UL_DCCH_MessageType__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UL_DCCH_MessageType__c1__helper4 : (forall b : choice UL_DCCH_MessageType__c1__list, choice_cond UL_DCCH_MessageType__c1__list b -> UL_DCCH_MessageType__c1__cond (UL_DCCH_MessageType__c1__F2 b) /\ UL_DCCH_MessageType__c1__F1 (UL_DCCH_MessageType__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UL_DCCH_MessageType__c1__F1 UL_DCCH_MessageType__c1__F2.
Definition UL_DCCH_MessageType__c1__Format : T_Format UL_DCCH_MessageType__c1__Type UL_DCCH_MessageType__c1__cond :=
  (* Eval compute in *) proj2_format UL_DCCH_MessageType__c1__cond UL_DCCH_MessageType__c1__list__Format UL_DCCH_MessageType__c1__F1 UL_DCCH_MessageType__c1__F2 UL_DCCH_MessageType__c1__helper2 UL_DCCH_MessageType__c1__helper3 UL_DCCH_MessageType__c1__helper4.
Opaque UL_DCCH_MessageType__c1__cond UL_DCCH_MessageType__c1__Format.


Definition UL_DCCH_MessageType__messageClassExtension__c2__Format_Type := Eval cbn in get_formats UL_DCCH_MessageType__messageClassExtension__c2__list.
Definition UL_DCCH_MessageType__messageClassExtension__c2__Format_list : UL_DCCH_MessageType__messageClassExtension__c2__Format_Type :=
  (ULDedicatedMessageSegment_r16__Format, (DedicatedSIBRequest_r16__Format, (MCGFailureInformation_r16__Format, (UEInformationResponse_r16__Format, (SidelinkUEInformationNR_r16__Format, (ULInformationTransferIRAT_r16__Format, (IABOtherInformation_r16__Format, (MBSInterestIndication_r17__Format, (UEPositioningAssistanceInfo_r17__Format, (MeasurementReportAppLayer_r17__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))))))))))))))).
Definition UL_DCCH_MessageType__messageClassExtension__c2__list__Format := Eval compute in choice_format UL_DCCH_MessageType__messageClassExtension__c2__list UL_DCCH_MessageType__messageClassExtension__c2__len_helper1 UL_DCCH_MessageType__messageClassExtension__c2__len_helper2  UL_DCCH_MessageType__messageClassExtension__c2__Format_list.
Definition UL_DCCH_MessageType__messageClassExtension__c2__F1 (z : UL_DCCH_MessageType__messageClassExtension__c2__Type) : (choice UL_DCCH_MessageType__messageClassExtension__c2__list) :=
  match z with
   | UL_DCCH_MessageType__messageClassExtension__c2__ulDedicatedMessageSegment_r16 t => existT _ 0 t
  | UL_DCCH_MessageType__messageClassExtension__c2__dedicatedSIBRequest_r16 t => existT _ 1 t
  | UL_DCCH_MessageType__messageClassExtension__c2__mcgFailureInformation_r16 t => existT _ 2 t
  | UL_DCCH_MessageType__messageClassExtension__c2__ueInformationResponse_r16 t => existT _ 3 t
  | UL_DCCH_MessageType__messageClassExtension__c2__sidelinkUEInformationNR_r16 t => existT _ 4 t
  | UL_DCCH_MessageType__messageClassExtension__c2__ulInformationTransferIRAT_r16 t => existT _ 5 t
  | UL_DCCH_MessageType__messageClassExtension__c2__iabOtherInformation_r16 t => existT _ 6 t
  | UL_DCCH_MessageType__messageClassExtension__c2__mbsInterestIndication_r17 t => existT _ 7 t
  | UL_DCCH_MessageType__messageClassExtension__c2__uePositioningAssistanceInfo_r17 t => existT _ 8 t
  | UL_DCCH_MessageType__messageClassExtension__c2__measurementReportAppLayer_r17 t => existT _ 9 t
  | UL_DCCH_MessageType__messageClassExtension__c2__spare6 t => existT _ 10 t
  | UL_DCCH_MessageType__messageClassExtension__c2__spare5 t => existT _ 11 t
  | UL_DCCH_MessageType__messageClassExtension__c2__spare4 t => existT _ 12 t
  | UL_DCCH_MessageType__messageClassExtension__c2__spare3 t => existT _ 13 t
  | UL_DCCH_MessageType__messageClassExtension__c2__spare2 t => existT _ 14 t
  | UL_DCCH_MessageType__messageClassExtension__c2__spare1 t => existT _ 15 t
  end.
Definition UL_DCCH_MessageType__messageClassExtension__c2__g := (fun n => typ_set (get_nth_typ UL_DCCH_MessageType__messageClassExtension__c2__list n)).
Definition UL_DCCH_MessageType__messageClassExtension__c2__F2 (y : choice UL_DCCH_MessageType__messageClassExtension__c2__list) : UL_DCCH_MessageType__messageClassExtension__c2__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UL_DCCH_MessageType__messageClassExtension__c2__g n -> UL_DCCH_MessageType__messageClassExtension__c2__Type) with
    | 0 => fun (t : ULDedicatedMessageSegment_r16__Type) => UL_DCCH_MessageType__messageClassExtension__c2__ulDedicatedMessageSegment_r16 t 
    | 1 => fun (t : DedicatedSIBRequest_r16__Type) => UL_DCCH_MessageType__messageClassExtension__c2__dedicatedSIBRequest_r16 t 
    | 2 => fun (t : MCGFailureInformation_r16__Type) => UL_DCCH_MessageType__messageClassExtension__c2__mcgFailureInformation_r16 t 
    | 3 => fun (t : UEInformationResponse_r16__Type) => UL_DCCH_MessageType__messageClassExtension__c2__ueInformationResponse_r16 t 
    | 4 => fun (t : SidelinkUEInformationNR_r16__Type) => UL_DCCH_MessageType__messageClassExtension__c2__sidelinkUEInformationNR_r16 t 
    | 5 => fun (t : ULInformationTransferIRAT_r16__Type) => UL_DCCH_MessageType__messageClassExtension__c2__ulInformationTransferIRAT_r16 t 
    | 6 => fun (t : IABOtherInformation_r16__Type) => UL_DCCH_MessageType__messageClassExtension__c2__iabOtherInformation_r16 t 
    | 7 => fun (t : MBSInterestIndication_r17__Type) => UL_DCCH_MessageType__messageClassExtension__c2__mbsInterestIndication_r17 t 
    | 8 => fun (t : UEPositioningAssistanceInfo_r17__Type) => UL_DCCH_MessageType__messageClassExtension__c2__uePositioningAssistanceInfo_r17 t 
    | 9 => fun (t : MeasurementReportAppLayer_r17__Type) => UL_DCCH_MessageType__messageClassExtension__c2__measurementReportAppLayer_r17 t 
    | 10 => fun (t : unit) => UL_DCCH_MessageType__messageClassExtension__c2__spare6 t 
    | 11 => fun (t : unit) => UL_DCCH_MessageType__messageClassExtension__c2__spare5 t 
    | 12 => fun (t : unit) => UL_DCCH_MessageType__messageClassExtension__c2__spare4 t 
    | 13 => fun (t : unit) => UL_DCCH_MessageType__messageClassExtension__c2__spare3 t 
    | 14 => fun (t : unit) => UL_DCCH_MessageType__messageClassExtension__c2__spare2 t 
    | 15 => fun (t : unit) => UL_DCCH_MessageType__messageClassExtension__c2__spare1 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0)))))))))))))))) => (fun (x' : nat) (t'' : UL_DCCH_MessageType__messageClassExtension__c2__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ UL_DCCH_MessageType__messageClassExtension__c2__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UL_DCCH_MessageType__messageClassExtension__c2__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))))))))) in match t' return UL_DCCH_MessageType__messageClassExtension__c2__Type with end) n0
           end t0).

Lemma UL_DCCH_MessageType__messageClassExtension__c2__helper2 :  forall (y : UL_DCCH_MessageType__messageClassExtension__c2__Type), UL_DCCH_MessageType__messageClassExtension__c2__cond y -> choice_cond UL_DCCH_MessageType__messageClassExtension__c2__list (UL_DCCH_MessageType__messageClassExtension__c2__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UL_DCCH_MessageType__messageClassExtension__c2__helper3 :  forall (y : UL_DCCH_MessageType__messageClassExtension__c2__Type), UL_DCCH_MessageType__messageClassExtension__c2__F2 (UL_DCCH_MessageType__messageClassExtension__c2__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UL_DCCH_MessageType__messageClassExtension__c2__helper4 : (forall b : choice UL_DCCH_MessageType__messageClassExtension__c2__list, choice_cond UL_DCCH_MessageType__messageClassExtension__c2__list b -> UL_DCCH_MessageType__messageClassExtension__c2__cond (UL_DCCH_MessageType__messageClassExtension__c2__F2 b) /\ UL_DCCH_MessageType__messageClassExtension__c2__F1 (UL_DCCH_MessageType__messageClassExtension__c2__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UL_DCCH_MessageType__messageClassExtension__c2__F1 UL_DCCH_MessageType__messageClassExtension__c2__F2.
Definition UL_DCCH_MessageType__messageClassExtension__c2__Format : T_Format UL_DCCH_MessageType__messageClassExtension__c2__Type UL_DCCH_MessageType__messageClassExtension__c2__cond :=
  (* Eval compute in *) proj2_format UL_DCCH_MessageType__messageClassExtension__c2__cond UL_DCCH_MessageType__messageClassExtension__c2__list__Format UL_DCCH_MessageType__messageClassExtension__c2__F1 UL_DCCH_MessageType__messageClassExtension__c2__F2 UL_DCCH_MessageType__messageClassExtension__c2__helper2 UL_DCCH_MessageType__messageClassExtension__c2__helper3 UL_DCCH_MessageType__messageClassExtension__c2__helper4.
Opaque UL_DCCH_MessageType__messageClassExtension__c2__cond UL_DCCH_MessageType__messageClassExtension__c2__Format.

Definition UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__helper : forall a : UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type, True -> True /\ make__UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type = a.
  eq_unit_helper_tact. Qed.
Definition UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Format : T_Format UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type)
    UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__helper unit_unique (fun _ => left I).

Opaque UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__cond UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Format.


Definition UL_DCCH_MessageType__messageClassExtension__Format_Type := Eval cbn in get_formats UL_DCCH_MessageType__messageClassExtension__list.
Definition UL_DCCH_MessageType__messageClassExtension__Format_list : UL_DCCH_MessageType__messageClassExtension__Format_Type :=
  (UL_DCCH_MessageType__messageClassExtension__c2__Format, (UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Format, unit__Format)).
Definition UL_DCCH_MessageType__messageClassExtension__list__Format := Eval compute in choice_format UL_DCCH_MessageType__messageClassExtension__list UL_DCCH_MessageType__messageClassExtension__len_helper1 UL_DCCH_MessageType__messageClassExtension__len_helper2  UL_DCCH_MessageType__messageClassExtension__Format_list.
Definition UL_DCCH_MessageType__messageClassExtension__F1 (z : UL_DCCH_MessageType__messageClassExtension__Type) : (choice UL_DCCH_MessageType__messageClassExtension__list) :=
  match z with
   | UL_DCCH_MessageType__messageClassExtension__c2 t => existT _ 0 t
  | UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16 t => existT _ 1 t
  end.
Definition UL_DCCH_MessageType__messageClassExtension__g := (fun n => typ_set (get_nth_typ UL_DCCH_MessageType__messageClassExtension__list n)).
Definition UL_DCCH_MessageType__messageClassExtension__F2 (y : choice UL_DCCH_MessageType__messageClassExtension__list) : UL_DCCH_MessageType__messageClassExtension__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UL_DCCH_MessageType__messageClassExtension__g n -> UL_DCCH_MessageType__messageClassExtension__Type) with
    | 0 => fun (t : UL_DCCH_MessageType__messageClassExtension__c2__Type) => UL_DCCH_MessageType__messageClassExtension__c2 t 
    | 1 => fun (t : UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16__Type) => UL_DCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UL_DCCH_MessageType__messageClassExtension__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UL_DCCH_MessageType__messageClassExtension__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UL_DCCH_MessageType__messageClassExtension__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UL_DCCH_MessageType__messageClassExtension__Type with end) n0
           end t0).

Lemma UL_DCCH_MessageType__messageClassExtension__helper2 :  forall (y : UL_DCCH_MessageType__messageClassExtension__Type), UL_DCCH_MessageType__messageClassExtension__cond y -> choice_cond UL_DCCH_MessageType__messageClassExtension__list (UL_DCCH_MessageType__messageClassExtension__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UL_DCCH_MessageType__messageClassExtension__helper3 :  forall (y : UL_DCCH_MessageType__messageClassExtension__Type), UL_DCCH_MessageType__messageClassExtension__F2 (UL_DCCH_MessageType__messageClassExtension__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UL_DCCH_MessageType__messageClassExtension__helper4 : (forall b : choice UL_DCCH_MessageType__messageClassExtension__list, choice_cond UL_DCCH_MessageType__messageClassExtension__list b -> UL_DCCH_MessageType__messageClassExtension__cond (UL_DCCH_MessageType__messageClassExtension__F2 b) /\ UL_DCCH_MessageType__messageClassExtension__F1 (UL_DCCH_MessageType__messageClassExtension__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UL_DCCH_MessageType__messageClassExtension__F1 UL_DCCH_MessageType__messageClassExtension__F2.
Definition UL_DCCH_MessageType__messageClassExtension__Format : T_Format UL_DCCH_MessageType__messageClassExtension__Type UL_DCCH_MessageType__messageClassExtension__cond :=
  (* Eval compute in *) proj2_format UL_DCCH_MessageType__messageClassExtension__cond UL_DCCH_MessageType__messageClassExtension__list__Format UL_DCCH_MessageType__messageClassExtension__F1 UL_DCCH_MessageType__messageClassExtension__F2 UL_DCCH_MessageType__messageClassExtension__helper2 UL_DCCH_MessageType__messageClassExtension__helper3 UL_DCCH_MessageType__messageClassExtension__helper4.
Opaque UL_DCCH_MessageType__messageClassExtension__cond UL_DCCH_MessageType__messageClassExtension__Format.


Definition UL_DCCH_MessageType__Format_Type := Eval cbn in get_formats UL_DCCH_MessageType__list.
Definition UL_DCCH_MessageType__Format_list : UL_DCCH_MessageType__Format_Type :=
  (UL_DCCH_MessageType__c1__Format, (UL_DCCH_MessageType__messageClassExtension__Format, unit__Format)).
Definition UL_DCCH_MessageType__list__Format := Eval compute in choice_format UL_DCCH_MessageType__list UL_DCCH_MessageType__len_helper1 UL_DCCH_MessageType__len_helper2  UL_DCCH_MessageType__Format_list.
Definition UL_DCCH_MessageType__F1 (z : UL_DCCH_MessageType__Type) : (choice UL_DCCH_MessageType__list) :=
  match z with
   | UL_DCCH_MessageType__c1 t => existT _ 0 t
  | UL_DCCH_MessageType__messageClassExtension t => existT _ 1 t
  end.
Definition UL_DCCH_MessageType__g := (fun n => typ_set (get_nth_typ UL_DCCH_MessageType__list n)).
Definition UL_DCCH_MessageType__F2 (y : choice UL_DCCH_MessageType__list) : UL_DCCH_MessageType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (UL_DCCH_MessageType__g n -> UL_DCCH_MessageType__Type) with
    | 0 => fun (t : UL_DCCH_MessageType__c1__Type) => UL_DCCH_MessageType__c1 t 
    | 1 => fun (t : UL_DCCH_MessageType__messageClassExtension__Type) => UL_DCCH_MessageType__messageClassExtension t 
 | (S (S n0)) => (fun (x' : nat) (t'' : UL_DCCH_MessageType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ UL_DCCH_MessageType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len UL_DCCH_MessageType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return UL_DCCH_MessageType__Type with end) n0
           end t0).

Lemma UL_DCCH_MessageType__helper2 :  forall (y : UL_DCCH_MessageType__Type), UL_DCCH_MessageType__cond y -> choice_cond UL_DCCH_MessageType__list (UL_DCCH_MessageType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma UL_DCCH_MessageType__helper3 :  forall (y : UL_DCCH_MessageType__Type), UL_DCCH_MessageType__F2 (UL_DCCH_MessageType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma UL_DCCH_MessageType__helper4 : (forall b : choice UL_DCCH_MessageType__list, choice_cond UL_DCCH_MessageType__list b -> UL_DCCH_MessageType__cond (UL_DCCH_MessageType__F2 b) /\ UL_DCCH_MessageType__F1 (UL_DCCH_MessageType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length UL_DCCH_MessageType__F1 UL_DCCH_MessageType__F2.
Definition UL_DCCH_MessageType__Format : T_Format UL_DCCH_MessageType__Type UL_DCCH_MessageType__cond :=
  (* Eval compute in *) proj2_format UL_DCCH_MessageType__cond UL_DCCH_MessageType__list__Format UL_DCCH_MessageType__F1 UL_DCCH_MessageType__F2 UL_DCCH_MessageType__helper2 UL_DCCH_MessageType__helper3 UL_DCCH_MessageType__helper4.
Opaque UL_DCCH_MessageType__cond UL_DCCH_MessageType__Format.

