Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.MeasurementReportSidelink.

Opaque MeasurementReportSidelink__cond MeasurementReportSidelink__Format.

Require Import NR.RRCReconfigurationSidelink.

Opaque RRCReconfigurationSidelink__cond RRCReconfigurationSidelink__Format.

Require Import NR.RRCReconfigurationCompleteSidelink.

Opaque RRCReconfigurationCompleteSidelink__cond RRCReconfigurationCompleteSidelink__Format.

Require Import NR.RRCReconfigurationFailureSidelink.

Opaque RRCReconfigurationFailureSidelink__cond RRCReconfigurationFailureSidelink__Format.

Require Import NR.UECapabilityEnquirySidelink.

Opaque UECapabilityEnquirySidelink__cond UECapabilityEnquirySidelink__Format.

Require Import NR.UECapabilityInformationSidelink.

Opaque UECapabilityInformationSidelink__cond UECapabilityInformationSidelink__Format.

Require Import NR.UuMessageTransferSidelink_r17.

Opaque UuMessageTransferSidelink_r17__cond UuMessageTransferSidelink_r17__Format.

Require Import NR.RemoteUEInformationSidelink_r17.

Opaque RemoteUEInformationSidelink_r17__cond RemoteUEInformationSidelink_r17__Format.


Inductive SCCH_MessageType__c1__Type : Set :=
  | SCCH_MessageType__c1__measurementReportSidelink : MeasurementReportSidelink__Type -> SCCH_MessageType__c1__Type
  | SCCH_MessageType__c1__rrcReconfigurationSidelink : RRCReconfigurationSidelink__Type -> SCCH_MessageType__c1__Type
  | SCCH_MessageType__c1__rrcReconfigurationCompleteSidelink : RRCReconfigurationCompleteSidelink__Type -> SCCH_MessageType__c1__Type
  | SCCH_MessageType__c1__rrcReconfigurationFailureSidelink : RRCReconfigurationFailureSidelink__Type -> SCCH_MessageType__c1__Type
  | SCCH_MessageType__c1__ueCapabilityEnquirySidelink : UECapabilityEnquirySidelink__Type -> SCCH_MessageType__c1__Type
  | SCCH_MessageType__c1__ueCapabilityInformationSidelink : UECapabilityInformationSidelink__Type -> SCCH_MessageType__c1__Type
  | SCCH_MessageType__c1__uuMessageTransferSidelink_r17 : UuMessageTransferSidelink_r17__Type -> SCCH_MessageType__c1__Type
  | SCCH_MessageType__c1__remoteUEInformationSidelink_r17 : RemoteUEInformationSidelink_r17__Type -> SCCH_MessageType__c1__Type
.
Definition SCCH_MessageType__c1__list : list typ := (
typ_cons MeasurementReportSidelink__Type MeasurementReportSidelink__cond ::
typ_cons RRCReconfigurationSidelink__Type RRCReconfigurationSidelink__cond ::
typ_cons RRCReconfigurationCompleteSidelink__Type RRCReconfigurationCompleteSidelink__cond ::
typ_cons RRCReconfigurationFailureSidelink__Type RRCReconfigurationFailureSidelink__cond ::
typ_cons UECapabilityEnquirySidelink__Type UECapabilityEnquirySidelink__cond ::
typ_cons UECapabilityInformationSidelink__Type UECapabilityInformationSidelink__cond ::
typ_cons UuMessageTransferSidelink_r17__Type UuMessageTransferSidelink_r17__cond ::
typ_cons RemoteUEInformationSidelink_r17__Type RemoteUEInformationSidelink_r17__cond ::
 nil).
Definition SCCH_MessageType__c1__cond (c : SCCH_MessageType__c1__Type) := 
  match c with
  | SCCH_MessageType__c1__measurementReportSidelink t => MeasurementReportSidelink__cond t 
  | SCCH_MessageType__c1__rrcReconfigurationSidelink t => RRCReconfigurationSidelink__cond t 
  | SCCH_MessageType__c1__rrcReconfigurationCompleteSidelink t => RRCReconfigurationCompleteSidelink__cond t 
  | SCCH_MessageType__c1__rrcReconfigurationFailureSidelink t => RRCReconfigurationFailureSidelink__cond t 
  | SCCH_MessageType__c1__ueCapabilityEnquirySidelink t => UECapabilityEnquirySidelink__cond t 
  | SCCH_MessageType__c1__ueCapabilityInformationSidelink t => UECapabilityInformationSidelink__cond t 
  | SCCH_MessageType__c1__uuMessageTransferSidelink_r17 t => UuMessageTransferSidelink_r17__cond t 
  | SCCH_MessageType__c1__remoteUEInformationSidelink_r17 t => RemoteUEInformationSidelink_r17__cond t 
  end.

Lemma SCCH_MessageType__c1__len_helper1 : to_bit_sz (length SCCH_MessageType__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SCCH_MessageType__c1__len_helper2 : 2 <= length2 SCCH_MessageType__c1__list.
 simpl. lia. Qed.
Require Import NR.NotificationMessageSidelink_r17.

Opaque NotificationMessageSidelink_r17__cond NotificationMessageSidelink_r17__Format.

Require Import NR.UEAssistanceInformationSidelink_r17.

Opaque UEAssistanceInformationSidelink_r17__cond UEAssistanceInformationSidelink_r17__Format.


Inductive SCCH_MessageType__messageClassExtension__c2__Type : Set :=
  | SCCH_MessageType__messageClassExtension__c2__notificationMessageSidelink_r17 : NotificationMessageSidelink_r17__Type -> SCCH_MessageType__messageClassExtension__c2__Type
  | SCCH_MessageType__messageClassExtension__c2__ueAssistanceInformationSidelink_r17 : UEAssistanceInformationSidelink_r17__Type -> SCCH_MessageType__messageClassExtension__c2__Type
  | SCCH_MessageType__messageClassExtension__c2__spare6 : unit -> SCCH_MessageType__messageClassExtension__c2__Type
  | SCCH_MessageType__messageClassExtension__c2__spare5 : unit -> SCCH_MessageType__messageClassExtension__c2__Type
  | SCCH_MessageType__messageClassExtension__c2__spare4 : unit -> SCCH_MessageType__messageClassExtension__c2__Type
  | SCCH_MessageType__messageClassExtension__c2__spare3 : unit -> SCCH_MessageType__messageClassExtension__c2__Type
  | SCCH_MessageType__messageClassExtension__c2__spare2 : unit -> SCCH_MessageType__messageClassExtension__c2__Type
  | SCCH_MessageType__messageClassExtension__c2__spare1 : unit -> SCCH_MessageType__messageClassExtension__c2__Type
.
Definition SCCH_MessageType__messageClassExtension__c2__list : list typ := (
typ_cons NotificationMessageSidelink_r17__Type NotificationMessageSidelink_r17__cond ::
typ_cons UEAssistanceInformationSidelink_r17__Type UEAssistanceInformationSidelink_r17__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition SCCH_MessageType__messageClassExtension__c2__cond (c : SCCH_MessageType__messageClassExtension__c2__Type) := 
  match c with
  | SCCH_MessageType__messageClassExtension__c2__notificationMessageSidelink_r17 t => NotificationMessageSidelink_r17__cond t 
  | SCCH_MessageType__messageClassExtension__c2__ueAssistanceInformationSidelink_r17 t => UEAssistanceInformationSidelink_r17__cond t 
  | SCCH_MessageType__messageClassExtension__c2__spare6 t => (fun _ => True) t 
  | SCCH_MessageType__messageClassExtension__c2__spare5 t => (fun _ => True) t 
  | SCCH_MessageType__messageClassExtension__c2__spare4 t => (fun _ => True) t 
  | SCCH_MessageType__messageClassExtension__c2__spare3 t => (fun _ => True) t 
  | SCCH_MessageType__messageClassExtension__c2__spare2 t => (fun _ => True) t 
  | SCCH_MessageType__messageClassExtension__c2__spare1 t => (fun _ => True) t 
  end.

Lemma SCCH_MessageType__messageClassExtension__c2__len_helper1 : to_bit_sz (length SCCH_MessageType__messageClassExtension__c2__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SCCH_MessageType__messageClassExtension__c2__len_helper2 : 2 <= length2 SCCH_MessageType__messageClassExtension__c2__list.
 simpl. lia. Qed.
Record SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type : Set := make__SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type {}.
Definition SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__cond (z : SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type) := True.

Inductive SCCH_MessageType__messageClassExtension__Type : Set :=
  | SCCH_MessageType__messageClassExtension__c2 : SCCH_MessageType__messageClassExtension__c2__Type -> SCCH_MessageType__messageClassExtension__Type
  | SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17 : SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type -> SCCH_MessageType__messageClassExtension__Type
.
Definition SCCH_MessageType__messageClassExtension__list : list typ := (
typ_cons SCCH_MessageType__messageClassExtension__c2__Type SCCH_MessageType__messageClassExtension__c2__cond ::
typ_cons SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__cond ::
 nil).
Definition SCCH_MessageType__messageClassExtension__cond (c : SCCH_MessageType__messageClassExtension__Type) := 
  match c with
  | SCCH_MessageType__messageClassExtension__c2 t => SCCH_MessageType__messageClassExtension__c2__cond t 
  | SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17 t => SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__cond t 
  end.

Lemma SCCH_MessageType__messageClassExtension__len_helper1 : to_bit_sz (length SCCH_MessageType__messageClassExtension__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SCCH_MessageType__messageClassExtension__len_helper2 : 2 <= length2 SCCH_MessageType__messageClassExtension__list.
 simpl. lia. Qed.

Inductive SCCH_MessageType__Type : Set :=
  | SCCH_MessageType__c1 : SCCH_MessageType__c1__Type -> SCCH_MessageType__Type
  | SCCH_MessageType__messageClassExtension : SCCH_MessageType__messageClassExtension__Type -> SCCH_MessageType__Type
.
Definition SCCH_MessageType__list : list typ := (
typ_cons SCCH_MessageType__c1__Type SCCH_MessageType__c1__cond ::
typ_cons SCCH_MessageType__messageClassExtension__Type SCCH_MessageType__messageClassExtension__cond ::
 nil).
Definition SCCH_MessageType__cond (c : SCCH_MessageType__Type) := 
  match c with
  | SCCH_MessageType__c1 t => SCCH_MessageType__c1__cond t 
  | SCCH_MessageType__messageClassExtension t => SCCH_MessageType__messageClassExtension__cond t 
  end.

Lemma SCCH_MessageType__len_helper1 : to_bit_sz (length SCCH_MessageType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SCCH_MessageType__len_helper2 : 2 <= length2 SCCH_MessageType__list.
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

Definition SCCH_MessageType__c1__Format_Type := Eval cbn in get_formats SCCH_MessageType__c1__list.
Definition SCCH_MessageType__c1__Format_list : SCCH_MessageType__c1__Format_Type :=
  (MeasurementReportSidelink__Format, (RRCReconfigurationSidelink__Format, (RRCReconfigurationCompleteSidelink__Format, (RRCReconfigurationFailureSidelink__Format, (UECapabilityEnquirySidelink__Format, (UECapabilityInformationSidelink__Format, (UuMessageTransferSidelink_r17__Format, (RemoteUEInformationSidelink_r17__Format, unit__Format)))))))).
Definition SCCH_MessageType__c1__list__Format := Eval compute in choice_format SCCH_MessageType__c1__list SCCH_MessageType__c1__len_helper1 SCCH_MessageType__c1__len_helper2  SCCH_MessageType__c1__Format_list.
Definition SCCH_MessageType__c1__F1 (z : SCCH_MessageType__c1__Type) : (choice SCCH_MessageType__c1__list) :=
  match z with
   | SCCH_MessageType__c1__measurementReportSidelink t => existT _ 0 t
  | SCCH_MessageType__c1__rrcReconfigurationSidelink t => existT _ 1 t
  | SCCH_MessageType__c1__rrcReconfigurationCompleteSidelink t => existT _ 2 t
  | SCCH_MessageType__c1__rrcReconfigurationFailureSidelink t => existT _ 3 t
  | SCCH_MessageType__c1__ueCapabilityEnquirySidelink t => existT _ 4 t
  | SCCH_MessageType__c1__ueCapabilityInformationSidelink t => existT _ 5 t
  | SCCH_MessageType__c1__uuMessageTransferSidelink_r17 t => existT _ 6 t
  | SCCH_MessageType__c1__remoteUEInformationSidelink_r17 t => existT _ 7 t
  end.
Definition SCCH_MessageType__c1__g := (fun n => typ_set (get_nth_typ SCCH_MessageType__c1__list n)).
Definition SCCH_MessageType__c1__F2 (y : choice SCCH_MessageType__c1__list) : SCCH_MessageType__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SCCH_MessageType__c1__g n -> SCCH_MessageType__c1__Type) with
    | 0 => fun (t : MeasurementReportSidelink__Type) => SCCH_MessageType__c1__measurementReportSidelink t 
    | 1 => fun (t : RRCReconfigurationSidelink__Type) => SCCH_MessageType__c1__rrcReconfigurationSidelink t 
    | 2 => fun (t : RRCReconfigurationCompleteSidelink__Type) => SCCH_MessageType__c1__rrcReconfigurationCompleteSidelink t 
    | 3 => fun (t : RRCReconfigurationFailureSidelink__Type) => SCCH_MessageType__c1__rrcReconfigurationFailureSidelink t 
    | 4 => fun (t : UECapabilityEnquirySidelink__Type) => SCCH_MessageType__c1__ueCapabilityEnquirySidelink t 
    | 5 => fun (t : UECapabilityInformationSidelink__Type) => SCCH_MessageType__c1__ueCapabilityInformationSidelink t 
    | 6 => fun (t : UuMessageTransferSidelink_r17__Type) => SCCH_MessageType__c1__uuMessageTransferSidelink_r17 t 
    | 7 => fun (t : RemoteUEInformationSidelink_r17__Type) => SCCH_MessageType__c1__remoteUEInformationSidelink_r17 t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : SCCH_MessageType__c1__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ SCCH_MessageType__c1__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SCCH_MessageType__c1__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return SCCH_MessageType__c1__Type with end) n0
           end t0).

Lemma SCCH_MessageType__c1__helper2 :  forall (y : SCCH_MessageType__c1__Type), SCCH_MessageType__c1__cond y -> choice_cond SCCH_MessageType__c1__list (SCCH_MessageType__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SCCH_MessageType__c1__helper3 :  forall (y : SCCH_MessageType__c1__Type), SCCH_MessageType__c1__F2 (SCCH_MessageType__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SCCH_MessageType__c1__helper4 : (forall b : choice SCCH_MessageType__c1__list, choice_cond SCCH_MessageType__c1__list b -> SCCH_MessageType__c1__cond (SCCH_MessageType__c1__F2 b) /\ SCCH_MessageType__c1__F1 (SCCH_MessageType__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SCCH_MessageType__c1__F1 SCCH_MessageType__c1__F2.
Definition SCCH_MessageType__c1__Format : T_Format SCCH_MessageType__c1__Type SCCH_MessageType__c1__cond :=
  (* Eval compute in *) proj2_format SCCH_MessageType__c1__cond SCCH_MessageType__c1__list__Format SCCH_MessageType__c1__F1 SCCH_MessageType__c1__F2 SCCH_MessageType__c1__helper2 SCCH_MessageType__c1__helper3 SCCH_MessageType__c1__helper4.
Opaque SCCH_MessageType__c1__cond SCCH_MessageType__c1__Format.


Definition SCCH_MessageType__messageClassExtension__c2__Format_Type := Eval cbn in get_formats SCCH_MessageType__messageClassExtension__c2__list.
Definition SCCH_MessageType__messageClassExtension__c2__Format_list : SCCH_MessageType__messageClassExtension__c2__Format_Type :=
  (NotificationMessageSidelink_r17__Format, (UEAssistanceInformationSidelink_r17__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))))))).
Definition SCCH_MessageType__messageClassExtension__c2__list__Format := Eval compute in choice_format SCCH_MessageType__messageClassExtension__c2__list SCCH_MessageType__messageClassExtension__c2__len_helper1 SCCH_MessageType__messageClassExtension__c2__len_helper2  SCCH_MessageType__messageClassExtension__c2__Format_list.
Definition SCCH_MessageType__messageClassExtension__c2__F1 (z : SCCH_MessageType__messageClassExtension__c2__Type) : (choice SCCH_MessageType__messageClassExtension__c2__list) :=
  match z with
   | SCCH_MessageType__messageClassExtension__c2__notificationMessageSidelink_r17 t => existT _ 0 t
  | SCCH_MessageType__messageClassExtension__c2__ueAssistanceInformationSidelink_r17 t => existT _ 1 t
  | SCCH_MessageType__messageClassExtension__c2__spare6 t => existT _ 2 t
  | SCCH_MessageType__messageClassExtension__c2__spare5 t => existT _ 3 t
  | SCCH_MessageType__messageClassExtension__c2__spare4 t => existT _ 4 t
  | SCCH_MessageType__messageClassExtension__c2__spare3 t => existT _ 5 t
  | SCCH_MessageType__messageClassExtension__c2__spare2 t => existT _ 6 t
  | SCCH_MessageType__messageClassExtension__c2__spare1 t => existT _ 7 t
  end.
Definition SCCH_MessageType__messageClassExtension__c2__g := (fun n => typ_set (get_nth_typ SCCH_MessageType__messageClassExtension__c2__list n)).
Definition SCCH_MessageType__messageClassExtension__c2__F2 (y : choice SCCH_MessageType__messageClassExtension__c2__list) : SCCH_MessageType__messageClassExtension__c2__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SCCH_MessageType__messageClassExtension__c2__g n -> SCCH_MessageType__messageClassExtension__c2__Type) with
    | 0 => fun (t : NotificationMessageSidelink_r17__Type) => SCCH_MessageType__messageClassExtension__c2__notificationMessageSidelink_r17 t 
    | 1 => fun (t : UEAssistanceInformationSidelink_r17__Type) => SCCH_MessageType__messageClassExtension__c2__ueAssistanceInformationSidelink_r17 t 
    | 2 => fun (t : unit) => SCCH_MessageType__messageClassExtension__c2__spare6 t 
    | 3 => fun (t : unit) => SCCH_MessageType__messageClassExtension__c2__spare5 t 
    | 4 => fun (t : unit) => SCCH_MessageType__messageClassExtension__c2__spare4 t 
    | 5 => fun (t : unit) => SCCH_MessageType__messageClassExtension__c2__spare3 t 
    | 6 => fun (t : unit) => SCCH_MessageType__messageClassExtension__c2__spare2 t 
    | 7 => fun (t : unit) => SCCH_MessageType__messageClassExtension__c2__spare1 t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : SCCH_MessageType__messageClassExtension__c2__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ SCCH_MessageType__messageClassExtension__c2__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SCCH_MessageType__messageClassExtension__c2__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return SCCH_MessageType__messageClassExtension__c2__Type with end) n0
           end t0).

Lemma SCCH_MessageType__messageClassExtension__c2__helper2 :  forall (y : SCCH_MessageType__messageClassExtension__c2__Type), SCCH_MessageType__messageClassExtension__c2__cond y -> choice_cond SCCH_MessageType__messageClassExtension__c2__list (SCCH_MessageType__messageClassExtension__c2__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SCCH_MessageType__messageClassExtension__c2__helper3 :  forall (y : SCCH_MessageType__messageClassExtension__c2__Type), SCCH_MessageType__messageClassExtension__c2__F2 (SCCH_MessageType__messageClassExtension__c2__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SCCH_MessageType__messageClassExtension__c2__helper4 : (forall b : choice SCCH_MessageType__messageClassExtension__c2__list, choice_cond SCCH_MessageType__messageClassExtension__c2__list b -> SCCH_MessageType__messageClassExtension__c2__cond (SCCH_MessageType__messageClassExtension__c2__F2 b) /\ SCCH_MessageType__messageClassExtension__c2__F1 (SCCH_MessageType__messageClassExtension__c2__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SCCH_MessageType__messageClassExtension__c2__F1 SCCH_MessageType__messageClassExtension__c2__F2.
Definition SCCH_MessageType__messageClassExtension__c2__Format : T_Format SCCH_MessageType__messageClassExtension__c2__Type SCCH_MessageType__messageClassExtension__c2__cond :=
  (* Eval compute in *) proj2_format SCCH_MessageType__messageClassExtension__c2__cond SCCH_MessageType__messageClassExtension__c2__list__Format SCCH_MessageType__messageClassExtension__c2__F1 SCCH_MessageType__messageClassExtension__c2__F2 SCCH_MessageType__messageClassExtension__c2__helper2 SCCH_MessageType__messageClassExtension__c2__helper3 SCCH_MessageType__messageClassExtension__c2__helper4.
Opaque SCCH_MessageType__messageClassExtension__c2__cond SCCH_MessageType__messageClassExtension__c2__Format.

Definition SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__helper : forall a : SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type, True -> True /\ make__SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type = a.
  eq_unit_helper_tact. Qed.
Definition SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Format : T_Format SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type)
    SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__helper unit_unique (fun _ => left I).

Opaque SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__cond SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Format.


Definition SCCH_MessageType__messageClassExtension__Format_Type := Eval cbn in get_formats SCCH_MessageType__messageClassExtension__list.
Definition SCCH_MessageType__messageClassExtension__Format_list : SCCH_MessageType__messageClassExtension__Format_Type :=
  (SCCH_MessageType__messageClassExtension__c2__Format, (SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Format, unit__Format)).
Definition SCCH_MessageType__messageClassExtension__list__Format := Eval compute in choice_format SCCH_MessageType__messageClassExtension__list SCCH_MessageType__messageClassExtension__len_helper1 SCCH_MessageType__messageClassExtension__len_helper2  SCCH_MessageType__messageClassExtension__Format_list.
Definition SCCH_MessageType__messageClassExtension__F1 (z : SCCH_MessageType__messageClassExtension__Type) : (choice SCCH_MessageType__messageClassExtension__list) :=
  match z with
   | SCCH_MessageType__messageClassExtension__c2 t => existT _ 0 t
  | SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17 t => existT _ 1 t
  end.
Definition SCCH_MessageType__messageClassExtension__g := (fun n => typ_set (get_nth_typ SCCH_MessageType__messageClassExtension__list n)).
Definition SCCH_MessageType__messageClassExtension__F2 (y : choice SCCH_MessageType__messageClassExtension__list) : SCCH_MessageType__messageClassExtension__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SCCH_MessageType__messageClassExtension__g n -> SCCH_MessageType__messageClassExtension__Type) with
    | 0 => fun (t : SCCH_MessageType__messageClassExtension__c2__Type) => SCCH_MessageType__messageClassExtension__c2 t 
    | 1 => fun (t : SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17__Type) => SCCH_MessageType__messageClassExtension__messageClassExtensionFuture_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SCCH_MessageType__messageClassExtension__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SCCH_MessageType__messageClassExtension__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SCCH_MessageType__messageClassExtension__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SCCH_MessageType__messageClassExtension__Type with end) n0
           end t0).

Lemma SCCH_MessageType__messageClassExtension__helper2 :  forall (y : SCCH_MessageType__messageClassExtension__Type), SCCH_MessageType__messageClassExtension__cond y -> choice_cond SCCH_MessageType__messageClassExtension__list (SCCH_MessageType__messageClassExtension__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SCCH_MessageType__messageClassExtension__helper3 :  forall (y : SCCH_MessageType__messageClassExtension__Type), SCCH_MessageType__messageClassExtension__F2 (SCCH_MessageType__messageClassExtension__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SCCH_MessageType__messageClassExtension__helper4 : (forall b : choice SCCH_MessageType__messageClassExtension__list, choice_cond SCCH_MessageType__messageClassExtension__list b -> SCCH_MessageType__messageClassExtension__cond (SCCH_MessageType__messageClassExtension__F2 b) /\ SCCH_MessageType__messageClassExtension__F1 (SCCH_MessageType__messageClassExtension__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SCCH_MessageType__messageClassExtension__F1 SCCH_MessageType__messageClassExtension__F2.
Definition SCCH_MessageType__messageClassExtension__Format : T_Format SCCH_MessageType__messageClassExtension__Type SCCH_MessageType__messageClassExtension__cond :=
  (* Eval compute in *) proj2_format SCCH_MessageType__messageClassExtension__cond SCCH_MessageType__messageClassExtension__list__Format SCCH_MessageType__messageClassExtension__F1 SCCH_MessageType__messageClassExtension__F2 SCCH_MessageType__messageClassExtension__helper2 SCCH_MessageType__messageClassExtension__helper3 SCCH_MessageType__messageClassExtension__helper4.
Opaque SCCH_MessageType__messageClassExtension__cond SCCH_MessageType__messageClassExtension__Format.


Definition SCCH_MessageType__Format_Type := Eval cbn in get_formats SCCH_MessageType__list.
Definition SCCH_MessageType__Format_list : SCCH_MessageType__Format_Type :=
  (SCCH_MessageType__c1__Format, (SCCH_MessageType__messageClassExtension__Format, unit__Format)).
Definition SCCH_MessageType__list__Format := Eval compute in choice_format SCCH_MessageType__list SCCH_MessageType__len_helper1 SCCH_MessageType__len_helper2  SCCH_MessageType__Format_list.
Definition SCCH_MessageType__F1 (z : SCCH_MessageType__Type) : (choice SCCH_MessageType__list) :=
  match z with
   | SCCH_MessageType__c1 t => existT _ 0 t
  | SCCH_MessageType__messageClassExtension t => existT _ 1 t
  end.
Definition SCCH_MessageType__g := (fun n => typ_set (get_nth_typ SCCH_MessageType__list n)).
Definition SCCH_MessageType__F2 (y : choice SCCH_MessageType__list) : SCCH_MessageType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SCCH_MessageType__g n -> SCCH_MessageType__Type) with
    | 0 => fun (t : SCCH_MessageType__c1__Type) => SCCH_MessageType__c1 t 
    | 1 => fun (t : SCCH_MessageType__messageClassExtension__Type) => SCCH_MessageType__messageClassExtension t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SCCH_MessageType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SCCH_MessageType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SCCH_MessageType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SCCH_MessageType__Type with end) n0
           end t0).

Lemma SCCH_MessageType__helper2 :  forall (y : SCCH_MessageType__Type), SCCH_MessageType__cond y -> choice_cond SCCH_MessageType__list (SCCH_MessageType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SCCH_MessageType__helper3 :  forall (y : SCCH_MessageType__Type), SCCH_MessageType__F2 (SCCH_MessageType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SCCH_MessageType__helper4 : (forall b : choice SCCH_MessageType__list, choice_cond SCCH_MessageType__list b -> SCCH_MessageType__cond (SCCH_MessageType__F2 b) /\ SCCH_MessageType__F1 (SCCH_MessageType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SCCH_MessageType__F1 SCCH_MessageType__F2.
Definition SCCH_MessageType__Format : T_Format SCCH_MessageType__Type SCCH_MessageType__cond :=
  (* Eval compute in *) proj2_format SCCH_MessageType__cond SCCH_MessageType__list__Format SCCH_MessageType__F1 SCCH_MessageType__F2 SCCH_MessageType__helper2 SCCH_MessageType__helper3 SCCH_MessageType__helper4.
Opaque SCCH_MessageType__cond SCCH_MessageType__Format.

