Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RRCReconfiguration.

Opaque RRCReconfiguration__cond RRCReconfiguration__Format.

Require Import NR.RRCResume.

Opaque RRCResume__cond RRCResume__Format.

Require Import NR.RRCRelease.

Opaque RRCRelease__cond RRCRelease__Format.

Require Import NR.RRCReestablishment.

Opaque RRCReestablishment__cond RRCReestablishment__Format.

Require Import NR.SecurityModeCommand.

Opaque SecurityModeCommand__cond SecurityModeCommand__Format.

Require Import NR.DLInformationTransfer.

Opaque DLInformationTransfer__cond DLInformationTransfer__Format.

Require Import NR.UECapabilityEnquiry.

Opaque UECapabilityEnquiry__cond UECapabilityEnquiry__Format.

Require Import NR.CounterCheck.

Opaque CounterCheck__cond CounterCheck__Format.

Require Import NR.MobilityFromNRCommand.

Opaque MobilityFromNRCommand__cond MobilityFromNRCommand__Format.

Require Import NR.DLDedicatedMessageSegment_r16.

Opaque DLDedicatedMessageSegment_r16__cond DLDedicatedMessageSegment_r16__Format.

Require Import NR.UEInformationRequest_r16.

Opaque UEInformationRequest_r16__cond UEInformationRequest_r16__Format.

Require Import NR.DLInformationTransferMRDC_r16.

Opaque DLInformationTransferMRDC_r16__cond DLInformationTransferMRDC_r16__Format.

Require Import NR.LoggedMeasurementConfiguration_r16.

Opaque LoggedMeasurementConfiguration_r16__cond LoggedMeasurementConfiguration_r16__Format.


Inductive DL_DCCH_MessageType__c1__Type : Set :=
  | DL_DCCH_MessageType__c1__rrcReconfiguration : RRCReconfiguration__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__rrcResume : RRCResume__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__rrcRelease : RRCRelease__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__rrcReestablishment : RRCReestablishment__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__securityModeCommand : SecurityModeCommand__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__dlInformationTransfer : DLInformationTransfer__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__ueCapabilityEnquiry : UECapabilityEnquiry__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__counterCheck : CounterCheck__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__mobilityFromNRCommand : MobilityFromNRCommand__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__dlDedicatedMessageSegment_r16 : DLDedicatedMessageSegment_r16__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__ueInformationRequest_r16 : UEInformationRequest_r16__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__dlInformationTransferMRDC_r16 : DLInformationTransferMRDC_r16__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__loggedMeasurementConfiguration_r16 : LoggedMeasurementConfiguration_r16__Type -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__spare3 : unit -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__spare2 : unit -> DL_DCCH_MessageType__c1__Type
  | DL_DCCH_MessageType__c1__spare1 : unit -> DL_DCCH_MessageType__c1__Type
.
Definition DL_DCCH_MessageType__c1__list : list typ := (
typ_cons RRCReconfiguration__Type RRCReconfiguration__cond ::
typ_cons RRCResume__Type RRCResume__cond ::
typ_cons RRCRelease__Type RRCRelease__cond ::
typ_cons RRCReestablishment__Type RRCReestablishment__cond ::
typ_cons SecurityModeCommand__Type SecurityModeCommand__cond ::
typ_cons DLInformationTransfer__Type DLInformationTransfer__cond ::
typ_cons UECapabilityEnquiry__Type UECapabilityEnquiry__cond ::
typ_cons CounterCheck__Type CounterCheck__cond ::
typ_cons MobilityFromNRCommand__Type MobilityFromNRCommand__cond ::
typ_cons DLDedicatedMessageSegment_r16__Type DLDedicatedMessageSegment_r16__cond ::
typ_cons UEInformationRequest_r16__Type UEInformationRequest_r16__cond ::
typ_cons DLInformationTransferMRDC_r16__Type DLInformationTransferMRDC_r16__cond ::
typ_cons LoggedMeasurementConfiguration_r16__Type LoggedMeasurementConfiguration_r16__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition DL_DCCH_MessageType__c1__cond (c : DL_DCCH_MessageType__c1__Type) := 
  match c with
  | DL_DCCH_MessageType__c1__rrcReconfiguration t => RRCReconfiguration__cond t 
  | DL_DCCH_MessageType__c1__rrcResume t => RRCResume__cond t 
  | DL_DCCH_MessageType__c1__rrcRelease t => RRCRelease__cond t 
  | DL_DCCH_MessageType__c1__rrcReestablishment t => RRCReestablishment__cond t 
  | DL_DCCH_MessageType__c1__securityModeCommand t => SecurityModeCommand__cond t 
  | DL_DCCH_MessageType__c1__dlInformationTransfer t => DLInformationTransfer__cond t 
  | DL_DCCH_MessageType__c1__ueCapabilityEnquiry t => UECapabilityEnquiry__cond t 
  | DL_DCCH_MessageType__c1__counterCheck t => CounterCheck__cond t 
  | DL_DCCH_MessageType__c1__mobilityFromNRCommand t => MobilityFromNRCommand__cond t 
  | DL_DCCH_MessageType__c1__dlDedicatedMessageSegment_r16 t => DLDedicatedMessageSegment_r16__cond t 
  | DL_DCCH_MessageType__c1__ueInformationRequest_r16 t => UEInformationRequest_r16__cond t 
  | DL_DCCH_MessageType__c1__dlInformationTransferMRDC_r16 t => DLInformationTransferMRDC_r16__cond t 
  | DL_DCCH_MessageType__c1__loggedMeasurementConfiguration_r16 t => LoggedMeasurementConfiguration_r16__cond t 
  | DL_DCCH_MessageType__c1__spare3 t => (fun _ => True) t 
  | DL_DCCH_MessageType__c1__spare2 t => (fun _ => True) t 
  | DL_DCCH_MessageType__c1__spare1 t => (fun _ => True) t 
  end.

Lemma DL_DCCH_MessageType__c1__len_helper1 : to_bit_sz (length DL_DCCH_MessageType__c1__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DL_DCCH_MessageType__c1__len_helper2 : 2 <= length2 DL_DCCH_MessageType__c1__list.
 simpl. lia. Qed.
Record DL_DCCH_MessageType__messageClassExtension__Type : Set := make__DL_DCCH_MessageType__messageClassExtension__Type {}.
Definition DL_DCCH_MessageType__messageClassExtension__cond (z : DL_DCCH_MessageType__messageClassExtension__Type) := True.

Inductive DL_DCCH_MessageType__Type : Set :=
  | DL_DCCH_MessageType__c1 : DL_DCCH_MessageType__c1__Type -> DL_DCCH_MessageType__Type
  | DL_DCCH_MessageType__messageClassExtension : DL_DCCH_MessageType__messageClassExtension__Type -> DL_DCCH_MessageType__Type
.
Definition DL_DCCH_MessageType__list : list typ := (
typ_cons DL_DCCH_MessageType__c1__Type DL_DCCH_MessageType__c1__cond ::
typ_cons DL_DCCH_MessageType__messageClassExtension__Type DL_DCCH_MessageType__messageClassExtension__cond ::
 nil).
Definition DL_DCCH_MessageType__cond (c : DL_DCCH_MessageType__Type) := 
  match c with
  | DL_DCCH_MessageType__c1 t => DL_DCCH_MessageType__c1__cond t 
  | DL_DCCH_MessageType__messageClassExtension t => DL_DCCH_MessageType__messageClassExtension__cond t 
  end.

Lemma DL_DCCH_MessageType__len_helper1 : to_bit_sz (length DL_DCCH_MessageType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma DL_DCCH_MessageType__len_helper2 : 2 <= length2 DL_DCCH_MessageType__list.
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

Definition DL_DCCH_MessageType__c1__Format_Type := Eval cbn in get_formats DL_DCCH_MessageType__c1__list.
Definition DL_DCCH_MessageType__c1__Format_list : DL_DCCH_MessageType__c1__Format_Type :=
  (RRCReconfiguration__Format, (RRCResume__Format, (RRCRelease__Format, (RRCReestablishment__Format, (SecurityModeCommand__Format, (DLInformationTransfer__Format, (UECapabilityEnquiry__Format, (CounterCheck__Format, (MobilityFromNRCommand__Format, (DLDedicatedMessageSegment_r16__Format, (UEInformationRequest_r16__Format, (DLInformationTransferMRDC_r16__Format, (LoggedMeasurementConfiguration_r16__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))))))))))))))).
Definition DL_DCCH_MessageType__c1__list__Format := Eval compute in choice_format DL_DCCH_MessageType__c1__list DL_DCCH_MessageType__c1__len_helper1 DL_DCCH_MessageType__c1__len_helper2  DL_DCCH_MessageType__c1__Format_list.
Definition DL_DCCH_MessageType__c1__F1 (z : DL_DCCH_MessageType__c1__Type) : (choice DL_DCCH_MessageType__c1__list) :=
  match z with
   | DL_DCCH_MessageType__c1__rrcReconfiguration t => existT _ 0 t
  | DL_DCCH_MessageType__c1__rrcResume t => existT _ 1 t
  | DL_DCCH_MessageType__c1__rrcRelease t => existT _ 2 t
  | DL_DCCH_MessageType__c1__rrcReestablishment t => existT _ 3 t
  | DL_DCCH_MessageType__c1__securityModeCommand t => existT _ 4 t
  | DL_DCCH_MessageType__c1__dlInformationTransfer t => existT _ 5 t
  | DL_DCCH_MessageType__c1__ueCapabilityEnquiry t => existT _ 6 t
  | DL_DCCH_MessageType__c1__counterCheck t => existT _ 7 t
  | DL_DCCH_MessageType__c1__mobilityFromNRCommand t => existT _ 8 t
  | DL_DCCH_MessageType__c1__dlDedicatedMessageSegment_r16 t => existT _ 9 t
  | DL_DCCH_MessageType__c1__ueInformationRequest_r16 t => existT _ 10 t
  | DL_DCCH_MessageType__c1__dlInformationTransferMRDC_r16 t => existT _ 11 t
  | DL_DCCH_MessageType__c1__loggedMeasurementConfiguration_r16 t => existT _ 12 t
  | DL_DCCH_MessageType__c1__spare3 t => existT _ 13 t
  | DL_DCCH_MessageType__c1__spare2 t => existT _ 14 t
  | DL_DCCH_MessageType__c1__spare1 t => existT _ 15 t
  end.
Definition DL_DCCH_MessageType__c1__g := (fun n => typ_set (get_nth_typ DL_DCCH_MessageType__c1__list n)).
Definition DL_DCCH_MessageType__c1__F2 (y : choice DL_DCCH_MessageType__c1__list) : DL_DCCH_MessageType__c1__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DL_DCCH_MessageType__c1__g n -> DL_DCCH_MessageType__c1__Type) with
    | 0 => fun (t : RRCReconfiguration__Type) => DL_DCCH_MessageType__c1__rrcReconfiguration t 
    | 1 => fun (t : RRCResume__Type) => DL_DCCH_MessageType__c1__rrcResume t 
    | 2 => fun (t : RRCRelease__Type) => DL_DCCH_MessageType__c1__rrcRelease t 
    | 3 => fun (t : RRCReestablishment__Type) => DL_DCCH_MessageType__c1__rrcReestablishment t 
    | 4 => fun (t : SecurityModeCommand__Type) => DL_DCCH_MessageType__c1__securityModeCommand t 
    | 5 => fun (t : DLInformationTransfer__Type) => DL_DCCH_MessageType__c1__dlInformationTransfer t 
    | 6 => fun (t : UECapabilityEnquiry__Type) => DL_DCCH_MessageType__c1__ueCapabilityEnquiry t 
    | 7 => fun (t : CounterCheck__Type) => DL_DCCH_MessageType__c1__counterCheck t 
    | 8 => fun (t : MobilityFromNRCommand__Type) => DL_DCCH_MessageType__c1__mobilityFromNRCommand t 
    | 9 => fun (t : DLDedicatedMessageSegment_r16__Type) => DL_DCCH_MessageType__c1__dlDedicatedMessageSegment_r16 t 
    | 10 => fun (t : UEInformationRequest_r16__Type) => DL_DCCH_MessageType__c1__ueInformationRequest_r16 t 
    | 11 => fun (t : DLInformationTransferMRDC_r16__Type) => DL_DCCH_MessageType__c1__dlInformationTransferMRDC_r16 t 
    | 12 => fun (t : LoggedMeasurementConfiguration_r16__Type) => DL_DCCH_MessageType__c1__loggedMeasurementConfiguration_r16 t 
    | 13 => fun (t : unit) => DL_DCCH_MessageType__c1__spare3 t 
    | 14 => fun (t : unit) => DL_DCCH_MessageType__c1__spare2 t 
    | 15 => fun (t : unit) => DL_DCCH_MessageType__c1__spare1 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0)))))))))))))))) => (fun (x' : nat) (t'' : DL_DCCH_MessageType__c1__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ DL_DCCH_MessageType__c1__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DL_DCCH_MessageType__c1__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))))))))) in match t' return DL_DCCH_MessageType__c1__Type with end) n0
           end t0).

Lemma DL_DCCH_MessageType__c1__helper2 :  forall (y : DL_DCCH_MessageType__c1__Type), DL_DCCH_MessageType__c1__cond y -> choice_cond DL_DCCH_MessageType__c1__list (DL_DCCH_MessageType__c1__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DL_DCCH_MessageType__c1__helper3 :  forall (y : DL_DCCH_MessageType__c1__Type), DL_DCCH_MessageType__c1__F2 (DL_DCCH_MessageType__c1__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DL_DCCH_MessageType__c1__helper4 : (forall b : choice DL_DCCH_MessageType__c1__list, choice_cond DL_DCCH_MessageType__c1__list b -> DL_DCCH_MessageType__c1__cond (DL_DCCH_MessageType__c1__F2 b) /\ DL_DCCH_MessageType__c1__F1 (DL_DCCH_MessageType__c1__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DL_DCCH_MessageType__c1__F1 DL_DCCH_MessageType__c1__F2.
Definition DL_DCCH_MessageType__c1__Format : T_Format DL_DCCH_MessageType__c1__Type DL_DCCH_MessageType__c1__cond :=
  (* Eval compute in *) proj2_format DL_DCCH_MessageType__c1__cond DL_DCCH_MessageType__c1__list__Format DL_DCCH_MessageType__c1__F1 DL_DCCH_MessageType__c1__F2 DL_DCCH_MessageType__c1__helper2 DL_DCCH_MessageType__c1__helper3 DL_DCCH_MessageType__c1__helper4.
Opaque DL_DCCH_MessageType__c1__cond DL_DCCH_MessageType__c1__Format.

Definition DL_DCCH_MessageType__messageClassExtension__helper : forall a : DL_DCCH_MessageType__messageClassExtension__Type, True -> True /\ make__DL_DCCH_MessageType__messageClassExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition DL_DCCH_MessageType__messageClassExtension__Format : T_Format DL_DCCH_MessageType__messageClassExtension__Type DL_DCCH_MessageType__messageClassExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__DL_DCCH_MessageType__messageClassExtension__Type)
    DL_DCCH_MessageType__messageClassExtension__helper unit_unique (fun _ => left I).

Opaque DL_DCCH_MessageType__messageClassExtension__cond DL_DCCH_MessageType__messageClassExtension__Format.


Definition DL_DCCH_MessageType__Format_Type := Eval cbn in get_formats DL_DCCH_MessageType__list.
Definition DL_DCCH_MessageType__Format_list : DL_DCCH_MessageType__Format_Type :=
  (DL_DCCH_MessageType__c1__Format, (DL_DCCH_MessageType__messageClassExtension__Format, unit__Format)).
Definition DL_DCCH_MessageType__list__Format := Eval compute in choice_format DL_DCCH_MessageType__list DL_DCCH_MessageType__len_helper1 DL_DCCH_MessageType__len_helper2  DL_DCCH_MessageType__Format_list.
Definition DL_DCCH_MessageType__F1 (z : DL_DCCH_MessageType__Type) : (choice DL_DCCH_MessageType__list) :=
  match z with
   | DL_DCCH_MessageType__c1 t => existT _ 0 t
  | DL_DCCH_MessageType__messageClassExtension t => existT _ 1 t
  end.
Definition DL_DCCH_MessageType__g := (fun n => typ_set (get_nth_typ DL_DCCH_MessageType__list n)).
Definition DL_DCCH_MessageType__F2 (y : choice DL_DCCH_MessageType__list) : DL_DCCH_MessageType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (DL_DCCH_MessageType__g n -> DL_DCCH_MessageType__Type) with
    | 0 => fun (t : DL_DCCH_MessageType__c1__Type) => DL_DCCH_MessageType__c1 t 
    | 1 => fun (t : DL_DCCH_MessageType__messageClassExtension__Type) => DL_DCCH_MessageType__messageClassExtension t 
 | (S (S n0)) => (fun (x' : nat) (t'' : DL_DCCH_MessageType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ DL_DCCH_MessageType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len DL_DCCH_MessageType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return DL_DCCH_MessageType__Type with end) n0
           end t0).

Lemma DL_DCCH_MessageType__helper2 :  forall (y : DL_DCCH_MessageType__Type), DL_DCCH_MessageType__cond y -> choice_cond DL_DCCH_MessageType__list (DL_DCCH_MessageType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma DL_DCCH_MessageType__helper3 :  forall (y : DL_DCCH_MessageType__Type), DL_DCCH_MessageType__F2 (DL_DCCH_MessageType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma DL_DCCH_MessageType__helper4 : (forall b : choice DL_DCCH_MessageType__list, choice_cond DL_DCCH_MessageType__list b -> DL_DCCH_MessageType__cond (DL_DCCH_MessageType__F2 b) /\ DL_DCCH_MessageType__F1 (DL_DCCH_MessageType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length DL_DCCH_MessageType__F1 DL_DCCH_MessageType__F2.
Definition DL_DCCH_MessageType__Format : T_Format DL_DCCH_MessageType__Type DL_DCCH_MessageType__cond :=
  (* Eval compute in *) proj2_format DL_DCCH_MessageType__cond DL_DCCH_MessageType__list__Format DL_DCCH_MessageType__F1 DL_DCCH_MessageType__F2 DL_DCCH_MessageType__helper2 DL_DCCH_MessageType__helper3 DL_DCCH_MessageType__helper4.
Opaque DL_DCCH_MessageType__cond DL_DCCH_MessageType__Format.

