Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasResultRLFNR_r16.

Opaque MeasResultRLFNR_r16__cond MeasResultRLFNR_r16__Format.

Require Import NR.MeasResultList2NR_r16.

Opaque MeasResultList2NR_r16__cond MeasResultList2NR_r16__Format.

Require Import NR.MeasResultList2EUTRA_r16.

Opaque MeasResultList2EUTRA_r16__cond MeasResultList2EUTRA_r16__Format.

Record RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type : Set :=
  make__RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type {
    RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__measResultListNR_r16 : option MeasResultList2NR_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__measResultListEUTRA_r16 : option MeasResultList2EUTRA_r16__Type ;
}.
Definition RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list := (
 Opt MeasResultList2NR_r16__Type MeasResultList2NR_r16__cond ::
 Opt MeasResultList2EUTRA_r16__Type MeasResultList2EUTRA_r16__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond z := 
  opt_cond MeasResultList2NR_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__measResultListNR_r16 z) /\
  opt_cond MeasResultList2EUTRA_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__measResultListEUTRA_r16 z) /\
  True.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.CGI_InfoEUTRALogging.

Opaque CGI_InfoEUTRALogging__cond CGI_InfoEUTRALogging__Format.


Inductive RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type : Set :=
  | RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__nrPreviousCell_r16 : CGI_Info_Logging_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type
  | RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__eutraPreviousCell_r16 : CGI_InfoEUTRALogging__Type -> RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type
.
Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list : list typ := (
typ_cons CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
typ_cons CGI_InfoEUTRALogging__Type CGI_InfoEUTRALogging__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__cond (c : RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type) := 
  match c with
  | RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__nrPreviousCell_r16 t => CGI_Info_Logging_r16__cond t 
  | RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__eutraPreviousCell_r16 t => CGI_InfoEUTRALogging__cond t 
  end.

Lemma RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__len_helper1 : to_bit_sz (length RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__len_helper2 : 2 <= length2 RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list.
 simpl. lia. Qed.
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.PCI_ARFCN_NR_r16.

Opaque PCI_ARFCN_NR_r16__cond PCI_ARFCN_NR_r16__Format.


Inductive RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type : Set :=
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cellGlobalId_r16 : CGI_Info_Logging_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__pci_arfcn_r16 : PCI_ARFCN_NR_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type
.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list : list typ := (
typ_cons CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
typ_cons PCI_ARFCN_NR_r16__Type PCI_ARFCN_NR_r16__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cond (c : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type) := 
  match c with
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cellGlobalId_r16 t => CGI_Info_Logging_r16__cond t 
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__pci_arfcn_r16 t => PCI_ARFCN_NR_r16__cond t 
  end.

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__len_helper1 : to_bit_sz (length RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__len_helper2 : 2 <= length2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list.
 simpl. lia. Qed.
Require Import NR.CGI_InfoEUTRALogging.

Opaque CGI_InfoEUTRALogging__cond CGI_InfoEUTRALogging__Format.

Require Import NR.PCI_ARFCN_EUTRA_r16.

Opaque PCI_ARFCN_EUTRA_r16__cond PCI_ARFCN_EUTRA_r16__Format.


Inductive RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type : Set :=
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cellGlobalId_r16 : CGI_InfoEUTRALogging__Type -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__pci_arfcn_r16 : PCI_ARFCN_EUTRA_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type
.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list : list typ := (
typ_cons CGI_InfoEUTRALogging__Type CGI_InfoEUTRALogging__cond ::
typ_cons PCI_ARFCN_EUTRA_r16__Type PCI_ARFCN_EUTRA_r16__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cond (c : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type) := 
  match c with
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cellGlobalId_r16 t => CGI_InfoEUTRALogging__cond t 
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__pci_arfcn_r16 t => PCI_ARFCN_EUTRA_r16__cond t 
  end.

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__len_helper1 : to_bit_sz (length RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__len_helper2 : 2 <= length2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list.
 simpl. lia. Qed.

Inductive RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type : Set :=
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16 : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16 : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type
.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list : list typ := (
typ_cons RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cond ::
typ_cons RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__cond (c : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type) := 
  match c with
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16 t => RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cond t 
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16 t => RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cond t 
  end.

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__len_helper1 : to_bit_sz (length RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__len_helper2 : 2 <= length2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list.
 simpl. lia. Qed.
Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.CGI_InfoEUTRALogging.

Opaque CGI_InfoEUTRALogging__cond CGI_InfoEUTRALogging__Format.


Inductive RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type : Set :=
  | RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__nrReconnectCellId_r16 : CGI_Info_Logging_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type
  | RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__eutraReconnectCellId_r16 : CGI_InfoEUTRALogging__Type -> RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type
.
Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list : list typ := (
typ_cons CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
typ_cons CGI_InfoEUTRALogging__Type CGI_InfoEUTRALogging__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__cond (c : RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type) := 
  match c with
  | RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__nrReconnectCellId_r16 t => CGI_Info_Logging_r16__cond t 
  | RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__eutraReconnectCellId_r16 t => CGI_InfoEUTRALogging__cond t 
  end.

Lemma RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__len_helper1 : to_bit_sz (length RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__len_helper2 : 2 <= length2 RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list.
 simpl. lia. Qed.
Require Import NR.TimeUntilReconnection_r16.

Opaque TimeUntilReconnection_r16__cond TimeUntilReconnection_r16__Format.

Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Lemma RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__Type := Z.
Definition RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__cond := (fun z => (0 <= z <= 1023)%Z).
Require Import NR.TimeSinceFailure_r16.

Opaque TimeSinceFailure_r16__cond TimeSinceFailure_r16__Format.

Inductive RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type : Set :=
 | RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__rlf
 | RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__hof
.
Definition RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__cond := (fun (_ : RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type) => True).
Lemma RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__nat__helper.

Definition RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F1 t :=
  match t with
  | RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__rlf => 0
  | RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__hof => 1
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F2 n :=
  match n with
  | 0 => RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__rlf
  | 1 => RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__hof
  | _ => RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__rlf
  end.
Lemma RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F1F2 : forall x : RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type, (RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F1 x <= 1) /\ RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F1 x) = x. imp_solve. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F2F1 : forall (y : nat) (H : y <= 1), RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type : Set :=
 | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t310_Expiry
 | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__randomAccessProblem
 | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__rlc_MaxNumRetx
 | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__beamFailureRecoveryFailure
 | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__lbtFailure_r16
 | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__bh_rlfRecoveryFailure
 | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t312_expiry_r17
 | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__spare1
.
Definition RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__cond := (fun (_ : RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type) => True).
Lemma RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__nat__helper.

Definition RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F1 t :=
  match t with
  | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t310_Expiry => 0
  | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__randomAccessProblem => 1
  | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__rlc_MaxNumRetx => 2
  | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__beamFailureRecoveryFailure => 3
  | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__lbtFailure_r16 => 4
  | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__bh_rlfRecoveryFailure => 5
  | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t312_expiry_r17 => 6
  | RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__spare1 => 7
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F2 n :=
  match n with
  | 0 => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t310_Expiry
  | 1 => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__randomAccessProblem
  | 2 => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__rlc_MaxNumRetx
  | 3 => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__beamFailureRecoveryFailure
  | 4 => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__lbtFailure_r16
  | 5 => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__bh_rlfRecoveryFailure
  | 6 => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t312_expiry_r17
  | 7 => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__spare1
  | _ => RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__t310_Expiry
  end.
Lemma RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F1F2 : forall x : RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type, (RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F1 x <= 7) /\ RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F1 x) = x. imp_solve. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F2F1 : forall (y : nat) (H : y <= 7), RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.LocationInfo_r16.

Opaque LocationInfo_r16__cond LocationInfo_r16__Format.

Inductive RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type : Set :=
 | RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__true
.
Definition RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__cond := (fun (_ : RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type) => True).
Lemma RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__nat__helper.

Definition RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F1 t :=
  match t with
  | RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__true => 0
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F2 n :=
  match n with
  | 0 => RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__true
  | _ => RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__true
  end.
Lemma RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F1F2 : forall x : RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type, (RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F1 x <= 0) /\ RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F1 x) = x. imp_solve. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F2F1 : forall (y : nat) (H : y <= 0), RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RA_InformationCommon_r16.

Opaque RA_InformationCommon_r16__cond RA_InformationCommon_r16__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Type := bit_string_fixed.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 96 /\ bit_string_len_prop (fst z) (snd z)).
Record RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type : Set :=
  make__RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type {
    RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650 : option RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Type ;
}.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__list := (
 Opt RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Type RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond z := 
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__cond (RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650 z) /\
  True.

Definition RLF_Report_r16__nr_RLF_Report_r16__ext0__Type := RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0__cond := RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond.

Inductive RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type : Set :=
 | RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cho
 | RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__daps
 | RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__spare2
 | RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__spare1
.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cond := (fun (_ : RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type) => True).
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__nat__helper.

Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F1 t :=
  match t with
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cho => 0
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__daps => 1
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__spare2 => 2
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__spare1 => 3
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F2 n :=
  match n with
  | 0 => RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cho
  | 1 => RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__daps
  | 2 => RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__spare2
  | 3 => RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__spare1
  | _ => RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cho
  end.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F1F2 : forall x : RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type, (RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F1 x <= 3) /\ RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F2 (RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F1 x) = x. imp_solve. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F2F1 : forall (y : nat) (H : y <= 3), RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F1 (RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.TimeConnSourceDAPS_Failure_r17.

Opaque TimeConnSourceDAPS_Failure_r17__cond TimeConnSourceDAPS_Failure_r17__Format.

Require Import NR.TimeSinceCHO_Reconfig_r17.

Opaque TimeSinceCHO_Reconfig_r17__cond TimeSinceCHO_Reconfig_r17__Format.

Require Import NR.CGI_Info_Logging_r16.

Opaque CGI_Info_Logging_r16__cond CGI_Info_Logging_r16__Format.

Require Import NR.PCI_ARFCN_NR_r16.

Opaque PCI_ARFCN_NR_r16__cond PCI_ARFCN_NR_r16__Format.


Inductive RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type : Set :=
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cellGlobalId_r17 : CGI_Info_Logging_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__pci_arfcn_r17 : PCI_ARFCN_NR_r16__Type -> RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type
.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list : list typ := (
typ_cons CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
typ_cons PCI_ARFCN_NR_r16__Type PCI_ARFCN_NR_r16__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cond (c : RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type) := 
  match c with
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cellGlobalId_r17 t => CGI_Info_Logging_r16__cond t 
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__pci_arfcn_r17 t => PCI_ARFCN_NR_r16__cond t 
  end.

Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__len_helper1 : to_bit_sz (length RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__len_helper2 : 2 <= length2 RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list.
 simpl. lia. Qed.
Require Import NR.ChoCandidateCellList_r17.

Opaque ChoCandidateCellList_r17__cond ChoCandidateCellList_r17__Format.

Record RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type : Set :=
  make__RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type {
    RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17 : option RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__ext1O__timeConnSourceDAPS_Failure_r17 : option TimeConnSourceDAPS_Failure_r17__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__ext1O__timeSinceCHO_Reconfig_r17 : option TimeSinceCHO_Reconfig_r17__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17 : option RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCandidateCellList_r17 : option ChoCandidateCellList_r17__Type ;
}.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__list := (
 Opt RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cond ::
 Opt TimeConnSourceDAPS_Failure_r17__Type TimeConnSourceDAPS_Failure_r17__cond ::
 Opt TimeSinceCHO_Reconfig_r17__Type TimeSinceCHO_Reconfig_r17__cond ::
 Opt RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cond ::
 Opt ChoCandidateCellList_r17__Type ChoCandidateCellList_r17__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond z := 
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cond (RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17 z) /\
  opt_cond TimeConnSourceDAPS_Failure_r17__cond (RLF_Report_r16__nr_RLF_Report_r16__ext1O__timeConnSourceDAPS_Failure_r17 z) /\
  opt_cond TimeSinceCHO_Reconfig_r17__cond (RLF_Report_r16__nr_RLF_Report_r16__ext1O__timeSinceCHO_Reconfig_r17 z) /\
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cond (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17 z) /\
  opt_cond ChoCandidateCellList_r17__cond (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCandidateCellList_r17 z) /\
  True.

Definition RLF_Report_r16__nr_RLF_Report_r16__ext1__Type := RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1__cond := RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond.

Record RLF_Report_r16__nr_RLF_Report_r16__Type : Set :=
  make__RLF_Report_r16__nr_RLF_Report_r16__Type {
    RLF_Report_r16__nr_RLF_Report_r16__measResultLastServCell_r16 : MeasResultRLFNR_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16 : option RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__c_RNTI_r16 : RNTI_Value__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16 : option RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16 : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16 : option RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__timeUntilReconnection_r16 : option TimeUntilReconnection_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__reestablishmentCellId_r16 : option CGI_Info_Logging_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16 : option Z ;
    RLF_Report_r16__nr_RLF_Report_r16__timeSinceFailure_r16 : TimeSinceFailure_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16 : RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16 : RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__locationInfo_r16 : option LocationInfo_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16 : option RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__ra_InformationCommon_r16 : option RA_InformationCommon_r16__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__ext0 : option RLF_Report_r16__nr_RLF_Report_r16__ext0__Type ;
    RLF_Report_r16__nr_RLF_Report_r16__ext1 : option RLF_Report_r16__nr_RLF_Report_r16__ext1__Type ;
}.
Definition RLF_Report_r16__nr_RLF_Report_r16__root_list : list seq_elem := (
 Nor MeasResultRLFNR_r16__Type MeasResultRLFNR_r16__cond ::
 Opt RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond ::
 Nor RNTI_Value__Type RNTI_Value__cond ::
 Opt RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__cond ::
 Nor RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__cond ::
 Opt RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__cond ::
 Opt TimeUntilReconnection_r16__Type TimeUntilReconnection_r16__cond ::
 Opt CGI_Info_Logging_r16__Type CGI_Info_Logging_r16__cond ::
 Opt Z RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__cond ::
 Nor TimeSinceFailure_r16__Type TimeSinceFailure_r16__cond ::
 Nor RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__cond ::
 Nor RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__cond ::
 Opt LocationInfo_r16__Type LocationInfo_r16__cond ::
 Opt RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__cond ::
 Opt RA_InformationCommon_r16__Type RA_InformationCommon_r16__cond ::
 nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext_list : list typ := (
  typ_cons RLF_Report_r16__nr_RLF_Report_r16__ext0__Type RLF_Report_r16__nr_RLF_Report_r16__ext0__cond ::
  typ_cons RLF_Report_r16__nr_RLF_Report_r16__ext1__Type RLF_Report_r16__nr_RLF_Report_r16__ext1__cond ::
  nil).
Definition RLF_Report_r16__nr_RLF_Report_r16__cond (z : RLF_Report_r16__nr_RLF_Report_r16__Type) := 
(  MeasResultRLFNR_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__measResultLastServCell_r16 z) /\
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16 z) /\
  RNTI_Value__cond (RLF_Report_r16__nr_RLF_Report_r16__c_RNTI_r16 z) /\
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16 z) /\
  RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16 z) /\
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16 z) /\
  opt_cond TimeUntilReconnection_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__timeUntilReconnection_r16 z) /\
  opt_cond CGI_Info_Logging_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__reestablishmentCellId_r16 z) /\
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16 z) /\
  TimeSinceFailure_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__timeSinceFailure_r16 z) /\
  RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16 z) /\
  RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16 z) /\
  opt_cond LocationInfo_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__locationInfo_r16 z) /\
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16 z) /\
  opt_cond RA_InformationCommon_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__ra_InformationCommon_r16 z) /\
  True) /\ 
(  opt_cond RLF_Report_r16__nr_RLF_Report_r16__ext0__cond (RLF_Report_r16__nr_RLF_Report_r16__ext0 z) /\
  opt_cond RLF_Report_r16__nr_RLF_Report_r16__ext1__cond (RLF_Report_r16__nr_RLF_Report_r16__ext1 z) /\
  True).

Require Import NR.CGI_InfoEUTRALogging.

Opaque CGI_InfoEUTRALogging__cond CGI_InfoEUTRALogging__Format.

Record RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type : Set :=
  make__RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type {
    RLF_Report_r16__eutra_RLF_Report_r16__ext0O__measResult_RLF_Report_EUTRA_v1690 : option octet_string ;
}.
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list := (
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond z := 
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RLF_Report_r16__eutra_RLF_Report_r16__ext0O__measResult_RLF_Report_EUTRA_v1690 z) /\
  True.

Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0__Type := RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type.
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0__cond := RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond.

Record RLF_Report_r16__eutra_RLF_Report_r16__Type : Set :=
  make__RLF_Report_r16__eutra_RLF_Report_r16__Type {
    RLF_Report_r16__eutra_RLF_Report_r16__failedPCellId_EUTRA : CGI_InfoEUTRALogging__Type ;
    RLF_Report_r16__eutra_RLF_Report_r16__measResult_RLF_Report_EUTRA_r16 : octet_string ;
    RLF_Report_r16__eutra_RLF_Report_r16__ext0 : option RLF_Report_r16__eutra_RLF_Report_r16__ext0__Type ;
}.
Definition RLF_Report_r16__eutra_RLF_Report_r16__root_list : list seq_elem := (
 Nor CGI_InfoEUTRALogging__Type CGI_InfoEUTRALogging__cond ::
 Nor octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 nil).
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext_list : list typ := (
  typ_cons RLF_Report_r16__eutra_RLF_Report_r16__ext0__Type RLF_Report_r16__eutra_RLF_Report_r16__ext0__cond ::
  nil).
Definition RLF_Report_r16__eutra_RLF_Report_r16__cond (z : RLF_Report_r16__eutra_RLF_Report_r16__Type) := 
(  CGI_InfoEUTRALogging__cond (RLF_Report_r16__eutra_RLF_Report_r16__failedPCellId_EUTRA z) /\
  (fun (b : octet_string) => length b < Nat.pow 2 14) (RLF_Report_r16__eutra_RLF_Report_r16__measResult_RLF_Report_EUTRA_r16 z) /\
  True) /\ 
(  opt_cond RLF_Report_r16__eutra_RLF_Report_r16__ext0__cond (RLF_Report_r16__eutra_RLF_Report_r16__ext0 z) /\
  True).


Inductive RLF_Report_r16__Type : Set :=
  | RLF_Report_r16__nr_RLF_Report_r16 : RLF_Report_r16__nr_RLF_Report_r16__Type -> RLF_Report_r16__Type
  | RLF_Report_r16__eutra_RLF_Report_r16 : RLF_Report_r16__eutra_RLF_Report_r16__Type -> RLF_Report_r16__Type
.
Definition RLF_Report_r16__list : list typ := (
typ_cons RLF_Report_r16__nr_RLF_Report_r16__Type RLF_Report_r16__nr_RLF_Report_r16__cond ::
typ_cons RLF_Report_r16__eutra_RLF_Report_r16__Type RLF_Report_r16__eutra_RLF_Report_r16__cond ::
 nil).
Definition RLF_Report_r16__cond (c : RLF_Report_r16__Type) := 
  match c with
  | RLF_Report_r16__nr_RLF_Report_r16 t => RLF_Report_r16__nr_RLF_Report_r16__cond t 
  | RLF_Report_r16__eutra_RLF_Report_r16 t => RLF_Report_r16__eutra_RLF_Report_r16__cond t 
  end.

Lemma RLF_Report_r16__len_helper1 : to_bit_sz (length RLF_Report_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RLF_Report_r16__len_helper2 : 2 <= length2 RLF_Report_r16__list.
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

Definition RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format_Type := Eval cbn in seq_format_prod RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format_list : RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format_Type :=
  (MeasResultList2NR_r16__Format, (MeasResultList2EUTRA_r16__Format, unit_format)).
Definition RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list__Format := (*Eval compute in *) seq_format RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1 z :=
  (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__measResultListNR_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__measResultListEUTRA_r16 z, tt)).
Definition RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F2 (y : seq_type RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type i0 i1
  end.
Lemma RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1F2_cond (z : RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type)
  : RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond z ->
  (seq_cond RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1 z)).
intro H. unfold RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond in H. simpl. auto. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1F2_cond2 (z : RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type)
 : RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F2F1_cond (y : seq_type RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list)
  : seq_cond RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list y ->
 (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F2 y)) /\  RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond. simpl in *. auto.
 - simpl. unfold RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Type RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond :=
        proj2_format  RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__list__Format
    RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1F2_cond  RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F1F2_cond2 RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__F2F1_cond.
Opaque RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__cond RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Format_Type := Eval cbn in get_formats RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Format_list : RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Format_Type :=
  (CGI_Info_Logging_r16__Format, (CGI_InfoEUTRALogging__Format, unit__Format)).
Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list__Format := Eval compute in choice_format RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__len_helper1 RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__len_helper2  RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F1 (z : RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type) : (choice RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list) :=
  match z with
   | RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__nrPreviousCell_r16 t => existT _ 0 t
  | RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__eutraPreviousCell_r16 t => existT _ 1 t
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__g := (fun n => typ_set (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list n)).
Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F2 (y : choice RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list) : RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__g n -> RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type) with
    | 0 => fun (t : CGI_Info_Logging_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__nrPreviousCell_r16 t 
    | 1 => fun (t : CGI_InfoEUTRALogging__Type) => RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__eutraPreviousCell_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type with end) n0
           end t0).

Lemma RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__helper2 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__cond y -> choice_cond RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list (RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__helper3 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__helper4 : (forall b : choice RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list, choice_cond RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list b -> RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F2 b) /\ RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F2.
Definition RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__cond :=
  (* Eval compute in *) proj2_format RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__list__Format RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__helper2 RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__helper3 RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__helper4.
Opaque RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Format_Type := Eval cbn in get_formats RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Format_list : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Format_Type :=
  (CGI_Info_Logging_r16__Format, (PCI_ARFCN_NR_r16__Format, unit__Format)).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list__Format := Eval compute in choice_format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__len_helper1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__len_helper2  RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F1 (z : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type) : (choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list) :=
  match z with
   | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cellGlobalId_r16 t => existT _ 0 t
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__pci_arfcn_r16 t => existT _ 1 t
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__g := (fun n => typ_set (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list n)).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F2 (y : choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list) : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__g n -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type) with
    | 0 => fun (t : CGI_Info_Logging_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cellGlobalId_r16 t 
    | 1 => fun (t : PCI_ARFCN_NR_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__pci_arfcn_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type with end) n0
           end t0).

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__helper2 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cond y -> choice_cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__helper3 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__helper4 : (forall b : choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list, choice_cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list b -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F2 b) /\ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F2.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cond :=
  (* Eval compute in *) proj2_format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__list__Format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__helper2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__helper3 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__helper4.
Opaque RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Format_Type := Eval cbn in get_formats RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Format_list : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Format_Type :=
  (CGI_InfoEUTRALogging__Format, (PCI_ARFCN_EUTRA_r16__Format, unit__Format)).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list__Format := Eval compute in choice_format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__len_helper1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__len_helper2  RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F1 (z : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type) : (choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list) :=
  match z with
   | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cellGlobalId_r16 t => existT _ 0 t
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__pci_arfcn_r16 t => existT _ 1 t
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__g := (fun n => typ_set (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list n)).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F2 (y : choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list) : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__g n -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type) with
    | 0 => fun (t : CGI_InfoEUTRALogging__Type) => RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cellGlobalId_r16 t 
    | 1 => fun (t : PCI_ARFCN_EUTRA_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__pci_arfcn_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type with end) n0
           end t0).

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__helper2 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cond y -> choice_cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__helper3 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__helper4 : (forall b : choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list, choice_cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list b -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F2 b) /\ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F2.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cond :=
  (* Eval compute in *) proj2_format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__list__Format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__helper2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__helper3 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__helper4.
Opaque RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Format_Type := Eval cbn in get_formats RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Format_list : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Format_Type :=
  (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Format, (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Format, unit__Format)).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list__Format := Eval compute in choice_format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__len_helper1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__len_helper2  RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F1 (z : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type) : (choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list) :=
  match z with
   | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16 t => existT _ 0 t
  | RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16 t => existT _ 1 t
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__g := (fun n => typ_set (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list n)).
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F2 (y : choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list) : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__g n -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type) with
    | 0 => fun (t : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__nrFailedPCellId_r16 t 
    | 1 => fun (t : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__eutraFailedPCellId_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type with end) n0
           end t0).

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__helper2 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__cond y -> choice_cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__helper3 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__helper4 : (forall b : choice RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list, choice_cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list b -> RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F2 b) /\ RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F2.
Definition RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__cond :=
  (* Eval compute in *) proj2_format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__list__Format RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__helper2 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__helper3 RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__helper4.
Opaque RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Format_Type := Eval cbn in get_formats RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Format_list : RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Format_Type :=
  (CGI_Info_Logging_r16__Format, (CGI_InfoEUTRALogging__Format, unit__Format)).
Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list__Format := Eval compute in choice_format RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__len_helper1 RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__len_helper2  RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F1 (z : RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type) : (choice RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list) :=
  match z with
   | RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__nrReconnectCellId_r16 t => existT _ 0 t
  | RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__eutraReconnectCellId_r16 t => existT _ 1 t
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__g := (fun n => typ_set (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list n)).
Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F2 (y : choice RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list) : RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__g n -> RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type) with
    | 0 => fun (t : CGI_Info_Logging_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__nrReconnectCellId_r16 t 
    | 1 => fun (t : CGI_InfoEUTRALogging__Type) => RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__eutraReconnectCellId_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type with end) n0
           end t0).

Lemma RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__helper2 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__cond y -> choice_cond RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list (RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__helper3 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type), RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__helper4 : (forall b : choice RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list, choice_cond RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list b -> RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F2 b) /\ RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F2.
Definition RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Type RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__cond :=
  (* Eval compute in *) proj2_format RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__list__Format RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__helper2 RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__helper3 RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__helper4.
Opaque RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__cond RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__Format : T_Format Z RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__cond :=
 ranged_int_format (0) (1023) RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__helper1 RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__helper2.

Opaque RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__cond RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__nat__Format RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F1F2 RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__F2F1.

Opaque RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__cond RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__nat__Format RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F1F2 RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__F2F1.

Opaque RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__cond RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__nat__Format RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F1F2 RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__F2F1.

Opaque RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__cond RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Type RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__cond := (* Eval compute in *) bit_string_fixed_format 96.
Opaque RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__cond RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__Format_Type := Eval cbn in seq_format_prod RLF_Report_r16__nr_RLF_Report_r16__ext0O__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__Format_list : RLF_Report_r16__nr_RLF_Report_r16__ext0O__Format_Type :=
  (RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650__Format, unit_format).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__list__Format := (*Eval compute in *) seq_format RLF_Report_r16__nr_RLF_Report_r16__ext0O__list RLF_Report_r16__nr_RLF_Report_r16__ext0O__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1 z :=
  (RLF_Report_r16__nr_RLF_Report_r16__ext0O__csi_rsRLMConfigBitmap_v1650 z, tt).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__F2 (y : seq_type RLF_Report_r16__nr_RLF_Report_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type i0
  end.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1F2_cond (z : RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type)
  : RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond z ->
  (seq_cond RLF_Report_r16__nr_RLF_Report_r16__ext0O__list (RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1 z)).
intro H. unfold RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1F2_cond2 (z : RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type)
 : RLF_Report_r16__nr_RLF_Report_r16__ext0O__F2 (RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext0O__F2F1_cond (y : seq_type RLF_Report_r16__nr_RLF_Report_r16__ext0O__list)
  : seq_cond RLF_Report_r16__nr_RLF_Report_r16__ext0O__list y ->
 (RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond (RLF_Report_r16__nr_RLF_Report_r16__ext0O__F2 y)) /\  RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1 (RLF_Report_r16__nr_RLF_Report_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0O__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond :=
        proj2_format  RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond RLF_Report_r16__nr_RLF_Report_r16__ext0O__list__Format
    RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1 RLF_Report_r16__nr_RLF_Report_r16__ext0O__F2 RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1F2_cond  RLF_Report_r16__nr_RLF_Report_r16__ext0O__F1F2_cond2 RLF_Report_r16__nr_RLF_Report_r16__ext0O__F2F1_cond.
Opaque RLF_Report_r16__nr_RLF_Report_r16__ext0O__cond RLF_Report_r16__nr_RLF_Report_r16__ext0O__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__ext0__check_all_none (b : RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type) : bool :=
match b with 
  | make__RLF_Report_r16__nr_RLF_Report_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext0__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__ext0__Type RLF_Report_r16__nr_RLF_Report_r16__ext0__cond :=
  restrict_add_format RLF_Report_r16__nr_RLF_Report_r16__ext0__check_all_none RLF_Report_r16__nr_RLF_Report_r16__ext0O__Format.

Opaque RLF_Report_r16__nr_RLF_Report_r16__ext0__cond RLF_Report_r16__nr_RLF_Report_r16__ext0__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__nat__Format RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F1 RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F2 RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F1F2 RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__F2F1.

Opaque RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Format_Type := Eval cbn in get_formats RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Format_list : RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Format_Type :=
  (CGI_Info_Logging_r16__Format, (PCI_ARFCN_NR_r16__Format, unit__Format)).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list__Format := Eval compute in choice_format RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__len_helper1 RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__len_helper2  RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F1 (z : RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type) : (choice RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list) :=
  match z with
   | RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cellGlobalId_r17 t => existT _ 0 t
  | RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__pci_arfcn_r17 t => existT _ 1 t
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__g := (fun n => typ_set (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list n)).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F2 (y : choice RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list) : RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__g n -> RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type) with
    | 0 => fun (t : CGI_Info_Logging_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cellGlobalId_r17 t 
    | 1 => fun (t : PCI_ARFCN_NR_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__pci_arfcn_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type with end) n0
           end t0).

Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__helper2 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type), RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cond y -> choice_cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__helper3 :  forall (y : RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type), RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F2 (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__helper4 : (forall b : choice RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list, choice_cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list b -> RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cond (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F2 b) /\ RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F1 (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F1 RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F2.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Type RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cond :=
  (* Eval compute in *) proj2_format RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__list__Format RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F1 RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__F2 RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__helper2 RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__helper3 RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__helper4.
Opaque RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__Format_Type := Eval cbn in seq_format_prod RLF_Report_r16__nr_RLF_Report_r16__ext1O__list.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__Format_list : RLF_Report_r16__nr_RLF_Report_r16__ext1O__Format_Type :=
  (RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17__Format, (TimeConnSourceDAPS_Failure_r17__Format, (TimeSinceCHO_Reconfig_r17__Format, (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17__Format, (ChoCandidateCellList_r17__Format, unit_format))))).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__list__Format := (*Eval compute in *) seq_format RLF_Report_r16__nr_RLF_Report_r16__ext1O__list RLF_Report_r16__nr_RLF_Report_r16__ext1O__Format_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1 z :=
  (RLF_Report_r16__nr_RLF_Report_r16__ext1O__lastHO_Type_r17 z, (RLF_Report_r16__nr_RLF_Report_r16__ext1O__timeConnSourceDAPS_Failure_r17 z, (RLF_Report_r16__nr_RLF_Report_r16__ext1O__timeSinceCHO_Reconfig_r17 z, (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCellId_r17 z, (RLF_Report_r16__nr_RLF_Report_r16__ext1O__choCandidateCellList_r17 z, tt))))).
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__F2 (y : seq_type RLF_Report_r16__nr_RLF_Report_r16__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type i0 i1 i2 i3 i4
  end.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1F2_cond (z : RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type)
  : RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond z ->
  (seq_cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__list (RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1 z)).
intro H. unfold RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond in H. simpl. auto. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1F2_cond2 (z : RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type)
 : RLF_Report_r16__nr_RLF_Report_r16__ext1O__F2 (RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLF_Report_r16__nr_RLF_Report_r16__ext1O__F2F1_cond (y : seq_type RLF_Report_r16__nr_RLF_Report_r16__ext1O__list)
  : seq_cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__list y ->
 (RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond (RLF_Report_r16__nr_RLF_Report_r16__ext1O__F2 y)) /\  RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1 (RLF_Report_r16__nr_RLF_Report_r16__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond. simpl in *. auto.
 - simpl. unfold RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1O__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond :=
        proj2_format  RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__list__Format
    RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1 RLF_Report_r16__nr_RLF_Report_r16__ext1O__F2 RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1F2_cond  RLF_Report_r16__nr_RLF_Report_r16__ext1O__F1F2_cond2 RLF_Report_r16__nr_RLF_Report_r16__ext1O__F2F1_cond.
Opaque RLF_Report_r16__nr_RLF_Report_r16__ext1O__cond RLF_Report_r16__nr_RLF_Report_r16__ext1O__Format.

Definition RLF_Report_r16__nr_RLF_Report_r16__ext1__check_all_none (b : RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type) : bool :=
match b with 
  | make__RLF_Report_r16__nr_RLF_Report_r16__ext1O__Type None None None None None  => false 
  | _ => true 
 end.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext1__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__ext1__Type RLF_Report_r16__nr_RLF_Report_r16__ext1__cond :=
  restrict_add_format RLF_Report_r16__nr_RLF_Report_r16__ext1__check_all_none RLF_Report_r16__nr_RLF_Report_r16__ext1O__Format.

Opaque RLF_Report_r16__nr_RLF_Report_r16__ext1__cond RLF_Report_r16__nr_RLF_Report_r16__ext1__Format.


Definition RLF_Report_r16__nr_RLF_Report_r16__root_Format_Type := Eval cbn in seq_format_prod RLF_Report_r16__nr_RLF_Report_r16__root_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__root_Format_list : RLF_Report_r16__nr_RLF_Report_r16__root_Format_Type :=
  (MeasResultRLFNR_r16__Format, (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16__Format, (RNTI_Value__Format, (RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16__Format, (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16__Format, (RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16__Format, (TimeUntilReconnection_r16__Format, (CGI_Info_Logging_r16__Format, (RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16__Format, (TimeSinceFailure_r16__Format, (RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16__Format, (RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16__Format, (LocationInfo_r16__Format, (RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16__Format, (RA_InformationCommon_r16__Format, unit_format))))))))))))))).

Definition RLF_Report_r16__nr_RLF_Report_r16__ext_Format_Type := Eval cbn in get_formats RLF_Report_r16__nr_RLF_Report_r16__ext_list.
Definition RLF_Report_r16__nr_RLF_Report_r16__ext_Format_list : RLF_Report_r16__nr_RLF_Report_r16__ext_Format_Type :=
  (RLF_Report_r16__nr_RLF_Report_r16__ext0__Format, (RLF_Report_r16__nr_RLF_Report_r16__ext1__Format, unit__Format)).

Definition RLF_Report_r16__nr_RLF_Report_r16__list_type : Set := (seq_type RLF_Report_r16__nr_RLF_Report_r16__root_list) * (seq_ext_type RLF_Report_r16__nr_RLF_Report_r16__ext_list).
Definition RLF_Report_r16__nr_RLF_Report_r16__list_cond (z : RLF_Report_r16__nr_RLF_Report_r16__list_type) : Prop :=
        (seq_cond RLF_Report_r16__nr_RLF_Report_r16__root_list (fst z)) /\ (seq_ext_cond RLF_Report_r16__nr_RLF_Report_r16__ext_list (snd z)).
Definition RLF_Report_r16__nr_RLF_Report_r16__list_format : T_Format RLF_Report_r16__nr_RLF_Report_r16__list_type RLF_Report_r16__nr_RLF_Report_r16__list_cond :=
 (* Eval compute in *) seq_ext_format RLF_Report_r16__nr_RLF_Report_r16__root_list RLF_Report_r16__nr_RLF_Report_r16__root_Format_list RLF_Report_r16__nr_RLF_Report_r16__ext_list RLF_Report_r16__nr_RLF_Report_r16__ext_Format_list.

Opaque RLF_Report_r16__nr_RLF_Report_r16__list_format.
Definition RLF_Report_r16__nr_RLF_Report_r16__F1 (z : RLF_Report_r16__nr_RLF_Report_r16__Type) : RLF_Report_r16__nr_RLF_Report_r16__list_type :=
  (((RLF_Report_r16__nr_RLF_Report_r16__measResultLastServCell_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__measResultNeighCells_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__c_RNTI_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__previousPCellId_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__failedPCellId_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__reconnectCellId_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__timeUntilReconnection_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__reestablishmentCellId_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__timeConnFailure_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__timeSinceFailure_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__connectionFailureType_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__rlf_Cause_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__locationInfo_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__noSuitableCellFound_r16 z, (RLF_Report_r16__nr_RLF_Report_r16__ra_InformationCommon_r16 z, tt)))))))))))))))), (
(RLF_Report_r16__nr_RLF_Report_r16__ext0 z, (RLF_Report_r16__nr_RLF_Report_r16__ext1 z, tt)))).
Definition RLF_Report_r16__nr_RLF_Report_r16__F2 (y : RLF_Report_r16__nr_RLF_Report_r16__list_type) : RLF_Report_r16__nr_RLF_Report_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, _))))))))))))))), (i0, (i1, _)))=>
    make__RLF_Report_r16__nr_RLF_Report_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 i0 i1
  end.
Definition RLF_Report_r16__nr_RLF_Report_r16__helper1 : (forall a : RLF_Report_r16__nr_RLF_Report_r16__Type, RLF_Report_r16__nr_RLF_Report_r16__cond a -> RLF_Report_r16__nr_RLF_Report_r16__list_cond (RLF_Report_r16__nr_RLF_Report_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__helper2 : (forall a : RLF_Report_r16__nr_RLF_Report_r16__Type, RLF_Report_r16__nr_RLF_Report_r16__F2 (RLF_Report_r16__nr_RLF_Report_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__helper3 : (forall b : RLF_Report_r16__nr_RLF_Report_r16__list_type, RLF_Report_r16__nr_RLF_Report_r16__list_cond b -> RLF_Report_r16__nr_RLF_Report_r16__cond (RLF_Report_r16__nr_RLF_Report_r16__F2 b) /\ RLF_Report_r16__nr_RLF_Report_r16__F1 (RLF_Report_r16__nr_RLF_Report_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RLF_Report_r16__nr_RLF_Report_r16__cond, RLF_Report_r16__nr_RLF_Report_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RLF_Report_r16__nr_RLF_Report_r16__Format : T_Format RLF_Report_r16__nr_RLF_Report_r16__Type RLF_Report_r16__nr_RLF_Report_r16__cond :=
 proj2_format RLF_Report_r16__nr_RLF_Report_r16__cond RLF_Report_r16__nr_RLF_Report_r16__list_format  RLF_Report_r16__nr_RLF_Report_r16__F1 RLF_Report_r16__nr_RLF_Report_r16__F2 RLF_Report_r16__nr_RLF_Report_r16__helper1 RLF_Report_r16__nr_RLF_Report_r16__helper2 RLF_Report_r16__nr_RLF_Report_r16__helper3.

Opaque RLF_Report_r16__nr_RLF_Report_r16__cond RLF_Report_r16__nr_RLF_Report_r16__Format.


Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format_Type := Eval cbn in seq_format_prod RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list.
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format_list : RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format_Type :=
  (octet_string_nc__Format, unit_format).
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list__Format := (*Eval compute in *) seq_format RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format_list.
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1 z :=
  (RLF_Report_r16__eutra_RLF_Report_r16__ext0O__measResult_RLF_Report_EUTRA_v1690 z, tt).
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F2 (y : seq_type RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type i0
  end.
Lemma RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1F2_cond (z : RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type)
  : RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond z ->
  (seq_cond RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list (RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1 z)).
intro H. unfold RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1F2_cond2 (z : RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type)
 : RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F2 (RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F2F1_cond (y : seq_type RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list)
  : seq_cond RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list y ->
 (RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond (RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F2 y)) /\  RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1 (RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format : T_Format RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond :=
        proj2_format  RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond RLF_Report_r16__eutra_RLF_Report_r16__ext0O__list__Format
    RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1 RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F2 RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1F2_cond  RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F1F2_cond2 RLF_Report_r16__eutra_RLF_Report_r16__ext0O__F2F1_cond.
Opaque RLF_Report_r16__eutra_RLF_Report_r16__ext0O__cond RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format.

Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0__check_all_none (b : RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type) : bool :=
match b with 
  | make__RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext0__Format : T_Format RLF_Report_r16__eutra_RLF_Report_r16__ext0__Type RLF_Report_r16__eutra_RLF_Report_r16__ext0__cond :=
  restrict_add_format RLF_Report_r16__eutra_RLF_Report_r16__ext0__check_all_none RLF_Report_r16__eutra_RLF_Report_r16__ext0O__Format.

Opaque RLF_Report_r16__eutra_RLF_Report_r16__ext0__cond RLF_Report_r16__eutra_RLF_Report_r16__ext0__Format.


Definition RLF_Report_r16__eutra_RLF_Report_r16__root_Format_Type := Eval cbn in seq_format_prod RLF_Report_r16__eutra_RLF_Report_r16__root_list.
Definition RLF_Report_r16__eutra_RLF_Report_r16__root_Format_list : RLF_Report_r16__eutra_RLF_Report_r16__root_Format_Type :=
  (CGI_InfoEUTRALogging__Format, (octet_string_nc__Format, unit_format)).

Definition RLF_Report_r16__eutra_RLF_Report_r16__ext_Format_Type := Eval cbn in get_formats RLF_Report_r16__eutra_RLF_Report_r16__ext_list.
Definition RLF_Report_r16__eutra_RLF_Report_r16__ext_Format_list : RLF_Report_r16__eutra_RLF_Report_r16__ext_Format_Type :=
  (RLF_Report_r16__eutra_RLF_Report_r16__ext0__Format, unit__Format).

Definition RLF_Report_r16__eutra_RLF_Report_r16__list_type : Set := (seq_type RLF_Report_r16__eutra_RLF_Report_r16__root_list) * (seq_ext_type RLF_Report_r16__eutra_RLF_Report_r16__ext_list).
Definition RLF_Report_r16__eutra_RLF_Report_r16__list_cond (z : RLF_Report_r16__eutra_RLF_Report_r16__list_type) : Prop :=
        (seq_cond RLF_Report_r16__eutra_RLF_Report_r16__root_list (fst z)) /\ (seq_ext_cond RLF_Report_r16__eutra_RLF_Report_r16__ext_list (snd z)).
Definition RLF_Report_r16__eutra_RLF_Report_r16__list_format : T_Format RLF_Report_r16__eutra_RLF_Report_r16__list_type RLF_Report_r16__eutra_RLF_Report_r16__list_cond :=
 (* Eval compute in *) seq_ext_format RLF_Report_r16__eutra_RLF_Report_r16__root_list RLF_Report_r16__eutra_RLF_Report_r16__root_Format_list RLF_Report_r16__eutra_RLF_Report_r16__ext_list RLF_Report_r16__eutra_RLF_Report_r16__ext_Format_list.

Opaque RLF_Report_r16__eutra_RLF_Report_r16__list_format.
Definition RLF_Report_r16__eutra_RLF_Report_r16__F1 (z : RLF_Report_r16__eutra_RLF_Report_r16__Type) : RLF_Report_r16__eutra_RLF_Report_r16__list_type :=
  (((RLF_Report_r16__eutra_RLF_Report_r16__failedPCellId_EUTRA z, (RLF_Report_r16__eutra_RLF_Report_r16__measResult_RLF_Report_EUTRA_r16 z, tt))), (
(RLF_Report_r16__eutra_RLF_Report_r16__ext0 z, tt))).
Definition RLF_Report_r16__eutra_RLF_Report_r16__F2 (y : RLF_Report_r16__eutra_RLF_Report_r16__list_type) : RLF_Report_r16__eutra_RLF_Report_r16__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__RLF_Report_r16__eutra_RLF_Report_r16__Type j0 j1 i0
  end.
Definition RLF_Report_r16__eutra_RLF_Report_r16__helper1 : (forall a : RLF_Report_r16__eutra_RLF_Report_r16__Type, RLF_Report_r16__eutra_RLF_Report_r16__cond a -> RLF_Report_r16__eutra_RLF_Report_r16__list_cond (RLF_Report_r16__eutra_RLF_Report_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RLF_Report_r16__eutra_RLF_Report_r16__helper2 : (forall a : RLF_Report_r16__eutra_RLF_Report_r16__Type, RLF_Report_r16__eutra_RLF_Report_r16__F2 (RLF_Report_r16__eutra_RLF_Report_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RLF_Report_r16__eutra_RLF_Report_r16__helper3 : (forall b : RLF_Report_r16__eutra_RLF_Report_r16__list_type, RLF_Report_r16__eutra_RLF_Report_r16__list_cond b -> RLF_Report_r16__eutra_RLF_Report_r16__cond (RLF_Report_r16__eutra_RLF_Report_r16__F2 b) /\ RLF_Report_r16__eutra_RLF_Report_r16__F1 (RLF_Report_r16__eutra_RLF_Report_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RLF_Report_r16__eutra_RLF_Report_r16__cond, RLF_Report_r16__eutra_RLF_Report_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RLF_Report_r16__eutra_RLF_Report_r16__Format : T_Format RLF_Report_r16__eutra_RLF_Report_r16__Type RLF_Report_r16__eutra_RLF_Report_r16__cond :=
 proj2_format RLF_Report_r16__eutra_RLF_Report_r16__cond RLF_Report_r16__eutra_RLF_Report_r16__list_format  RLF_Report_r16__eutra_RLF_Report_r16__F1 RLF_Report_r16__eutra_RLF_Report_r16__F2 RLF_Report_r16__eutra_RLF_Report_r16__helper1 RLF_Report_r16__eutra_RLF_Report_r16__helper2 RLF_Report_r16__eutra_RLF_Report_r16__helper3.

Opaque RLF_Report_r16__eutra_RLF_Report_r16__cond RLF_Report_r16__eutra_RLF_Report_r16__Format.


Definition RLF_Report_r16__Format_Type := Eval cbn in get_formats RLF_Report_r16__list.
Definition RLF_Report_r16__Format_list : RLF_Report_r16__Format_Type :=
  (RLF_Report_r16__nr_RLF_Report_r16__Format, (RLF_Report_r16__eutra_RLF_Report_r16__Format, unit__Format)).
Definition RLF_Report_r16__list__Format := Eval compute in choice_format RLF_Report_r16__list RLF_Report_r16__len_helper1 RLF_Report_r16__len_helper2  RLF_Report_r16__Format_list.
Definition RLF_Report_r16__F1 (z : RLF_Report_r16__Type) : (choice RLF_Report_r16__list) :=
  match z with
   | RLF_Report_r16__nr_RLF_Report_r16 t => existT _ 0 t
  | RLF_Report_r16__eutra_RLF_Report_r16 t => existT _ 1 t
  end.
Definition RLF_Report_r16__g := (fun n => typ_set (get_nth_typ RLF_Report_r16__list n)).
Definition RLF_Report_r16__F2 (y : choice RLF_Report_r16__list) : RLF_Report_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RLF_Report_r16__g n -> RLF_Report_r16__Type) with
    | 0 => fun (t : RLF_Report_r16__nr_RLF_Report_r16__Type) => RLF_Report_r16__nr_RLF_Report_r16 t 
    | 1 => fun (t : RLF_Report_r16__eutra_RLF_Report_r16__Type) => RLF_Report_r16__eutra_RLF_Report_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RLF_Report_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RLF_Report_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RLF_Report_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RLF_Report_r16__Type with end) n0
           end t0).

Lemma RLF_Report_r16__helper2 :  forall (y : RLF_Report_r16__Type), RLF_Report_r16__cond y -> choice_cond RLF_Report_r16__list (RLF_Report_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RLF_Report_r16__helper3 :  forall (y : RLF_Report_r16__Type), RLF_Report_r16__F2 (RLF_Report_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RLF_Report_r16__helper4 : (forall b : choice RLF_Report_r16__list, choice_cond RLF_Report_r16__list b -> RLF_Report_r16__cond (RLF_Report_r16__F2 b) /\ RLF_Report_r16__F1 (RLF_Report_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RLF_Report_r16__F1 RLF_Report_r16__F2.
Definition RLF_Report_r16__Format : T_Format RLF_Report_r16__Type RLF_Report_r16__cond :=
  (* Eval compute in *) proj2_format RLF_Report_r16__cond RLF_Report_r16__list__Format RLF_Report_r16__F1 RLF_Report_r16__F2 RLF_Report_r16__helper2 RLF_Report_r16__helper3 RLF_Report_r16__helper4.
Opaque RLF_Report_r16__cond RLF_Report_r16__Format.

