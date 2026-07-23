Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Type : Set :=
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n4
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n8
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n16
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n32
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n64
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n128
.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__cond := (fun (_ : MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Type) => True).
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__nat__helper.

Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F1 t :=
  match t with
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n4 => 0
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n8 => 1
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n16 => 2
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n32 => 3
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n64 => 4
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n128 => 5
  end.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n4
  | 1 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n8
  | 2 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n16
  | 3 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n32
  | 4 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n64
  | 5 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n128
  | _ => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__n4
  end.
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F1F2 : forall x : MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Type, (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F1 x <= 5) /\ MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F2 (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F2F1 : forall (y : nat) (H : y <= 5), MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F1 (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Type : Set :=
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n1
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n2
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n4
 | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n8
.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__cond := (fun (_ : MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Type) => True).
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__nat__helper.

Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F1 t :=
  match t with
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n1 => 0
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n2 => 1
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n4 => 2
  | MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n8 => 3
  end.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n1
  | 1 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n2
  | 2 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n4
  | 3 => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n8
  | _ => MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__n1
  end.
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F1F2 : forall x : MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Type, (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F1 x <= 3) /\ MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F2 (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F1 (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__tci_StatePDSCH__Type : Set :=
  make__MIMO_ParametersPerBand__tci_StatePDSCH__Type {
    MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC : option MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Type ;
    MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP : option MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Type ;
}.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__list := (
 Opt MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Type MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__cond ::
 Opt MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Type MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__cond ::
 nil).
Definition MIMO_ParametersPerBand__tci_StatePDSCH__cond z := 
  opt_cond MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__cond (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC z) /\
  opt_cond MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__cond (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP z) /\
  True.

Inductive MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Type : Set :=
 | MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__supported
.
Definition MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__cond := (fun (_ : MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Type) => True).
Lemma MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__nat__helper.

Definition MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F1 t :=
  match t with
  | MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__supported => 0
  end.
Definition MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__supported
  | _ => MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__supported
  end.
Lemma MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F1F2 : forall x : MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Type, (MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F1 x <= 0) /\ MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F2 (MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F1 (MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__pusch_TransCoherence__Type : Set :=
 | MIMO_ParametersPerBand__pusch_TransCoherence__nonCoherent
 | MIMO_ParametersPerBand__pusch_TransCoherence__partialCoherent
 | MIMO_ParametersPerBand__pusch_TransCoherence__fullCoherent
.
Definition MIMO_ParametersPerBand__pusch_TransCoherence__cond := (fun (_ : MIMO_ParametersPerBand__pusch_TransCoherence__Type) => True).
Lemma MIMO_ParametersPerBand__pusch_TransCoherence__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__pusch_TransCoherence__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__pusch_TransCoherence__nat__helper.

Definition MIMO_ParametersPerBand__pusch_TransCoherence__F1 t :=
  match t with
  | MIMO_ParametersPerBand__pusch_TransCoherence__nonCoherent => 0
  | MIMO_ParametersPerBand__pusch_TransCoherence__partialCoherent => 1
  | MIMO_ParametersPerBand__pusch_TransCoherence__fullCoherent => 2
  end.
Definition MIMO_ParametersPerBand__pusch_TransCoherence__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__pusch_TransCoherence__nonCoherent
  | 1 => MIMO_ParametersPerBand__pusch_TransCoherence__partialCoherent
  | 2 => MIMO_ParametersPerBand__pusch_TransCoherence__fullCoherent
  | _ => MIMO_ParametersPerBand__pusch_TransCoherence__nonCoherent
  end.
Lemma MIMO_ParametersPerBand__pusch_TransCoherence__F1F2 : forall x : MIMO_ParametersPerBand__pusch_TransCoherence__Type, (MIMO_ParametersPerBand__pusch_TransCoherence__F1 x <= 2) /\ MIMO_ParametersPerBand__pusch_TransCoherence__F2 (MIMO_ParametersPerBand__pusch_TransCoherence__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__pusch_TransCoherence__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__pusch_TransCoherence__F1 (MIMO_ParametersPerBand__pusch_TransCoherence__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Type : Set :=
 | MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__supported
.
Definition MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__cond := (fun (_ : MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Type) => True).
Lemma MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__nat__helper.

Definition MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F1 t :=
  match t with
  | MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__supported => 0
  end.
Definition MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__supported
  | _ => MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__supported
  end.
Lemma MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F1F2 : forall x : MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Type, (MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F1 x <= 0) /\ MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F2 (MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F1 (MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__periodicBeamReport__Type : Set :=
 | MIMO_ParametersPerBand__periodicBeamReport__supported
.
Definition MIMO_ParametersPerBand__periodicBeamReport__cond := (fun (_ : MIMO_ParametersPerBand__periodicBeamReport__Type) => True).
Lemma MIMO_ParametersPerBand__periodicBeamReport__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__periodicBeamReport__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__periodicBeamReport__nat__helper.

Definition MIMO_ParametersPerBand__periodicBeamReport__F1 t :=
  match t with
  | MIMO_ParametersPerBand__periodicBeamReport__supported => 0
  end.
Definition MIMO_ParametersPerBand__periodicBeamReport__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__periodicBeamReport__supported
  | _ => MIMO_ParametersPerBand__periodicBeamReport__supported
  end.
Lemma MIMO_ParametersPerBand__periodicBeamReport__F1F2 : forall x : MIMO_ParametersPerBand__periodicBeamReport__Type, (MIMO_ParametersPerBand__periodicBeamReport__F1 x <= 0) /\ MIMO_ParametersPerBand__periodicBeamReport__F2 (MIMO_ParametersPerBand__periodicBeamReport__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__periodicBeamReport__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__periodicBeamReport__F1 (MIMO_ParametersPerBand__periodicBeamReport__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__aperiodicBeamReport__Type : Set :=
 | MIMO_ParametersPerBand__aperiodicBeamReport__supported
.
Definition MIMO_ParametersPerBand__aperiodicBeamReport__cond := (fun (_ : MIMO_ParametersPerBand__aperiodicBeamReport__Type) => True).
Lemma MIMO_ParametersPerBand__aperiodicBeamReport__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__aperiodicBeamReport__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__aperiodicBeamReport__nat__helper.

Definition MIMO_ParametersPerBand__aperiodicBeamReport__F1 t :=
  match t with
  | MIMO_ParametersPerBand__aperiodicBeamReport__supported => 0
  end.
Definition MIMO_ParametersPerBand__aperiodicBeamReport__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__aperiodicBeamReport__supported
  | _ => MIMO_ParametersPerBand__aperiodicBeamReport__supported
  end.
Lemma MIMO_ParametersPerBand__aperiodicBeamReport__F1F2 : forall x : MIMO_ParametersPerBand__aperiodicBeamReport__Type, (MIMO_ParametersPerBand__aperiodicBeamReport__F1 x <= 0) /\ MIMO_ParametersPerBand__aperiodicBeamReport__F2 (MIMO_ParametersPerBand__aperiodicBeamReport__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__aperiodicBeamReport__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__aperiodicBeamReport__F1 (MIMO_ParametersPerBand__aperiodicBeamReport__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__sp_BeamReportPUCCH__Type : Set :=
 | MIMO_ParametersPerBand__sp_BeamReportPUCCH__supported
.
Definition MIMO_ParametersPerBand__sp_BeamReportPUCCH__cond := (fun (_ : MIMO_ParametersPerBand__sp_BeamReportPUCCH__Type) => True).
Lemma MIMO_ParametersPerBand__sp_BeamReportPUCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__sp_BeamReportPUCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__sp_BeamReportPUCCH__nat__helper.

Definition MIMO_ParametersPerBand__sp_BeamReportPUCCH__F1 t :=
  match t with
  | MIMO_ParametersPerBand__sp_BeamReportPUCCH__supported => 0
  end.
Definition MIMO_ParametersPerBand__sp_BeamReportPUCCH__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__sp_BeamReportPUCCH__supported
  | _ => MIMO_ParametersPerBand__sp_BeamReportPUCCH__supported
  end.
Lemma MIMO_ParametersPerBand__sp_BeamReportPUCCH__F1F2 : forall x : MIMO_ParametersPerBand__sp_BeamReportPUCCH__Type, (MIMO_ParametersPerBand__sp_BeamReportPUCCH__F1 x <= 0) /\ MIMO_ParametersPerBand__sp_BeamReportPUCCH__F2 (MIMO_ParametersPerBand__sp_BeamReportPUCCH__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__sp_BeamReportPUCCH__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__sp_BeamReportPUCCH__F1 (MIMO_ParametersPerBand__sp_BeamReportPUCCH__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__sp_BeamReportPUSCH__Type : Set :=
 | MIMO_ParametersPerBand__sp_BeamReportPUSCH__supported
.
Definition MIMO_ParametersPerBand__sp_BeamReportPUSCH__cond := (fun (_ : MIMO_ParametersPerBand__sp_BeamReportPUSCH__Type) => True).
Lemma MIMO_ParametersPerBand__sp_BeamReportPUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__sp_BeamReportPUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__sp_BeamReportPUSCH__nat__helper.

Definition MIMO_ParametersPerBand__sp_BeamReportPUSCH__F1 t :=
  match t with
  | MIMO_ParametersPerBand__sp_BeamReportPUSCH__supported => 0
  end.
Definition MIMO_ParametersPerBand__sp_BeamReportPUSCH__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__sp_BeamReportPUSCH__supported
  | _ => MIMO_ParametersPerBand__sp_BeamReportPUSCH__supported
  end.
Lemma MIMO_ParametersPerBand__sp_BeamReportPUSCH__F1F2 : forall x : MIMO_ParametersPerBand__sp_BeamReportPUSCH__Type, (MIMO_ParametersPerBand__sp_BeamReportPUSCH__F1 x <= 0) /\ MIMO_ParametersPerBand__sp_BeamReportPUSCH__F2 (MIMO_ParametersPerBand__sp_BeamReportPUSCH__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__sp_BeamReportPUSCH__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__sp_BeamReportPUSCH__F1 (MIMO_ParametersPerBand__sp_BeamReportPUSCH__F2 y) = y. enum_solve H y. Qed.

Require Import NR.DummyG.

Opaque DummyG__cond DummyG__Format.

Lemma MIMO_ParametersPerBand__maxNumberRxBeam__helper1 : (2 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__maxNumberRxBeam__helper2 : to_bit_sz (Z.to_nat (8 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__maxNumberRxBeam__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__maxNumberRxBeam__Type := Z.
Definition MIMO_ParametersPerBand__maxNumberRxBeam__cond := (fun z => (2 <= z <= 8)%Z).
Inductive MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Type : Set :=
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n4
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n7
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n14
.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__cond := (fun (_ : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Type) => True).
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__nat__helper.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n4 => 0
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n7 => 1
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n14 => 2
  end.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n4
  | 1 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n7
  | 2 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n14
  | _ => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__n4
  end.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F1F2 : forall x : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Type, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F1 x <= 2) /\ MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F2 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F1 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Type : Set :=
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n4
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n7
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n14
.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__cond := (fun (_ : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Type) => True).
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__nat__helper.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n4 => 0
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n7 => 1
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n14 => 2
  end.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n4
  | 1 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n7
  | 2 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n14
  | _ => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__n4
  end.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F1F2 : forall x : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Type, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F1 x <= 2) /\ MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F2 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F1 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Type : Set :=
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n4
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n7
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n14
.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__cond := (fun (_ : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Type) => True).
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__nat__helper.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n4 => 0
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n7 => 1
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n14 => 2
  end.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n4
  | 1 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n7
  | 2 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n14
  | _ => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__n4
  end.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F1F2 : forall x : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Type, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F1 x <= 2) /\ MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F2 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F1 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Type : Set :=
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n4
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n7
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n14
.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__cond := (fun (_ : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Type) => True).
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__nat__helper.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n4 => 0
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n7 => 1
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n14 => 2
  end.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n4
  | 1 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n7
  | 2 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n14
  | _ => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__n4
  end.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F1F2 : forall x : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Type, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F1 x <= 2) /\ MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F2 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F1 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Type : Set :=
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n4
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n7
 | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n14
.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__cond := (fun (_ : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Type) => True).
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__nat__helper.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n4 => 0
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n7 => 1
  | MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n14 => 2
  end.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n4
  | 1 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n7
  | 2 => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n14
  | _ => MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__n4
  end.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F1F2 : forall x : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Type, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F1 x <= 2) /\ MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F2 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F1 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Type : Set :=
  make__MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Type {
    MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz : option MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Type ;
    MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz : option MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Type ;
    MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz : option MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Type ;
    MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz : option MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Type ;
    MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz : option MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Type ;
}.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list := (
 Opt MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__cond ::
 Opt MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__cond ::
 Opt MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__cond ::
 Opt MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__cond ::
 Opt MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__cond ::
 nil).
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond z := 
  opt_cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__cond (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__cond (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__cond (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__cond (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__cond (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz z) /\
  True.

Inductive MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Type : Set :=
 | MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n1
 | MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n2
 | MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n4
.
Definition MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__cond := (fun (_ : MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Type) => True).
Lemma MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__nat__helper.

Definition MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F1 t :=
  match t with
  | MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n1 => 0
  | MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n2 => 1
  | MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n4 => 2
  end.
Definition MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n1
  | 1 => MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n2
  | 2 => MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n4
  | _ => MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__n1
  end.
Lemma MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F1F2 : forall x : MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Type, (MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F1 x <= 2) /\ MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F2 (MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F1 (MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__groupBeamReporting__Type : Set :=
 | MIMO_ParametersPerBand__groupBeamReporting__supported
.
Definition MIMO_ParametersPerBand__groupBeamReporting__cond := (fun (_ : MIMO_ParametersPerBand__groupBeamReporting__Type) => True).
Lemma MIMO_ParametersPerBand__groupBeamReporting__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__groupBeamReporting__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__groupBeamReporting__nat__helper.

Definition MIMO_ParametersPerBand__groupBeamReporting__F1 t :=
  match t with
  | MIMO_ParametersPerBand__groupBeamReporting__supported => 0
  end.
Definition MIMO_ParametersPerBand__groupBeamReporting__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__groupBeamReporting__supported
  | _ => MIMO_ParametersPerBand__groupBeamReporting__supported
  end.
Lemma MIMO_ParametersPerBand__groupBeamReporting__F1F2 : forall x : MIMO_ParametersPerBand__groupBeamReporting__Type, (MIMO_ParametersPerBand__groupBeamReporting__F1 x <= 0) /\ MIMO_ParametersPerBand__groupBeamReporting__F2 (MIMO_ParametersPerBand__groupBeamReporting__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__groupBeamReporting__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__groupBeamReporting__F1 (MIMO_ParametersPerBand__groupBeamReporting__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Type : Set :=
 | MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n2
 | MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n4
 | MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n8
 | MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n16
.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__cond := (fun (_ : MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Type) => True).
Lemma MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__nat__helper.

Definition MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F1 t :=
  match t with
  | MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n2 => 0
  | MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n4 => 1
  | MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n8 => 2
  | MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n16 => 3
  end.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n2
  | 1 => MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n4
  | 2 => MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n8
  | 3 => MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n16
  | _ => MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__n2
  end.
Lemma MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F1F2 : forall x : MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Type, (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F1 x <= 3) /\ MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F2 (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F1 (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__Type := Z.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__cond := (fun z => (1 <= z <= 8)%Z).
Record MIMO_ParametersPerBand__uplinkBeamManagement__Type : Set :=
  make__MIMO_ParametersPerBand__uplinkBeamManagement__Type {
    MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM : MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Type ;
    MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet : Z ;
}.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__list := (
 Nor MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Type MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__cond ::
 Nor Z MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__cond ::
 nil).
Definition MIMO_ParametersPerBand__uplinkBeamManagement__cond z := 
  MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__cond (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM z) /\
  MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__cond (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet z) /\
  True.

Lemma MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__Type := Z.
Definition MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__cond := (fun z => (1 <= z <= 64)%Z).
Lemma MIMO_ParametersPerBand__maxNumberSSB_BFD__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__maxNumberSSB_BFD__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__maxNumberSSB_BFD__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__maxNumberSSB_BFD__Type := Z.
Definition MIMO_ParametersPerBand__maxNumberSSB_BFD__cond := (fun z => (1 <= z <= 64)%Z).
Lemma MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__helper1 : (1 <= 256)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__helper2 : to_bit_sz (Z.to_nat (256 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__Type := Z.
Definition MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__cond := (fun z => (1 <= z <= 256)%Z).
Inductive MIMO_ParametersPerBand__dummy2__Type : Set :=
 | MIMO_ParametersPerBand__dummy2__supported
.
Definition MIMO_ParametersPerBand__dummy2__cond := (fun (_ : MIMO_ParametersPerBand__dummy2__Type) => True).
Lemma MIMO_ParametersPerBand__dummy2__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__dummy2__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__dummy2__nat__helper.

Definition MIMO_ParametersPerBand__dummy2__F1 t :=
  match t with
  | MIMO_ParametersPerBand__dummy2__supported => 0
  end.
Definition MIMO_ParametersPerBand__dummy2__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__dummy2__supported
  | _ => MIMO_ParametersPerBand__dummy2__supported
  end.
Lemma MIMO_ParametersPerBand__dummy2__F1F2 : forall x : MIMO_ParametersPerBand__dummy2__Type, (MIMO_ParametersPerBand__dummy2__F1 x <= 0) /\ MIMO_ParametersPerBand__dummy2__F2 (MIMO_ParametersPerBand__dummy2__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__dummy2__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__dummy2__F1 (MIMO_ParametersPerBand__dummy2__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__twoPortsPTRS_UL__Type : Set :=
 | MIMO_ParametersPerBand__twoPortsPTRS_UL__supported
.
Definition MIMO_ParametersPerBand__twoPortsPTRS_UL__cond := (fun (_ : MIMO_ParametersPerBand__twoPortsPTRS_UL__Type) => True).
Lemma MIMO_ParametersPerBand__twoPortsPTRS_UL__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__twoPortsPTRS_UL__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__twoPortsPTRS_UL__nat__helper.

Definition MIMO_ParametersPerBand__twoPortsPTRS_UL__F1 t :=
  match t with
  | MIMO_ParametersPerBand__twoPortsPTRS_UL__supported => 0
  end.
Definition MIMO_ParametersPerBand__twoPortsPTRS_UL__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__twoPortsPTRS_UL__supported
  | _ => MIMO_ParametersPerBand__twoPortsPTRS_UL__supported
  end.
Lemma MIMO_ParametersPerBand__twoPortsPTRS_UL__F1F2 : forall x : MIMO_ParametersPerBand__twoPortsPTRS_UL__Type, (MIMO_ParametersPerBand__twoPortsPTRS_UL__F1 x <= 0) /\ MIMO_ParametersPerBand__twoPortsPTRS_UL__F2 (MIMO_ParametersPerBand__twoPortsPTRS_UL__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__twoPortsPTRS_UL__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__twoPortsPTRS_UL__F1 (MIMO_ParametersPerBand__twoPortsPTRS_UL__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SRS_Resources.

Opaque SRS_Resources__cond SRS_Resources__Format.

Lemma MIMO_ParametersPerBand__dummy3__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__dummy3__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__dummy3__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__dummy3__Type := Z.
Definition MIMO_ParametersPerBand__dummy3__cond := (fun z => (1 <= z <= 4)%Z).
Inductive MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Type : Set :=
 | MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym2
 | MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym4
 | MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym8
.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__cond := (fun (_ : MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Type) => True).
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__nat__helper.

Definition MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym2 => 0
  | MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym4 => 1
  | MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym8 => 2
  end.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym2
  | 1 => MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym4
  | 2 => MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym8
  | _ => MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__sym2
  end.
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F1F2 : forall x : MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Type, (MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F1 x <= 2) /\ MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F2 (MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F1 (MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Type : Set :=
 | MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym4
 | MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym8
 | MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym14
 | MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym28
.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__cond := (fun (_ : MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Type) => True).
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__nat__helper.

Definition MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym4 => 0
  | MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym8 => 1
  | MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym14 => 2
  | MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym28 => 3
  end.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym4
  | 1 => MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym8
  | 2 => MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym14
  | 3 => MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym28
  | _ => MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__sym4
  end.
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F1F2 : forall x : MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Type, (MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F1 x <= 3) /\ MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F2 (MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F1 (MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Type : Set :=
 | MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym8
 | MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym14
 | MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym28
.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__cond := (fun (_ : MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Type) => True).
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__nat__helper.

Definition MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym8 => 0
  | MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym14 => 1
  | MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym28 => 2
  end.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym8
  | 1 => MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym14
  | 2 => MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym28
  | _ => MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__sym8
  end.
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F1F2 : forall x : MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Type, (MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F1 x <= 2) /\ MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F2 (MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F1 (MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Type : Set :=
 | MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym14
 | MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym28
 | MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym56
.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__cond := (fun (_ : MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Type) => True).
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__nat__helper.

Definition MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym14 => 0
  | MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym28 => 1
  | MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym56 => 2
  end.
Definition MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym14
  | 1 => MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym28
  | 2 => MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym56
  | _ => MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__sym14
  end.
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F1F2 : forall x : MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Type, (MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F1 x <= 2) /\ MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F2 (MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F1 (MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__beamReportTiming__Type : Set :=
  make__MIMO_ParametersPerBand__beamReportTiming__Type {
    MIMO_ParametersPerBand__beamReportTiming__scs_15kHz : option MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Type ;
    MIMO_ParametersPerBand__beamReportTiming__scs_30kHz : option MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Type ;
    MIMO_ParametersPerBand__beamReportTiming__scs_60kHz : option MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Type ;
    MIMO_ParametersPerBand__beamReportTiming__scs_120kHz : option MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Type ;
}.
Definition MIMO_ParametersPerBand__beamReportTiming__list := (
 Opt MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Type MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__cond ::
 Opt MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Type MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__cond ::
 Opt MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Type MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__cond ::
 Opt MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Type MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__cond ::
 nil).
Definition MIMO_ParametersPerBand__beamReportTiming__cond z := 
  opt_cond MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__cond (MIMO_ParametersPerBand__beamReportTiming__scs_15kHz z) /\
  opt_cond MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__cond (MIMO_ParametersPerBand__beamReportTiming__scs_30kHz z) /\
  opt_cond MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__cond (MIMO_ParametersPerBand__beamReportTiming__scs_60kHz z) /\
  opt_cond MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__cond (MIMO_ParametersPerBand__beamReportTiming__scs_120kHz z) /\
  True.

Require Import NR.PTRS_DensityRecommendationDL.

Opaque PTRS_DensityRecommendationDL__cond PTRS_DensityRecommendationDL__Format.

Require Import NR.PTRS_DensityRecommendationDL.

Opaque PTRS_DensityRecommendationDL__cond PTRS_DensityRecommendationDL__Format.

Require Import NR.PTRS_DensityRecommendationDL.

Opaque PTRS_DensityRecommendationDL__cond PTRS_DensityRecommendationDL__Format.

Require Import NR.PTRS_DensityRecommendationDL.

Opaque PTRS_DensityRecommendationDL__cond PTRS_DensityRecommendationDL__Format.

Record MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Type : Set :=
  make__MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Type {
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_15kHz : option PTRS_DensityRecommendationDL__Type ;
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_30kHz : option PTRS_DensityRecommendationDL__Type ;
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_60kHz : option PTRS_DensityRecommendationDL__Type ;
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_120kHz : option PTRS_DensityRecommendationDL__Type ;
}.
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list := (
 Opt PTRS_DensityRecommendationDL__Type PTRS_DensityRecommendationDL__cond ::
 Opt PTRS_DensityRecommendationDL__Type PTRS_DensityRecommendationDL__cond ::
 Opt PTRS_DensityRecommendationDL__Type PTRS_DensityRecommendationDL__cond ::
 Opt PTRS_DensityRecommendationDL__Type PTRS_DensityRecommendationDL__cond ::
 nil).
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond z := 
  opt_cond PTRS_DensityRecommendationDL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_15kHz z) /\
  opt_cond PTRS_DensityRecommendationDL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_30kHz z) /\
  opt_cond PTRS_DensityRecommendationDL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_60kHz z) /\
  opt_cond PTRS_DensityRecommendationDL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_120kHz z) /\
  True.

Require Import NR.PTRS_DensityRecommendationUL.

Opaque PTRS_DensityRecommendationUL__cond PTRS_DensityRecommendationUL__Format.

Require Import NR.PTRS_DensityRecommendationUL.

Opaque PTRS_DensityRecommendationUL__cond PTRS_DensityRecommendationUL__Format.

Require Import NR.PTRS_DensityRecommendationUL.

Opaque PTRS_DensityRecommendationUL__cond PTRS_DensityRecommendationUL__Format.

Require Import NR.PTRS_DensityRecommendationUL.

Opaque PTRS_DensityRecommendationUL__cond PTRS_DensityRecommendationUL__Format.

Record MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Type : Set :=
  make__MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Type {
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_15kHz : option PTRS_DensityRecommendationUL__Type ;
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_30kHz : option PTRS_DensityRecommendationUL__Type ;
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_60kHz : option PTRS_DensityRecommendationUL__Type ;
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_120kHz : option PTRS_DensityRecommendationUL__Type ;
}.
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list := (
 Opt PTRS_DensityRecommendationUL__Type PTRS_DensityRecommendationUL__cond ::
 Opt PTRS_DensityRecommendationUL__Type PTRS_DensityRecommendationUL__cond ::
 Opt PTRS_DensityRecommendationUL__Type PTRS_DensityRecommendationUL__cond ::
 Opt PTRS_DensityRecommendationUL__Type PTRS_DensityRecommendationUL__cond ::
 nil).
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond z := 
  opt_cond PTRS_DensityRecommendationUL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_15kHz z) /\
  opt_cond PTRS_DensityRecommendationUL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_30kHz z) /\
  opt_cond PTRS_DensityRecommendationUL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_60kHz z) /\
  opt_cond PTRS_DensityRecommendationUL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_120kHz z) /\
  True.

Require Import NR.DummyH.

Opaque DummyH__cond DummyH__Format.

Inductive MIMO_ParametersPerBand__aperiodicTRS__Type : Set :=
 | MIMO_ParametersPerBand__aperiodicTRS__supported
.
Definition MIMO_ParametersPerBand__aperiodicTRS__cond := (fun (_ : MIMO_ParametersPerBand__aperiodicTRS__Type) => True).
Lemma MIMO_ParametersPerBand__aperiodicTRS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__aperiodicTRS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__aperiodicTRS__nat__helper.

Definition MIMO_ParametersPerBand__aperiodicTRS__F1 t :=
  match t with
  | MIMO_ParametersPerBand__aperiodicTRS__supported => 0
  end.
Definition MIMO_ParametersPerBand__aperiodicTRS__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__aperiodicTRS__supported
  | _ => MIMO_ParametersPerBand__aperiodicTRS__supported
  end.
Lemma MIMO_ParametersPerBand__aperiodicTRS__F1F2 : forall x : MIMO_ParametersPerBand__aperiodicTRS__Type, (MIMO_ParametersPerBand__aperiodicTRS__F1 x <= 0) /\ MIMO_ParametersPerBand__aperiodicTRS__F2 (MIMO_ParametersPerBand__aperiodicTRS__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__aperiodicTRS__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__aperiodicTRS__F1 (MIMO_ParametersPerBand__aperiodicTRS__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext0O__dummy6__Type : Set :=
 | MIMO_ParametersPerBand__ext0O__dummy6__true
.
Definition MIMO_ParametersPerBand__ext0O__dummy6__cond := (fun (_ : MIMO_ParametersPerBand__ext0O__dummy6__Type) => True).
Lemma MIMO_ParametersPerBand__ext0O__dummy6__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext0O__dummy6__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext0O__dummy6__nat__helper.

Definition MIMO_ParametersPerBand__ext0O__dummy6__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext0O__dummy6__true => 0
  end.
Definition MIMO_ParametersPerBand__ext0O__dummy6__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext0O__dummy6__true
  | _ => MIMO_ParametersPerBand__ext0O__dummy6__true
  end.
Lemma MIMO_ParametersPerBand__ext0O__dummy6__F1F2 : forall x : MIMO_ParametersPerBand__ext0O__dummy6__Type, (MIMO_ParametersPerBand__ext0O__dummy6__F1 x <= 0) /\ MIMO_ParametersPerBand__ext0O__dummy6__F2 (MIMO_ParametersPerBand__ext0O__dummy6__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext0O__dummy6__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext0O__dummy6__F1 (MIMO_ParametersPerBand__ext0O__dummy6__F2 y) = y. enum_solve H y. Qed.

Require Import NR.BeamManagementSSB_CSI_RS.

Opaque BeamManagementSSB_CSI_RS__cond BeamManagementSSB_CSI_RS__Format.

Inductive MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Type : Set :=
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym14
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym28
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym48
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym224
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym336
.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__cond := (fun (_ : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Type) => True).
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__nat__helper.

Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym14 => 0
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym28 => 1
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym48 => 2
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym224 => 3
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym336 => 4
  end.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym14
  | 1 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym28
  | 2 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym48
  | 3 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym224
  | 4 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym336
  | _ => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__sym14
  end.
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F1F2 : forall x : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Type, (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F1 x <= 4) /\ MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F2 (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F1 (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Type : Set :=
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym14
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym28
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym48
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym224
 | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym336
.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__cond := (fun (_ : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Type) => True).
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__nat__helper.

Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym14 => 0
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym28 => 1
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym48 => 2
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym224 => 3
  | MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym336 => 4
  end.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym14
  | 1 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym28
  | 2 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym48
  | 3 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym224
  | 4 => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym336
  | _ => MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__sym14
  end.
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F1F2 : forall x : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Type, (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F1 x <= 4) /\ MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F2 (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F1 (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Type : Set :=
  make__MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Type {
    MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz : option MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Type ;
    MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz : option MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Type ;
}.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list := (
 Opt MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Type MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__cond ::
 Opt MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Type MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond z := 
  opt_cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__cond (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz z) /\
  opt_cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__cond (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz z) /\
  True.

Require Import NR.CodebookParameters.

Opaque CodebookParameters__cond CodebookParameters__Format.

Require Import NR.CSI_RS_IM_ReceptionForFeedback.

Opaque CSI_RS_IM_ReceptionForFeedback__cond CSI_RS_IM_ReceptionForFeedback__Format.

Require Import NR.CSI_RS_ProcFrameworkForSRS.

Opaque CSI_RS_ProcFrameworkForSRS__cond CSI_RS_ProcFrameworkForSRS__Format.

Require Import NR.CSI_ReportFramework.

Opaque CSI_ReportFramework__cond CSI_ReportFramework__Format.

Require Import NR.CSI_RS_ForTracking.

Opaque CSI_RS_ForTracking__cond CSI_RS_ForTracking__Format.

Require Import NR.SupportedCSI_RS_Resource.

Opaque SupportedCSI_RS_Resource__cond SupportedCSI_RS_Resource__Format.

Definition MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__Type := list SupportedCSI_RS_Resource__Type.

Lemma MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__helper1 : (0 <= 1 <= maxNrofCSI_RS_Resources)%Z. unfold maxNrofCSI_RS_Resources.
 lia. Qed.
Lemma MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__helper2 : to_bit_sz (Z.to_nat (maxNrofCSI_RS_Resources - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCSI_RS_Resources - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__cond (z : MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofCSI_RS_Resources)%Z /\ (list_and SupportedCSI_RS_Resource__cond z) .

Require Import NR.SpatialRelations.

Opaque SpatialRelations__cond SpatialRelations__Format.

Record MIMO_ParametersPerBand__ext0O__Type : Set :=
  make__MIMO_ParametersPerBand__ext0O__Type {
    MIMO_ParametersPerBand__ext0O__dummy6 : option MIMO_ParametersPerBand__ext0O__dummy6__Type ;
    MIMO_ParametersPerBand__ext0O__beamManagementSSB_CSI_RS : option BeamManagementSSB_CSI_RS__Type ;
    MIMO_ParametersPerBand__ext0O__beamSwitchTiming : option MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Type ;
    MIMO_ParametersPerBand__ext0O__codebookParameters : option CodebookParameters__Type ;
    MIMO_ParametersPerBand__ext0O__csi_RS_IM_ReceptionForFeedback : option CSI_RS_IM_ReceptionForFeedback__Type ;
    MIMO_ParametersPerBand__ext0O__csi_RS_ProcFrameworkForSRS : option CSI_RS_ProcFrameworkForSRS__Type ;
    MIMO_ParametersPerBand__ext0O__csi_ReportFramework : option CSI_ReportFramework__Type ;
    MIMO_ParametersPerBand__ext0O__csi_RS_ForTracking : option CSI_RS_ForTracking__Type ;
    MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS : option MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__Type ;
    MIMO_ParametersPerBand__ext0O__spatialRelations : option SpatialRelations__Type ;
}.
Definition MIMO_ParametersPerBand__ext0O__list := (
 Opt MIMO_ParametersPerBand__ext0O__dummy6__Type MIMO_ParametersPerBand__ext0O__dummy6__cond ::
 Opt BeamManagementSSB_CSI_RS__Type BeamManagementSSB_CSI_RS__cond ::
 Opt MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Type MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond ::
 Opt CodebookParameters__Type CodebookParameters__cond ::
 Opt CSI_RS_IM_ReceptionForFeedback__Type CSI_RS_IM_ReceptionForFeedback__cond ::
 Opt CSI_RS_ProcFrameworkForSRS__Type CSI_RS_ProcFrameworkForSRS__cond ::
 Opt CSI_ReportFramework__Type CSI_ReportFramework__cond ::
 Opt CSI_RS_ForTracking__Type CSI_RS_ForTracking__cond ::
 Opt MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__Type MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__cond ::
 Opt SpatialRelations__Type SpatialRelations__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext0O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext0O__dummy6__cond (MIMO_ParametersPerBand__ext0O__dummy6 z) /\
  opt_cond BeamManagementSSB_CSI_RS__cond (MIMO_ParametersPerBand__ext0O__beamManagementSSB_CSI_RS z) /\
  opt_cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond (MIMO_ParametersPerBand__ext0O__beamSwitchTiming z) /\
  opt_cond CodebookParameters__cond (MIMO_ParametersPerBand__ext0O__codebookParameters z) /\
  opt_cond CSI_RS_IM_ReceptionForFeedback__cond (MIMO_ParametersPerBand__ext0O__csi_RS_IM_ReceptionForFeedback z) /\
  opt_cond CSI_RS_ProcFrameworkForSRS__cond (MIMO_ParametersPerBand__ext0O__csi_RS_ProcFrameworkForSRS z) /\
  opt_cond CSI_ReportFramework__cond (MIMO_ParametersPerBand__ext0O__csi_ReportFramework z) /\
  opt_cond CSI_RS_ForTracking__cond (MIMO_ParametersPerBand__ext0O__csi_RS_ForTracking z) /\
  opt_cond MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__cond (MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS z) /\
  opt_cond SpatialRelations__cond (MIMO_ParametersPerBand__ext0O__spatialRelations z) /\
  True.

Definition MIMO_ParametersPerBand__ext0__Type := MIMO_ParametersPerBand__ext0O__Type.
Definition MIMO_ParametersPerBand__ext0__cond := MIMO_ParametersPerBand__ext0O__cond.

Inductive MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Type, (MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F2 (MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F1 (MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CodebookParameters_v1610.

Opaque CodebookParameters_v1610__cond CodebookParameters_v1610__Format.

Inductive MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Type, (MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F2 (MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F1 (MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n1
 | MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n2
 | MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n4
 | MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n8
.
Definition MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n1 => 0
  | MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n2 => 1
  | MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n4 => 2
  | MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n8 => 3
  end.
Definition MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n1
  | 1 => MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n2
  | 2 => MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n4
  | 3 => MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n8
  | _ => MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__n1
  end.
Lemma MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Type, (MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F1 x <= 3) /\ MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F2 (MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F1 (MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Type, (MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F2 (MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F1 (MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n8
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n16
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n32
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n64
.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n8 => 0
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n16 => 1
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n32 => 2
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n64 => 3
  end.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n8
  | 1 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n16
  | 2 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n32
  | 3 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n64
  | _ => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__n8
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Type, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F1 x <= 3) /\ MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n8
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n16
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n32
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n64
.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n8 => 0
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n16 => 1
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n32 => 2
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n64 => 3
  end.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n8
  | 1 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n16
  | 2 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n32
  | 3 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n64
  | _ => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__n8
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Type, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F1 x <= 3) /\ MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n0
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n4
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n8
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n16
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n32
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n64
.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n0 => 0
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n4 => 1
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n8 => 2
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n16 => 3
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n32 => 4
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n64 => 5
  end.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n0
  | 1 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n4
  | 2 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n8
  | 3 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n16
  | 4 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n32
  | 5 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n64
  | _ => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__n0
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Type, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F1 x <= 5) /\ MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F2F1 : forall (y : nat) (H : y <= 5), MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n8
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n16
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n32
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n64
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n128
.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n8 => 0
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n16 => 1
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n32 => 2
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n64 => 3
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n128 => 4
  end.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n8
  | 1 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n16
  | 2 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n32
  | 3 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n64
  | 4 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n128
  | _ => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__n8
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Type, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F1 x <= 4) /\ MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n8
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n16
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n32
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n64
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n128
.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n8 => 0
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n16 => 1
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n32 => 2
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n64 => 3
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n128 => 4
  end.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n8
  | 1 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n16
  | 2 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n32
  | 3 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n64
  | 4 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n128
  | _ => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__n8
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Type, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F1 x <= 4) /\ MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__one
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__three
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__oneAndThree
.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__one => 0
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__three => 1
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__oneAndThree => 2
  end.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__one
  | 1 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__three
  | 2 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__oneAndThree
  | _ => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__one
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Type, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F1 x <= 2) /\ MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n2
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n4
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n8
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n16
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n32
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n64
.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n2 => 0
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n4 => 1
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n8 => 2
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n16 => 3
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n32 => 4
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n64 => 5
  end.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n2
  | 1 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n4
  | 2 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n8
  | 3 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n16
  | 4 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n32
  | 5 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n64
  | _ => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__n2
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Type, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F1 x <= 5) /\ MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F2F1 : forall (y : nat) (H : y <= 5), MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__ssbWithCSI_IM
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__ssbWithNZP_IMR
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__csirsWithNZP_IMR
 | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__csi_RSWithoutIMR
.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__ssbWithCSI_IM => 0
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__ssbWithNZP_IMR => 1
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__csirsWithNZP_IMR => 2
  | MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__csi_RSWithoutIMR => 3
  end.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__ssbWithCSI_IM
  | 1 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__ssbWithNZP_IMR
  | 2 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__csirsWithNZP_IMR
  | 3 => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__csi_RSWithoutIMR
  | _ => MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__ssbWithCSI_IM
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Type, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F1 x <= 3) /\ MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Type : Set :=
  make__MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Type {
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16 : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Type ;
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16 : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Type ;
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16 : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Type ;
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16 : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Type ;
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16 : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Type ;
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16 : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Type ;
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16 : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Type ;
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16 : option MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list := (
 Nor MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__cond ::
 Nor MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__cond ::
 Nor MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__cond ::
 Nor MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__cond ::
 Nor MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__cond ::
 Nor MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__cond ::
 Nor MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond z := 
  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16 z) /\
  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16 z) /\
  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16 z) /\
  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16 z) /\
  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16 z) /\
  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16 z) /\
  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n1
 | MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n2
 | MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n4
.
Definition MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n1 => 0
  | MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n2 => 1
  | MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n4 => 2
  end.
Definition MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n1
  | 1 => MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n2
  | 2 => MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n4
  | _ => MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__n1
  end.
Lemma MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Type, (MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F1 x <= 2) /\ MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F2 (MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F1 (MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Type, (MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F2 (MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F1 (MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__Type := Z.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__cond := (fun z => (1 <= z <= 2)%Z).
Inductive MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Type, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Type, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Type, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Type : Set :=
  make__MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Type {
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Type ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list := (
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond z := 
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Type, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Type, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Type, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n1
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n2
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n4
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n8
.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n1 => 0
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n2 => 1
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n4 => 2
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n8 => 3
  end.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n1
  | 1 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n2
  | 2 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n4
  | 3 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n8
  | _ => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__n1
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Type, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F1 x <= 3) /\ MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n2
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n4
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n8
 | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n16
.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n2 => 0
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n4 => 1
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n8 => 2
  | MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n16 => 3
  end.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n2
  | 1 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n4
  | 2 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n8
  | 3 => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n16
  | _ => MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__n2
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Type, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F1 x <= 3) /\ MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Type : Set :=
  make__MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Type {
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16 : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Type ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16 : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list := (
 Nor MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__cond ::
 Nor MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond z := 
  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16 z) /\
  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16 z) /\
  True.

Record MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Type : Set :=
  make__MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Type {
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16 : option Z ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Type ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Type ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Type ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Type ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Type ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list := (
 Opt Z MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond z := 
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported1
 | MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported2
 | MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported3
.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported1 => 0
  | MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported2 => 1
  | MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported3 => 2
  end.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported1
  | 1 => MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported2
  | 2 => MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported3
  | _ => MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__supported1
  end.
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Type, (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F1 x <= 2) /\ MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F2 (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F1 (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Type, (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F2 (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F1 (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Type : Set :=
  make__MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Type {
    MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16 : option MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Type ;
    MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16 : option MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list := (
 Opt MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Type MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Type MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond z := 
  opt_cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__cond (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__cond (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Type, (MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F2 (MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F1 (MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Type, (MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F2 (MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F1 (MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb3
 | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb5
 | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb10
 | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb20
 | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__noRestriction
.
Definition MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb3 => 0
  | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb5 => 1
  | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb10 => 2
  | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb20 => 3
  | MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__noRestriction => 4
  end.
Definition MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb3
  | 1 => MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb5
  | 2 => MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb10
  | 3 => MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb20
  | 4 => MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__noRestriction
  | _ => MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__kb3
  end.
Lemma MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Type, (MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F1 x <= 4) /\ MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F2 (MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F1 (MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n2
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n3
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n4
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n5
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n6
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n7
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n8
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n16
.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n2 => 0
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n3 => 1
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n4 => 2
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n5 => 3
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n6 => 4
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n7 => 5
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n8 => 6
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n16 => 7
  end.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n2
  | 1 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n3
  | 2 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n4
  | 3 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n5
  | 4 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n6
  | 5 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n7
  | 6 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n8
  | 7 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n16
  | _ => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__n2
  end.
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Type, (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F1 x <= 7) /\ MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F2 (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F2F1 : forall (y : nat) (H : y <= 7), MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F1 (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb3
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb5
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb10
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb20
 | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__noRestriction
.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb3 => 0
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb5 => 1
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb10 => 2
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb20 => 3
  | MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__noRestriction => 4
  end.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb3
  | 1 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb5
  | 2 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb10
  | 3 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb20
  | 4 => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__noRestriction
  | _ => MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__kb3
  end.
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Type, (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F1 x <= 4) /\ MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F2 (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F1 (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__Type := Z.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__cond := (fun z => (1 <= z <= 2)%Z).
Record MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Type : Set :=
  make__MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Type {
    MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16 : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Type ;
    MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16 : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Type ;
    MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16 : Z ;
}.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list := (
 Nor MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Type MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__cond ::
 Nor MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Type MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__cond ::
 Nor Z MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond z := 
  MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__cond (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16 z) /\
  MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__cond (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16 z) /\
  MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__cond (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Type, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F2 (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F1 (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Type, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F2 (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F1 (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Type, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F2 (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F1 (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Type, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F2 (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F1 (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CSI_ReportFrameworkExt_r16.

Opaque CSI_ReportFrameworkExt_r16__cond CSI_ReportFrameworkExt_r16__Format.

Require Import NR.CodebookParametersAddition_r16.

Opaque CodebookParametersAddition_r16__cond CodebookParametersAddition_r16__Format.

Require Import NR.CodebookComboParametersAddition_r16.

Opaque CodebookComboParametersAddition_r16__cond CodebookComboParametersAddition_r16__Format.

Inductive MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Type, (MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F2 (MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F1 (MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__supported
.
Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__supported
  | _ => MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Type, (MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F2 (MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F1 (MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__sym224
 | MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__sym336
.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__sym224 => 0
  | MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__sym336 => 1
  end.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__sym224
  | 1 => MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__sym336
  | _ => MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__sym224
  end.
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Type, (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F1 x <= 1) /\ MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F2 (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F2F1 : forall (y : nat) (H : y <= 1), MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F1 (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__sym224
 | MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__sym336
.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__sym224 => 0
  | MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__sym336 => 1
  end.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__sym224
  | 1 => MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__sym336
  | _ => MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__sym224
  end.
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Type, (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F1 x <= 1) /\ MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F2 (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F2F1 : forall (y : nat) (H : y <= 1), MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F1 (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Type : Set :=
  make__MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Type {
    MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16 : option MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Type ;
    MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16 : option MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list := (
 Opt MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Type MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Type MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond z := 
  opt_cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__cond (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__cond (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16 z) /\
  True.

Record MIMO_ParametersPerBand__ext1O__Type : Set :=
  make__MIMO_ParametersPerBand__ext1O__Type {
    MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16 : option MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Type ;
    MIMO_ParametersPerBand__ext1O__codebookParametersPerBand_r16 : option CodebookParameters_v1610__Type ;
    MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16 : option MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Type ;
    MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16 : option MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Type ;
    MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16 : option MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Type ;
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16 : option MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Type ;
    MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16 : option MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Type ;
    MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16 : option MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Type ;
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16 : option MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Type ;
    MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16 : option MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Type ;
    MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16 : option MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Type ;
    MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16 : option MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Type ;
    MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16 : option MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Type ;
    MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16 : option MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Type ;
    MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16 : option MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Type ;
    MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16 : option MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Type ;
    MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16 : option MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Type ;
    MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16 : option MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Type ;
    MIMO_ParametersPerBand__ext1O__csi_ReportFrameworkExt_r16 : option CSI_ReportFrameworkExt_r16__Type ;
    MIMO_ParametersPerBand__ext1O__codebookParametersAddition_r16 : option CodebookParametersAddition_r16__Type ;
    MIMO_ParametersPerBand__ext1O__codebookComboParametersAddition_r16 : option CodebookComboParametersAddition_r16__Type ;
    MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16 : option MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Type ;
    MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16 : option MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Type ;
    MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16 : option MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext1O__list := (
 Opt MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Type MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__cond ::
 Opt CodebookParameters_v1610__Type CodebookParameters_v1610__cond ::
 Opt MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Type MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Type MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Type MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Type MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Type MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Type MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Type MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Type MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Type MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Type MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Type MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Type MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Type MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Type MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__cond ::
 Opt CSI_ReportFrameworkExt_r16__Type CSI_ReportFrameworkExt_r16__cond ::
 Opt CodebookParametersAddition_r16__Type CodebookParametersAddition_r16__cond ::
 Opt CodebookComboParametersAddition_r16__Type CodebookComboParametersAddition_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Type MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Type MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__cond ::
 Opt MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Type MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext1O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__cond (MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16 z) /\
  opt_cond CodebookParameters_v1610__cond (MIMO_ParametersPerBand__ext1O__codebookParametersPerBand_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__cond (MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__cond (MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__cond (MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__cond (MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__cond (MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__cond (MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__cond (MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__cond (MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__cond (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__cond (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__cond (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__cond (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16 z) /\
  opt_cond CSI_ReportFrameworkExt_r16__cond (MIMO_ParametersPerBand__ext1O__csi_ReportFrameworkExt_r16 z) /\
  opt_cond CodebookParametersAddition_r16__cond (MIMO_ParametersPerBand__ext1O__codebookParametersAddition_r16 z) /\
  opt_cond CodebookComboParametersAddition_r16__cond (MIMO_ParametersPerBand__ext1O__codebookComboParametersAddition_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__cond (MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__cond (MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16 z) /\
  True.

Definition MIMO_ParametersPerBand__ext1__Type := MIMO_ParametersPerBand__ext1O__Type.
Definition MIMO_ParametersPerBand__ext1__cond := MIMO_ParametersPerBand__ext1O__cond.

Inductive MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__supported
.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__supported
  | _ => MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Type, (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F2 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F1 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__supported
.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__supported
  | _ => MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Type, (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F2 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F1 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Type : Set :=
  make__MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Type {
    MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16 : option MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Type ;
    MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16 : option MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list := (
 Opt MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Type MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__cond ::
 Opt MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Type MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond z := 
  opt_cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__cond (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__cond (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__supported
.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__supported
  | _ => MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Type, (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F2 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F1 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext2O__Type : Set :=
  make__MIMO_ParametersPerBand__ext2O__Type {
    MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16 : option MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Type ;
    MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16 : option MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext2O__list := (
 Opt MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Type MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond ::
 Opt MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Type MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext2O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16 z) /\
  opt_cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__cond (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16 z) /\
  True.

Definition MIMO_ParametersPerBand__ext2__Type := MIMO_ParametersPerBand__ext2O__Type.
Definition MIMO_ParametersPerBand__ext2__cond := MIMO_ParametersPerBand__ext2O__cond.

Inductive MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Type : Set :=
 | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n96
 | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n128
 | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n160
 | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n192
 | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n224
 | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n256
 | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n288
 | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n320
.
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__cond := (fun (_ : MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Type) => True).
Lemma MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__nat__helper.

Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n96 => 0
  | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n128 => 1
  | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n160 => 2
  | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n192 => 3
  | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n224 => 4
  | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n256 => 5
  | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n288 => 6
  | MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n320 => 7
  end.
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n96
  | 1 => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n128
  | 2 => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n160
  | 3 => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n192
  | 4 => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n224
  | 5 => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n256
  | 6 => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n288
  | 7 => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n320
  | _ => MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__n96
  end.
Lemma MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F1F2 : forall x : MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Type, (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F1 x <= 7) /\ MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F2 (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F2F1 : forall (y : nat) (H : y <= 7), MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F1 (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Type : Set :=
  make__MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Type {
    MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640 : MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Type ;
}.
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list := (
 Nor MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Type MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond z := 
  MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__cond (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__supported
.
Definition MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__supported
  | _ => MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Type, (MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F2 (MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F1 (MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext3O__Type : Set :=
  make__MIMO_ParametersPerBand__ext3O__Type {
    MIMO_ParametersPerBand__ext3O__spatialRelations_v1640 : option MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Type ;
    MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16 : option MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext3O__list := (
 Opt MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Type MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond ::
 Opt MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Type MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext3O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640 z) /\
  opt_cond MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__cond (MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16 z) /\
  True.

Definition MIMO_ParametersPerBand__ext3__Type := MIMO_ParametersPerBand__ext3O__Type.
Definition MIMO_ParametersPerBand__ext3__cond := MIMO_ParametersPerBand__ext3O__cond.

Inductive MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Type : Set :=
 | MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__supported
.
Definition MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__cond := (fun (_ : MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Type) => True).
Lemma MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__nat__helper.

Definition MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__supported
  | _ => MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__supported
  end.
Lemma MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F1F2 : forall x : MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Type, (MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F1 x <= 0) /\ MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F2 (MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F1 (MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext4O__Type : Set :=
  make__MIMO_ParametersPerBand__ext4O__Type {
    MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16 : option MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Type ;
}.
Definition MIMO_ParametersPerBand__ext4O__list := (
 Opt MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Type MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext4O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__cond (MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16 z) /\
  True.

Definition MIMO_ParametersPerBand__ext4__Type := MIMO_ParametersPerBand__ext4O__Type.
Definition MIMO_ParametersPerBand__ext4__cond := MIMO_ParametersPerBand__ext4O__cond.

Definition MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__Type := bit_string_fixed.
Definition MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Record MIMO_ParametersPerBand__ext5O__Type : Set :=
  make__MIMO_ParametersPerBand__ext5O__Type {
    MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670 : option MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__Type ;
}.
Definition MIMO_ParametersPerBand__ext5O__list := (
 Opt MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__Type MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext5O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__cond (MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670 z) /\
  True.

Definition MIMO_ParametersPerBand__ext5__Type := MIMO_ParametersPerBand__ext5O__Type.
Definition MIMO_ParametersPerBand__ext5__cond := MIMO_ParametersPerBand__ext5O__cond.

Inductive MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_combEight_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__srs_combEight_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_combEight_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_combEight_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__srs_combEight_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_combEight_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_combEight_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__srs_combEight_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CodebookParametersfetype2_r17.

Opaque CodebookParametersfetype2_r17__cond CodebookParametersfetype2_r17__Format.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf0_2
 | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf1_3_4
 | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf0_4
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf0_2 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf1_3_4 => 1
  | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf0_4 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf0_2
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf1_3_4
  | 2 => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf0_4
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__pf0_2
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__n1
 | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__n2
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__n2 => 1
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__n2
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F1 x <= 1) /\ MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__helper1 : (1 <= 9)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__helper2 : to_bit_sz (Z.to_nat (9 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__cond := (fun z => (1 <= z <= 9)%Z).
Inductive MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n2
 | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n3
 | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n2 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n3 => 1
  | MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n4 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n2
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n3
  | 2 => MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__n2
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Type {
    MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17 : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17 : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list := (
 Nor MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__cond ::
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__n1
 | MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__n2
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__n2 => 1
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__n2
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F1 x <= 1) /\ MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Type, (MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F2 (MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F1 (MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Type, (MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F2 (MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F1 (MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Type, (MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F2 (MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F1 (MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n1
 | MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n2
 | MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n4 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CodebookComboParameterMixedType_r17.

Opaque CodebookComboParameterMixedType_r17__cond CodebookComboParameterMixedType_r17__Format.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n8
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n12
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n16
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n24
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n32
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n48
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n64
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n128
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n8 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n12 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n16 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n24 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n32 => 4
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n48 => 5
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n64 => 6
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n128 => 7
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n8
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n12
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n16
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n24
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n32
  | 5 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n48
  | 6 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n64
  | 7 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n128
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__n8
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F1 x <= 7) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F2F1 : forall (y : nat) (H : y <= 7), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n8
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n16
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n8 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n16 => 4
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n8
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n16
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F1 x <= 4) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Type {
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list := (
 Nor MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n7
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n14
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n28
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n42
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n56
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n70
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n84
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n98
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n112
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n224
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n336
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__nat__helper : to_bit_sz 13 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__nat__Format : T_Format nat (fun z => (z <= 13)) :=
  nat_enum_format 13 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n7 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n14 => 4
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n28 => 5
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n42 => 6
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n56 => 7
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n70 => 8
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n84 => 9
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n98 => 10
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n112 => 11
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n224 => 12
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n336 => 13
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n7
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n14
  | 5 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n28
  | 6 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n42
  | 7 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n56
  | 8 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n70
  | 9 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n84
  | 10 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n98
  | 11 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n112
  | 12 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n224
  | 13 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n336
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 x <= 13) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2F1 : forall (y : nat) (H : y <= 13), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n2
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n3
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n4
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n5
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n6
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n7
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n8
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n2 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n3 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n5 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n6 => 4
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n7 => 5
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n8 => 6
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n2
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n3
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n5
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n6
  | 5 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n7
  | 6 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n8
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__n2
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F1 x <= 6) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F2F1 : forall (y : nat) (H : y <= 6), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Type {
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list := (
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond z := 
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n8
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n8 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n8
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n0
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n0 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n1 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n2 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n4 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n0
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n1
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n2
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__n0
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n0
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n0 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n1 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n2 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n4 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n0
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n1
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n2
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__n0
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Type {
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list := (
 Nor MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n8
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n12
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n16
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n24
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n32
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n48
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n64
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n128
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__nat__helper : to_bit_sz 8 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__nat__Format : T_Format nat (fun z => (z <= 8)) :=
  nat_enum_format 8 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n4 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n8 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n12 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n16 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n24 => 4
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n32 => 5
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n48 => 6
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n64 => 7
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n128 => 8
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n4
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n8
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n12
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n16
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n24
  | 5 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n32
  | 6 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n48
  | 7 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n64
  | 8 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n128
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__n4
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F1 x <= 8) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F2F1 : forall (y : nat) (H : y <= 8), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n8
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n12
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n16
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n24
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n32
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n48
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n64
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n4 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n8 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n12 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n16 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n24 => 4
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n32 => 5
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n48 => 6
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n64 => 7
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n4
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n8
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n12
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n16
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n24
  | 5 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n32
  | 6 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n48
  | 7 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n64
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__n4
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F1 x <= 7) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F2F1 : forall (y : nat) (H : y <= 7), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n8
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n16
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n8 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n16 => 4
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n8
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n16
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F1 x <= 4) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n8
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n16
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n8 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n16 => 4
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n8
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n16
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F1 x <= 4) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Type {
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list := (
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n7
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n14
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n28
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n42
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n56
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n70
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n84
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n98
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n112
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n224
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n336
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__nat__helper : to_bit_sz 13 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__nat__Format : T_Format nat (fun z => (z <= 13)) :=
  nat_enum_format 13 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n7 => 3
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n14 => 4
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n28 => 5
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n42 => 6
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n56 => 7
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n70 => 8
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n84 => 9
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n98 => 10
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n112 => 11
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n224 => 12
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n336 => 13
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n7
  | 4 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n14
  | 5 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n28
  | 6 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n42
  | 7 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n56
  | 8 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n70
  | 9 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n84
  | 10 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n98
  | 11 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n112
  | 12 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n224
  | 13 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n336
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 x <= 13) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2F1 : forall (y : nat) (H : y <= 13), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__helper1 : (2 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__helper2 : to_bit_sz (Z.to_nat (8 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__cond := (fun z => (2 <= z <= 8)%Z).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__helper1 : (2 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__helper2 : to_bit_sz (Z.to_nat (8 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__cond := (fun z => (2 <= z <= 8)%Z).
Record MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Type {
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17 : Z ;
}.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list := (
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__cond ::
 Nor Z MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__cond ::
 Nor Z MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n8
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n8 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n8
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n8
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n8 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n8
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Type {
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17 : option MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17 : option MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list := (
 Opt MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond z := 
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n0
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n0 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n1 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n2 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n4 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n0
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n1
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n2
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__n0
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n0
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n0 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n1 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n2 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n4 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n0
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n1
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n2
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__n0
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n0
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n0 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n1 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n2 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n4 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n0
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n1
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n2
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__n0
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n0
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n0 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n1 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n2 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n4 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n0
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n1
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n2
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__n0
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Type {
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list := (
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17 z) /\
  True.

Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__helper1 : (1 <= 7)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__helper2 : to_bit_sz (Z.to_nat (7 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__cond := (fun z => (1 <= z <= 7)%Z).
Inductive MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n1
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n2
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n4
 | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n8
.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n8 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n8
  | _ => MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Type, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Type {
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list := (
 Nor Z MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17 z) /\
  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17 z) /\
  True.

Lemma MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__cond := (fun z => (1 <= z <= 4)%Z).
Inductive MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n1
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n2
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n4
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n8
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n12
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n16
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n28
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n32
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n48
 | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n64
.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n8 => 3
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n12 => 4
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n16 => 5
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n28 => 6
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n32 => 7
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n48 => 8
  | MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n64 => 9
  end.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n8
  | 4 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n12
  | 5 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n16
  | 6 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n28
  | 7 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n32
  | 8 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n48
  | 9 => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n64
  | _ => MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Type, (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F1 x <= 9) /\ MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F2 (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F2F1 : forall (y : nat) (H : y <= 9), MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F1 (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Type {
    MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17 : MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list := (
 Nor Z MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Type MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__cond (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__cond (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n1
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n2
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n4 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n1
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n2
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n4 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n1
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n2
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n4 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n1
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n2
 | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n4
.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n4 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n4
  | _ => MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Type {
    MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17 : option MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17 : option MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17 : option MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17 : option MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list := (
 Opt MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Type MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Type MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Type MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Type MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond z := 
  opt_cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__cond (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__cond (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__cond (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__cond (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__cond := (fun z => (1 <= z <= 8)%Z).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__cond := (fun z => (1 <= z <= 8)%Z).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__helper1 : (0 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__helper2 : to_bit_sz (Z.to_nat (8 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__cond := (fun z => (0 <= z <= 8)%Z).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__cond := (fun z => (1 <= z <= 16)%Z).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__cond := (fun z => (1 <= z <= 2)%Z).
Record MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Type {
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17 : Z ;
}.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list := (
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__cond ::
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__cond ::
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__cond ::
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__cond ::
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__typeA
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__typeB
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__both
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__typeA => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__typeB => 1
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__both => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__typeA
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__typeB
  | 2 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__both
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__typeA
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__helper1 : (3 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__helper2 : to_bit_sz (Z.to_nat (8 - 3)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 3))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__cond := (fun z => (3 <= z <= 8)%Z).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__helper1 : (1 <= 7)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__helper2 : to_bit_sz (Z.to_nat (7 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__cond := (fun z => (1 <= z <= 7)%Z).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__cond := (fun z => (0 <= z <= 7)%Z).
Record MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Type {
    MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17 : Z ;
}.
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list := (
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__cond ::
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17 z) /\
  True.

Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__helper1 : (1 <= 4)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__cond := (fun z => (1 <= z <= 4)%Z).
Inductive MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n2
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n3
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n4
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n8
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n16
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n32
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n64
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n2 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n3 => 1
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n8 => 3
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n16 => 4
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n32 => 5
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n64 => 6
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n2
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n3
  | 2 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n8
  | 4 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n16
  | 5 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n32
  | 6 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n64
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__n2
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F1 x <= 6) /\ MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F2F1 : forall (y : nat) (H : y <= 6), MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n8
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n16
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n32
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n64
 | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n128
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n8 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n16 => 1
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n32 => 2
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n64 => 3
  | MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n128 => 4
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n8
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n16
  | 2 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n32
  | 3 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n64
  | 4 => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n128
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__n8
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F1 x <= 4) /\ MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Type {
    MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17 : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17 : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list := (
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n4
 | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n8
 | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n12
 | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n16
 | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n32
 | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n48
 | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n64
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n4 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n8 => 1
  | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n12 => 2
  | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n16 => 3
  | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n32 => 4
  | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n48 => 5
  | MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n64 => 6
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n4
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n8
  | 2 => MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n12
  | 3 => MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n16
  | 4 => MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n32
  | 5 => MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n48
  | 6 => MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n64
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__n4
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F1 x <= 6) /\ MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F2F1 : forall (y : nat) (H : y <= 6), MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__helper1 : (2 <= 8)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__helper2 : to_bit_sz (Z.to_nat (8 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__Type := Z.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__cond := (fun z => (2 <= z <= 8)%Z).
Inductive MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__mode1
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__mode2
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__both
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__mode1 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__mode2 => 1
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__both => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__mode1
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__mode2
  | 2 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__both
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__mode1
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CSI_MultiTRP_SupportedCombinations_r17.

Opaque CSI_MultiTRP_SupportedCombinations_r17__cond CSI_MultiTRP_SupportedCombinations_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__Type := list CSI_MultiTRP_SupportedCombinations_r17__Type.

Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__helper1 : (0 <= 1 <= 16)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__cond (z : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__Type) :=  (1 <= Z.of_nat (length z) <= 16)%Z /\ (list_and CSI_MultiTRP_SupportedCombinations_r17__cond z) .

Inductive MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__mode1
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__mode1And2
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__mode1 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__mode1And2 => 1
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__mode1
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__mode1And2
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__mode1
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F1 x <= 1) /\ MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Type {
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17 : Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17 : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17 : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17 : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list := (
 Nor Z MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__cond ::
 Nor MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond z := 
  MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17 z) /\
  MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17 z) /\
  True.

Require Import NR.CodebookComboParameterMultiTRP_r17.

Opaque CodebookComboParameterMultiTRP_r17__cond CodebookComboParameterMultiTRP_r17__Format.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__x1
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__x2
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__x1 => 0
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__x2 => 1
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__x1
  | 1 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__x2
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__x1
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F1 x <= 1) /\ MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Type, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__supported
.
Definition MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__supported
  | _ => MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Type, (MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym56
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym112
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym192
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym896
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym1344
.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym56 => 0
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym112 => 1
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym192 => 2
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym896 => 3
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym1344 => 4
  end.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym56
  | 1 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym112
  | 2 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym192
  | 3 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym896
  | 4 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym1344
  | _ => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__sym56
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Type, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F1 x <= 4) /\ MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F2 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F1 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym112
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym224
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym384
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym1792
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym2688
.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym112 => 0
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym224 => 1
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym384 => 2
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym1792 => 3
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym2688 => 4
  end.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym112
  | 1 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym224
  | 2 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym384
  | 3 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym1792
  | 4 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym2688
  | _ => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__sym112
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Type, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F1 x <= 4) /\ MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F2 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F2F1 : forall (y : nat) (H : y <= 4), MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F1 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Type {
    MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz : option MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Type ;
    MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz : option MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list := (
 Opt MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__cond ::
 Opt MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond z := 
  opt_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__cond (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__cond (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__sym896
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__sym1344
.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__sym896 => 0
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__sym1344 => 1
  end.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__sym896
  | 1 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__sym1344
  | _ => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__sym896
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Type, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F1 x <= 1) /\ MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F2 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F1 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__sym1792
 | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__sym2688
.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__sym1792 => 0
  | MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__sym2688 => 1
  end.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__sym1792
  | 1 => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__sym2688
  | _ => MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__sym1792
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Type, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F1 x <= 1) /\ MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F2 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 1), MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F1 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Type {
    MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17 : option MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Type ;
    MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17 : option MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list := (
 Opt MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond z := 
  opt_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__cond (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__cond (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym56
 | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym112
 | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym224
.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym56 => 0
  | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym112 => 1
  | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym224 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym56
  | 1 => MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym112
  | 2 => MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym224
  | _ => MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__sym56
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Type, (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F2 (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F1 (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym112
 | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym224
 | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym448
.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym112 => 0
  | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym224 => 1
  | MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym448 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym112
  | 1 => MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym224
  | 2 => MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym448
  | _ => MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__sym112
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Type, (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F2 (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F1 (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Type {
    MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17 : option MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Type ;
    MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17 : option MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list := (
 Opt MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Type MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Type MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond z := 
  opt_cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__cond (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__cond (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17 z) /\
  True.

Inductive MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n2
 | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n4
 | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n7
.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n2 => 0
  | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n4 => 1
  | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n7 => 2
  end.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n2
  | 1 => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n4
  | 2 => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n7
  | _ => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__n2
  end.
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Type, (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F2 (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F1 (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n1
 | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n2
 | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n4
 | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n7
.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n1 => 0
  | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n2 => 1
  | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n4 => 2
  | MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n7 => 3
  end.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n1
  | 1 => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n2
  | 2 => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n4
  | 3 => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n7
  | _ => MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__n1
  end.
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Type, (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F1 x <= 3) /\ MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F2 (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F2F1 : forall (y : nat) (H : y <= 3), MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F1 (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Type {
    MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17 : option MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Type ;
    MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17 : option MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list := (
 Opt MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Type MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Type MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond z := 
  opt_cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__cond (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__cond (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17 z) /\
  True.

Record MIMO_ParametersPerBand__ext6O__Type : Set :=
  make__MIMO_ParametersPerBand__ext6O__Type {
    MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17 : option MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17 : option MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17 : option MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_combEight_r17 : option MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Type ;
    MIMO_ParametersPerBand__ext6O__codebookParametersfetype2_r17 : option CodebookParametersfetype2_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Type ;
    MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17 : option MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17 : option MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Type ;
    MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17 : option MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17 : option MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17 : option MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__codebookComboParameterMixedType_r17 : option CodebookComboParameterMixedType_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17 : option MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17 : option MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17 : option MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17 : option MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17 : option MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17 : option MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Type ;
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17 : option MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17 : option MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_PortReport_r17 : option MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17 : option Z ;
    MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Type ;
    MIMO_ParametersPerBand__ext6O__codebookComboParameterMultiTRP_r17 : option CodebookComboParameterMultiTRP_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Type ;
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17 : option MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Type ;
    MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17 : option MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Type ;
    MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710 : option MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Type ;
    MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17 : option MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Type ;
    MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710 : option MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Type ;
    MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710 : option MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Type ;
}.
Definition MIMO_ParametersPerBand__ext6O__list := (
 Opt MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Type MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Type MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Type MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Type MIMO_ParametersPerBand__ext6O__srs_combEight_r17__cond ::
 Opt CodebookParametersfetype2_r17__Type CodebookParametersfetype2_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Type MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Type MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Type MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Type MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Type MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__cond ::
 Opt CodebookComboParameterMixedType_r17__Type CodebookComboParameterMixedType_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Type MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Type MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__cond ::
 Opt Z MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond ::
 Opt CodebookComboParameterMultiTRP_r17__Type CodebookComboParameterMultiTRP_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Type MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond ::
 Opt MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond ::
 Opt MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Type MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond ::
 Opt MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Type MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext6O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__cond (MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__cond (MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__cond (MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_combEight_r17__cond (MIMO_ParametersPerBand__ext6O__srs_combEight_r17 z) /\
  opt_cond CodebookParametersfetype2_r17__cond (MIMO_ParametersPerBand__ext6O__codebookParametersfetype2_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__cond (MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__cond (MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__cond (MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__cond (MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__cond (MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17 z) /\
  opt_cond CodebookComboParameterMixedType_r17__cond (MIMO_ParametersPerBand__ext6O__codebookComboParameterMixedType_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_r17__cond (MIMO_ParametersPerBand__ext6O__codebookComboParameterMultiTRP_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__cond (MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710 z) /\
  opt_cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710 z) /\
  True.

Definition MIMO_ParametersPerBand__ext6__Type := MIMO_ParametersPerBand__ext6O__Type.
Definition MIMO_ParametersPerBand__ext6__cond := MIMO_ParametersPerBand__ext6O__cond.

Inductive MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__supported
.
Definition MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__supported
  | _ => MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Type, (MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F2 (MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F1 (MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__helper1 : (9 <= 12)%Z.  lia. Qed.
Lemma MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__helper2 : to_bit_sz (Z.to_nat (12 - 9)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (12 - 9))%Z). { apply Zorder.Zle_minus_le_0. apply MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__Type := Z.
Definition MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__cond := (fun z => (9 <= z <= 12)%Z).
Inductive MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__supported
.
Definition MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__supported
  | _ => MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Type, (MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F2 (MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F1 (MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__supported
.
Definition MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__supported => 0
  end.
Definition MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__supported
  | _ => MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__supported
  end.
Lemma MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Type, (MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F1 x <= 0) /\ MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F2 (MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F2F1 : forall (y : nat) (H : y <= 0), MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F1 (MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n2
 | MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n3
 | MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n4
.
Definition MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n2 => 0
  | MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n3 => 1
  | MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n4 => 2
  end.
Definition MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n2
  | 1 => MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n3
  | 2 => MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n4
  | _ => MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__n2
  end.
Lemma MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Type, (MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F1 x <= 2) /\ MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F2 (MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F2F1 : forall (y : nat) (H : y <= 2), MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F1 (MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext7O__Type : Set :=
  make__MIMO_ParametersPerBand__ext7O__Type {
    MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17 : option MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Type ;
    MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720 : option Z ;
    MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17 : option MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Type ;
    MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17 : option MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Type ;
    MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17 : option MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext7O__list := (
 Opt MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Type MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__cond ::
 Opt Z MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__cond ::
 Opt MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Type MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__cond ::
 Opt MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Type MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__cond ::
 Opt MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Type MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext7O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__cond (MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__cond (MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720 z) /\
  opt_cond MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__cond (MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__cond (MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17 z) /\
  opt_cond MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__cond (MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17 z) /\
  True.

Definition MIMO_ParametersPerBand__ext7__Type := MIMO_ParametersPerBand__ext7O__Type.
Definition MIMO_ParametersPerBand__ext7__cond := MIMO_ParametersPerBand__ext7O__cond.

Inductive MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Type : Set :=
 | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n2
 | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n3
 | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n4
 | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n5
 | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n6
 | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n7
 | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n8
 | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n16
.
Definition MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__cond := (fun (_ : MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Type) => True).
Lemma MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__nat__helper.

Definition MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F1 t :=
  match t with
  | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n2 => 0
  | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n3 => 1
  | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n4 => 2
  | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n5 => 3
  | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n6 => 4
  | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n7 => 5
  | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n8 => 6
  | MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n16 => 7
  end.
Definition MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F2 n :=
  match n with
  | 0 => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n2
  | 1 => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n3
  | 2 => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n4
  | 3 => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n5
  | 4 => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n6
  | 5 => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n7
  | 6 => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n8
  | 7 => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n16
  | _ => MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__n2
  end.
Lemma MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F1F2 : forall x : MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Type, (MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F1 x <= 7) /\ MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F2 (MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F2F1 : forall (y : nat) (H : y <= 7), MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F1 (MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Record MIMO_ParametersPerBand__ext8O__Type : Set :=
  make__MIMO_ParametersPerBand__ext8O__Type {
    MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17 : option MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Type ;
}.
Definition MIMO_ParametersPerBand__ext8O__list := (
 Opt MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Type MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext8O__cond z := 
  opt_cond MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__cond (MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17 z) /\
  True.

Definition MIMO_ParametersPerBand__ext8__Type := MIMO_ParametersPerBand__ext8O__Type.
Definition MIMO_ParametersPerBand__ext8__cond := MIMO_ParametersPerBand__ext8O__cond.

Record MIMO_ParametersPerBand__Type : Set :=
  make__MIMO_ParametersPerBand__Type {
    MIMO_ParametersPerBand__tci_StatePDSCH : option MIMO_ParametersPerBand__tci_StatePDSCH__Type ;
    MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH : option MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Type ;
    MIMO_ParametersPerBand__pusch_TransCoherence : option MIMO_ParametersPerBand__pusch_TransCoherence__Type ;
    MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping : option MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Type ;
    MIMO_ParametersPerBand__periodicBeamReport : option MIMO_ParametersPerBand__periodicBeamReport__Type ;
    MIMO_ParametersPerBand__aperiodicBeamReport : option MIMO_ParametersPerBand__aperiodicBeamReport__Type ;
    MIMO_ParametersPerBand__sp_BeamReportPUCCH : option MIMO_ParametersPerBand__sp_BeamReportPUCCH__Type ;
    MIMO_ParametersPerBand__sp_BeamReportPUSCH : option MIMO_ParametersPerBand__sp_BeamReportPUSCH__Type ;
    MIMO_ParametersPerBand__dummy1 : option DummyG__Type ;
    MIMO_ParametersPerBand__maxNumberRxBeam : option Z ;
    MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL : option MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Type ;
    MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting : option MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Type ;
    MIMO_ParametersPerBand__groupBeamReporting : option MIMO_ParametersPerBand__groupBeamReporting__Type ;
    MIMO_ParametersPerBand__uplinkBeamManagement : option MIMO_ParametersPerBand__uplinkBeamManagement__Type ;
    MIMO_ParametersPerBand__maxNumberCSI_RS_BFD : option Z ;
    MIMO_ParametersPerBand__maxNumberSSB_BFD : option Z ;
    MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD : option Z ;
    MIMO_ParametersPerBand__dummy2 : option MIMO_ParametersPerBand__dummy2__Type ;
    MIMO_ParametersPerBand__twoPortsPTRS_UL : option MIMO_ParametersPerBand__twoPortsPTRS_UL__Type ;
    MIMO_ParametersPerBand__dummy5 : option SRS_Resources__Type ;
    MIMO_ParametersPerBand__dummy3 : option Z ;
    MIMO_ParametersPerBand__beamReportTiming : option MIMO_ParametersPerBand__beamReportTiming__Type ;
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL : option MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Type ;
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL : option MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Type ;
    MIMO_ParametersPerBand__dummy4 : option DummyH__Type ;
    MIMO_ParametersPerBand__aperiodicTRS : option MIMO_ParametersPerBand__aperiodicTRS__Type ;
    MIMO_ParametersPerBand__ext0 : option MIMO_ParametersPerBand__ext0__Type ;
    MIMO_ParametersPerBand__ext1 : option MIMO_ParametersPerBand__ext1__Type ;
    MIMO_ParametersPerBand__ext2 : option MIMO_ParametersPerBand__ext2__Type ;
    MIMO_ParametersPerBand__ext3 : option MIMO_ParametersPerBand__ext3__Type ;
    MIMO_ParametersPerBand__ext4 : option MIMO_ParametersPerBand__ext4__Type ;
    MIMO_ParametersPerBand__ext5 : option MIMO_ParametersPerBand__ext5__Type ;
    MIMO_ParametersPerBand__ext6 : option MIMO_ParametersPerBand__ext6__Type ;
    MIMO_ParametersPerBand__ext7 : option MIMO_ParametersPerBand__ext7__Type ;
    MIMO_ParametersPerBand__ext8 : option MIMO_ParametersPerBand__ext8__Type ;
}.
Definition MIMO_ParametersPerBand__root_list : list seq_elem := (
 Opt MIMO_ParametersPerBand__tci_StatePDSCH__Type MIMO_ParametersPerBand__tci_StatePDSCH__cond ::
 Opt MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Type MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__cond ::
 Opt MIMO_ParametersPerBand__pusch_TransCoherence__Type MIMO_ParametersPerBand__pusch_TransCoherence__cond ::
 Opt MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Type MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__cond ::
 Opt MIMO_ParametersPerBand__periodicBeamReport__Type MIMO_ParametersPerBand__periodicBeamReport__cond ::
 Opt MIMO_ParametersPerBand__aperiodicBeamReport__Type MIMO_ParametersPerBand__aperiodicBeamReport__cond ::
 Opt MIMO_ParametersPerBand__sp_BeamReportPUCCH__Type MIMO_ParametersPerBand__sp_BeamReportPUCCH__cond ::
 Opt MIMO_ParametersPerBand__sp_BeamReportPUSCH__Type MIMO_ParametersPerBand__sp_BeamReportPUSCH__cond ::
 Opt DummyG__Type DummyG__cond ::
 Opt Z MIMO_ParametersPerBand__maxNumberRxBeam__cond ::
 Opt MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond ::
 Opt MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Type MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__cond ::
 Opt MIMO_ParametersPerBand__groupBeamReporting__Type MIMO_ParametersPerBand__groupBeamReporting__cond ::
 Opt MIMO_ParametersPerBand__uplinkBeamManagement__Type MIMO_ParametersPerBand__uplinkBeamManagement__cond ::
 Opt Z MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__cond ::
 Opt Z MIMO_ParametersPerBand__maxNumberSSB_BFD__cond ::
 Opt Z MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__cond ::
 Opt MIMO_ParametersPerBand__dummy2__Type MIMO_ParametersPerBand__dummy2__cond ::
 Opt MIMO_ParametersPerBand__twoPortsPTRS_UL__Type MIMO_ParametersPerBand__twoPortsPTRS_UL__cond ::
 Opt SRS_Resources__Type SRS_Resources__cond ::
 Opt Z MIMO_ParametersPerBand__dummy3__cond ::
 Opt MIMO_ParametersPerBand__beamReportTiming__Type MIMO_ParametersPerBand__beamReportTiming__cond ::
 Opt MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Type MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond ::
 Opt MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Type MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond ::
 Opt DummyH__Type DummyH__cond ::
 Opt MIMO_ParametersPerBand__aperiodicTRS__Type MIMO_ParametersPerBand__aperiodicTRS__cond ::
 nil).
Definition MIMO_ParametersPerBand__ext_list : list typ := (
  typ_cons MIMO_ParametersPerBand__ext0__Type MIMO_ParametersPerBand__ext0__cond ::
  typ_cons MIMO_ParametersPerBand__ext1__Type MIMO_ParametersPerBand__ext1__cond ::
  typ_cons MIMO_ParametersPerBand__ext2__Type MIMO_ParametersPerBand__ext2__cond ::
  typ_cons MIMO_ParametersPerBand__ext3__Type MIMO_ParametersPerBand__ext3__cond ::
  typ_cons MIMO_ParametersPerBand__ext4__Type MIMO_ParametersPerBand__ext4__cond ::
  typ_cons MIMO_ParametersPerBand__ext5__Type MIMO_ParametersPerBand__ext5__cond ::
  typ_cons MIMO_ParametersPerBand__ext6__Type MIMO_ParametersPerBand__ext6__cond ::
  typ_cons MIMO_ParametersPerBand__ext7__Type MIMO_ParametersPerBand__ext7__cond ::
  typ_cons MIMO_ParametersPerBand__ext8__Type MIMO_ParametersPerBand__ext8__cond ::
  nil).
Definition MIMO_ParametersPerBand__cond (z : MIMO_ParametersPerBand__Type) := 
(  opt_cond MIMO_ParametersPerBand__tci_StatePDSCH__cond (MIMO_ParametersPerBand__tci_StatePDSCH z) /\
  opt_cond MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__cond (MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH z) /\
  opt_cond MIMO_ParametersPerBand__pusch_TransCoherence__cond (MIMO_ParametersPerBand__pusch_TransCoherence z) /\
  opt_cond MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__cond (MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping z) /\
  opt_cond MIMO_ParametersPerBand__periodicBeamReport__cond (MIMO_ParametersPerBand__periodicBeamReport z) /\
  opt_cond MIMO_ParametersPerBand__aperiodicBeamReport__cond (MIMO_ParametersPerBand__aperiodicBeamReport z) /\
  opt_cond MIMO_ParametersPerBand__sp_BeamReportPUCCH__cond (MIMO_ParametersPerBand__sp_BeamReportPUCCH z) /\
  opt_cond MIMO_ParametersPerBand__sp_BeamReportPUSCH__cond (MIMO_ParametersPerBand__sp_BeamReportPUSCH z) /\
  opt_cond DummyG__cond (MIMO_ParametersPerBand__dummy1 z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberRxBeam__cond (MIMO_ParametersPerBand__maxNumberRxBeam z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__cond (MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting z) /\
  opt_cond MIMO_ParametersPerBand__groupBeamReporting__cond (MIMO_ParametersPerBand__groupBeamReporting z) /\
  opt_cond MIMO_ParametersPerBand__uplinkBeamManagement__cond (MIMO_ParametersPerBand__uplinkBeamManagement z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__cond (MIMO_ParametersPerBand__maxNumberCSI_RS_BFD z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberSSB_BFD__cond (MIMO_ParametersPerBand__maxNumberSSB_BFD z) /\
  opt_cond MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__cond (MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD z) /\
  opt_cond MIMO_ParametersPerBand__dummy2__cond (MIMO_ParametersPerBand__dummy2 z) /\
  opt_cond MIMO_ParametersPerBand__twoPortsPTRS_UL__cond (MIMO_ParametersPerBand__twoPortsPTRS_UL z) /\
  opt_cond SRS_Resources__cond (MIMO_ParametersPerBand__dummy5 z) /\
  opt_cond MIMO_ParametersPerBand__dummy3__cond (MIMO_ParametersPerBand__dummy3 z) /\
  opt_cond MIMO_ParametersPerBand__beamReportTiming__cond (MIMO_ParametersPerBand__beamReportTiming z) /\
  opt_cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL z) /\
  opt_cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL z) /\
  opt_cond DummyH__cond (MIMO_ParametersPerBand__dummy4 z) /\
  opt_cond MIMO_ParametersPerBand__aperiodicTRS__cond (MIMO_ParametersPerBand__aperiodicTRS z) /\
  True) /\ 
(  opt_cond MIMO_ParametersPerBand__ext0__cond (MIMO_ParametersPerBand__ext0 z) /\
  opt_cond MIMO_ParametersPerBand__ext1__cond (MIMO_ParametersPerBand__ext1 z) /\
  opt_cond MIMO_ParametersPerBand__ext2__cond (MIMO_ParametersPerBand__ext2 z) /\
  opt_cond MIMO_ParametersPerBand__ext3__cond (MIMO_ParametersPerBand__ext3 z) /\
  opt_cond MIMO_ParametersPerBand__ext4__cond (MIMO_ParametersPerBand__ext4 z) /\
  opt_cond MIMO_ParametersPerBand__ext5__cond (MIMO_ParametersPerBand__ext5 z) /\
  opt_cond MIMO_ParametersPerBand__ext6__cond (MIMO_ParametersPerBand__ext6 z) /\
  opt_cond MIMO_ParametersPerBand__ext7__cond (MIMO_ParametersPerBand__ext7 z) /\
  opt_cond MIMO_ParametersPerBand__ext8__cond (MIMO_ParametersPerBand__ext8 z) /\
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
Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Format : T_Format MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__nat__Format MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F1 MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F2 MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F1F2 MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__F2F1.

Opaque MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__cond MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Format.

Definition MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Format : T_Format MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__nat__Format MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F1 MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F2 MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F1F2 MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__F2F1.

Opaque MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__cond MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Format.


Definition MIMO_ParametersPerBand__tci_StatePDSCH__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__tci_StatePDSCH__list.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__Format_list : MIMO_ParametersPerBand__tci_StatePDSCH__Format_Type :=
  (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC__Format, (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP__Format, unit_format)).
Definition MIMO_ParametersPerBand__tci_StatePDSCH__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__tci_StatePDSCH__list MIMO_ParametersPerBand__tci_StatePDSCH__Format_list.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__F1 z :=
  (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberConfiguredTCI_StatesPerCC z, (MIMO_ParametersPerBand__tci_StatePDSCH__maxNumberActiveTCI_PerBWP z, tt)).
Definition MIMO_ParametersPerBand__tci_StatePDSCH__F2 (y : seq_type MIMO_ParametersPerBand__tci_StatePDSCH__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__tci_StatePDSCH__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__F1F2_cond (z : MIMO_ParametersPerBand__tci_StatePDSCH__Type)
  : MIMO_ParametersPerBand__tci_StatePDSCH__cond z ->
  (seq_cond MIMO_ParametersPerBand__tci_StatePDSCH__list (MIMO_ParametersPerBand__tci_StatePDSCH__F1 z)).
intro H. unfold MIMO_ParametersPerBand__tci_StatePDSCH__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__F1F2_cond2 (z : MIMO_ParametersPerBand__tci_StatePDSCH__Type)
 : MIMO_ParametersPerBand__tci_StatePDSCH__F2 (MIMO_ParametersPerBand__tci_StatePDSCH__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__tci_StatePDSCH__F2F1_cond (y : seq_type MIMO_ParametersPerBand__tci_StatePDSCH__list)
  : seq_cond MIMO_ParametersPerBand__tci_StatePDSCH__list y ->
 (MIMO_ParametersPerBand__tci_StatePDSCH__cond (MIMO_ParametersPerBand__tci_StatePDSCH__F2 y)) /\  MIMO_ParametersPerBand__tci_StatePDSCH__F1 (MIMO_ParametersPerBand__tci_StatePDSCH__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__tci_StatePDSCH__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__tci_StatePDSCH__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__tci_StatePDSCH__Format : T_Format MIMO_ParametersPerBand__tci_StatePDSCH__Type MIMO_ParametersPerBand__tci_StatePDSCH__cond :=
        proj2_format  MIMO_ParametersPerBand__tci_StatePDSCH__cond MIMO_ParametersPerBand__tci_StatePDSCH__list__Format
    MIMO_ParametersPerBand__tci_StatePDSCH__F1 MIMO_ParametersPerBand__tci_StatePDSCH__F2 MIMO_ParametersPerBand__tci_StatePDSCH__F1F2_cond  MIMO_ParametersPerBand__tci_StatePDSCH__F1F2_cond2 MIMO_ParametersPerBand__tci_StatePDSCH__F2F1_cond.
Opaque MIMO_ParametersPerBand__tci_StatePDSCH__cond MIMO_ParametersPerBand__tci_StatePDSCH__Format.

Definition MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Format : T_Format MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__nat__Format MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F1 MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F2 MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F1F2 MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__F2F1.

Opaque MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__cond MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Format.

Definition MIMO_ParametersPerBand__pusch_TransCoherence__Format : T_Format MIMO_ParametersPerBand__pusch_TransCoherence__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__pusch_TransCoherence__nat__Format MIMO_ParametersPerBand__pusch_TransCoherence__F1 MIMO_ParametersPerBand__pusch_TransCoherence__F2 MIMO_ParametersPerBand__pusch_TransCoherence__F1F2 MIMO_ParametersPerBand__pusch_TransCoherence__F2F1.

Opaque MIMO_ParametersPerBand__pusch_TransCoherence__cond MIMO_ParametersPerBand__pusch_TransCoherence__Format.

Definition MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Format : T_Format MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__nat__Format MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F1 MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F2 MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F1F2 MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__F2F1.

Opaque MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__cond MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Format.

Definition MIMO_ParametersPerBand__periodicBeamReport__Format : T_Format MIMO_ParametersPerBand__periodicBeamReport__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__periodicBeamReport__nat__Format MIMO_ParametersPerBand__periodicBeamReport__F1 MIMO_ParametersPerBand__periodicBeamReport__F2 MIMO_ParametersPerBand__periodicBeamReport__F1F2 MIMO_ParametersPerBand__periodicBeamReport__F2F1.

Opaque MIMO_ParametersPerBand__periodicBeamReport__cond MIMO_ParametersPerBand__periodicBeamReport__Format.

Definition MIMO_ParametersPerBand__aperiodicBeamReport__Format : T_Format MIMO_ParametersPerBand__aperiodicBeamReport__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__aperiodicBeamReport__nat__Format MIMO_ParametersPerBand__aperiodicBeamReport__F1 MIMO_ParametersPerBand__aperiodicBeamReport__F2 MIMO_ParametersPerBand__aperiodicBeamReport__F1F2 MIMO_ParametersPerBand__aperiodicBeamReport__F2F1.

Opaque MIMO_ParametersPerBand__aperiodicBeamReport__cond MIMO_ParametersPerBand__aperiodicBeamReport__Format.

Definition MIMO_ParametersPerBand__sp_BeamReportPUCCH__Format : T_Format MIMO_ParametersPerBand__sp_BeamReportPUCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__sp_BeamReportPUCCH__nat__Format MIMO_ParametersPerBand__sp_BeamReportPUCCH__F1 MIMO_ParametersPerBand__sp_BeamReportPUCCH__F2 MIMO_ParametersPerBand__sp_BeamReportPUCCH__F1F2 MIMO_ParametersPerBand__sp_BeamReportPUCCH__F2F1.

Opaque MIMO_ParametersPerBand__sp_BeamReportPUCCH__cond MIMO_ParametersPerBand__sp_BeamReportPUCCH__Format.

Definition MIMO_ParametersPerBand__sp_BeamReportPUSCH__Format : T_Format MIMO_ParametersPerBand__sp_BeamReportPUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__sp_BeamReportPUSCH__nat__Format MIMO_ParametersPerBand__sp_BeamReportPUSCH__F1 MIMO_ParametersPerBand__sp_BeamReportPUSCH__F2 MIMO_ParametersPerBand__sp_BeamReportPUSCH__F1F2 MIMO_ParametersPerBand__sp_BeamReportPUSCH__F2F1.

Opaque MIMO_ParametersPerBand__sp_BeamReportPUSCH__cond MIMO_ParametersPerBand__sp_BeamReportPUSCH__Format.

Definition MIMO_ParametersPerBand__maxNumberRxBeam__Format : T_Format Z MIMO_ParametersPerBand__maxNumberRxBeam__cond :=
 ranged_int_format (2) (8) MIMO_ParametersPerBand__maxNumberRxBeam__helper1 MIMO_ParametersPerBand__maxNumberRxBeam__helper2.

Opaque MIMO_ParametersPerBand__maxNumberRxBeam__cond MIMO_ParametersPerBand__maxNumberRxBeam__Format.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Format : T_Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__nat__Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F1 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F1F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__F2F1.

Opaque MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Format.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Format : T_Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__nat__Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F1 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F1F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__F2F1.

Opaque MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Format.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Format : T_Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__nat__Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F1 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F1F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__F2F1.

Opaque MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Format.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Format : T_Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__nat__Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F1 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F1F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__F2F1.

Opaque MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Format.

Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Format : T_Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__nat__Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F1 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F1F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__F2F1.

Opaque MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Format.


Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Format_list : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Format_Type :=
  (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz__Format, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz__Format, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz__Format, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz__Format, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz__Format, unit_format))))).
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Format_list.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1 z :=
  (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_15kHz z, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_30kHz z, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_60kHz z, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_120kHz z, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__scs_240kHz z, tt))))).
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F2 (y : seq_type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Type i0 i1 i2 i3 i4
  end.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1F2_cond (z : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Type)
  : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond z ->
  (seq_cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1 z)).
intro H. unfold MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1F2_cond2 (z : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Type)
 : MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F2 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F2F1_cond (y : seq_type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list)
  : seq_cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list y ->
 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F2 y)) /\  MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1 (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Format : T_Format MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Type MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond :=
        proj2_format  MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__list__Format
    MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1F2_cond  MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F1F2_cond2 MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__F2F1_cond.
Opaque MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__cond MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Format.

Definition MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Format : T_Format MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__nat__Format MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F1 MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F2 MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F1F2 MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__F2F1.

Opaque MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__cond MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Format.

Definition MIMO_ParametersPerBand__groupBeamReporting__Format : T_Format MIMO_ParametersPerBand__groupBeamReporting__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__groupBeamReporting__nat__Format MIMO_ParametersPerBand__groupBeamReporting__F1 MIMO_ParametersPerBand__groupBeamReporting__F2 MIMO_ParametersPerBand__groupBeamReporting__F1F2 MIMO_ParametersPerBand__groupBeamReporting__F2F1.

Opaque MIMO_ParametersPerBand__groupBeamReporting__cond MIMO_ParametersPerBand__groupBeamReporting__Format.

Definition MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Format : T_Format MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__nat__Format MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F1 MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F2 MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F1F2 MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__F2F1.

Opaque MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__cond MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Format.

Definition MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__Format : T_Format Z MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__cond :=
 ranged_int_format (1) (8) MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__helper1 MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__helper2.

Opaque MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__cond MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__Format.


Definition MIMO_ParametersPerBand__uplinkBeamManagement__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__uplinkBeamManagement__list.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__Format_list : MIMO_ParametersPerBand__uplinkBeamManagement__Format_Type :=
  (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM__Format, (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet__Format, unit_format)).
Definition MIMO_ParametersPerBand__uplinkBeamManagement__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__uplinkBeamManagement__list MIMO_ParametersPerBand__uplinkBeamManagement__Format_list.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__F1 z :=
  (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourcePerSet_BM z, (MIMO_ParametersPerBand__uplinkBeamManagement__maxNumberSRS_ResourceSet z, tt)).
Definition MIMO_ParametersPerBand__uplinkBeamManagement__F2 (y : seq_type MIMO_ParametersPerBand__uplinkBeamManagement__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__uplinkBeamManagement__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__uplinkBeamManagement__F1F2_cond (z : MIMO_ParametersPerBand__uplinkBeamManagement__Type)
  : MIMO_ParametersPerBand__uplinkBeamManagement__cond z ->
  (seq_cond MIMO_ParametersPerBand__uplinkBeamManagement__list (MIMO_ParametersPerBand__uplinkBeamManagement__F1 z)).
intro H. unfold MIMO_ParametersPerBand__uplinkBeamManagement__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__uplinkBeamManagement__F1F2_cond2 (z : MIMO_ParametersPerBand__uplinkBeamManagement__Type)
 : MIMO_ParametersPerBand__uplinkBeamManagement__F2 (MIMO_ParametersPerBand__uplinkBeamManagement__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__uplinkBeamManagement__F2F1_cond (y : seq_type MIMO_ParametersPerBand__uplinkBeamManagement__list)
  : seq_cond MIMO_ParametersPerBand__uplinkBeamManagement__list y ->
 (MIMO_ParametersPerBand__uplinkBeamManagement__cond (MIMO_ParametersPerBand__uplinkBeamManagement__F2 y)) /\  MIMO_ParametersPerBand__uplinkBeamManagement__F1 (MIMO_ParametersPerBand__uplinkBeamManagement__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__uplinkBeamManagement__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__uplinkBeamManagement__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__uplinkBeamManagement__Format : T_Format MIMO_ParametersPerBand__uplinkBeamManagement__Type MIMO_ParametersPerBand__uplinkBeamManagement__cond :=
        proj2_format  MIMO_ParametersPerBand__uplinkBeamManagement__cond MIMO_ParametersPerBand__uplinkBeamManagement__list__Format
    MIMO_ParametersPerBand__uplinkBeamManagement__F1 MIMO_ParametersPerBand__uplinkBeamManagement__F2 MIMO_ParametersPerBand__uplinkBeamManagement__F1F2_cond  MIMO_ParametersPerBand__uplinkBeamManagement__F1F2_cond2 MIMO_ParametersPerBand__uplinkBeamManagement__F2F1_cond.
Opaque MIMO_ParametersPerBand__uplinkBeamManagement__cond MIMO_ParametersPerBand__uplinkBeamManagement__Format.

Definition MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__Format : T_Format Z MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__cond :=
 ranged_int_format (1) (64) MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__helper1 MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__helper2.

Opaque MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__cond MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__Format.

Definition MIMO_ParametersPerBand__maxNumberSSB_BFD__Format : T_Format Z MIMO_ParametersPerBand__maxNumberSSB_BFD__cond :=
 ranged_int_format (1) (64) MIMO_ParametersPerBand__maxNumberSSB_BFD__helper1 MIMO_ParametersPerBand__maxNumberSSB_BFD__helper2.

Opaque MIMO_ParametersPerBand__maxNumberSSB_BFD__cond MIMO_ParametersPerBand__maxNumberSSB_BFD__Format.

Definition MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__Format : T_Format Z MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__cond :=
 ranged_int_format (1) (256) MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__helper1 MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__helper2.

Opaque MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__cond MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__Format.

Definition MIMO_ParametersPerBand__dummy2__Format : T_Format MIMO_ParametersPerBand__dummy2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__dummy2__nat__Format MIMO_ParametersPerBand__dummy2__F1 MIMO_ParametersPerBand__dummy2__F2 MIMO_ParametersPerBand__dummy2__F1F2 MIMO_ParametersPerBand__dummy2__F2F1.

Opaque MIMO_ParametersPerBand__dummy2__cond MIMO_ParametersPerBand__dummy2__Format.

Definition MIMO_ParametersPerBand__twoPortsPTRS_UL__Format : T_Format MIMO_ParametersPerBand__twoPortsPTRS_UL__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__twoPortsPTRS_UL__nat__Format MIMO_ParametersPerBand__twoPortsPTRS_UL__F1 MIMO_ParametersPerBand__twoPortsPTRS_UL__F2 MIMO_ParametersPerBand__twoPortsPTRS_UL__F1F2 MIMO_ParametersPerBand__twoPortsPTRS_UL__F2F1.

Opaque MIMO_ParametersPerBand__twoPortsPTRS_UL__cond MIMO_ParametersPerBand__twoPortsPTRS_UL__Format.

Definition MIMO_ParametersPerBand__dummy3__Format : T_Format Z MIMO_ParametersPerBand__dummy3__cond :=
 ranged_int_format (1) (4) MIMO_ParametersPerBand__dummy3__helper1 MIMO_ParametersPerBand__dummy3__helper2.

Opaque MIMO_ParametersPerBand__dummy3__cond MIMO_ParametersPerBand__dummy3__Format.

Definition MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Format : T_Format MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__nat__Format MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F1 MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F2 MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F1F2 MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__F2F1.

Opaque MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__cond MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Format.

Definition MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Format : T_Format MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__nat__Format MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F1 MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F2 MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F1F2 MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__F2F1.

Opaque MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__cond MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Format.

Definition MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Format : T_Format MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__nat__Format MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F1 MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F2 MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F1F2 MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__F2F1.

Opaque MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__cond MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Format.

Definition MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Format : T_Format MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__nat__Format MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F1 MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F2 MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F1F2 MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__F2F1.

Opaque MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__cond MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Format.


Definition MIMO_ParametersPerBand__beamReportTiming__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__beamReportTiming__list.
Definition MIMO_ParametersPerBand__beamReportTiming__Format_list : MIMO_ParametersPerBand__beamReportTiming__Format_Type :=
  (MIMO_ParametersPerBand__beamReportTiming__scs_15kHz__Format, (MIMO_ParametersPerBand__beamReportTiming__scs_30kHz__Format, (MIMO_ParametersPerBand__beamReportTiming__scs_60kHz__Format, (MIMO_ParametersPerBand__beamReportTiming__scs_120kHz__Format, unit_format)))).
Definition MIMO_ParametersPerBand__beamReportTiming__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__beamReportTiming__list MIMO_ParametersPerBand__beamReportTiming__Format_list.
Definition MIMO_ParametersPerBand__beamReportTiming__F1 z :=
  (MIMO_ParametersPerBand__beamReportTiming__scs_15kHz z, (MIMO_ParametersPerBand__beamReportTiming__scs_30kHz z, (MIMO_ParametersPerBand__beamReportTiming__scs_60kHz z, (MIMO_ParametersPerBand__beamReportTiming__scs_120kHz z, tt)))).
Definition MIMO_ParametersPerBand__beamReportTiming__F2 (y : seq_type MIMO_ParametersPerBand__beamReportTiming__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MIMO_ParametersPerBand__beamReportTiming__Type i0 i1 i2 i3
  end.
Lemma MIMO_ParametersPerBand__beamReportTiming__F1F2_cond (z : MIMO_ParametersPerBand__beamReportTiming__Type)
  : MIMO_ParametersPerBand__beamReportTiming__cond z ->
  (seq_cond MIMO_ParametersPerBand__beamReportTiming__list (MIMO_ParametersPerBand__beamReportTiming__F1 z)).
intro H. unfold MIMO_ParametersPerBand__beamReportTiming__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__beamReportTiming__F1F2_cond2 (z : MIMO_ParametersPerBand__beamReportTiming__Type)
 : MIMO_ParametersPerBand__beamReportTiming__F2 (MIMO_ParametersPerBand__beamReportTiming__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__beamReportTiming__F2F1_cond (y : seq_type MIMO_ParametersPerBand__beamReportTiming__list)
  : seq_cond MIMO_ParametersPerBand__beamReportTiming__list y ->
 (MIMO_ParametersPerBand__beamReportTiming__cond (MIMO_ParametersPerBand__beamReportTiming__F2 y)) /\  MIMO_ParametersPerBand__beamReportTiming__F1 (MIMO_ParametersPerBand__beamReportTiming__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__beamReportTiming__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__beamReportTiming__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__beamReportTiming__Format : T_Format MIMO_ParametersPerBand__beamReportTiming__Type MIMO_ParametersPerBand__beamReportTiming__cond :=
        proj2_format  MIMO_ParametersPerBand__beamReportTiming__cond MIMO_ParametersPerBand__beamReportTiming__list__Format
    MIMO_ParametersPerBand__beamReportTiming__F1 MIMO_ParametersPerBand__beamReportTiming__F2 MIMO_ParametersPerBand__beamReportTiming__F1F2_cond  MIMO_ParametersPerBand__beamReportTiming__F1F2_cond2 MIMO_ParametersPerBand__beamReportTiming__F2F1_cond.
Opaque MIMO_ParametersPerBand__beamReportTiming__cond MIMO_ParametersPerBand__beamReportTiming__Format.


Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list.
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Format_list : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Format_Type :=
  (PTRS_DensityRecommendationDL__Format, (PTRS_DensityRecommendationDL__Format, (PTRS_DensityRecommendationDL__Format, (PTRS_DensityRecommendationDL__Format, unit_format)))).
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Format_list.
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1 z :=
  (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_15kHz z, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_30kHz z, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_60kHz z, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__scs_120kHz z, tt)))).
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F2 (y : seq_type MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Type i0 i1 i2 i3
  end.
Lemma MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1F2_cond (z : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Type)
  : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond z ->
  (seq_cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1F2_cond2 (z : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Type)
 : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F2 (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list)
  : seq_cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list y ->
 (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F2 y)) /\  MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1 (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Format : T_Format MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Type MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond :=
        proj2_format  MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__list__Format
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1 MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F2 MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1F2_cond  MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F1F2_cond2 MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__F2F1_cond.
Opaque MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Format.


Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list.
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Format_list : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Format_Type :=
  (PTRS_DensityRecommendationUL__Format, (PTRS_DensityRecommendationUL__Format, (PTRS_DensityRecommendationUL__Format, (PTRS_DensityRecommendationUL__Format, unit_format)))).
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Format_list.
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1 z :=
  (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_15kHz z, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_30kHz z, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_60kHz z, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__scs_120kHz z, tt)))).
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F2 (y : seq_type MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Type i0 i1 i2 i3
  end.
Lemma MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1F2_cond (z : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Type)
  : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond z ->
  (seq_cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1F2_cond2 (z : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Type)
 : MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F2 (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list)
  : seq_cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list y ->
 (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F2 y)) /\  MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1 (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Format : T_Format MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Type MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond :=
        proj2_format  MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__list__Format
    MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1 MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F2 MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1F2_cond  MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F1F2_cond2 MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__F2F1_cond.
Opaque MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__cond MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Format.

Definition MIMO_ParametersPerBand__aperiodicTRS__Format : T_Format MIMO_ParametersPerBand__aperiodicTRS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__aperiodicTRS__nat__Format MIMO_ParametersPerBand__aperiodicTRS__F1 MIMO_ParametersPerBand__aperiodicTRS__F2 MIMO_ParametersPerBand__aperiodicTRS__F1F2 MIMO_ParametersPerBand__aperiodicTRS__F2F1.

Opaque MIMO_ParametersPerBand__aperiodicTRS__cond MIMO_ParametersPerBand__aperiodicTRS__Format.

Definition MIMO_ParametersPerBand__ext0O__dummy6__Format : T_Format MIMO_ParametersPerBand__ext0O__dummy6__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext0O__dummy6__nat__Format MIMO_ParametersPerBand__ext0O__dummy6__F1 MIMO_ParametersPerBand__ext0O__dummy6__F2 MIMO_ParametersPerBand__ext0O__dummy6__F1F2 MIMO_ParametersPerBand__ext0O__dummy6__F2F1.

Opaque MIMO_ParametersPerBand__ext0O__dummy6__cond MIMO_ParametersPerBand__ext0O__dummy6__Format.

Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Format : T_Format MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__nat__Format MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F1 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F2 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F1F2 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__F2F1.

Opaque MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Format.

Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Format : T_Format MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__nat__Format MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F1 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F2 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F1F2 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__F2F1.

Opaque MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Format.


Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Format_list : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Format_Type :=
  (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz__Format, (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Format_list.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1 z :=
  (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_60kHz z, (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__scs_120kHz z, tt)).
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F2 (y : seq_type MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1F2_cond (z : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Type)
  : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1F2_cond2 (z : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Type)
 : MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F2 (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list)
  : seq_cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list y ->
 (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F2 y)) /\  MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1 (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Format : T_Format MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Type MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond :=
        proj2_format  MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__list__Format
    MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F2 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1F2_cond  MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F1F2_cond2 MIMO_ParametersPerBand__ext0O__beamSwitchTiming__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext0O__beamSwitchTiming__cond MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Format.

Definition MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__Format : T_Format MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__Type MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__cond := seq_of_format SupportedCSI_RS_Resource__Format 1 maxNrofCSI_RS_Resources MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__helper1 MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__helper2.

Opaque MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__cond MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__Format.


Definition MIMO_ParametersPerBand__ext0O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext0O__list.
Definition MIMO_ParametersPerBand__ext0O__Format_list : MIMO_ParametersPerBand__ext0O__Format_Type :=
  (MIMO_ParametersPerBand__ext0O__dummy6__Format, (BeamManagementSSB_CSI_RS__Format, (MIMO_ParametersPerBand__ext0O__beamSwitchTiming__Format, (CodebookParameters__Format, (CSI_RS_IM_ReceptionForFeedback__Format, (CSI_RS_ProcFrameworkForSRS__Format, (CSI_ReportFramework__Format, (CSI_RS_ForTracking__Format, (MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS__Format, (SpatialRelations__Format, unit_format)))))))))).
Definition MIMO_ParametersPerBand__ext0O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext0O__list MIMO_ParametersPerBand__ext0O__Format_list.
Definition MIMO_ParametersPerBand__ext0O__F1 z :=
  (MIMO_ParametersPerBand__ext0O__dummy6 z, (MIMO_ParametersPerBand__ext0O__beamManagementSSB_CSI_RS z, (MIMO_ParametersPerBand__ext0O__beamSwitchTiming z, (MIMO_ParametersPerBand__ext0O__codebookParameters z, (MIMO_ParametersPerBand__ext0O__csi_RS_IM_ReceptionForFeedback z, (MIMO_ParametersPerBand__ext0O__csi_RS_ProcFrameworkForSRS z, (MIMO_ParametersPerBand__ext0O__csi_ReportFramework z, (MIMO_ParametersPerBand__ext0O__csi_RS_ForTracking z, (MIMO_ParametersPerBand__ext0O__srs_AssocCSI_RS z, (MIMO_ParametersPerBand__ext0O__spatialRelations z, tt)))))))))).
Definition MIMO_ParametersPerBand__ext0O__F2 (y : seq_type MIMO_ParametersPerBand__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, _))))))))))=>
    make__MIMO_ParametersPerBand__ext0O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9
  end.
Lemma MIMO_ParametersPerBand__ext0O__F1F2_cond (z : MIMO_ParametersPerBand__ext0O__Type)
  : MIMO_ParametersPerBand__ext0O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext0O__list (MIMO_ParametersPerBand__ext0O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext0O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext0O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext0O__Type)
 : MIMO_ParametersPerBand__ext0O__F2 (MIMO_ParametersPerBand__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext0O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext0O__list)
  : seq_cond MIMO_ParametersPerBand__ext0O__list y ->
 (MIMO_ParametersPerBand__ext0O__cond (MIMO_ParametersPerBand__ext0O__F2 y)) /\  MIMO_ParametersPerBand__ext0O__F1 (MIMO_ParametersPerBand__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext0O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext0O__Format : T_Format MIMO_ParametersPerBand__ext0O__Type MIMO_ParametersPerBand__ext0O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext0O__cond MIMO_ParametersPerBand__ext0O__list__Format
    MIMO_ParametersPerBand__ext0O__F1 MIMO_ParametersPerBand__ext0O__F2 MIMO_ParametersPerBand__ext0O__F1F2_cond  MIMO_ParametersPerBand__ext0O__F1F2_cond2 MIMO_ParametersPerBand__ext0O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext0O__cond MIMO_ParametersPerBand__ext0O__Format.

Definition MIMO_ParametersPerBand__ext0__check_all_none (b : MIMO_ParametersPerBand__ext0O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext0O__Type None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext0__Format : T_Format MIMO_ParametersPerBand__ext0__Type MIMO_ParametersPerBand__ext0__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext0__check_all_none MIMO_ParametersPerBand__ext0O__Format.

Opaque MIMO_ParametersPerBand__ext0__cond MIMO_ParametersPerBand__ext0__Format.

Definition MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__nat__Format MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F1 MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F2 MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F1F2 MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__cond MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__nat__Format MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F1 MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F2 MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F1F2 MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__cond MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__nat__Format MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F1 MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F2 MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F1F2 MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__cond MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__nat__Format MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F1 MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F2 MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F1F2 MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__cond MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__nat__Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F1F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__nat__Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F1F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__nat__Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F1F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__nat__Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F1F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__nat__Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F1F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__nat__Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F1F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__nat__Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F1F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__nat__Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F1F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Format.


Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Format_list : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Format_Type :=
  (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16__Format, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16__Format, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16__Format, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16__Format, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16__Format, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16__Format, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16__Format, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16__Format, unit_format)))))))).
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Format_list.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1 z :=
  (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_OneTx_CMR_r16 z, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_r16 z, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSIRS_2Tx_res_r16 z, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberSSB_CSIRS_res_r16 z, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberCSI_IM_NZP_IMR_res_mem_r16 z, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedCSI_RS_Density_CMR_r16 z, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__maxNumberAperiodicCSI_RS_Res_r16 z, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__supportedSINR_meas_r16 z, tt)))))))).
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F2 (y : seq_type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1F2_cond (z : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Type)
  : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1F2_cond2 (z : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Type)
 : MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F2 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list)
  : seq_cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list y ->
 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F2 y)) /\  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1 (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Type MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond :=
        proj2_format  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__list__Format
    MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1F2_cond  MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F1F2_cond2 MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__cond MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__nat__Format MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F1 MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F2 MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F1F2 MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__cond MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__nat__Format MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F1 MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F2 MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F1F2 MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__cond MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__Format : T_Format Z MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__cond :=
 ranged_int_format (1) (2) MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__helper1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__helper2.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__nat__Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F1F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__nat__Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F1F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__nat__Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F1F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Format.


Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Format_list : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Format_Type :=
  (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Format_list.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1 z :=
  (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDCCH_ToPDSCH_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__supportPDSCH_ToHARQ_ACK_r16 z, tt)).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F2 (y : seq_type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1F2_cond (z : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Type)
  : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1F2_cond2 (z : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Type)
 : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list)
  : seq_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list y ->
 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F2 y)) /\  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond :=
        proj2_format  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__list__Format
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1F2_cond  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F1F2_cond2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__nat__Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F1F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__nat__Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F1F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__nat__Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F1F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__nat__Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F1F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__nat__Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F1F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Format.


Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Format_list : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Format_Type :=
  (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Format_list.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1 z :=
  (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxNumberPerCORESET_Pool_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__maxTotalNumberAcrossCORESET_Pool_r16 z, tt)).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F2 (y : seq_type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1F2_cond (z : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Type)
  : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1F2_cond2 (z : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Type)
 : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list)
  : seq_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list y ->
 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F2 y)) /\  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond :=
        proj2_format  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__list__Format
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1F2_cond  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F1F2_cond2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Format.


Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Format_list : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Format_Type :=
  (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16__Format, unit_format))))))).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Format_list.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1 z :=
  (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsFullyFreqTime_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__overlapPDSCHsInTimePartiallyFreq_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationDL_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__outOfOrderOperationUL_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__separateCRS_RateMatching_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__defaultQCL_PerCORESETPoolIndex_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__maxNumberActivatedTCI_States_r16 z, tt))))))).
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F2 (y : seq_type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1F2_cond (z : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Type)
  : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1F2_cond2 (z : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Type)
 : MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F2 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list)
  : seq_cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list y ->
 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F2 y)) /\  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1 (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Type MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond :=
        proj2_format  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__list__Format
    MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1F2_cond  MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F1F2_cond2 MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__cond MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__nat__Format MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F1 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F2 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F1F2 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__nat__Format MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F1 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F2 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F1F2 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Format.


Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Format_list : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Format_Type :=
  (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16__Format, (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Format_list.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1 z :=
  (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportNewDMRS_Port_r16 z, (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__supportTwoPortDL_PTRS_r16 z, tt)).
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F2 (y : seq_type MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1F2_cond (z : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Type)
  : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1F2_cond2 (z : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Type)
 : MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F2 (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list)
  : seq_cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list y ->
 (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F2 y)) /\  MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1 (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Type MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond :=
        proj2_format  MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__list__Format
    MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F2 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1F2_cond  MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F1F2_cond2 MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__cond MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__nat__Format MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F1 MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F2 MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F1F2 MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__cond MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__nat__Format MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F1 MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F2 MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F1F2 MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__cond MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__nat__Format MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F1 MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F2 MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F1F2 MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__cond MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__nat__Format MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F1 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F2 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F1F2 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__cond MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__nat__Format MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F1 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F2 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F1F2 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__cond MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__Format : T_Format Z MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__cond :=
 ranged_int_format (1) (2) MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__helper1 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__helper2.

Opaque MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__cond MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__Format.


Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Format_list : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Format_Type :=
  (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16__Format, (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16__Format, (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16__Format, unit_format))).
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Format_list.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1 z :=
  (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__supportRepNumPDSCH_TDRA_r16 z, (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxTBS_Size_r16 z, (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__maxNumberTCI_states_r16 z, tt))).
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F2 (y : seq_type MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Type i0 i1 i2
  end.
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1F2_cond (z : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Type)
  : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1F2_cond2 (z : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Type)
 : MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F2 (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list)
  : seq_cond MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list y ->
 (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F2 y)) /\  MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1 (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Type MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond :=
        proj2_format  MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__list__Format
    MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F2 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1F2_cond  MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F1F2_cond2 MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__cond MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__nat__Format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F1 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F2 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F1F2 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__cond MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__nat__Format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F1 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F2 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F1F2 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__cond MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__nat__Format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F1 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F2 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F1F2 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__cond MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__nat__Format MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F1 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F2 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F1F2 MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__cond MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__nat__Format MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F1 MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F2 MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F1F2 MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__cond MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__nat__Format MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F1 MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F2 MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F1F2 MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__cond MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__nat__Format MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F1 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F2 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F1F2 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Format.

Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__nat__Format MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F1 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F2 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F1F2 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Format.


Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Format_list : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Format_Type :=
  (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16__Format, (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Format_list.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1 z :=
  (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_60kHz_r16 z, (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__scs_120kHz_r16 z, tt)).
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F2 (y : seq_type MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1F2_cond (z : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Type)
  : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1F2_cond2 (z : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Type)
 : MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F2 (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list)
  : seq_cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list y ->
 (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F2 y)) /\  MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1 (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Format : T_Format MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Type MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond :=
        proj2_format  MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__list__Format
    MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F2 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1F2_cond  MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F1F2_cond2 MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__cond MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Format.


Definition MIMO_ParametersPerBand__ext1O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext1O__list.
Definition MIMO_ParametersPerBand__ext1O__Format_list : MIMO_ParametersPerBand__ext1O__Format_Type :=
  (MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16__Format, (CodebookParameters_v1610__Format, (MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16__Format, (MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16__Format, (MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16__Format, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16__Format, (MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16__Format, (MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16__Format, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16__Format, (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16__Format, (MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16__Format, (MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16__Format, (MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16__Format, (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16__Format, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16__Format, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16__Format, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16__Format, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16__Format, (CSI_ReportFrameworkExt_r16__Format, (CodebookParametersAddition_r16__Format, (CodebookComboParametersAddition_r16__Format, (MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16__Format, (MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16__Format, (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16__Format, unit_format)))))))))))))))))))))))).
Definition MIMO_ParametersPerBand__ext1O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext1O__list MIMO_ParametersPerBand__ext1O__Format_list.
Definition MIMO_ParametersPerBand__ext1O__F1 z :=
  (MIMO_ParametersPerBand__ext1O__defaultQCL_TwoTCI_r16 z, (MIMO_ParametersPerBand__ext1O__codebookParametersPerBand_r16 z, (MIMO_ParametersPerBand__ext1O__simul_SpatialRelationUpdatePUCCHResGroup_r16 z, (MIMO_ParametersPerBand__ext1O__maxNumberSCellBFR_r16 z, (MIMO_ParametersPerBand__ext1O__simultaneousReceptionDiffTypeD_r16 z, (MIMO_ParametersPerBand__ext1O__ssb_csirs_SINR_measurement_r16 z, (MIMO_ParametersPerBand__ext1O__nonGroupSINR_reporting_r16 z, (MIMO_ParametersPerBand__ext1O__groupSINR_reporting_r16 z, (MIMO_ParametersPerBand__ext1O__multiDCI_multiTRP_Parameters_r16 z, (MIMO_ParametersPerBand__ext1O__singleDCI_SDM_scheme_Parameters_r16 z, (MIMO_ParametersPerBand__ext1O__supportFDM_SchemeA_r16 z, (MIMO_ParametersPerBand__ext1O__supportCodeWordSoftCombining_r16 z, (MIMO_ParametersPerBand__ext1O__supportTDM_SchemeA_r16 z, (MIMO_ParametersPerBand__ext1O__supportInter_slotTDM_r16 z, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PDSCH_r16 z, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithoutPrecoding_r16 z, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUCCH_r16 z, (MIMO_ParametersPerBand__ext1O__lowPAPR_DMRS_PUSCHwithPrecoding_r16 z, (MIMO_ParametersPerBand__ext1O__csi_ReportFrameworkExt_r16 z, (MIMO_ParametersPerBand__ext1O__codebookParametersAddition_r16 z, (MIMO_ParametersPerBand__ext1O__codebookComboParametersAddition_r16 z, (MIMO_ParametersPerBand__ext1O__beamCorrespondenceSSB_based_r16 z, (MIMO_ParametersPerBand__ext1O__beamCorrespondenceCSI_RS_based_r16 z, (MIMO_ParametersPerBand__ext1O__beamSwitchTiming_r16 z, tt)))))))))))))))))))))))).
Definition MIMO_ParametersPerBand__ext1O__F2 (y : seq_type MIMO_ParametersPerBand__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, _))))))))))))))))))))))))=>
    make__MIMO_ParametersPerBand__ext1O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23
  end.
Lemma MIMO_ParametersPerBand__ext1O__F1F2_cond (z : MIMO_ParametersPerBand__ext1O__Type)
  : MIMO_ParametersPerBand__ext1O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext1O__list (MIMO_ParametersPerBand__ext1O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext1O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext1O__Type)
 : MIMO_ParametersPerBand__ext1O__F2 (MIMO_ParametersPerBand__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext1O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext1O__list)
  : seq_cond MIMO_ParametersPerBand__ext1O__list y ->
 (MIMO_ParametersPerBand__ext1O__cond (MIMO_ParametersPerBand__ext1O__F2 y)) /\  MIMO_ParametersPerBand__ext1O__F1 (MIMO_ParametersPerBand__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext1O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext1O__Format : T_Format MIMO_ParametersPerBand__ext1O__Type MIMO_ParametersPerBand__ext1O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext1O__cond MIMO_ParametersPerBand__ext1O__list__Format
    MIMO_ParametersPerBand__ext1O__F1 MIMO_ParametersPerBand__ext1O__F2 MIMO_ParametersPerBand__ext1O__F1F2_cond  MIMO_ParametersPerBand__ext1O__F1F2_cond2 MIMO_ParametersPerBand__ext1O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext1O__cond MIMO_ParametersPerBand__ext1O__Format.

Definition MIMO_ParametersPerBand__ext1__check_all_none (b : MIMO_ParametersPerBand__ext1O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext1O__Type None None None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext1__Format : T_Format MIMO_ParametersPerBand__ext1__Type MIMO_ParametersPerBand__ext1__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext1__check_all_none MIMO_ParametersPerBand__ext1O__Format.

Opaque MIMO_ParametersPerBand__ext1__cond MIMO_ParametersPerBand__ext1__Format.

Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Format : T_Format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__nat__Format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F1 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F2 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F1F2 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Format.

Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Format : T_Format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__nat__Format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F1 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F2 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F1F2 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Format.


Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Format_list : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Format_Type :=
  (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16__Format, (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Format_list.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1 z :=
  (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat1_2OFDM_syms_r16 z, (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__supportReportFormat4_14OFDM_syms_r16 z, tt)).
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F2 (y : seq_type MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1F2_cond (z : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Type)
  : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1F2_cond2 (z : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Type)
 : MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F2 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list)
  : seq_cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list y ->
 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F2 y)) /\  MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1 (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Format : T_Format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Type MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond :=
        proj2_format  MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__list__Format
    MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F2 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1F2_cond  MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F1F2_cond2 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Format.

Definition MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Format : T_Format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__nat__Format MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F1 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F2 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F1F2 MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__cond MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Format.


Definition MIMO_ParametersPerBand__ext2O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext2O__list.
Definition MIMO_ParametersPerBand__ext2O__Format_list : MIMO_ParametersPerBand__ext2O__Format_Type :=
  (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16__Format, (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext2O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext2O__list MIMO_ParametersPerBand__ext2O__Format_list.
Definition MIMO_ParametersPerBand__ext2O__F1 z :=
  (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUCCH_r16 z, (MIMO_ParametersPerBand__ext2O__semi_PersistentL1_SINR_Report_PUSCH_r16 z, tt)).
Definition MIMO_ParametersPerBand__ext2O__F2 (y : seq_type MIMO_ParametersPerBand__ext2O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext2O__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext2O__F1F2_cond (z : MIMO_ParametersPerBand__ext2O__Type)
  : MIMO_ParametersPerBand__ext2O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext2O__list (MIMO_ParametersPerBand__ext2O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext2O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext2O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext2O__Type)
 : MIMO_ParametersPerBand__ext2O__F2 (MIMO_ParametersPerBand__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext2O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext2O__list)
  : seq_cond MIMO_ParametersPerBand__ext2O__list y ->
 (MIMO_ParametersPerBand__ext2O__cond (MIMO_ParametersPerBand__ext2O__F2 y)) /\  MIMO_ParametersPerBand__ext2O__F1 (MIMO_ParametersPerBand__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext2O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext2O__Format : T_Format MIMO_ParametersPerBand__ext2O__Type MIMO_ParametersPerBand__ext2O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext2O__cond MIMO_ParametersPerBand__ext2O__list__Format
    MIMO_ParametersPerBand__ext2O__F1 MIMO_ParametersPerBand__ext2O__F2 MIMO_ParametersPerBand__ext2O__F1F2_cond  MIMO_ParametersPerBand__ext2O__F1F2_cond2 MIMO_ParametersPerBand__ext2O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext2O__cond MIMO_ParametersPerBand__ext2O__Format.

Definition MIMO_ParametersPerBand__ext2__check_all_none (b : MIMO_ParametersPerBand__ext2O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext2O__Type None None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext2__Format : T_Format MIMO_ParametersPerBand__ext2__Type MIMO_ParametersPerBand__ext2__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext2__check_all_none MIMO_ParametersPerBand__ext2O__Format.

Opaque MIMO_ParametersPerBand__ext2__cond MIMO_ParametersPerBand__ext2__Format.

Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Format : T_Format MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__nat__Format MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F1 MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F2 MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F1F2 MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__F2F1.

Opaque MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__cond MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Format.


Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list.
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Format_list : MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Format_Type :=
  (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640__Format, unit_format).
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Format_list.
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1 z :=
  (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__maxNumberConfiguredSpatialRelations_v1640 z, tt).
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F2 (y : seq_type MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list) :=
  match y with
  | (i0, _)=>
    make__MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Type i0
  end.
Lemma MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1F2_cond (z : MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Type)
  : MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1F2_cond2 (z : MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Type)
 : MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F2 (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list)
  : seq_cond MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list y ->
 (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F2 y)) /\  MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1 (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Format : T_Format MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Type MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond :=
        proj2_format  MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__list__Format
    MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1 MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F2 MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1F2_cond  MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F1F2_cond2 MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__cond MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Format.

Definition MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Format : T_Format MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__nat__Format MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F1 MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F2 MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F1F2 MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__cond MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Format.


Definition MIMO_ParametersPerBand__ext3O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext3O__list.
Definition MIMO_ParametersPerBand__ext3O__Format_list : MIMO_ParametersPerBand__ext3O__Format_Type :=
  (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640__Format, (MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext3O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext3O__list MIMO_ParametersPerBand__ext3O__Format_list.
Definition MIMO_ParametersPerBand__ext3O__F1 z :=
  (MIMO_ParametersPerBand__ext3O__spatialRelations_v1640 z, (MIMO_ParametersPerBand__ext3O__support64CandidateBeamRS_BFR_r16 z, tt)).
Definition MIMO_ParametersPerBand__ext3O__F2 (y : seq_type MIMO_ParametersPerBand__ext3O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext3O__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext3O__F1F2_cond (z : MIMO_ParametersPerBand__ext3O__Type)
  : MIMO_ParametersPerBand__ext3O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext3O__list (MIMO_ParametersPerBand__ext3O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext3O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext3O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext3O__Type)
 : MIMO_ParametersPerBand__ext3O__F2 (MIMO_ParametersPerBand__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext3O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext3O__list)
  : seq_cond MIMO_ParametersPerBand__ext3O__list y ->
 (MIMO_ParametersPerBand__ext3O__cond (MIMO_ParametersPerBand__ext3O__F2 y)) /\  MIMO_ParametersPerBand__ext3O__F1 (MIMO_ParametersPerBand__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext3O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext3O__Format : T_Format MIMO_ParametersPerBand__ext3O__Type MIMO_ParametersPerBand__ext3O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext3O__cond MIMO_ParametersPerBand__ext3O__list__Format
    MIMO_ParametersPerBand__ext3O__F1 MIMO_ParametersPerBand__ext3O__F2 MIMO_ParametersPerBand__ext3O__F1F2_cond  MIMO_ParametersPerBand__ext3O__F1F2_cond2 MIMO_ParametersPerBand__ext3O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext3O__cond MIMO_ParametersPerBand__ext3O__Format.

Definition MIMO_ParametersPerBand__ext3__check_all_none (b : MIMO_ParametersPerBand__ext3O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext3O__Type None None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext3__Format : T_Format MIMO_ParametersPerBand__ext3__Type MIMO_ParametersPerBand__ext3__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext3__check_all_none MIMO_ParametersPerBand__ext3O__Format.

Opaque MIMO_ParametersPerBand__ext3__cond MIMO_ParametersPerBand__ext3__Format.

Definition MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Format : T_Format MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__nat__Format MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F1 MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F2 MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F1F2 MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__F2F1.

Opaque MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__cond MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Format.


Definition MIMO_ParametersPerBand__ext4O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext4O__list.
Definition MIMO_ParametersPerBand__ext4O__Format_list : MIMO_ParametersPerBand__ext4O__Format_Type :=
  (MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16__Format, unit_format).
Definition MIMO_ParametersPerBand__ext4O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext4O__list MIMO_ParametersPerBand__ext4O__Format_list.
Definition MIMO_ParametersPerBand__ext4O__F1 z :=
  (MIMO_ParametersPerBand__ext4O__maxMIMO_LayersForMulti_DCI_mTRP_r16 z, tt).
Definition MIMO_ParametersPerBand__ext4O__F2 (y : seq_type MIMO_ParametersPerBand__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__MIMO_ParametersPerBand__ext4O__Type i0
  end.
Lemma MIMO_ParametersPerBand__ext4O__F1F2_cond (z : MIMO_ParametersPerBand__ext4O__Type)
  : MIMO_ParametersPerBand__ext4O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext4O__list (MIMO_ParametersPerBand__ext4O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext4O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext4O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext4O__Type)
 : MIMO_ParametersPerBand__ext4O__F2 (MIMO_ParametersPerBand__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext4O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext4O__list)
  : seq_cond MIMO_ParametersPerBand__ext4O__list y ->
 (MIMO_ParametersPerBand__ext4O__cond (MIMO_ParametersPerBand__ext4O__F2 y)) /\  MIMO_ParametersPerBand__ext4O__F1 (MIMO_ParametersPerBand__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext4O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext4O__Format : T_Format MIMO_ParametersPerBand__ext4O__Type MIMO_ParametersPerBand__ext4O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext4O__cond MIMO_ParametersPerBand__ext4O__list__Format
    MIMO_ParametersPerBand__ext4O__F1 MIMO_ParametersPerBand__ext4O__F2 MIMO_ParametersPerBand__ext4O__F1F2_cond  MIMO_ParametersPerBand__ext4O__F1F2_cond2 MIMO_ParametersPerBand__ext4O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext4O__cond MIMO_ParametersPerBand__ext4O__Format.

Definition MIMO_ParametersPerBand__ext4__check_all_none (b : MIMO_ParametersPerBand__ext4O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext4O__Type None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext4__Format : T_Format MIMO_ParametersPerBand__ext4__Type MIMO_ParametersPerBand__ext4__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext4__check_all_none MIMO_ParametersPerBand__ext4O__Format.

Opaque MIMO_ParametersPerBand__ext4__cond MIMO_ParametersPerBand__ext4__Format.

Definition MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__Format : T_Format MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__Type MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__cond MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__Format.


Definition MIMO_ParametersPerBand__ext5O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext5O__list.
Definition MIMO_ParametersPerBand__ext5O__Format_list : MIMO_ParametersPerBand__ext5O__Format_Type :=
  (MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670__Format, unit_format).
Definition MIMO_ParametersPerBand__ext5O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext5O__list MIMO_ParametersPerBand__ext5O__Format_list.
Definition MIMO_ParametersPerBand__ext5O__F1 z :=
  (MIMO_ParametersPerBand__ext5O__supportedSINR_meas_v1670 z, tt).
Definition MIMO_ParametersPerBand__ext5O__F2 (y : seq_type MIMO_ParametersPerBand__ext5O__list) :=
  match y with
  | (i0, _)=>
    make__MIMO_ParametersPerBand__ext5O__Type i0
  end.
Lemma MIMO_ParametersPerBand__ext5O__F1F2_cond (z : MIMO_ParametersPerBand__ext5O__Type)
  : MIMO_ParametersPerBand__ext5O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext5O__list (MIMO_ParametersPerBand__ext5O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext5O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext5O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext5O__Type)
 : MIMO_ParametersPerBand__ext5O__F2 (MIMO_ParametersPerBand__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext5O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext5O__list)
  : seq_cond MIMO_ParametersPerBand__ext5O__list y ->
 (MIMO_ParametersPerBand__ext5O__cond (MIMO_ParametersPerBand__ext5O__F2 y)) /\  MIMO_ParametersPerBand__ext5O__F1 (MIMO_ParametersPerBand__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext5O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext5O__Format : T_Format MIMO_ParametersPerBand__ext5O__Type MIMO_ParametersPerBand__ext5O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext5O__cond MIMO_ParametersPerBand__ext5O__list__Format
    MIMO_ParametersPerBand__ext5O__F1 MIMO_ParametersPerBand__ext5O__F2 MIMO_ParametersPerBand__ext5O__F1F2_cond  MIMO_ParametersPerBand__ext5O__F1F2_cond2 MIMO_ParametersPerBand__ext5O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext5O__cond MIMO_ParametersPerBand__ext5O__Format.

Definition MIMO_ParametersPerBand__ext5__check_all_none (b : MIMO_ParametersPerBand__ext5O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext5O__Type None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext5__Format : T_Format MIMO_ParametersPerBand__ext5__Type MIMO_ParametersPerBand__ext5__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext5__check_all_none MIMO_ParametersPerBand__ext5O__Format.

Opaque MIMO_ParametersPerBand__ext5__cond MIMO_ParametersPerBand__ext5__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F1 MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F2 MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__cond MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F1 MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F2 MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__cond MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F1 MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F2 MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__cond MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_combEight_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F1 MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F2 MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_combEight_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_combEight_r17__cond MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__cond :=
 ranged_int_format (1) (9) MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Format_list : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17__Format, unit_format))).
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesPerSetPerBWP_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFR_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__maxBFD_RS_resourcesAcrossSetsPerBWP_r17 z, tt))).
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Type i0 i1 i2
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Type)
  : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Type)
 : MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__list__Format
    MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F1 MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F2 MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__cond MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__nat__Format MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F1 MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F2 MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F1F2 MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__cond MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__nat__Format MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F1 MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F2 MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F1F2 MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__cond MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F1 MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F2 MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__cond MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F1 MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F2 MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__cond MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Format_list : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxConfiguredJointTCI_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__maxActivatedTCIAcrossCC_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Type)
  : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Type)
 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__list__Format
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Format.


Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Format_list : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__minBeamApplicationTime_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__maxNumMAC_CE_PerCC z, tt)).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Type)
  : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Type)
 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__list__Format
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Format_list : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_PerCC_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__additionalMAC_CE_AcrossCC_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Type)
  : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Type)
 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__list__Format
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Format_list : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17__Format, unit_format)))).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredDL_TCI_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxConfiguredUL_TCI_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedDL_TCIAcrossCC_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__maxActivatedUL_TCIAcrossCC_r17 z, tt)))).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Type i0 i1 i2 i3
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Type)
  : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Type)
 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__list__Format
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__cond :=
 ranged_int_format (2) (8) MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__helper1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__cond :=
 ranged_int_format (2) (8) MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__helper1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Format_list : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17__Format, unit_format))).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__minBeamApplicationTime_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedDL_TCIPerCC_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__maxActivatedUL_TCIPerCC_r17 z, tt))).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Type i0 i1 i2
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Type)
  : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Type)
 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__list__Format
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Format_list : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListDL_TCI_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__maxNumListUL_TCI_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Type)
  : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Type)
 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__list__Format
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Format_list : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17__Format, unit_format)))).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_PerCC_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_PerCC_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_DL_AcrossCC_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__k_UL_AcrossCC_r17 z, tt)))).
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Type i0 i1 i2 i3
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Type)
  : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Type)
 : MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Type MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__list__Format
    MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__cond MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__cond :=
 ranged_int_format (1) (7) MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__helper1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__nat__Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F1F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Format_list : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumAdditionalPCI_L1_RSRP_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__maxNumSSB_ResourceL1_RSRP_AcrossCC_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Type)
  : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Type)
 : MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F2 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1 (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Type MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__list__Format
    MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__cond MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__cond :=
 ranged_int_format (1) (4) MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__helper1 MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__cond MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__nat__Format MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F1 MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F2 MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F1F2 MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__cond MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Format_list : MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17__Format, (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumP_MPR_RI_pairs_r17 z, (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__maxNumConfRS_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Type)
  : MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Type)
 : MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F2 (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1 (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Type MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__list__Format
    MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1 MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F2 MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__cond MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F1 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F1 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F1 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F1 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Format_list : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17__Format, unit_format)))).
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal1_r17 z, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal2_r17 z, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal3_r17 z, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__capVal4_r17 z, tt)))).
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Type i0 i1 i2 i3
  end.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Type)
  : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Type)
 : MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F2 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1 (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Type MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__list__Format
    MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__cond MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__cond :=
 ranged_int_format (1) (8) MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__cond :=
 ranged_int_format (1) (8) MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__cond :=
 ranged_int_format (0) (8) MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__cond :=
 ranged_int_format (1) (16) MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__cond :=
 ranged_int_format (1) (2) MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Format_list : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17__Format, unit_format))))).
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumPeriodicSRS_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumAperiodicSRS_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__maxNumSP_SRS_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourcePerCC_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__numSRS_ResourceNonCodebook_r17 z, tt))))).
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Type i0 i1 i2 i3 i4
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Type)
  : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Type)
 : MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__list__Format
    MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__cond :=
 ranged_int_format (3) (8) MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__cond :=
 ranged_int_format (1) (7) MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__cond :=
 ranged_int_format (0) (7) MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Format_list : MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case1_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__maxNumAdditionalPCI_Case2_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Type)
  : MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Type)
 : MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__list__Format
    MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__cond :=
 ranged_int_format (1) (4) MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Format_list : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17__Format, unit_format))).
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumBeamGroups_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_WithinSlot_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__maxNumRS_AcrossSlot_r17 z, tt))).
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Type i0 i1 i2
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Type)
  : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Type)
 : MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__list__Format
    MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__Format : T_Format Z MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__cond :=
 ranged_int_format (2) (8) MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__cond := seq_of_format CSI_MultiTRP_SupportedCombinations_r17__Format 1 16 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__helper1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__helper2.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Format_list : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17__Format, unit_format)))).
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__maxNumNZP_CSI_RS_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cSI_Report_mode_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__supportedComboAcrossCCs_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__codebookModeNCJT_r17 z, tt)))).
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Type i0 i1 i2 i3
  end.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Type)
  : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Type)
 : MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F2 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1 (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Type MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__list__Format
    MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__nat__Format MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F1 MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F1F2 MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__cond MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__nat__Format MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F1 MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F2 MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F1F2 MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__cond MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Format : T_Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__nat__Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F1 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F1F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Format.

Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Format : T_Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__nat__Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F1 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F1F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Format.


Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Format_list : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz__Format, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Format_list.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1 z :=
  (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_480kHz z, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__scs_960kHz z, tt)).
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Type)
  : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Type)
 : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F2 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list y ->
 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F2 y)) /\  MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Format : T_Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__list__Format
    MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1F2_cond  MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F1F2_cond2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Format.

Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__nat__Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F1 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F1F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__nat__Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F1 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F1F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Format_list : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17__Format, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Format_list.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1 z :=
  (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_480kHz_r17 z, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__scs_960kHz_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Type)
  : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Type)
 : MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F2 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list y ->
 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F2 y)) /\  MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1 (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Type MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__list__Format
    MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1F2_cond  MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F1F2_cond2 MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__cond MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__nat__Format MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F1 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F2 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F1F2 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__nat__Format MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F1 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F2 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F1F2 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Format_list : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17__Format, (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Format_list.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1 z :=
  (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_480kHz_r17 z, (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__scs_960kHz_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Type)
  : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Type)
 : MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F2 (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list y ->
 (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F2 y)) /\  MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1 (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Format : T_Format MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Type MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__list__Format
    MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F2 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1F2_cond  MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F1F2_cond2 MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__cond MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Format.

Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__nat__Format MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F1 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F2 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F1F2 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Format.

Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Format : T_Format MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__nat__Format MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F1 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F2 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F1F2 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Format.


Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Format_list : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17__Format, (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17__Format, unit_format)).
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Format_list.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1 z :=
  (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_480kHz_r17 z, (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__scs_960kHz_r17 z, tt)).
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Type i0 i1
  end.
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Type)
  : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Type)
 : MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F2 (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list y ->
 (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F2 y)) /\  MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1 (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Format : T_Format MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Type MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__list__Format
    MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F2 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1F2_cond  MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F1F2_cond2 MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__cond MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Format.


Definition MIMO_ParametersPerBand__ext6O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext6O__list.
Definition MIMO_ParametersPerBand__ext6O__Format_list : MIMO_ParametersPerBand__ext6O__Format_Type :=
  (MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_combEight_r17__Format, (CodebookParametersfetype2_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17__Format, (MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17__Format, (MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17__Format, (MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17__Format, (CodebookComboParameterMixedType_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17__Format, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17__Format, (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17__Format, (CodebookComboParameterMultiTRP_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17__Format, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17__Format, (MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17__Format, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710__Format, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17__Format, (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710__Format, (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710__Format, unit_format)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition MIMO_ParametersPerBand__ext6O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext6O__list MIMO_ParametersPerBand__ext6O__Format_list.
Definition MIMO_ParametersPerBand__ext6O__F1 z :=
  (MIMO_ParametersPerBand__ext6O__srs_increasedRepetition_r17 z, (MIMO_ParametersPerBand__ext6O__srs_partialFrequencySounding_r17 z, (MIMO_ParametersPerBand__ext6O__srs_startRB_locationHoppingPartial_r17 z, (MIMO_ParametersPerBand__ext6O__srs_combEight_r17 z, (MIMO_ParametersPerBand__ext6O__codebookParametersfetype2_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoCSI_RS_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_InterSlot_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_CyclicMapping_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_SecondTPC_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_twoBFD_RS_Set_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_PUCCH_SR_perCG_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_BFR_association_PUCCH_SR_r17 z, (MIMO_ParametersPerBand__ext6O__sfn_SimulTwoTCI_AcrossMultiCC_r17 z, (MIMO_ParametersPerBand__ext6O__sfn_DefaultDL_BeamSetup_r17 z, (MIMO_ParametersPerBand__ext6O__sfn_DefaultUL_BeamSetup_r17 z, (MIMO_ParametersPerBand__ext6O__srs_TriggeringOffset_r17 z, (MIMO_ParametersPerBand__ext6O__srs_TriggeringDCI_r17 z, (MIMO_ParametersPerBand__ext6O__codebookComboParameterMixedType_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_multiMAC_CE_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_perBWP_CA_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_ListSharingCA_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_commonMultiCC_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_BeamAlignDLRS_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_PC_association_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_SRS_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_Legacy_CORESET0_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_SCellBFR_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_InterCell_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_multiMAC_CE_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_perBWP_CA_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_ListSharingCA_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_commonMultiCC_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedSeparateTCI_InterCell_r17 z, (MIMO_ParametersPerBand__ext6O__unifiedJointTCI_mTRP_InterCell_BM_r17 z, (MIMO_ParametersPerBand__ext6O__mpe_Mitigation_r17 z, (MIMO_ParametersPerBand__ext6O__srs_PortReport_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_individual_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_anySpan_3Symbols_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PDCCH_TwoQCL_TypeD_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CSI_RS_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_cyclicMapping_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_secondTPC_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_twoPHR_Reporting_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_A_CSI_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_SP_CSI_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUSCH_CG_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_MAC_CE_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_PUCCH_maxNum_PC_FR1_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_inter_Cell_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_GroupBasedL1_RSRP_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_BFD_RS_MAC_CE_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_EnhancementPerBand_r17 z, (MIMO_ParametersPerBand__ext6O__codebookComboParameterMultiTRP_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_additionalCSI_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_N_Max2_r17 z, (MIMO_ParametersPerBand__ext6O__mTRP_CSI_CMR_r17 z, (MIMO_ParametersPerBand__ext6O__srs_partialFreqSounding_r17 z, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_v1710 z, (MIMO_ParametersPerBand__ext6O__beamSwitchTiming_r17 z, (MIMO_ParametersPerBand__ext6O__beamReportTiming_v1710 z, (MIMO_ParametersPerBand__ext6O__maxNumberRxTxBeamSwitchDL_v1710 z, tt)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition MIMO_ParametersPerBand__ext6O__F2 (y : seq_type MIMO_ParametersPerBand__ext6O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, (i24, (i25, (i26, (i27, (i28, (i29, (i30, (i31, (i32, (i33, (i34, (i35, (i36, (i37, (i38, (i39, (i40, (i41, (i42, (i43, (i44, (i45, (i46, (i47, (i48, (i49, (i50, (i51, (i52, (i53, (i54, (i55, (i56, (i57, (i58, (i59, (i60, (i61, (i62, (i63, _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))=>
    make__MIMO_ParametersPerBand__ext6O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32 i33 i34 i35 i36 i37 i38 i39 i40 i41 i42 i43 i44 i45 i46 i47 i48 i49 i50 i51 i52 i53 i54 i55 i56 i57 i58 i59 i60 i61 i62 i63
  end.
Lemma MIMO_ParametersPerBand__ext6O__F1F2_cond (z : MIMO_ParametersPerBand__ext6O__Type)
  : MIMO_ParametersPerBand__ext6O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext6O__list (MIMO_ParametersPerBand__ext6O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext6O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext6O__Type)
 : MIMO_ParametersPerBand__ext6O__F2 (MIMO_ParametersPerBand__ext6O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext6O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext6O__list)
  : seq_cond MIMO_ParametersPerBand__ext6O__list y ->
 (MIMO_ParametersPerBand__ext6O__cond (MIMO_ParametersPerBand__ext6O__F2 y)) /\  MIMO_ParametersPerBand__ext6O__F1 (MIMO_ParametersPerBand__ext6O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext6O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext6O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext6O__Format : T_Format MIMO_ParametersPerBand__ext6O__Type MIMO_ParametersPerBand__ext6O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext6O__cond MIMO_ParametersPerBand__ext6O__list__Format
    MIMO_ParametersPerBand__ext6O__F1 MIMO_ParametersPerBand__ext6O__F2 MIMO_ParametersPerBand__ext6O__F1F2_cond  MIMO_ParametersPerBand__ext6O__F1F2_cond2 MIMO_ParametersPerBand__ext6O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext6O__cond MIMO_ParametersPerBand__ext6O__Format.

Definition MIMO_ParametersPerBand__ext6__check_all_none (b : MIMO_ParametersPerBand__ext6O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext6O__Type None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext6__Format : T_Format MIMO_ParametersPerBand__ext6__Type MIMO_ParametersPerBand__ext6__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext6__check_all_none MIMO_ParametersPerBand__ext6O__Format.

Opaque MIMO_ParametersPerBand__ext6__cond MIMO_ParametersPerBand__ext6__Format.

Definition MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Format : T_Format MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__nat__Format MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F1 MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F2 MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F1F2 MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__cond MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Format.

Definition MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__Format : T_Format Z MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__cond :=
 ranged_int_format (9) (12) MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__helper1 MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__helper2.

Opaque MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__cond MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__Format.

Definition MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Format : T_Format MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__nat__Format MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F1 MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F2 MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F1F2 MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__cond MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Format.

Definition MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Format : T_Format MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__nat__Format MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F1 MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F2 MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F1F2 MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__cond MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Format.

Definition MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Format : T_Format MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__nat__Format MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F1 MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F2 MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F1F2 MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__cond MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Format.


Definition MIMO_ParametersPerBand__ext7O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext7O__list.
Definition MIMO_ParametersPerBand__ext7O__Format_list : MIMO_ParametersPerBand__ext7O__Format_Type :=
  (MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17__Format, (MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720__Format, (MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17__Format, (MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17__Format, (MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17__Format, unit_format))))).
Definition MIMO_ParametersPerBand__ext7O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext7O__list MIMO_ParametersPerBand__ext7O__Format_list.
Definition MIMO_ParametersPerBand__ext7O__F1 z :=
  (MIMO_ParametersPerBand__ext7O__srs_PortReportSP_AP_r17 z, (MIMO_ParametersPerBand__ext7O__maxNumberRxBeam_v1720 z, (MIMO_ParametersPerBand__ext7O__sfn_ImplicitRS_twoTCI_r17 z, (MIMO_ParametersPerBand__ext7O__sfn_QCL_TypeD_Collision_twoTCI_r17 z, (MIMO_ParametersPerBand__ext7O__mTRP_CSI_numCPU_r17 z, tt))))).
Definition MIMO_ParametersPerBand__ext7O__F2 (y : seq_type MIMO_ParametersPerBand__ext7O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__MIMO_ParametersPerBand__ext7O__Type i0 i1 i2 i3 i4
  end.
Lemma MIMO_ParametersPerBand__ext7O__F1F2_cond (z : MIMO_ParametersPerBand__ext7O__Type)
  : MIMO_ParametersPerBand__ext7O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext7O__list (MIMO_ParametersPerBand__ext7O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext7O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext7O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext7O__Type)
 : MIMO_ParametersPerBand__ext7O__F2 (MIMO_ParametersPerBand__ext7O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext7O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext7O__list)
  : seq_cond MIMO_ParametersPerBand__ext7O__list y ->
 (MIMO_ParametersPerBand__ext7O__cond (MIMO_ParametersPerBand__ext7O__F2 y)) /\  MIMO_ParametersPerBand__ext7O__F1 (MIMO_ParametersPerBand__ext7O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext7O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext7O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext7O__Format : T_Format MIMO_ParametersPerBand__ext7O__Type MIMO_ParametersPerBand__ext7O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext7O__cond MIMO_ParametersPerBand__ext7O__list__Format
    MIMO_ParametersPerBand__ext7O__F1 MIMO_ParametersPerBand__ext7O__F2 MIMO_ParametersPerBand__ext7O__F1F2_cond  MIMO_ParametersPerBand__ext7O__F1F2_cond2 MIMO_ParametersPerBand__ext7O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext7O__cond MIMO_ParametersPerBand__ext7O__Format.

Definition MIMO_ParametersPerBand__ext7__check_all_none (b : MIMO_ParametersPerBand__ext7O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext7O__Type None None None None None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext7__Format : T_Format MIMO_ParametersPerBand__ext7__Type MIMO_ParametersPerBand__ext7__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext7__check_all_none MIMO_ParametersPerBand__ext7O__Format.

Opaque MIMO_ParametersPerBand__ext7__cond MIMO_ParametersPerBand__ext7__Format.

Definition MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Format : T_Format MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__nat__Format MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F1 MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F2 MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F1F2 MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__F2F1.

Opaque MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__cond MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Format.


Definition MIMO_ParametersPerBand__ext8O__Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__ext8O__list.
Definition MIMO_ParametersPerBand__ext8O__Format_list : MIMO_ParametersPerBand__ext8O__Format_Type :=
  (MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17__Format, unit_format).
Definition MIMO_ParametersPerBand__ext8O__list__Format := (*Eval compute in *) seq_format MIMO_ParametersPerBand__ext8O__list MIMO_ParametersPerBand__ext8O__Format_list.
Definition MIMO_ParametersPerBand__ext8O__F1 z :=
  (MIMO_ParametersPerBand__ext8O__supportRepNumPDSCH_TDRA_DCI_1_2_r17 z, tt).
Definition MIMO_ParametersPerBand__ext8O__F2 (y : seq_type MIMO_ParametersPerBand__ext8O__list) :=
  match y with
  | (i0, _)=>
    make__MIMO_ParametersPerBand__ext8O__Type i0
  end.
Lemma MIMO_ParametersPerBand__ext8O__F1F2_cond (z : MIMO_ParametersPerBand__ext8O__Type)
  : MIMO_ParametersPerBand__ext8O__cond z ->
  (seq_cond MIMO_ParametersPerBand__ext8O__list (MIMO_ParametersPerBand__ext8O__F1 z)).
intro H. unfold MIMO_ParametersPerBand__ext8O__cond in H. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext8O__F1F2_cond2 (z : MIMO_ParametersPerBand__ext8O__Type)
 : MIMO_ParametersPerBand__ext8O__F2 (MIMO_ParametersPerBand__ext8O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MIMO_ParametersPerBand__ext8O__F2F1_cond (y : seq_type MIMO_ParametersPerBand__ext8O__list)
  : seq_cond MIMO_ParametersPerBand__ext8O__list y ->
 (MIMO_ParametersPerBand__ext8O__cond (MIMO_ParametersPerBand__ext8O__F2 y)) /\  MIMO_ParametersPerBand__ext8O__F1 (MIMO_ParametersPerBand__ext8O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MIMO_ParametersPerBand__ext8O__cond. simpl in *. auto.
 - simpl. unfold MIMO_ParametersPerBand__ext8O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MIMO_ParametersPerBand__ext8O__Format : T_Format MIMO_ParametersPerBand__ext8O__Type MIMO_ParametersPerBand__ext8O__cond :=
        proj2_format  MIMO_ParametersPerBand__ext8O__cond MIMO_ParametersPerBand__ext8O__list__Format
    MIMO_ParametersPerBand__ext8O__F1 MIMO_ParametersPerBand__ext8O__F2 MIMO_ParametersPerBand__ext8O__F1F2_cond  MIMO_ParametersPerBand__ext8O__F1F2_cond2 MIMO_ParametersPerBand__ext8O__F2F1_cond.
Opaque MIMO_ParametersPerBand__ext8O__cond MIMO_ParametersPerBand__ext8O__Format.

Definition MIMO_ParametersPerBand__ext8__check_all_none (b : MIMO_ParametersPerBand__ext8O__Type) : bool :=
match b with 
  | make__MIMO_ParametersPerBand__ext8O__Type None  => false 
  | _ => true 
 end.
Definition MIMO_ParametersPerBand__ext8__Format : T_Format MIMO_ParametersPerBand__ext8__Type MIMO_ParametersPerBand__ext8__cond :=
  restrict_add_format MIMO_ParametersPerBand__ext8__check_all_none MIMO_ParametersPerBand__ext8O__Format.

Opaque MIMO_ParametersPerBand__ext8__cond MIMO_ParametersPerBand__ext8__Format.


Definition MIMO_ParametersPerBand__root_Format_Type := Eval cbn in seq_format_prod MIMO_ParametersPerBand__root_list.
Definition MIMO_ParametersPerBand__root_Format_list : MIMO_ParametersPerBand__root_Format_Type :=
  (MIMO_ParametersPerBand__tci_StatePDSCH__Format, (MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH__Format, (MIMO_ParametersPerBand__pusch_TransCoherence__Format, (MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping__Format, (MIMO_ParametersPerBand__periodicBeamReport__Format, (MIMO_ParametersPerBand__aperiodicBeamReport__Format, (MIMO_ParametersPerBand__sp_BeamReportPUCCH__Format, (MIMO_ParametersPerBand__sp_BeamReportPUSCH__Format, (DummyG__Format, (MIMO_ParametersPerBand__maxNumberRxBeam__Format, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL__Format, (MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting__Format, (MIMO_ParametersPerBand__groupBeamReporting__Format, (MIMO_ParametersPerBand__uplinkBeamManagement__Format, (MIMO_ParametersPerBand__maxNumberCSI_RS_BFD__Format, (MIMO_ParametersPerBand__maxNumberSSB_BFD__Format, (MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD__Format, (MIMO_ParametersPerBand__dummy2__Format, (MIMO_ParametersPerBand__twoPortsPTRS_UL__Format, (SRS_Resources__Format, (MIMO_ParametersPerBand__dummy3__Format, (MIMO_ParametersPerBand__beamReportTiming__Format, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL__Format, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL__Format, (DummyH__Format, (MIMO_ParametersPerBand__aperiodicTRS__Format, unit_format)))))))))))))))))))))))))).

Definition MIMO_ParametersPerBand__ext_Format_Type := Eval cbn in get_formats MIMO_ParametersPerBand__ext_list.
Definition MIMO_ParametersPerBand__ext_Format_list : MIMO_ParametersPerBand__ext_Format_Type :=
  (MIMO_ParametersPerBand__ext0__Format, (MIMO_ParametersPerBand__ext1__Format, (MIMO_ParametersPerBand__ext2__Format, (MIMO_ParametersPerBand__ext3__Format, (MIMO_ParametersPerBand__ext4__Format, (MIMO_ParametersPerBand__ext5__Format, (MIMO_ParametersPerBand__ext6__Format, (MIMO_ParametersPerBand__ext7__Format, (MIMO_ParametersPerBand__ext8__Format, unit__Format))))))))).

Definition MIMO_ParametersPerBand__list_type : Set := (seq_type MIMO_ParametersPerBand__root_list) * (seq_ext_type MIMO_ParametersPerBand__ext_list).
Definition MIMO_ParametersPerBand__list_cond (z : MIMO_ParametersPerBand__list_type) : Prop :=
        (seq_cond MIMO_ParametersPerBand__root_list (fst z)) /\ (seq_ext_cond MIMO_ParametersPerBand__ext_list (snd z)).
Definition MIMO_ParametersPerBand__list_format : T_Format MIMO_ParametersPerBand__list_type MIMO_ParametersPerBand__list_cond :=
 (* Eval compute in *) seq_ext_format MIMO_ParametersPerBand__root_list MIMO_ParametersPerBand__root_Format_list MIMO_ParametersPerBand__ext_list MIMO_ParametersPerBand__ext_Format_list.

Opaque MIMO_ParametersPerBand__list_format.
Definition MIMO_ParametersPerBand__F1 (z : MIMO_ParametersPerBand__Type) : MIMO_ParametersPerBand__list_type :=
  (((MIMO_ParametersPerBand__tci_StatePDSCH z, (MIMO_ParametersPerBand__additionalActiveTCI_StatePDCCH z, (MIMO_ParametersPerBand__pusch_TransCoherence z, (MIMO_ParametersPerBand__beamCorrespondenceWithoutUL_BeamSweeping z, (MIMO_ParametersPerBand__periodicBeamReport z, (MIMO_ParametersPerBand__aperiodicBeamReport z, (MIMO_ParametersPerBand__sp_BeamReportPUCCH z, (MIMO_ParametersPerBand__sp_BeamReportPUSCH z, (MIMO_ParametersPerBand__dummy1 z, (MIMO_ParametersPerBand__maxNumberRxBeam z, (MIMO_ParametersPerBand__maxNumberRxTxBeamSwitchDL z, (MIMO_ParametersPerBand__maxNumberNonGroupBeamReporting z, (MIMO_ParametersPerBand__groupBeamReporting z, (MIMO_ParametersPerBand__uplinkBeamManagement z, (MIMO_ParametersPerBand__maxNumberCSI_RS_BFD z, (MIMO_ParametersPerBand__maxNumberSSB_BFD z, (MIMO_ParametersPerBand__maxNumberCSI_RS_SSB_CBD z, (MIMO_ParametersPerBand__dummy2 z, (MIMO_ParametersPerBand__twoPortsPTRS_UL z, (MIMO_ParametersPerBand__dummy5 z, (MIMO_ParametersPerBand__dummy3 z, (MIMO_ParametersPerBand__beamReportTiming z, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetDL z, (MIMO_ParametersPerBand__ptrs_DensityRecommendationSetUL z, (MIMO_ParametersPerBand__dummy4 z, (MIMO_ParametersPerBand__aperiodicTRS z, tt))))))))))))))))))))))))))), (
(MIMO_ParametersPerBand__ext0 z, (MIMO_ParametersPerBand__ext1 z, (MIMO_ParametersPerBand__ext2 z, (MIMO_ParametersPerBand__ext3 z, (MIMO_ParametersPerBand__ext4 z, (MIMO_ParametersPerBand__ext5 z, (MIMO_ParametersPerBand__ext6 z, (MIMO_ParametersPerBand__ext7 z, (MIMO_ParametersPerBand__ext8 z, tt))))))))))).
Definition MIMO_ParametersPerBand__F2 (y : MIMO_ParametersPerBand__list_type) : MIMO_ParametersPerBand__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, (j16, (j17, (j18, (j19, (j20, (j21, (j22, (j23, (j24, (j25, _)))))))))))))))))))))))))), (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _))))))))))=>
    make__MIMO_ParametersPerBand__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j22 j23 j24 j25 i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Definition MIMO_ParametersPerBand__helper1 : (forall a : MIMO_ParametersPerBand__Type, MIMO_ParametersPerBand__cond a -> MIMO_ParametersPerBand__list_cond (MIMO_ParametersPerBand__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MIMO_ParametersPerBand__helper2 : (forall a : MIMO_ParametersPerBand__Type, MIMO_ParametersPerBand__F2 (MIMO_ParametersPerBand__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MIMO_ParametersPerBand__helper3 : (forall b : MIMO_ParametersPerBand__list_type, MIMO_ParametersPerBand__list_cond b -> MIMO_ParametersPerBand__cond (MIMO_ParametersPerBand__F2 b) /\ MIMO_ParametersPerBand__F1 (MIMO_ParametersPerBand__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MIMO_ParametersPerBand__cond, MIMO_ParametersPerBand__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MIMO_ParametersPerBand__Format : T_Format MIMO_ParametersPerBand__Type MIMO_ParametersPerBand__cond :=
 proj2_format MIMO_ParametersPerBand__cond MIMO_ParametersPerBand__list_format  MIMO_ParametersPerBand__F1 MIMO_ParametersPerBand__F2 MIMO_ParametersPerBand__helper1 MIMO_ParametersPerBand__helper2 MIMO_ParametersPerBand__helper3.

Opaque MIMO_ParametersPerBand__cond MIMO_ParametersPerBand__Format.

