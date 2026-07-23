Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CodebookParametersfetype2PerBC_r17.

Opaque CodebookParametersfetype2PerBC_r17__cond CodebookParametersfetype2PerBC_r17__Format.

Inductive CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Type : Set :=
 | CA_ParametersNR_v1700__demodulationEnhancementCA_r17__supported
.
Definition CA_ParametersNR_v1700__demodulationEnhancementCA_r17__cond := (fun (_ : CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Type) => True).
Lemma CA_ParametersNR_v1700__demodulationEnhancementCA_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__demodulationEnhancementCA_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1700__demodulationEnhancementCA_r17__nat__helper.

Definition CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__demodulationEnhancementCA_r17__supported => 0
  end.
Definition CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__demodulationEnhancementCA_r17__supported
  | _ => CA_ParametersNR_v1700__demodulationEnhancementCA_r17__supported
  end.
Lemma CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F1F2 : forall x : CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Type, (CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F1 x <= 0) /\ CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F2 (CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F1 (CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Type : Set :=
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n50
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n60
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n70
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n80
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n90
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n100
.
Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__cond := (fun (_ : CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Type) => True).
Lemma CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__nat__helper.

Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n50 => 0
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n60 => 1
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n70 => 2
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n80 => 3
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n90 => 4
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n100 => 5
  end.
Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n50
  | 1 => CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n60
  | 2 => CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n70
  | 3 => CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n80
  | 4 => CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n90
  | 5 => CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n100
  | _ => CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__n50
  end.
Lemma CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F1F2 : forall x : CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Type, (CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F1 x <= 5) /\ CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F2 (CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F2F1 : forall (y : nat) (H : y <= 5), CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F1 (CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Type : Set :=
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n50
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n60
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n70
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n80
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n90
 | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n100
.
Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__cond := (fun (_ : CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Type) => True).
Lemma CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__nat__helper.

Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n50 => 0
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n60 => 1
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n70 => 2
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n80 => 3
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n90 => 4
  | CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n100 => 5
  end.
Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n50
  | 1 => CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n60
  | 2 => CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n70
  | 3 => CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n80
  | 4 => CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n90
  | 5 => CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n100
  | _ => CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__n50
  end.
Lemma CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F1F2 : forall x : CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Type, (CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F1 x <= 5) /\ CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F2 (CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F2F1 : forall (y : nat) (H : y <= 5), CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F1 (CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1700__beamManagementType_CBM_r17__Type : Set :=
 | CA_ParametersNR_v1700__beamManagementType_CBM_r17__supported
.
Definition CA_ParametersNR_v1700__beamManagementType_CBM_r17__cond := (fun (_ : CA_ParametersNR_v1700__beamManagementType_CBM_r17__Type) => True).
Lemma CA_ParametersNR_v1700__beamManagementType_CBM_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__beamManagementType_CBM_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1700__beamManagementType_CBM_r17__nat__helper.

Definition CA_ParametersNR_v1700__beamManagementType_CBM_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__beamManagementType_CBM_r17__supported => 0
  end.
Definition CA_ParametersNR_v1700__beamManagementType_CBM_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__beamManagementType_CBM_r17__supported
  | _ => CA_ParametersNR_v1700__beamManagementType_CBM_r17__supported
  end.
Lemma CA_ParametersNR_v1700__beamManagementType_CBM_r17__F1F2 : forall x : CA_ParametersNR_v1700__beamManagementType_CBM_r17__Type, (CA_ParametersNR_v1700__beamManagementType_CBM_r17__F1 x <= 0) /\ CA_ParametersNR_v1700__beamManagementType_CBM_r17__F2 (CA_ParametersNR_v1700__beamManagementType_CBM_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__beamManagementType_CBM_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1700__beamManagementType_CBM_r17__F1 (CA_ParametersNR_v1700__beamManagementType_CBM_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Type : Set :=
 | CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__supported
.
Definition CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__cond := (fun (_ : CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Type) => True).
Lemma CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__nat__helper.

Definition CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__supported => 0
  end.
Definition CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__supported
  | _ => CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__supported
  end.
Lemma CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F1F2 : forall x : CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Type, (CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F1 x <= 0) /\ CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F2 (CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F1 (CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CodebookComboParameterMixedTypePerBC_r17.

Opaque CodebookComboParameterMixedTypePerBC_r17__cond CodebookComboParameterMixedTypePerBC_r17__Format.

Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__helper1 : (2 <= 8)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__helper2 : to_bit_sz (Z.to_nat (8 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__Type := Z.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__cond := (fun z => (2 <= z <= 8)%Z).
Inductive CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Type : Set :=
 | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__mode1
 | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__mode2
 | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__both
.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__cond := (fun (_ : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Type) => True).
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__nat__helper.

Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__mode1 => 0
  | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__mode2 => 1
  | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__both => 2
  end.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__mode1
  | 1 => CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__mode2
  | 2 => CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__both
  | _ => CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__mode1
  end.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F1F2 : forall x : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Type, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F1 x <= 2) /\ CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F2 (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F1 (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CSI_MultiTRP_SupportedCombinations_r17.

Opaque CSI_MultiTRP_SupportedCombinations_r17__cond CSI_MultiTRP_SupportedCombinations_r17__Format.

Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__Type := list CSI_MultiTRP_SupportedCombinations_r17__Type.

Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__helper1 : (0 <= 1 <= 16)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__cond (z : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__Type) :=  (1 <= Z.of_nat (length z) <= 16)%Z /\ (list_and CSI_MultiTRP_SupportedCombinations_r17__cond z) .

Inductive CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Type : Set :=
 | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__mode1
 | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__mode1And2
.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__cond := (fun (_ : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Type) => True).
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__nat__helper.

Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__mode1 => 0
  | CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__mode1And2 => 1
  end.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__mode1
  | 1 => CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__mode1And2
  | _ => CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__mode1
  end.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F1F2 : forall x : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Type, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F1 x <= 1) /\ CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F2 (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F2F1 : forall (y : nat) (H : y <= 1), CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F1 (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F2 y) = y. enum_solve H y. Qed.

Record CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Type : Set :=
  make__CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Type {
    CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17 : Z ;
    CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17 : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Type ;
    CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17 : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__Type ;
    CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17 : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Type ;
}.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list := (
 Nor Z CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__cond ::
 Nor CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Type CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__cond ::
 Nor CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__Type CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__cond ::
 Nor CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Type CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__cond ::
 nil).
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond z := 
  CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__cond (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17 z) /\
  CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__cond (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17 z) /\
  CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__cond (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17 z) /\
  CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__cond (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17 z) /\
  True.

Require Import NR.CodebookComboParameterMultiTRP_PerBC_r17.

Opaque CodebookComboParameterMultiTRP_PerBC_r17__cond CodebookComboParameterMultiTRP_PerBC_r17__Format.

Inductive CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Type : Set :=
 | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n1
 | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n2
 | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n3
 | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n4
 | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n6
 | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n8
 | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n16
 | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n32
.
Definition CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__cond := (fun (_ : CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Type) => True).
Lemma CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__nat__helper.

Definition CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n1 => 0
  | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n2 => 1
  | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n3 => 2
  | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n4 => 3
  | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n6 => 4
  | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n8 => 5
  | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n16 => 6
  | CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n32 => 7
  end.
Definition CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n1
  | 1 => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n2
  | 2 => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n3
  | 3 => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n4
  | 4 => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n6
  | 5 => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n8
  | 6 => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n16
  | 7 => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n32
  | _ => CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__n1
  end.
Lemma CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F1F2 : forall x : CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Type, (CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F1 x <= 7) /\ CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F2 (CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F2F1 : forall (y : nat) (H : y <= 7), CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F1 (CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Type : Set :=
 | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n1
 | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n2
 | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n3
 | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n4
 | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n5
 | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n8
 | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n16
 | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n32
.
Definition CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__cond := (fun (_ : CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Type) => True).
Lemma CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__nat__helper.

Definition CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n1 => 0
  | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n2 => 1
  | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n3 => 2
  | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n4 => 3
  | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n5 => 4
  | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n8 => 5
  | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n16 => 6
  | CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n32 => 7
  end.
Definition CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n1
  | 1 => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n2
  | 2 => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n3
  | 3 => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n4
  | 4 => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n5
  | 5 => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n8
  | 6 => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n16
  | 7 => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n32
  | _ => CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__n1
  end.
Lemma CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F1F2 : forall x : CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Type, (CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F1 x <= 7) /\ CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F2 (CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F2F1 : forall (y : nat) (H : y <= 7), CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F1 (CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CrossCarrierSchedulingSCell_SpCell_r17.

Opaque CrossCarrierSchedulingSCell_SpCell_r17__cond CrossCarrierSchedulingSCell_SpCell_r17__Format.

Require Import NR.CrossCarrierSchedulingSCell_SpCell_r17.

Opaque CrossCarrierSchedulingSCell_SpCell_r17__cond CrossCarrierSchedulingSCell_SpCell_r17__Format.

Inductive CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Type : Set :=
 | CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__supported
.
Definition CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__cond := (fun (_ : CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Type) => True).
Lemma CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__nat__helper.

Definition CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__supported => 0
  end.
Definition CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__supported
  | _ => CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__supported
  end.
Lemma CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F1F2 : forall x : CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Type, (CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F1 x <= 0) /\ CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F2 (CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F1 (CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Type : Set :=
 | CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__supported
.
Definition CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__cond := (fun (_ : CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Type) => True).
Lemma CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__nat__helper.

Definition CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__supported => 0
  end.
Definition CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__supported
  | _ => CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__supported
  end.
Lemma CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F1F2 : forall x : CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Type, (CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F1 x <= 0) /\ CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F2 (CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F1 (CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Type : Set :=
 | CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__supported
.
Definition CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__cond := (fun (_ : CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Type) => True).
Lemma CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__nat__helper.

Definition CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F1 t :=
  match t with
  | CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__supported => 0
  end.
Definition CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__supported
  | _ => CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__supported
  end.
Lemma CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F1F2 : forall x : CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Type, (CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F1 x <= 0) /\ CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F2 (CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F1 (CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F2 y) = y. enum_solve H y. Qed.

Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__helper1 : (0 <= 1 <= 496)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__helper2 : to_bit_sz (Z.to_nat (496 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (496 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__Type := bit_string.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 496)%Z /\ bit_string_len_prop (fst z) (snd z)).
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__helper1 : (0 <= 1 <= 496)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__helper2 : to_bit_sz (Z.to_nat (496 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (496 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__Type := bit_string.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 496)%Z /\ bit_string_len_prop (fst z) (snd z)).
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__helper1 : (0 <= 1 <= 496)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__helper2 : to_bit_sz (Z.to_nat (496 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (496 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__Type := bit_string.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 496)%Z /\ bit_string_len_prop (fst z) (snd z)).
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__helper1 : (0 <= 1 <= 496)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__helper2 : to_bit_sz (Z.to_nat (496 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (496 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__Type := bit_string.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 496)%Z /\ bit_string_len_prop (fst z) (snd z)).
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__helper1 : (0 <= 1 <= 496)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__helper2 : to_bit_sz (Z.to_nat (496 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (496 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__Type := bit_string.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 496)%Z /\ bit_string_len_prop (fst z) (snd z)).
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__helper1 : (0 <= 1 <= 496)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__helper2 : to_bit_sz (Z.to_nat (496 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (496 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__Type := bit_string.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 496)%Z /\ bit_string_len_prop (fst z) (snd z)).
Record CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Type : Set :=
  make__CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Type {
    CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17 : option CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__Type ;
    CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17 : option CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__Type ;
    CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17 : option CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__Type ;
    CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17 : option CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__Type ;
    CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17 : option CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__Type ;
    CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17 : option CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__Type ;
}.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list := (
 Opt CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__cond ::
 Opt CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__cond ::
 Opt CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__cond ::
 Opt CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__cond ::
 Opt CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__cond ::
 Opt CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__cond ::
 nil).
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond z := 
  opt_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__cond (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17 z) /\
  opt_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__cond (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17 z) /\
  opt_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__cond (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17 z) /\
  opt_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__cond (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17 z) /\
  opt_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__cond (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17 z) /\
  opt_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__cond (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17 z) /\
  True.

Record CA_ParametersNR_v1700__Type : Set :=
  make__CA_ParametersNR_v1700__Type {
    CA_ParametersNR_v1700__codebookParametersfetype2PerBC_r17 : option CodebookParametersfetype2PerBC_r17__Type ;
    CA_ParametersNR_v1700__demodulationEnhancementCA_r17 : option CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Type ;
    CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17 : option CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Type ;
    CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17 : option CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Type ;
    CA_ParametersNR_v1700__beamManagementType_CBM_r17 : option CA_ParametersNR_v1700__beamManagementType_CBM_r17__Type ;
    CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17 : option CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Type ;
    CA_ParametersNR_v1700__codebookComboParameterMixedTypePerBC_r17 : option CodebookComboParameterMixedTypePerBC_r17__Type ;
    CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17 : option CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Type ;
    CA_ParametersNR_v1700__codebookComboParameterMultiTRP_PerBC_r17 : option CodebookComboParameterMultiTRP_PerBC_r17__Type ;
    CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17 : option CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Type ;
    CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17 : option CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Type ;
    CA_ParametersNR_v1700__crossCarrierSchedulingSCell_SpCellTypeB_r17 : option CrossCarrierSchedulingSCell_SpCell_r17__Type ;
    CA_ParametersNR_v1700__crossCarrierSchedulingSCell_SpCellTypeA_r17 : option CrossCarrierSchedulingSCell_SpCell_r17__Type ;
    CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17 : option CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Type ;
    CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17 : option CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Type ;
    CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17 : option CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Type ;
    CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17 : option CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Type ;
}.
Definition CA_ParametersNR_v1700__list := (
 Opt CodebookParametersfetype2PerBC_r17__Type CodebookParametersfetype2PerBC_r17__cond ::
 Opt CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Type CA_ParametersNR_v1700__demodulationEnhancementCA_r17__cond ::
 Opt CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Type CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__cond ::
 Opt CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Type CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__cond ::
 Opt CA_ParametersNR_v1700__beamManagementType_CBM_r17__Type CA_ParametersNR_v1700__beamManagementType_CBM_r17__cond ::
 Opt CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Type CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__cond ::
 Opt CodebookComboParameterMixedTypePerBC_r17__Type CodebookComboParameterMixedTypePerBC_r17__cond ::
 Opt CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Type CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond ::
 Opt CodebookComboParameterMultiTRP_PerBC_r17__Type CodebookComboParameterMultiTRP_PerBC_r17__cond ::
 Opt CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Type CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__cond ::
 Opt CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Type CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__cond ::
 Opt CrossCarrierSchedulingSCell_SpCell_r17__Type CrossCarrierSchedulingSCell_SpCell_r17__cond ::
 Opt CrossCarrierSchedulingSCell_SpCell_r17__Type CrossCarrierSchedulingSCell_SpCell_r17__cond ::
 Opt CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Type CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__cond ::
 Opt CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Type CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__cond ::
 Opt CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Type CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__cond ::
 Opt CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond ::
 nil).
Definition CA_ParametersNR_v1700__cond z := 
  opt_cond CodebookParametersfetype2PerBC_r17__cond (CA_ParametersNR_v1700__codebookParametersfetype2PerBC_r17 z) /\
  opt_cond CA_ParametersNR_v1700__demodulationEnhancementCA_r17__cond (CA_ParametersNR_v1700__demodulationEnhancementCA_r17 z) /\
  opt_cond CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__cond (CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17 z) /\
  opt_cond CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__cond (CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17 z) /\
  opt_cond CA_ParametersNR_v1700__beamManagementType_CBM_r17__cond (CA_ParametersNR_v1700__beamManagementType_CBM_r17 z) /\
  opt_cond CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__cond (CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17 z) /\
  opt_cond CodebookComboParameterMixedTypePerBC_r17__cond (CA_ParametersNR_v1700__codebookComboParameterMixedTypePerBC_r17 z) /\
  opt_cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17 z) /\
  opt_cond CodebookComboParameterMultiTRP_PerBC_r17__cond (CA_ParametersNR_v1700__codebookComboParameterMultiTRP_PerBC_r17 z) /\
  opt_cond CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__cond (CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17 z) /\
  opt_cond CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__cond (CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17 z) /\
  opt_cond CrossCarrierSchedulingSCell_SpCell_r17__cond (CA_ParametersNR_v1700__crossCarrierSchedulingSCell_SpCellTypeB_r17 z) /\
  opt_cond CrossCarrierSchedulingSCell_SpCell_r17__cond (CA_ParametersNR_v1700__crossCarrierSchedulingSCell_SpCellTypeA_r17 z) /\
  opt_cond CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__cond (CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17 z) /\
  opt_cond CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__cond (CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17 z) /\
  opt_cond CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__cond (CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17 z) /\
  opt_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17 z) /\
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
Definition CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Format : T_Format CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__demodulationEnhancementCA_r17__nat__Format CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F1 CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F2 CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F1F2 CA_ParametersNR_v1700__demodulationEnhancementCA_r17__F2F1.

Opaque CA_ParametersNR_v1700__demodulationEnhancementCA_r17__cond CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Format.

Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Format : T_Format CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__nat__Format CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F1 CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F2 CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F1F2 CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__F2F1.

Opaque CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__cond CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Format.

Definition CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Format : T_Format CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__nat__Format CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F1 CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F2 CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F1F2 CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__F2F1.

Opaque CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__cond CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Format.

Definition CA_ParametersNR_v1700__beamManagementType_CBM_r17__Format : T_Format CA_ParametersNR_v1700__beamManagementType_CBM_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__beamManagementType_CBM_r17__nat__Format CA_ParametersNR_v1700__beamManagementType_CBM_r17__F1 CA_ParametersNR_v1700__beamManagementType_CBM_r17__F2 CA_ParametersNR_v1700__beamManagementType_CBM_r17__F1F2 CA_ParametersNR_v1700__beamManagementType_CBM_r17__F2F1.

Opaque CA_ParametersNR_v1700__beamManagementType_CBM_r17__cond CA_ParametersNR_v1700__beamManagementType_CBM_r17__Format.

Definition CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Format : T_Format CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__nat__Format CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F1 CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F2 CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F1F2 CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__F2F1.

Opaque CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__cond CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Format.

Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__Format : T_Format Z CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__cond :=
 ranged_int_format (2) (8) CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__helper1 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__helper2.

Opaque CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__Format.

Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Format : T_Format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__nat__Format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F1 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F2 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F1F2 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__F2F1.

Opaque CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Format.

Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__Format : T_Format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__Type CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__cond := seq_of_format CSI_MultiTRP_SupportedCombinations_r17__Format 1 16 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__helper1 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__helper2.

Opaque CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__Format.

Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Format : T_Format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__nat__Format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F1 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F2 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F1F2 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__F2F1.

Opaque CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Format.


Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Format_list : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Format_Type :=
  (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17__Format, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17__Format, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17__Format, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17__Format, unit_format)))).
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Format_list.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1 z :=
  (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__maxNumNZP_CSI_RS_r17 z, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cSI_Report_mode_r17 z, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__supportedComboAcrossCCs_r17 z, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__codebookMode_NCJT_r17 z, tt)))).
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F2 (y : seq_type CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Type i0 i1 i2 i3
  end.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1F2_cond (z : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Type)
  : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond z ->
  (seq_cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1 z)).
intro H. unfold CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1F2_cond2 (z : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Type)
 : CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F2 (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F2F1_cond (y : seq_type CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list)
  : seq_cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list y ->
 (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F2 y)) /\  CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1 (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Format : T_Format CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Type CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond :=
        proj2_format  CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__list__Format
    CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F2 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1F2_cond  CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F1F2_cond2 CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__F2F1_cond.
Opaque CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__cond CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Format.

Definition CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Format : T_Format CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__nat__Format CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F1 CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F2 CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F1F2 CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__F2F1.

Opaque CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__cond CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Format.

Definition CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Format : T_Format CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__nat__Format CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F1 CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F2 CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F1F2 CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__F2F1.

Opaque CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__cond CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Format.

Definition CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Format : T_Format CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__nat__Format CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F1 CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F2 CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F1F2 CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__F2F1.

Opaque CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__cond CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Format.

Definition CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Format : T_Format CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__nat__Format CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F1 CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F2 CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F1F2 CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__F2F1.

Opaque CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__cond CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Format.

Definition CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Format : T_Format CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__nat__Format CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F1 CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F2 CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F1F2 CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__F2F1.

Opaque CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__cond CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Format.

Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__Format : T_Format CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 496 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__helper1 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__helper2.
Opaque CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__Format.

Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__Format : T_Format CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 496 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__helper1 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__helper2.
Opaque CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__Format.

Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__Format : T_Format CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 496 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__helper1 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__helper2.
Opaque CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__Format.

Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__Format : T_Format CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 496 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__helper1 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__helper2.
Opaque CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__Format.

Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__Format : T_Format CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 496 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__helper1 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__helper2.
Opaque CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__Format.

Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__Format : T_Format CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__cond := (* Eval compute in *) bit_string_ranged_format 1 496 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__helper1 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__helper2.
Opaque CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__Format.


Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Format_list : CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Format_Type :=
  (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17__Format, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17__Format, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17__Format, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17__Format, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17__Format, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17__Format, unit_format)))))).
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Format_list.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1 z :=
  (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_15kHz_r17 z, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_30kHz_r17 z, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs15kHz_60kHz_r17 z, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_30kHz_r17 z, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs30kHz_60kHz_r17 z, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__scs60kHz_60kHz_r17 z, tt)))))).
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F2 (y : seq_type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Type i0 i1 i2 i3 i4 i5
  end.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1F2_cond (z : CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Type)
  : CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond z ->
  (seq_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1 z)).
intro H. unfold CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1F2_cond2 (z : CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Type)
 : CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F2 (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F2F1_cond (y : seq_type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list)
  : seq_cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list y ->
 (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F2 y)) /\  CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1 (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Format : T_Format CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Type CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond :=
        proj2_format  CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__list__Format
    CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F2 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1F2_cond  CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F1F2_cond2 CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__F2F1_cond.
Opaque CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__cond CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Format.


Definition CA_ParametersNR_v1700__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1700__list.
Definition CA_ParametersNR_v1700__Format_list : CA_ParametersNR_v1700__Format_Type :=
  (CodebookParametersfetype2PerBC_r17__Format, (CA_ParametersNR_v1700__demodulationEnhancementCA_r17__Format, (CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17__Format, (CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17__Format, (CA_ParametersNR_v1700__beamManagementType_CBM_r17__Format, (CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17__Format, (CodebookComboParameterMixedTypePerBC_r17__Format, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17__Format, (CodebookComboParameterMultiTRP_PerBC_r17__Format, (CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17__Format, (CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17__Format, (CrossCarrierSchedulingSCell_SpCell_r17__Format, (CrossCarrierSchedulingSCell_SpCell_r17__Format, (CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17__Format, (CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17__Format, (CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17__Format, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17__Format, unit_format))))))))))))))))).
Definition CA_ParametersNR_v1700__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1700__list CA_ParametersNR_v1700__Format_list.
Definition CA_ParametersNR_v1700__F1 z :=
  (CA_ParametersNR_v1700__codebookParametersfetype2PerBC_r17 z, (CA_ParametersNR_v1700__demodulationEnhancementCA_r17 z, (CA_ParametersNR_v1700__maxUplinkDutyCycle_interBandCA_PC2_r17 z, (CA_ParametersNR_v1700__maxUplinkDutyCycle_SULcombination_PC2_r17 z, (CA_ParametersNR_v1700__beamManagementType_CBM_r17 z, (CA_ParametersNR_v1700__parallelTxPUCCH_PUSCH_r17 z, (CA_ParametersNR_v1700__codebookComboParameterMixedTypePerBC_r17 z, (CA_ParametersNR_v1700__mTRP_CSI_EnhancementPerBC_r17 z, (CA_ParametersNR_v1700__codebookComboParameterMultiTRP_PerBC_r17 z, (CA_ParametersNR_v1700__maxCC_32_DL_HARQ_ProcessFR2_2_r17 z, (CA_ParametersNR_v1700__maxCC_32_UL_HARQ_ProcessFR2_2_r17 z, (CA_ParametersNR_v1700__crossCarrierSchedulingSCell_SpCellTypeB_r17 z, (CA_ParametersNR_v1700__crossCarrierSchedulingSCell_SpCellTypeA_r17 z, (CA_ParametersNR_v1700__dci_FormatsPCellPSCellUSS_Sets_r17 z, (CA_ParametersNR_v1700__disablingScalingFactorDeactSCell_r17 z, (CA_ParametersNR_v1700__disablingScalingFactorDormantSCell_r17 z, (CA_ParametersNR_v1700__non_AlignedFrameBoundaries_r17 z, tt))))))))))))))))).
Definition CA_ParametersNR_v1700__F2 (y : seq_type CA_ParametersNR_v1700__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, _)))))))))))))))))=>
    make__CA_ParametersNR_v1700__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16
  end.
Lemma CA_ParametersNR_v1700__F1F2_cond (z : CA_ParametersNR_v1700__Type)
  : CA_ParametersNR_v1700__cond z ->
  (seq_cond CA_ParametersNR_v1700__list (CA_ParametersNR_v1700__F1 z)).
intro H. unfold CA_ParametersNR_v1700__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1700__F1F2_cond2 (z : CA_ParametersNR_v1700__Type)
 : CA_ParametersNR_v1700__F2 (CA_ParametersNR_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1700__F2F1_cond (y : seq_type CA_ParametersNR_v1700__list)
  : seq_cond CA_ParametersNR_v1700__list y ->
 (CA_ParametersNR_v1700__cond (CA_ParametersNR_v1700__F2 y)) /\  CA_ParametersNR_v1700__F1 (CA_ParametersNR_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1700__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1700__Format : T_Format CA_ParametersNR_v1700__Type CA_ParametersNR_v1700__cond :=
        proj2_format  CA_ParametersNR_v1700__cond CA_ParametersNR_v1700__list__Format
    CA_ParametersNR_v1700__F1 CA_ParametersNR_v1700__F2 CA_ParametersNR_v1700__F1F2_cond  CA_ParametersNR_v1700__F1F2_cond2 CA_ParametersNR_v1700__F2F1_cond.
Opaque CA_ParametersNR_v1700__cond CA_ParametersNR_v1700__Format.

