Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Type : Set :=
 | CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__supported
.
Definition CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__cond := (fun (_ : CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Type) => True).
Lemma CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__nat__helper.

Definition CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__supported
  | _ => CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__supported
  end.
Lemma CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F1F2 : forall x : CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Type, (CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F2 (CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F1 (CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__msgA_SUL_r16__Type : Set :=
 | CA_ParametersNR_v1610__msgA_SUL_r16__supported
.
Definition CA_ParametersNR_v1610__msgA_SUL_r16__cond := (fun (_ : CA_ParametersNR_v1610__msgA_SUL_r16__Type) => True).
Lemma CA_ParametersNR_v1610__msgA_SUL_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__msgA_SUL_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__msgA_SUL_r16__nat__helper.

Definition CA_ParametersNR_v1610__msgA_SUL_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__msgA_SUL_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__msgA_SUL_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__msgA_SUL_r16__supported
  | _ => CA_ParametersNR_v1610__msgA_SUL_r16__supported
  end.
Lemma CA_ParametersNR_v1610__msgA_SUL_r16__F1F2 : forall x : CA_ParametersNR_v1610__msgA_SUL_r16__Type, (CA_ParametersNR_v1610__msgA_SUL_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__msgA_SUL_r16__F2 (CA_ParametersNR_v1610__msgA_SUL_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__msgA_SUL_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__msgA_SUL_r16__F1 (CA_ParametersNR_v1610__msgA_SUL_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Type : Set :=
 | CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__supported
.
Definition CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__cond := (fun (_ : CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Type) => True).
Lemma CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__nat__helper.

Definition CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__supported
  | _ => CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__supported
  end.
Lemma CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F1F2 : forall x : CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Type, (CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F2 (CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F1 (CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Type : Set :=
 | CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__supported
.
Definition CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__cond := (fun (_ : CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__nat__helper.

Definition CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__supported
  | _ => CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__supported
  end.
Lemma CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F1F2 : forall x : CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Type, (CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F2 (CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F1 (CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Type : Set :=
 | CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__supported
.
Definition CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__cond := (fun (_ : CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Type) => True).
Lemma CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__nat__helper.

Definition CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__supported
  | _ => CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__supported
  end.
Lemma CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F1F2 : forall x : CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Type, (CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F2 (CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F1 (CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Type : Set :=
 | CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__supported
.
Definition CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__cond := (fun (_ : CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Type) => True).
Lemma CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__nat__helper.

Definition CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__supported
  | _ => CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__supported
  end.
Lemma CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F1F2 : forall x : CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Type, (CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F2 (CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F1 (CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Type : Set :=
 | CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__higherA_CSI_SCS
 | CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__lowerA_CSI_SCS
 | CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__both
.
Definition CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__cond := (fun (_ : CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__nat__helper.

Definition CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__higherA_CSI_SCS => 0
  | CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__lowerA_CSI_SCS => 1
  | CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__both => 2
  end.
Definition CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__higherA_CSI_SCS
  | 1 => CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__lowerA_CSI_SCS
  | 2 => CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__both
  | _ => CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__higherA_CSI_SCS
  end.
Lemma CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F1F2 : forall x : CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Type, (CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F1 x <= 2) /\ CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F2 (CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F1 (CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Type : Set :=
 | CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__diffOnly
 | CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__both
.
Definition CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__cond := (fun (_ : CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Type) => True).
Lemma CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__nat__helper.

Definition CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__diffOnly => 0
  | CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__both => 1
  end.
Definition CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__diffOnly
  | 1 => CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__both
  | _ => CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__diffOnly
  end.
Lemma CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F1F2 : forall x : CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Type, (CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F1 x <= 1) /\ CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F2 (CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F2F1 : forall (y : nat) (H : y <= 1), CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F1 (CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Type : Set :=
 | CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__supported
.
Definition CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__cond := (fun (_ : CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Type) => True).
Lemma CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__nat__helper.

Definition CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__supported
  | _ => CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__supported
  end.
Lemma CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F1F2 : forall x : CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Type, (CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F2 (CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F1 (CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Type : Set :=
 | CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__n2
.
Definition CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__cond := (fun (_ : CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Type) => True).
Lemma CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__nat__helper.

Definition CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__n2 => 0
  end.
Definition CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__n2
  | _ => CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__n2
  end.
Lemma CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F1F2 : forall x : CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Type, (CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F2 (CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F1 (CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Type : Set :=
 | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__supported
.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__cond := (fun (_ : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__nat__helper.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__supported
  | _ => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__supported
  end.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F1F2 : forall x : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Type, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F2 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F1 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Type : Set :=
 | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__supported
.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__cond := (fun (_ : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__nat__helper.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__supported
  | _ => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__supported
  end.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F1F2 : forall x : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Type, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F2 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F1 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Type : Set :=
 | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__supported
.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__cond := (fun (_ : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__nat__helper.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__supported
  | _ => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__supported
  end.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F1F2 : forall x : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Type, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F2 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F1 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Type : Set :=
 | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__supported
.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__cond := (fun (_ : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Type) => True).
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__nat__helper.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__supported
  | _ => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__supported
  end.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F1F2 : forall x : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Type, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F2 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F1 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Type : Set :=
 | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__supported
.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__cond := (fun (_ : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Type) => True).
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__nat__helper.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__supported
  | _ => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__supported
  end.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F1F2 : forall x : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Type, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F2 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F1 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Type : Set :=
 | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__short
 | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__long
.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__cond := (fun (_ : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__nat__helper.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__short => 0
  | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__long => 1
  end.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__short
  | 1 => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__long
  | _ => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__short
  end.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F1F2 : forall x : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Type, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F1 x <= 1) /\ CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F2 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F2F1 : forall (y : nat) (H : y <= 1), CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F1 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Type : Set :=
 | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__supported
.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__cond := (fun (_ : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__nat__helper.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__supported => 0
  end.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__supported
  | _ => CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__supported
  end.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F1F2 : forall x : CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Type, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F2 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F1 (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F2 y) = y. enum_solve H y. Qed.

Record CA_ParametersNR_v1610__interFreqDAPS_r16__Type : Set :=
  make__CA_ParametersNR_v1610__interFreqDAPS_r16__Type {
    CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16 : option CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Type ;
    CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16 : option CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Type ;
    CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16 : option CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Type ;
    CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16 : option CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Type ;
    CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16 : option CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Type ;
    CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16 : option CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Type ;
    CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16 : option CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Type ;
}.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__list := (
 Opt CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__cond ::
 Opt CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__cond ::
 Opt CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__cond ::
 Opt CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__cond ::
 Opt CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__cond ::
 Opt CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__cond ::
 Opt CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__cond ::
 nil).
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__cond z := 
  opt_cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16 z) /\
  opt_cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16 z) /\
  opt_cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16 z) /\
  opt_cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16 z) /\
  opt_cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16 z) /\
  opt_cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16 z) /\
  opt_cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16 z) /\
  True.

Require Import NR.CodebookParameters_v1610.

Opaque CodebookParameters_v1610__cond CodebookParameters_v1610__Format.

Lemma CA_ParametersNR_v1610__blindDetectFactor_r16__helper1 : (1 <= 2)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__blindDetectFactor_r16__helper2 : to_bit_sz (Z.to_nat (2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__blindDetectFactor_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__blindDetectFactor_r16__Type := Z.
Definition CA_ParametersNR_v1610__blindDetectFactor_r16__cond := (fun z => (1 <= z <= 2)%Z).
Lemma CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__helper1 : (2 <= 16)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__helper2 : to_bit_sz (Z.to_nat (16 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__cond := (fun z => (2 <= z <= 16)%Z).
Inductive CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Type : Set :=
 | CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__alignedOnly
 | CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__alignedAndNonAligned
.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__cond := (fun (_ : CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Type) => True).
Lemma CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__nat__helper.

Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__alignedOnly => 0
  | CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__alignedAndNonAligned => 1
  end.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__alignedOnly
  | 1 => CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__alignedAndNonAligned
  | _ => CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__alignedOnly
  end.
Lemma CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F1F2 : forall x : CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Type, (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F1 x <= 1) /\ CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F2 (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F2F1 : forall (y : nat) (H : y <= 1), CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F1 (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F2 y) = y. enum_solve H y. Qed.

Record CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Type : Set :=
  make__CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Type {
    CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16 : Z ;
    CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16 : CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Type ;
}.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list := (
 Nor Z CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__cond ::
 Nor CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Type CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__cond ::
 nil).
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond z := 
  CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__cond (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16 z) /\
  CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__cond (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16 z) /\
  True.

Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__cond := (fun z => (1 <= z <= 15)%Z).
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__cond := (fun z => (1 <= z <= 15)%Z).
Inductive CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Type : Set :=
 | CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__alignedOnly
 | CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__alignedAndNonAligned
.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__cond := (fun (_ : CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Type) => True).
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__nat__helper.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__alignedOnly => 0
  | CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__alignedAndNonAligned => 1
  end.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__alignedOnly
  | 1 => CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__alignedAndNonAligned
  | _ => CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__alignedOnly
  end.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F1F2 : forall x : CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Type, (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F1 x <= 1) /\ CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F2 (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F2F1 : forall (y : nat) (H : y <= 1), CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F1 (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F2 y) = y. enum_solve H y. Qed.

Record CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Type : Set :=
  make__CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Type {
    CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16 : Z ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16 : Z ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16 : CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Type ;
}.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list := (
 Nor Z CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__cond ::
 Nor Z CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__cond ::
 Nor CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Type CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__cond ::
 nil).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond z := 
  CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16 z) /\
  CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16 z) /\
  CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16 z) /\
  True.

Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__helper1 : (1 <= 14)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__helper2 : to_bit_sz (Z.to_nat (14 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (14 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__cond := (fun z => (1 <= z <= 14)%Z).
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__helper1 : (1 <= 14)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__helper2 : to_bit_sz (Z.to_nat (14 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (14 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__cond := (fun z => (1 <= z <= 14)%Z).
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__cond := (fun z => (0 <= z <= 15)%Z).
Record CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Type : Set :=
  make__CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Type {
    CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16 : Z ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16 : Z ;
}.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list := (
 Nor Z CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__cond ::
 Nor Z CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__cond ::
 nil).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond z := 
  CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16 z) /\
  CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16 z) /\
  True.

Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__Type := Z.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__cond := (fun z => (0 <= z <= 15)%Z).
Record CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Type : Set :=
  make__CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Type {
    CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16 : Z ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16 : Z ;
}.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list := (
 Nor Z CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__cond ::
 Nor Z CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__cond ::
 nil).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond z := 
  CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16 z) /\
  CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16 z) /\
  True.

Inductive CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Type : Set :=
 | CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__low_to_high
 | CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__high_to_low
 | CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__both
.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__cond := (fun (_ : CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__nat__helper.

Definition CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__low_to_high => 0
  | CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__high_to_low => 1
  | CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__both => 2
  end.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__low_to_high
  | 1 => CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__high_to_low
  | 2 => CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__both
  | _ => CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__low_to_high
  end.
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F1F2 : forall x : CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Type, (CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F1 x <= 2) /\ CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F2 (CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F1 (CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Type : Set :=
 | CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__diff_only
 | CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__both
.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__cond := (fun (_ : CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Type) => True).
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__nat__helper.

Definition CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__diff_only => 0
  | CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__both => 1
  end.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__diff_only
  | 1 => CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__both
  | _ => CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__diff_only
  end.
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F1F2 : forall x : CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Type, (CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F1 x <= 1) /\ CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F2 (CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F2F1 : forall (y : nat) (H : y <= 1), CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F1 (CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Type : Set :=
 | CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__low_to_high
 | CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__high_to_low
 | CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__both
.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__cond := (fun (_ : CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Type) => True).
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__nat__helper.

Definition CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__low_to_high => 0
  | CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__high_to_low => 1
  | CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__both => 2
  end.
Definition CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__low_to_high
  | 1 => CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__high_to_low
  | 2 => CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__both
  | _ => CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__low_to_high
  end.
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F1F2 : forall x : CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Type, (CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F1 x <= 2) /\ CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F2 (CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F2F1 : forall (y : nat) (H : y <= 2), CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F1 (CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Type : Set :=
 | CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__n2
.
Definition CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__cond := (fun (_ : CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Type) => True).
Lemma CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__nat__helper.

Definition CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F1 t :=
  match t with
  | CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__n2 => 0
  end.
Definition CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F2 n :=
  match n with
  | 0 => CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__n2
  | _ => CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__n2
  end.
Lemma CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F1F2 : forall x : CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Type, (CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F1 x <= 0) /\ CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F2 (CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F1 x) = x. imp_solve. Qed.
Lemma CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F2F1 : forall (y : nat) (H : y <= 0), CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F1 (CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CodebookParametersAdditionPerBC_r16.

Opaque CodebookParametersAdditionPerBC_r16__cond CodebookParametersAdditionPerBC_r16__Format.

Require Import NR.CodebookComboParametersAdditionPerBC_r16.

Opaque CodebookComboParametersAdditionPerBC_r16__cond CodebookComboParametersAdditionPerBC_r16__Format.

Record CA_ParametersNR_v1610__Type : Set :=
  make__CA_ParametersNR_v1610__Type {
    CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16 : option CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Type ;
    CA_ParametersNR_v1610__msgA_SUL_r16 : option CA_ParametersNR_v1610__msgA_SUL_r16__Type ;
    CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16 : option CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Type ;
    CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16 : option CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Type ;
    CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16 : option CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Type ;
    CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16 : option CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Type ;
    CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16 : option CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Type ;
    CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16 : option CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Type ;
    CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16 : option CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Type ;
    CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16 : option CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Type ;
    CA_ParametersNR_v1610__interFreqDAPS_r16 : option CA_ParametersNR_v1610__interFreqDAPS_r16__Type ;
    CA_ParametersNR_v1610__codebookParametersPerBC_r16 : option CodebookParameters_v1610__Type ;
    CA_ParametersNR_v1610__blindDetectFactor_r16 : option Z ;
    CA_ParametersNR_v1610__pdcch_MonitoringCA_r16 : option CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Type ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16 : option CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Type ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16 : option Z ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16 : option Z ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16 : option CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Type ;
    CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16 : option CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Type ;
    CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16 : option CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Type ;
    CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16 : option CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Type ;
    CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16 : option CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Type ;
    CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16 : option CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Type ;
    CA_ParametersNR_v1610__codebookParametersAdditionPerBC_r16 : option CodebookParametersAdditionPerBC_r16__Type ;
    CA_ParametersNR_v1610__codebookComboParametersAdditionPerBC_r16 : option CodebookComboParametersAdditionPerBC_r16__Type ;
}.
Definition CA_ParametersNR_v1610__list := (
 Opt CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Type CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__cond ::
 Opt CA_ParametersNR_v1610__msgA_SUL_r16__Type CA_ParametersNR_v1610__msgA_SUL_r16__cond ::
 Opt CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Type CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__cond ::
 Opt CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Type CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__cond ::
 Opt CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Type CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__cond ::
 Opt CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Type CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__cond ::
 Opt CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Type CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__cond ::
 Opt CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Type CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__cond ::
 Opt CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Type CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__cond ::
 Opt CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Type CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__cond ::
 Opt CA_ParametersNR_v1610__interFreqDAPS_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__cond ::
 Opt CodebookParameters_v1610__Type CodebookParameters_v1610__cond ::
 Opt Z CA_ParametersNR_v1610__blindDetectFactor_r16__cond ::
 Opt CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Type CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond ::
 Opt CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Type CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond ::
 Opt Z CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__cond ::
 Opt Z CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__cond ::
 Opt CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Type CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond ::
 Opt CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Type CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond ::
 Opt CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Type CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__cond ::
 Opt CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Type CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__cond ::
 Opt CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Type CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__cond ::
 Opt CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Type CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__cond ::
 Opt CodebookParametersAdditionPerBC_r16__Type CodebookParametersAdditionPerBC_r16__cond ::
 Opt CodebookComboParametersAdditionPerBC_r16__Type CodebookComboParametersAdditionPerBC_r16__cond ::
 nil).
Definition CA_ParametersNR_v1610__cond z := 
  opt_cond CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__cond (CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16 z) /\
  opt_cond CA_ParametersNR_v1610__msgA_SUL_r16__cond (CA_ParametersNR_v1610__msgA_SUL_r16 z) /\
  opt_cond CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__cond (CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16 z) /\
  opt_cond CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__cond (CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16 z) /\
  opt_cond CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__cond (CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16 z) /\
  opt_cond CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__cond (CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16 z) /\
  opt_cond CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__cond (CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16 z) /\
  opt_cond CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__cond (CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16 z) /\
  opt_cond CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__cond (CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16 z) /\
  opt_cond CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__cond (CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16 z) /\
  opt_cond CA_ParametersNR_v1610__interFreqDAPS_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16 z) /\
  opt_cond CodebookParameters_v1610__cond (CA_ParametersNR_v1610__codebookParametersPerBC_r16 z) /\
  opt_cond CA_ParametersNR_v1610__blindDetectFactor_r16__cond (CA_ParametersNR_v1610__blindDetectFactor_r16 z) /\
  opt_cond CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16 z) /\
  opt_cond CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16 z) /\
  opt_cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16 z) /\
  opt_cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16 z) /\
  opt_cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16 z) /\
  opt_cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16 z) /\
  opt_cond CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__cond (CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16 z) /\
  opt_cond CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__cond (CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16 z) /\
  opt_cond CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__cond (CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16 z) /\
  opt_cond CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__cond (CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16 z) /\
  opt_cond CodebookParametersAdditionPerBC_r16__cond (CA_ParametersNR_v1610__codebookParametersAdditionPerBC_r16 z) /\
  opt_cond CodebookComboParametersAdditionPerBC_r16__cond (CA_ParametersNR_v1610__codebookComboParametersAdditionPerBC_r16 z) /\
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
Definition CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Format : T_Format CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__nat__Format CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F1 CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F2 CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F1F2 CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__F2F1.

Opaque CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__cond CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Format.

Definition CA_ParametersNR_v1610__msgA_SUL_r16__Format : T_Format CA_ParametersNR_v1610__msgA_SUL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__msgA_SUL_r16__nat__Format CA_ParametersNR_v1610__msgA_SUL_r16__F1 CA_ParametersNR_v1610__msgA_SUL_r16__F2 CA_ParametersNR_v1610__msgA_SUL_r16__F1F2 CA_ParametersNR_v1610__msgA_SUL_r16__F2F1.

Opaque CA_ParametersNR_v1610__msgA_SUL_r16__cond CA_ParametersNR_v1610__msgA_SUL_r16__Format.

Definition CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Format : T_Format CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__nat__Format CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F1 CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F2 CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F1F2 CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__F2F1.

Opaque CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__cond CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Format.

Definition CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Format : T_Format CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__nat__Format CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F1 CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F2 CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F1F2 CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__F2F1.

Opaque CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__cond CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Format.

Definition CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Format : T_Format CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__nat__Format CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F1 CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F2 CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F1F2 CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__F2F1.

Opaque CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__cond CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Format.

Definition CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Format : T_Format CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__nat__Format CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F1 CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F2 CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F1F2 CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__F2F1.

Opaque CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__cond CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Format.

Definition CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Format : T_Format CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__nat__Format CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F1 CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F2 CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F1F2 CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__F2F1.

Opaque CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__cond CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Format.

Definition CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Format : T_Format CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__nat__Format CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F1 CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F2 CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F1F2 CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__F2F1.

Opaque CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__cond CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Format.

Definition CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Format : T_Format CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__nat__Format CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F1 CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F2 CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F1F2 CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__F2F1.

Opaque CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__cond CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Format.

Definition CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Format : T_Format CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__nat__Format CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F1 CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F2 CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F1F2 CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__F2F1.

Opaque CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__cond CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Format.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Format : T_Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__nat__Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F1 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F1F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__F2F1.

Opaque CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Format.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Format : T_Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__nat__Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F1 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F1F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__F2F1.

Opaque CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Format.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Format : T_Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__nat__Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F1 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F1F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__F2F1.

Opaque CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Format.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Format : T_Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__nat__Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F1 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F1F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__F2F1.

Opaque CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Format.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Format : T_Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__nat__Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F1 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F1F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__F2F1.

Opaque CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Format.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Format : T_Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__nat__Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F1 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F1F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__F2F1.

Opaque CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Format.

Definition CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Format : T_Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__nat__Format CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F1 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F1F2 CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__F2F1.

Opaque CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Format.


Definition CA_ParametersNR_v1610__interFreqDAPS_r16__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1610__interFreqDAPS_r16__list.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__Format_list : CA_ParametersNR_v1610__interFreqDAPS_r16__Format_Type :=
  (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16__Format, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16__Format, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16__Format, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16__Format, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16__Format, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16__Format, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16__Format, unit_format))))))).
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1610__interFreqDAPS_r16__list CA_ParametersNR_v1610__interFreqDAPS_r16__Format_list.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__F1 z :=
  (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqAsyncDAPS_r16 z, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDiffSCS_DAPS_r16 z, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqMultiUL_TransmissionDAPS_r16 z, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode1_r16 z, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqSemiStaticPowerSharingDAPS_Mode2_r16 z, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqDynamicPowerSharingDAPS_r16 z, (CA_ParametersNR_v1610__interFreqDAPS_r16__interFreqUL_TransCancellationDAPS_r16 z, tt))))))).
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__F2 (y : seq_type CA_ParametersNR_v1610__interFreqDAPS_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__CA_ParametersNR_v1610__interFreqDAPS_r16__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__F1F2_cond (z : CA_ParametersNR_v1610__interFreqDAPS_r16__Type)
  : CA_ParametersNR_v1610__interFreqDAPS_r16__cond z ->
  (seq_cond CA_ParametersNR_v1610__interFreqDAPS_r16__list (CA_ParametersNR_v1610__interFreqDAPS_r16__F1 z)).
intro H. unfold CA_ParametersNR_v1610__interFreqDAPS_r16__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__F1F2_cond2 (z : CA_ParametersNR_v1610__interFreqDAPS_r16__Type)
 : CA_ParametersNR_v1610__interFreqDAPS_r16__F2 (CA_ParametersNR_v1610__interFreqDAPS_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__interFreqDAPS_r16__F2F1_cond (y : seq_type CA_ParametersNR_v1610__interFreqDAPS_r16__list)
  : seq_cond CA_ParametersNR_v1610__interFreqDAPS_r16__list y ->
 (CA_ParametersNR_v1610__interFreqDAPS_r16__cond (CA_ParametersNR_v1610__interFreqDAPS_r16__F2 y)) /\  CA_ParametersNR_v1610__interFreqDAPS_r16__F1 (CA_ParametersNR_v1610__interFreqDAPS_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1610__interFreqDAPS_r16__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1610__interFreqDAPS_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1610__interFreqDAPS_r16__Format : T_Format CA_ParametersNR_v1610__interFreqDAPS_r16__Type CA_ParametersNR_v1610__interFreqDAPS_r16__cond :=
        proj2_format  CA_ParametersNR_v1610__interFreqDAPS_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__list__Format
    CA_ParametersNR_v1610__interFreqDAPS_r16__F1 CA_ParametersNR_v1610__interFreqDAPS_r16__F2 CA_ParametersNR_v1610__interFreqDAPS_r16__F1F2_cond  CA_ParametersNR_v1610__interFreqDAPS_r16__F1F2_cond2 CA_ParametersNR_v1610__interFreqDAPS_r16__F2F1_cond.
Opaque CA_ParametersNR_v1610__interFreqDAPS_r16__cond CA_ParametersNR_v1610__interFreqDAPS_r16__Format.

Definition CA_ParametersNR_v1610__blindDetectFactor_r16__Format : T_Format Z CA_ParametersNR_v1610__blindDetectFactor_r16__cond :=
 ranged_int_format (1) (2) CA_ParametersNR_v1610__blindDetectFactor_r16__helper1 CA_ParametersNR_v1610__blindDetectFactor_r16__helper2.

Opaque CA_ParametersNR_v1610__blindDetectFactor_r16__cond CA_ParametersNR_v1610__blindDetectFactor_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__cond :=
 ranged_int_format (2) (16) CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__helper1 CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__cond CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Format : T_Format CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__nat__Format CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F1 CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F2 CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F1F2 CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__F2F1.

Opaque CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__cond CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Format.


Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Format_list : CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Format_Type :=
  (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16__Format, (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16__Format, unit_format)).
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Format_list.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1 z :=
  (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__maxNumberOfMonitoringCC_r16 z, (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__supportedSpanArrangement_r16 z, tt)).
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F2 (y : seq_type CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Type i0 i1
  end.
Lemma CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1F2_cond (z : CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Type)
  : CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond z ->
  (seq_cond CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1 z)).
intro H. unfold CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1F2_cond2 (z : CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Type)
 : CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F2 (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F2F1_cond (y : seq_type CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list)
  : seq_cond CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list y ->
 (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F2 y)) /\  CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1 (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Format : T_Format CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Type CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond :=
        proj2_format  CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__list__Format
    CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1 CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F2 CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1F2_cond  CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F1F2_cond2 CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__F2F1_cond.
Opaque CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__cond CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__cond :=
 ranged_int_format (1) (15) CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__helper1 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__cond :=
 ranged_int_format (1) (15) CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__helper1 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Format : T_Format CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__nat__Format CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F1 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F2 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F1F2 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__F2F1.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Format.


Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Format_list : CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Format_Type :=
  (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16__Format, unit_format))).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Format_list.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1 z :=
  (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA1_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__pdcch_BlindDetectionCA2_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__supportedSpanArrangement_r16 z, tt))).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F2 (y : seq_type CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Type i0 i1 i2
  end.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1F2_cond (z : CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Type)
  : CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond z ->
  (seq_cond CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1 z)).
intro H. unfold CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1F2_cond2 (z : CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Type)
 : CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F2 (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F2F1_cond (y : seq_type CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list)
  : seq_cond CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list y ->
 (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F2 y)) /\  CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1 (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Format : T_Format CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Type CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond :=
        proj2_format  CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__list__Format
    CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F2 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1F2_cond  CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F1F2_cond2 CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__F2F1_cond.
Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__cond :=
 ranged_int_format (1) (14) CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__helper1 CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__cond :=
 ranged_int_format (1) (14) CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__helper1 CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__cond :=
 ranged_int_format (0) (15) CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__helper1 CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__cond :=
 ranged_int_format (0) (15) CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__helper1 CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__Format.


Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Format_list : CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Format_Type :=
  (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16__Format, unit_format)).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Format_list.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1 z :=
  (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE1_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__pdcch_BlindDetectionMCG_UE2_r16 z, tt)).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F2 (y : seq_type CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Type i0 i1
  end.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1F2_cond (z : CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Type)
  : CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond z ->
  (seq_cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1 z)).
intro H. unfold CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1F2_cond2 (z : CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Type)
 : CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F2 (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F2F1_cond (y : seq_type CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list)
  : seq_cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list y ->
 (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F2 y)) /\  CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1 (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Format : T_Format CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Type CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond :=
        proj2_format  CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__list__Format
    CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1 CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F2 CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1F2_cond  CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F1F2_cond2 CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__F2F1_cond.
Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__cond :=
 ranged_int_format (0) (15) CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__helper1 CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__Format.

Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__Format : T_Format Z CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__cond :=
 ranged_int_format (0) (15) CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__helper1 CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__helper2.

Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__Format.


Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Format_list : CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Format_Type :=
  (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16__Format, unit_format)).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Format_list.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1 z :=
  (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE1_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__pdcch_BlindDetectionSCG_UE2_r16 z, tt)).
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F2 (y : seq_type CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Type i0 i1
  end.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1F2_cond (z : CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Type)
  : CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond z ->
  (seq_cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1 z)).
intro H. unfold CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1F2_cond2 (z : CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Type)
 : CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F2 (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F2F1_cond (y : seq_type CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list)
  : seq_cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list y ->
 (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F2 y)) /\  CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1 (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Format : T_Format CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Type CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond :=
        proj2_format  CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__list__Format
    CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1 CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F2 CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1F2_cond  CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F1F2_cond2 CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__F2F1_cond.
Opaque CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__cond CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Format.

Definition CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Format : T_Format CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__nat__Format CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F1 CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F2 CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F1F2 CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__F2F1.

Opaque CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__cond CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Format.

Definition CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Format : T_Format CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__nat__Format CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F1 CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F2 CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F1F2 CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__F2F1.

Opaque CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__cond CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Format.

Definition CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Format : T_Format CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__nat__Format CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F1 CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F2 CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F1F2 CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__F2F1.

Opaque CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__cond CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Format.

Definition CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Format : T_Format CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__nat__Format CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F1 CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F2 CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F1F2 CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__F2F1.

Opaque CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__cond CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Format.


Definition CA_ParametersNR_v1610__Format_Type := Eval cbn in seq_format_prod CA_ParametersNR_v1610__list.
Definition CA_ParametersNR_v1610__Format_list : CA_ParametersNR_v1610__Format_Type :=
  (CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16__Format, (CA_ParametersNR_v1610__msgA_SUL_r16__Format, (CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16__Format, (CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16__Format, (CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16__Format, (CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16__Format, (CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16__Format, (CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16__Format, (CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16__Format, (CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16__Format, (CA_ParametersNR_v1610__interFreqDAPS_r16__Format, (CodebookParameters_v1610__Format, (CA_ParametersNR_v1610__blindDetectFactor_r16__Format, (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16__Format, (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16__Format, (CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16__Format, (CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16__Format, (CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16__Format, (CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16__Format, (CodebookParametersAdditionPerBC_r16__Format, (CodebookComboParametersAdditionPerBC_r16__Format, unit_format))))))))))))))))))))))))).
Definition CA_ParametersNR_v1610__list__Format := (*Eval compute in *) seq_format CA_ParametersNR_v1610__list CA_ParametersNR_v1610__Format_list.
Definition CA_ParametersNR_v1610__F1 z :=
  (CA_ParametersNR_v1610__parallelTxMsgA_SRS_PUCCH_PUSCH_r16 z, (CA_ParametersNR_v1610__msgA_SUL_r16 z, (CA_ParametersNR_v1610__jointSearchSpaceSwitchAcrossCells_r16 z, (CA_ParametersNR_v1610__half_DuplexTDD_CA_SameSCS_r16 z, (CA_ParametersNR_v1610__scellDormancyWithinActiveTime_r16 z, (CA_ParametersNR_v1610__scellDormancyOutsideActiveTime_r16 z, (CA_ParametersNR_v1610__crossCarrierA_CSI_trigDiffSCS_r16 z, (CA_ParametersNR_v1610__defaultQCL_CrossCarrierA_CSI_Trig_r16 z, (CA_ParametersNR_v1610__interCA_NonAlignedFrame_r16 z, (CA_ParametersNR_v1610__simul_SRS_Trans_BC_r16 z, (CA_ParametersNR_v1610__interFreqDAPS_r16 z, (CA_ParametersNR_v1610__codebookParametersPerBC_r16 z, (CA_ParametersNR_v1610__blindDetectFactor_r16 z, (CA_ParametersNR_v1610__pdcch_MonitoringCA_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionCA_Mixed_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionMCG_UE_Mixed_r16 z, (CA_ParametersNR_v1610__pdcch_BlindDetectionSCG_UE_Mixed_r16 z, (CA_ParametersNR_v1610__crossCarrierSchedulingDL_DiffSCS_r16 z, (CA_ParametersNR_v1610__crossCarrierSchedulingDefaultQCL_r16 z, (CA_ParametersNR_v1610__crossCarrierSchedulingUL_DiffSCS_r16 z, (CA_ParametersNR_v1610__simul_SRS_MIMO_Trans_BC_r16 z, (CA_ParametersNR_v1610__codebookParametersAdditionPerBC_r16 z, (CA_ParametersNR_v1610__codebookComboParametersAdditionPerBC_r16 z, tt))))))))))))))))))))))))).
Definition CA_ParametersNR_v1610__F2 (y : seq_type CA_ParametersNR_v1610__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, (i24, _)))))))))))))))))))))))))=>
    make__CA_ParametersNR_v1610__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24
  end.
Lemma CA_ParametersNR_v1610__F1F2_cond (z : CA_ParametersNR_v1610__Type)
  : CA_ParametersNR_v1610__cond z ->
  (seq_cond CA_ParametersNR_v1610__list (CA_ParametersNR_v1610__F1 z)).
intro H. unfold CA_ParametersNR_v1610__cond in H. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__F1F2_cond2 (z : CA_ParametersNR_v1610__Type)
 : CA_ParametersNR_v1610__F2 (CA_ParametersNR_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CA_ParametersNR_v1610__F2F1_cond (y : seq_type CA_ParametersNR_v1610__list)
  : seq_cond CA_ParametersNR_v1610__list y ->
 (CA_ParametersNR_v1610__cond (CA_ParametersNR_v1610__F2 y)) /\  CA_ParametersNR_v1610__F1 (CA_ParametersNR_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CA_ParametersNR_v1610__cond. simpl in *. auto.
 - simpl. unfold CA_ParametersNR_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CA_ParametersNR_v1610__Format : T_Format CA_ParametersNR_v1610__Type CA_ParametersNR_v1610__cond :=
        proj2_format  CA_ParametersNR_v1610__cond CA_ParametersNR_v1610__list__Format
    CA_ParametersNR_v1610__F1 CA_ParametersNR_v1610__F2 CA_ParametersNR_v1610__F1F2_cond  CA_ParametersNR_v1610__F1F2_cond2 CA_ParametersNR_v1610__F2F1_cond.
Opaque CA_ParametersNR_v1610__cond CA_ParametersNR_v1610__Format.

