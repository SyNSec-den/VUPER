Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.ReconfigurationWithSync.

Opaque ReconfigurationWithSync__cond ReconfigurationWithSync__Format.

Require Import NR.SetupRelease.
Require Import NR.RLF_TimersAndConstants.
Definition SpCellConfig__rlf_TimersAndConstants__Type := SetupRelease__Type RLF_TimersAndConstants__Type.
Definition SpCellConfig__rlf_TimersAndConstants__cond := SetupRelease__cond _ RLF_TimersAndConstants__cond.
Definition SpCellConfig__rlf_TimersAndConstants__Format : T_Format SpCellConfig__rlf_TimersAndConstants__Type SpCellConfig__rlf_TimersAndConstants__cond := SetupRelease__Format _ _ RLF_TimersAndConstants__Format.
Opaque SpCellConfig__rlf_TimersAndConstants__cond SpCellConfig__rlf_TimersAndConstants__Format.

Inductive SpCellConfig__rlmInSyncOutOfSyncThreshold__Type : Set :=
 | SpCellConfig__rlmInSyncOutOfSyncThreshold__n1
.
Definition SpCellConfig__rlmInSyncOutOfSyncThreshold__cond := (fun (_ : SpCellConfig__rlmInSyncOutOfSyncThreshold__Type) => True).
Lemma SpCellConfig__rlmInSyncOutOfSyncThreshold__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpCellConfig__rlmInSyncOutOfSyncThreshold__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SpCellConfig__rlmInSyncOutOfSyncThreshold__nat__helper.

Definition SpCellConfig__rlmInSyncOutOfSyncThreshold__F1 t :=
  match t with
  | SpCellConfig__rlmInSyncOutOfSyncThreshold__n1 => 0
  end.
Definition SpCellConfig__rlmInSyncOutOfSyncThreshold__F2 n :=
  match n with
  | 0 => SpCellConfig__rlmInSyncOutOfSyncThreshold__n1
  | _ => SpCellConfig__rlmInSyncOutOfSyncThreshold__n1
  end.
Lemma SpCellConfig__rlmInSyncOutOfSyncThreshold__F1F2 : forall x : SpCellConfig__rlmInSyncOutOfSyncThreshold__Type, (SpCellConfig__rlmInSyncOutOfSyncThreshold__F1 x <= 0) /\ SpCellConfig__rlmInSyncOutOfSyncThreshold__F2 (SpCellConfig__rlmInSyncOutOfSyncThreshold__F1 x) = x. imp_solve. Qed.
Lemma SpCellConfig__rlmInSyncOutOfSyncThreshold__F2F1 : forall (y : nat) (H : y <= 0), SpCellConfig__rlmInSyncOutOfSyncThreshold__F1 (SpCellConfig__rlmInSyncOutOfSyncThreshold__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ServingCellConfig.

Opaque ServingCellConfig__cond ServingCellConfig__Format.

Inductive SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Type : Set :=
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB3
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB6
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB9
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB12
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB15
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare3
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare2
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare1
.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__cond := (fun (_ : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Type) => True).
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__nat__helper.

Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F1 t :=
  match t with
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB3 => 0
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB6 => 1
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB9 => 2
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB12 => 3
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB15 => 4
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare3 => 5
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare2 => 6
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare1 => 7
  end.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F2 n :=
  match n with
  | 0 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB3
  | 1 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB6
  | 2 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB9
  | 3 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB12
  | 4 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB15
  | 5 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare3
  | 6 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare2
  | 7 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__spare1
  | _ => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__dB3
  end.
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F1F2 : forall x : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Type, (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F1 x <= 7) /\ SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F2 (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F1 x) = x. imp_solve. Qed.
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F2F1 : forall (y : nat) (H : y <= 7), SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F1 (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F2 y) = y. enum_solve H y. Qed.

Inductive SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Type : Set :=
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s5
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s10
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s20
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s30
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s60
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s120
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s180
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s240
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s300
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare7
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare6
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare5
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare4
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare3
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare2
 | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare1
.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__cond := (fun (_ : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Type) => True).
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__nat__helper.

Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F1 t :=
  match t with
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s5 => 0
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s10 => 1
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s20 => 2
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s30 => 3
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s60 => 4
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s120 => 5
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s180 => 6
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s240 => 7
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s300 => 8
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare7 => 9
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare6 => 10
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare5 => 11
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare4 => 12
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare3 => 13
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare2 => 14
  | SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare1 => 15
  end.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F2 n :=
  match n with
  | 0 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s5
  | 1 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s10
  | 2 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s20
  | 3 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s30
  | 4 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s60
  | 5 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s120
  | 6 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s180
  | 7 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s240
  | 8 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s300
  | 9 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare7
  | 10 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare6
  | 11 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare5
  | 12 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare4
  | 13 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare3
  | 14 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare2
  | 15 => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__spare1
  | _ => SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__s5
  end.
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F1F2 : forall x : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Type, (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F1 x <= 15) /\ SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F2 (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F1 x) = x. imp_solve. Qed.
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F2F1 : forall (y : nat) (H : y <= 15), SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F1 (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F2 y) = y. enum_solve H y. Qed.

Record SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Type : Set :=
  make__SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Type {
    SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17 : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Type ;
    SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17 : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Type ;
}.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list := (
 Nor SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Type SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__cond ::
 Nor SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Type SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__cond ::
 nil).
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond z := 
  SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__cond (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17 z) /\
  SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__cond (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17 z) /\
  True.

Require Import NR.GoodServingCellEvaluation_r17.

Opaque GoodServingCellEvaluation_r17__cond GoodServingCellEvaluation_r17__Format.

Require Import NR.GoodServingCellEvaluation_r17.

Opaque GoodServingCellEvaluation_r17__cond GoodServingCellEvaluation_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.DeactivatedSCG_Config_r17.
Definition SpCellConfig__ext0O__deactivatedSCG_Config_r17__Type := SetupRelease__Type DeactivatedSCG_Config_r17__Type.
Definition SpCellConfig__ext0O__deactivatedSCG_Config_r17__cond := SetupRelease__cond _ DeactivatedSCG_Config_r17__cond.
Definition SpCellConfig__ext0O__deactivatedSCG_Config_r17__Format : T_Format SpCellConfig__ext0O__deactivatedSCG_Config_r17__Type SpCellConfig__ext0O__deactivatedSCG_Config_r17__cond := SetupRelease__Format _ _ DeactivatedSCG_Config_r17__Format.
Opaque SpCellConfig__ext0O__deactivatedSCG_Config_r17__cond SpCellConfig__ext0O__deactivatedSCG_Config_r17__Format.

Record SpCellConfig__ext0O__Type : Set :=
  make__SpCellConfig__ext0O__Type {
    SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17 : option SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Type ;
    SpCellConfig__ext0O__goodServingCellEvaluationRLM_r17 : option GoodServingCellEvaluation_r17__Type ;
    SpCellConfig__ext0O__goodServingCellEvaluationBFD_r17 : option GoodServingCellEvaluation_r17__Type ;
    SpCellConfig__ext0O__deactivatedSCG_Config_r17 : option SpCellConfig__ext0O__deactivatedSCG_Config_r17__Type ;
}.
Definition SpCellConfig__ext0O__list := (
 Opt SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Type SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond ::
 Opt GoodServingCellEvaluation_r17__Type GoodServingCellEvaluation_r17__cond ::
 Opt GoodServingCellEvaluation_r17__Type GoodServingCellEvaluation_r17__cond ::
 Opt SpCellConfig__ext0O__deactivatedSCG_Config_r17__Type SpCellConfig__ext0O__deactivatedSCG_Config_r17__cond ::
 nil).
Definition SpCellConfig__ext0O__cond z := 
  opt_cond SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17 z) /\
  opt_cond GoodServingCellEvaluation_r17__cond (SpCellConfig__ext0O__goodServingCellEvaluationRLM_r17 z) /\
  opt_cond GoodServingCellEvaluation_r17__cond (SpCellConfig__ext0O__goodServingCellEvaluationBFD_r17 z) /\
  opt_cond SpCellConfig__ext0O__deactivatedSCG_Config_r17__cond (SpCellConfig__ext0O__deactivatedSCG_Config_r17 z) /\
  True.

Definition SpCellConfig__ext0__Type := SpCellConfig__ext0O__Type.
Definition SpCellConfig__ext0__cond := SpCellConfig__ext0O__cond.

Record SpCellConfig__Type : Set :=
  make__SpCellConfig__Type {
    SpCellConfig__servCellIndex : option ServCellIndex__Type ;
    SpCellConfig__reconfigurationWithSync : option ReconfigurationWithSync__Type ;
    SpCellConfig__rlf_TimersAndConstants : option SpCellConfig__rlf_TimersAndConstants__Type ;
    SpCellConfig__rlmInSyncOutOfSyncThreshold : option SpCellConfig__rlmInSyncOutOfSyncThreshold__Type ;
    SpCellConfig__spCellConfigDedicated : option ServingCellConfig__Type ;
    SpCellConfig__ext0 : option SpCellConfig__ext0__Type ;
}.
Definition SpCellConfig__root_list : list seq_elem := (
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Opt ReconfigurationWithSync__Type ReconfigurationWithSync__cond ::
 Opt SpCellConfig__rlf_TimersAndConstants__Type SpCellConfig__rlf_TimersAndConstants__cond ::
 Opt SpCellConfig__rlmInSyncOutOfSyncThreshold__Type SpCellConfig__rlmInSyncOutOfSyncThreshold__cond ::
 Opt ServingCellConfig__Type ServingCellConfig__cond ::
 nil).
Definition SpCellConfig__ext_list : list typ := (
  typ_cons SpCellConfig__ext0__Type SpCellConfig__ext0__cond ::
  nil).
Definition SpCellConfig__cond (z : SpCellConfig__Type) := 
(  opt_cond ServCellIndex__cond (SpCellConfig__servCellIndex z) /\
  opt_cond ReconfigurationWithSync__cond (SpCellConfig__reconfigurationWithSync z) /\
  opt_cond SpCellConfig__rlf_TimersAndConstants__cond (SpCellConfig__rlf_TimersAndConstants z) /\
  opt_cond SpCellConfig__rlmInSyncOutOfSyncThreshold__cond (SpCellConfig__rlmInSyncOutOfSyncThreshold z) /\
  opt_cond ServingCellConfig__cond (SpCellConfig__spCellConfigDedicated z) /\
  True) /\ 
(  opt_cond SpCellConfig__ext0__cond (SpCellConfig__ext0 z) /\
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
Opaque SpCellConfig__rlf_TimersAndConstants__cond SpCellConfig__rlf_TimersAndConstants__Format.

Definition SpCellConfig__rlmInSyncOutOfSyncThreshold__Format : T_Format SpCellConfig__rlmInSyncOutOfSyncThreshold__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpCellConfig__rlmInSyncOutOfSyncThreshold__nat__Format SpCellConfig__rlmInSyncOutOfSyncThreshold__F1 SpCellConfig__rlmInSyncOutOfSyncThreshold__F2 SpCellConfig__rlmInSyncOutOfSyncThreshold__F1F2 SpCellConfig__rlmInSyncOutOfSyncThreshold__F2F1.

Opaque SpCellConfig__rlmInSyncOutOfSyncThreshold__cond SpCellConfig__rlmInSyncOutOfSyncThreshold__Format.

Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Format : T_Format SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__nat__Format SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F1 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F2 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F1F2 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__F2F1.

Opaque SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__cond SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Format.

Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Format : T_Format SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__nat__Format SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F1 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F2 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F1F2 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__F2F1.

Opaque SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__cond SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Format.


Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Format_Type := Eval cbn in seq_format_prod SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Format_list : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Format_Type :=
  (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17__Format, (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17__Format, unit_format)).
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list__Format := (*Eval compute in *) seq_format SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Format_list.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1 z :=
  (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__s_SearchDeltaP_Connected_r17 z, (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__t_SearchDeltaP_Connected_r17 z, tt)).
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F2 (y : seq_type SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Type i0 i1
  end.
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1F2_cond (z : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Type)
  : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond z ->
  (seq_cond SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1 z)).
intro H. unfold SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond in H. simpl. auto. Qed.
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1F2_cond2 (z : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Type)
 : SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F2 (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F2F1_cond (y : seq_type SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list)
  : seq_cond SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list y ->
 (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F2 y)) /\  SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1 (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond. simpl in *. auto.
 - simpl. unfold SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Format : T_Format SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Type SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond :=
        proj2_format  SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__list__Format
    SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F2 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1F2_cond  SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F1F2_cond2 SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__F2F1_cond.
Opaque SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__cond SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Format.

Opaque SpCellConfig__ext0O__deactivatedSCG_Config_r17__cond SpCellConfig__ext0O__deactivatedSCG_Config_r17__Format.


Definition SpCellConfig__ext0O__Format_Type := Eval cbn in seq_format_prod SpCellConfig__ext0O__list.
Definition SpCellConfig__ext0O__Format_list : SpCellConfig__ext0O__Format_Type :=
  (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17__Format, (GoodServingCellEvaluation_r17__Format, (GoodServingCellEvaluation_r17__Format, (SpCellConfig__ext0O__deactivatedSCG_Config_r17__Format, unit_format)))).
Definition SpCellConfig__ext0O__list__Format := (*Eval compute in *) seq_format SpCellConfig__ext0O__list SpCellConfig__ext0O__Format_list.
Definition SpCellConfig__ext0O__F1 z :=
  (SpCellConfig__ext0O__lowMobilityEvaluationConnected_r17 z, (SpCellConfig__ext0O__goodServingCellEvaluationRLM_r17 z, (SpCellConfig__ext0O__goodServingCellEvaluationBFD_r17 z, (SpCellConfig__ext0O__deactivatedSCG_Config_r17 z, tt)))).
Definition SpCellConfig__ext0O__F2 (y : seq_type SpCellConfig__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SpCellConfig__ext0O__Type i0 i1 i2 i3
  end.
Lemma SpCellConfig__ext0O__F1F2_cond (z : SpCellConfig__ext0O__Type)
  : SpCellConfig__ext0O__cond z ->
  (seq_cond SpCellConfig__ext0O__list (SpCellConfig__ext0O__F1 z)).
intro H. unfold SpCellConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma SpCellConfig__ext0O__F1F2_cond2 (z : SpCellConfig__ext0O__Type)
 : SpCellConfig__ext0O__F2 (SpCellConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SpCellConfig__ext0O__F2F1_cond (y : seq_type SpCellConfig__ext0O__list)
  : seq_cond SpCellConfig__ext0O__list y ->
 (SpCellConfig__ext0O__cond (SpCellConfig__ext0O__F2 y)) /\  SpCellConfig__ext0O__F1 (SpCellConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SpCellConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold SpCellConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SpCellConfig__ext0O__Format : T_Format SpCellConfig__ext0O__Type SpCellConfig__ext0O__cond :=
        proj2_format  SpCellConfig__ext0O__cond SpCellConfig__ext0O__list__Format
    SpCellConfig__ext0O__F1 SpCellConfig__ext0O__F2 SpCellConfig__ext0O__F1F2_cond  SpCellConfig__ext0O__F1F2_cond2 SpCellConfig__ext0O__F2F1_cond.
Opaque SpCellConfig__ext0O__cond SpCellConfig__ext0O__Format.

Definition SpCellConfig__ext0__check_all_none (b : SpCellConfig__ext0O__Type) : bool :=
match b with 
  | make__SpCellConfig__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition SpCellConfig__ext0__Format : T_Format SpCellConfig__ext0__Type SpCellConfig__ext0__cond :=
  restrict_add_format SpCellConfig__ext0__check_all_none SpCellConfig__ext0O__Format.

Opaque SpCellConfig__ext0__cond SpCellConfig__ext0__Format.


Definition SpCellConfig__root_Format_Type := Eval cbn in seq_format_prod SpCellConfig__root_list.
Definition SpCellConfig__root_Format_list : SpCellConfig__root_Format_Type :=
  (ServCellIndex__Format, (ReconfigurationWithSync__Format, (SpCellConfig__rlf_TimersAndConstants__Format, (SpCellConfig__rlmInSyncOutOfSyncThreshold__Format, (ServingCellConfig__Format, unit_format))))).

Definition SpCellConfig__ext_Format_Type := Eval cbn in get_formats SpCellConfig__ext_list.
Definition SpCellConfig__ext_Format_list : SpCellConfig__ext_Format_Type :=
  (SpCellConfig__ext0__Format, unit__Format).

Definition SpCellConfig__list_type : Set := (seq_type SpCellConfig__root_list) * (seq_ext_type SpCellConfig__ext_list).
Definition SpCellConfig__list_cond (z : SpCellConfig__list_type) : Prop :=
        (seq_cond SpCellConfig__root_list (fst z)) /\ (seq_ext_cond SpCellConfig__ext_list (snd z)).
Definition SpCellConfig__list_format : T_Format SpCellConfig__list_type SpCellConfig__list_cond :=
 (* Eval compute in *) seq_ext_format SpCellConfig__root_list SpCellConfig__root_Format_list SpCellConfig__ext_list SpCellConfig__ext_Format_list.

Opaque SpCellConfig__list_format.
Definition SpCellConfig__F1 (z : SpCellConfig__Type) : SpCellConfig__list_type :=
  (((SpCellConfig__servCellIndex z, (SpCellConfig__reconfigurationWithSync z, (SpCellConfig__rlf_TimersAndConstants z, (SpCellConfig__rlmInSyncOutOfSyncThreshold z, (SpCellConfig__spCellConfigDedicated z, tt)))))), (
(SpCellConfig__ext0 z, tt))).
Definition SpCellConfig__F2 (y : SpCellConfig__list_type) : SpCellConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, _))=>
    make__SpCellConfig__Type j0 j1 j2 j3 j4 i0
  end.
Definition SpCellConfig__helper1 : (forall a : SpCellConfig__Type, SpCellConfig__cond a -> SpCellConfig__list_cond (SpCellConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SpCellConfig__helper2 : (forall a : SpCellConfig__Type, SpCellConfig__F2 (SpCellConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SpCellConfig__helper3 : (forall b : SpCellConfig__list_type, SpCellConfig__list_cond b -> SpCellConfig__cond (SpCellConfig__F2 b) /\ SpCellConfig__F1 (SpCellConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SpCellConfig__cond, SpCellConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SpCellConfig__Format : T_Format SpCellConfig__Type SpCellConfig__cond :=
 proj2_format SpCellConfig__cond SpCellConfig__list_format  SpCellConfig__F1 SpCellConfig__F2 SpCellConfig__helper1 SpCellConfig__helper2 SpCellConfig__helper3.

Opaque SpCellConfig__cond SpCellConfig__Format.

