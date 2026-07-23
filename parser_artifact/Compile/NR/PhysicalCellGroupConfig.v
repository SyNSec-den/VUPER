Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Type : Set :=
 | PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__true
.
Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__cond := (fun (_ : PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Type) => True).
Lemma PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__nat__helper.

Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F1 t :=
  match t with
  | PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__true => 0
  end.
Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__true
  | _ => PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__true
  end.
Lemma PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F1F2 : forall x : PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Type, (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F1 x <= 0) /\ PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F2 (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F1 (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Type : Set :=
 | PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__true
.
Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__cond := (fun (_ : PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Type) => True).
Lemma PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__nat__helper.

Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F1 t :=
  match t with
  | PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__true => 0
  end.
Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__true
  | _ => PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__true
  end.
Lemma PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F1F2 : forall x : PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Type, (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F1 x <= 0) /\ PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F2 (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F1 (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F2 y) = y. enum_solve H y. Qed.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Inductive PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Type : Set :=
 | PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__semiStatic
 | PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__dynamic
.
Definition PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__cond := (fun (_ : PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Type) => True).
Lemma PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__nat__helper.

Definition PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F1 t :=
  match t with
  | PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__semiStatic => 0
  | PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__dynamic => 1
  end.
Definition PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__semiStatic
  | 1 => PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__dynamic
  | _ => PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__semiStatic
  end.
Lemma PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F1F2 : forall x : PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Type, (PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F1 x <= 1) /\ PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F2 (PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F2F1 : forall (y : nat) (H : y <= 1), PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F1 (PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.SetupRelease.
Require Import NR.RNTI_Value.
Definition PhysicalCellGroupConfig__cs_RNTI__Type := SetupRelease__Type RNTI_Value__Type.
Definition PhysicalCellGroupConfig__cs_RNTI__cond := SetupRelease__cond _ RNTI_Value__cond.
Definition PhysicalCellGroupConfig__cs_RNTI__Format : T_Format PhysicalCellGroupConfig__cs_RNTI__Type PhysicalCellGroupConfig__cs_RNTI__cond := SetupRelease__Format _ _ RNTI_Value__Format.
Opaque PhysicalCellGroupConfig__cs_RNTI__cond PhysicalCellGroupConfig__cs_RNTI__Format.

Require Import NR.RNTI_Value.

Opaque RNTI_Value__cond RNTI_Value__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Record PhysicalCellGroupConfig__ext0O__Type : Set :=
  make__PhysicalCellGroupConfig__ext0O__Type {
    PhysicalCellGroupConfig__ext0O__mcs_C_RNTI : option RNTI_Value__Type ;
    PhysicalCellGroupConfig__ext0O__p_UE_FR1 : option P_Max__Type ;
}.
Definition PhysicalCellGroupConfig__ext0O__list := (
 Opt RNTI_Value__Type RNTI_Value__cond ::
 Opt P_Max__Type P_Max__cond ::
 nil).
Definition PhysicalCellGroupConfig__ext0O__cond z := 
  opt_cond RNTI_Value__cond (PhysicalCellGroupConfig__ext0O__mcs_C_RNTI z) /\
  opt_cond P_Max__cond (PhysicalCellGroupConfig__ext0O__p_UE_FR1 z) /\
  True.

Definition PhysicalCellGroupConfig__ext0__Type := PhysicalCellGroupConfig__ext0O__Type.
Definition PhysicalCellGroupConfig__ext0__cond := PhysicalCellGroupConfig__ext0O__cond.

Inductive PhysicalCellGroupConfig__ext1O__xScale__Type : Set :=
 | PhysicalCellGroupConfig__ext1O__xScale__dB0
 | PhysicalCellGroupConfig__ext1O__xScale__dB6
 | PhysicalCellGroupConfig__ext1O__xScale__spare2
 | PhysicalCellGroupConfig__ext1O__xScale__spare1
.
Definition PhysicalCellGroupConfig__ext1O__xScale__cond := (fun (_ : PhysicalCellGroupConfig__ext1O__xScale__Type) => True).
Lemma PhysicalCellGroupConfig__ext1O__xScale__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext1O__xScale__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 PhysicalCellGroupConfig__ext1O__xScale__nat__helper.

Definition PhysicalCellGroupConfig__ext1O__xScale__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext1O__xScale__dB0 => 0
  | PhysicalCellGroupConfig__ext1O__xScale__dB6 => 1
  | PhysicalCellGroupConfig__ext1O__xScale__spare2 => 2
  | PhysicalCellGroupConfig__ext1O__xScale__spare1 => 3
  end.
Definition PhysicalCellGroupConfig__ext1O__xScale__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext1O__xScale__dB0
  | 1 => PhysicalCellGroupConfig__ext1O__xScale__dB6
  | 2 => PhysicalCellGroupConfig__ext1O__xScale__spare2
  | 3 => PhysicalCellGroupConfig__ext1O__xScale__spare1
  | _ => PhysicalCellGroupConfig__ext1O__xScale__dB0
  end.
Lemma PhysicalCellGroupConfig__ext1O__xScale__F1F2 : forall x : PhysicalCellGroupConfig__ext1O__xScale__Type, (PhysicalCellGroupConfig__ext1O__xScale__F1 x <= 3) /\ PhysicalCellGroupConfig__ext1O__xScale__F2 (PhysicalCellGroupConfig__ext1O__xScale__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext1O__xScale__F2F1 : forall (y : nat) (H : y <= 3), PhysicalCellGroupConfig__ext1O__xScale__F1 (PhysicalCellGroupConfig__ext1O__xScale__F2 y) = y. enum_solve H y. Qed.

Record PhysicalCellGroupConfig__ext1O__Type : Set :=
  make__PhysicalCellGroupConfig__ext1O__Type {
    PhysicalCellGroupConfig__ext1O__xScale : option PhysicalCellGroupConfig__ext1O__xScale__Type ;
}.
Definition PhysicalCellGroupConfig__ext1O__list := (
 Opt PhysicalCellGroupConfig__ext1O__xScale__Type PhysicalCellGroupConfig__ext1O__xScale__cond ::
 nil).
Definition PhysicalCellGroupConfig__ext1O__cond z := 
  opt_cond PhysicalCellGroupConfig__ext1O__xScale__cond (PhysicalCellGroupConfig__ext1O__xScale z) /\
  True.

Definition PhysicalCellGroupConfig__ext1__Type := PhysicalCellGroupConfig__ext1O__Type.
Definition PhysicalCellGroupConfig__ext1__cond := PhysicalCellGroupConfig__ext1O__cond.

Require Import NR.SetupRelease.
Require Import NR.PDCCH_BlindDetection.
Definition PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__Type := SetupRelease__Type PDCCH_BlindDetection__Type.
Definition PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__cond := SetupRelease__cond _ PDCCH_BlindDetection__cond.
Definition PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__Format : T_Format PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__Type PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__cond := SetupRelease__Format _ _ PDCCH_BlindDetection__Format.
Opaque PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__cond PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__Format.

Record PhysicalCellGroupConfig__ext2O__Type : Set :=
  make__PhysicalCellGroupConfig__ext2O__Type {
    PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection : option PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__Type ;
}.
Definition PhysicalCellGroupConfig__ext2O__list := (
 Opt PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__Type PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__cond ::
 nil).
Definition PhysicalCellGroupConfig__ext2O__cond z := 
  opt_cond PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__cond (PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection z) /\
  True.

Definition PhysicalCellGroupConfig__ext2__Type := PhysicalCellGroupConfig__ext2O__Type.
Definition PhysicalCellGroupConfig__ext2__cond := PhysicalCellGroupConfig__ext2O__cond.

Require Import NR.SetupRelease.
Require Import NR.DCP_Config_r16.
Definition PhysicalCellGroupConfig__ext3O__dcp_Config_r16__Type := SetupRelease__Type DCP_Config_r16__Type.
Definition PhysicalCellGroupConfig__ext3O__dcp_Config_r16__cond := SetupRelease__cond _ DCP_Config_r16__cond.
Definition PhysicalCellGroupConfig__ext3O__dcp_Config_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__dcp_Config_r16__Type PhysicalCellGroupConfig__ext3O__dcp_Config_r16__cond := SetupRelease__Format _ _ DCP_Config_r16__Format.
Opaque PhysicalCellGroupConfig__ext3O__dcp_Config_r16__cond PhysicalCellGroupConfig__ext3O__dcp_Config_r16__Format.

Inductive PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__enabled
 | PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__disabled
.
Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__enabled => 0
  | PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__disabled => 1
  end.
Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__enabled
  | 1 => PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__disabled
  | _ => PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__enabled
  end.
Lemma PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Type, (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F1 x <= 1) /\ PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F2 (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F2F1 : forall (y : nat) (H : y <= 1), PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F1 (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__enabled
 | PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__disabled
.
Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__enabled => 0
  | PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__disabled => 1
  end.
Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__enabled
  | 1 => PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__disabled
  | _ => PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__enabled
  end.
Lemma PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Type, (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F1 x <= 1) /\ PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F2 (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F2F1 : forall (y : nat) (H : y <= 1), PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F1 (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__semiStatic
 | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__dynamic
.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__semiStatic => 0
  | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__dynamic => 1
  end.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__semiStatic
  | 1 => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__dynamic
  | _ => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__semiStatic
  end.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Type, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F1 x <= 1) /\ PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F2 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F2F1 : forall (y : nat) (H : y <= 1), PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F1 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Inductive PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__semi_static_mode1
 | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__semi_static_mode2
 | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__dynamic
.
Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__semi_static_mode1 => 0
  | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__semi_static_mode2 => 1
  | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__dynamic => 2
  end.
Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__semi_static_mode1
  | 1 => PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__semi_static_mode2
  | 2 => PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__dynamic
  | _ => PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__semi_static_mode1
  end.
Lemma PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Type, (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F1 x <= 2) /\ PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F2 (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F2F1 : forall (y : nat) (H : y <= 2), PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F1 (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__semi_static_mode1
 | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__semi_static_mode2
 | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__dynamic
.
Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__semi_static_mode1 => 0
  | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__semi_static_mode2 => 1
  | PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__dynamic => 2
  end.
Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__semi_static_mode1
  | 1 => PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__semi_static_mode2
  | 2 => PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__dynamic
  | _ => PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__semi_static_mode1
  end.
Lemma PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Type, (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F1 x <= 2) /\ PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F2 (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F2F1 : forall (y : nat) (H : y <= 2), PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F1 (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__enhancedDynamic
.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__enhancedDynamic => 0
  end.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__enhancedDynamic
  | _ => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__enhancedDynamic
  end.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Type, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F1 x <= 0) /\ PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F2 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F1 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__true
.
Definition PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__true => 0
  end.
Definition PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__true
  | _ => PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__true
  end.
Lemma PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Type, (PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F1 x <= 0) /\ PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F2 (PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F1 (PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__true
.
Definition PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__true => 0
  end.
Definition PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__true
  | _ => PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__true
  end.
Lemma PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Type, (PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F1 x <= 0) /\ PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F2 (PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F1 (PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__true
.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__true => 0
  end.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__true
  | _ => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__true
  end.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Type, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F1 x <= 0) /\ PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F2 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F1 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__true
.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__true => 0
  end.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__true
  | _ => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__true
  end.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Type, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F1 x <= 0) /\ PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F2 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F1 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__true
.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__true => 0
  end.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__true
  | _ => PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__true
  end.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Type, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F1 x <= 0) /\ PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F2 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F1 (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__enabled
.
Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__enabled
  | _ => PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__enabled
  end.
Lemma PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Type, (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F1 x <= 0) /\ PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F2 (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F1 (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n1
 | PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n2
 | PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n4
.
Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n1 => 0
  | PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n2 => 1
  | PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n4 => 2
  end.
Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n1
  | 1 => PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n2
  | 2 => PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n4
  | _ => PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__n1
  end.
Lemma PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Type, (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F1 x <= 2) /\ PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F2 (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F2F1 : forall (y : nat) (H : y <= 2), PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F1 (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PDSCH_HARQ_ACK_CodebookList_r16.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__Type := SetupRelease__Type PDSCH_HARQ_ACK_CodebookList_r16__Type.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__cond := SetupRelease__cond _ PDSCH_HARQ_ACK_CodebookList_r16__cond.
Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__Type PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__cond := SetupRelease__Format _ _ PDSCH_HARQ_ACK_CodebookList_r16__Format.
Opaque PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__Format.

Inductive PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__joint
 | PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__separate
.
Definition PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__joint => 0
  | PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__separate => 1
  end.
Definition PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__joint
  | 1 => PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__separate
  | _ => PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__joint
  end.
Lemma PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Type, (PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F1 x <= 1) /\ PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F2 (PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F2F1 : forall (y : nat) (H : y <= 1), PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F1 (PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PDCCH_BlindDetectionCA_CombIndicator_r16.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__Type := SetupRelease__Type PDCCH_BlindDetectionCA_CombIndicator_r16__Type.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__cond := SetupRelease__cond _ PDCCH_BlindDetectionCA_CombIndicator_r16__cond.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__Type PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__cond := SetupRelease__Format _ _ PDCCH_BlindDetectionCA_CombIndicator_r16__Format.
Opaque PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.PDCCH_BlindDetection2_r16.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__Type := SetupRelease__Type PDCCH_BlindDetection2_r16__Type.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__cond := SetupRelease__cond _ PDCCH_BlindDetection2_r16__cond.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__Type PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__cond := SetupRelease__Format _ _ PDCCH_BlindDetection2_r16__Format.
Opaque PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__Format.

Require Import NR.SetupRelease.
Require Import NR.PDCCH_BlindDetection3_r16.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__Type := SetupRelease__Type PDCCH_BlindDetection3_r16__Type.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__cond := SetupRelease__cond _ PDCCH_BlindDetection3_r16__cond.
Definition PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__Type PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__cond := SetupRelease__Format _ _ PDCCH_BlindDetection3_r16__Format.
Opaque PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__Format.

Inductive PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Type : Set :=
 | PhysicalCellGroupConfig__ext3O__bdFactorR_r16__n1
.
Definition PhysicalCellGroupConfig__ext3O__bdFactorR_r16__cond := (fun (_ : PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Type) => True).
Lemma PhysicalCellGroupConfig__ext3O__bdFactorR_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext3O__bdFactorR_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext3O__bdFactorR_r16__nat__helper.

Definition PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext3O__bdFactorR_r16__n1 => 0
  end.
Definition PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext3O__bdFactorR_r16__n1
  | _ => PhysicalCellGroupConfig__ext3O__bdFactorR_r16__n1
  end.
Lemma PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F1F2 : forall x : PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Type, (PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F1 x <= 0) /\ PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F2 (PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F1 (PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F2 y) = y. enum_solve H y. Qed.

Record PhysicalCellGroupConfig__ext3O__Type : Set :=
  make__PhysicalCellGroupConfig__ext3O__Type {
    PhysicalCellGroupConfig__ext3O__dcp_Config_r16 : option PhysicalCellGroupConfig__ext3O__dcp_Config_r16__Type ;
    PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16 : option PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Type ;
    PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16 : option PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16 : option PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Type ;
    PhysicalCellGroupConfig__ext3O__p_NR_FR2_r16 : option P_Max__Type ;
    PhysicalCellGroupConfig__ext3O__p_UE_FR2_r16 : option P_Max__Type ;
    PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16 : option PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Type ;
    PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16 : option PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16 : option PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Type ;
    PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16 : option PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Type ;
    PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16 : option PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16 : option PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16 : option PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16 : option PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Type ;
    PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16 : option PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Type ;
    PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16 : option PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16 : option PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__Type ;
    PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16 : option PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16 : option PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16 : option PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__Type ;
    PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16 : option PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__Type ;
    PhysicalCellGroupConfig__ext3O__bdFactorR_r16 : option PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Type ;
}.
Definition PhysicalCellGroupConfig__ext3O__list := (
 Opt PhysicalCellGroupConfig__ext3O__dcp_Config_r16__Type PhysicalCellGroupConfig__ext3O__dcp_Config_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Type PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Type PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Type PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__cond ::
 Opt P_Max__Type P_Max__cond ::
 Opt P_Max__Type P_Max__cond ::
 Opt PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Type PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Type PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Type PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Type PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Type PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Type PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Type PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Type PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Type PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Type PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__Type PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Type PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__Type PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__Type PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__Type PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__cond ::
 Opt PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Type PhysicalCellGroupConfig__ext3O__bdFactorR_r16__cond ::
 nil).
Definition PhysicalCellGroupConfig__ext3O__cond z := 
  opt_cond PhysicalCellGroupConfig__ext3O__dcp_Config_r16__cond (PhysicalCellGroupConfig__ext3O__dcp_Config_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__cond (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__cond (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__cond (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16 z) /\
  opt_cond P_Max__cond (PhysicalCellGroupConfig__ext3O__p_NR_FR2_r16 z) /\
  opt_cond P_Max__cond (PhysicalCellGroupConfig__ext3O__p_UE_FR2_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__cond (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__cond (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__cond (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__cond (PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__cond (PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__cond (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__cond (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__cond (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__cond (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__cond (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__cond (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__cond (PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__cond (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__cond (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__cond (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16 z) /\
  opt_cond PhysicalCellGroupConfig__ext3O__bdFactorR_r16__cond (PhysicalCellGroupConfig__ext3O__bdFactorR_r16 z) /\
  True.

Definition PhysicalCellGroupConfig__ext3__Type := PhysicalCellGroupConfig__ext3O__Type.
Definition PhysicalCellGroupConfig__ext3__cond := PhysicalCellGroupConfig__ext3O__cond.

Require Import NR.PDSCH_HARQ_ACK_EnhType3_r17.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__cond PDSCH_HARQ_ACK_EnhType3_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__Type := list PDSCH_HARQ_ACK_EnhType3_r17__Type.

Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__helper1 : (0 <= 1 <= maxNrofEnhType3HARQ_ACK_r17)%Z. unfold maxNrofEnhType3HARQ_ACK_r17.
 lia. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofEnhType3HARQ_ACK_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofEnhType3HARQ_ACK_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__cond (z : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofEnhType3HARQ_ACK_r17)%Z /\ (list_and PDSCH_HARQ_ACK_EnhType3_r17__cond z) .

Require Import NR.PDSCH_HARQ_ACK_EnhType3Index_r17.

Opaque PDSCH_HARQ_ACK_EnhType3Index_r17__cond PDSCH_HARQ_ACK_EnhType3Index_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__Type := list PDSCH_HARQ_ACK_EnhType3Index_r17__Type.

Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofEnhType3HARQ_ACK_r17)%Z. unfold maxNrofEnhType3HARQ_ACK_r17.
 lia. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofEnhType3HARQ_ACK_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofEnhType3HARQ_ACK_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__cond (z : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofEnhType3HARQ_ACK_r17)%Z /\ (list_and PDSCH_HARQ_ACK_EnhType3Index_r17__cond z) .

Require Import NR.PDSCH_HARQ_ACK_EnhType3_r17.

Opaque PDSCH_HARQ_ACK_EnhType3_r17__cond PDSCH_HARQ_ACK_EnhType3_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__Type := list PDSCH_HARQ_ACK_EnhType3_r17__Type.

Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__helper1 : (0 <= 1 <= maxNrofEnhType3HARQ_ACK_r17)%Z. unfold maxNrofEnhType3HARQ_ACK_r17.
 lia. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofEnhType3HARQ_ACK_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofEnhType3HARQ_ACK_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__cond (z : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofEnhType3HARQ_ACK_r17)%Z /\ (list_and PDSCH_HARQ_ACK_EnhType3_r17__cond z) .

Require Import NR.PDSCH_HARQ_ACK_EnhType3Index_r17.

Opaque PDSCH_HARQ_ACK_EnhType3Index_r17__cond PDSCH_HARQ_ACK_EnhType3Index_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__Type := list PDSCH_HARQ_ACK_EnhType3Index_r17__Type.

Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofEnhType3HARQ_ACK_r17)%Z. unfold maxNrofEnhType3HARQ_ACK_r17.
 lia. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofEnhType3HARQ_ACK_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofEnhType3HARQ_ACK_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__cond (z : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofEnhType3HARQ_ACK_r17)%Z /\ (list_and PDSCH_HARQ_ACK_EnhType3Index_r17__cond z) .

Inductive PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Type, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F2 (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F1 (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Type, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F2 (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F1 (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Type, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F2 (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F1 (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Type, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F2 (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F1 (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SCellIndex.

Opaque SCellIndex__cond SCellIndex__Format.

Require Import NR.SCellIndex.

Opaque SCellIndex__cond SCellIndex__Format.

Inductive PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Type, (PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F2 (PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F1 (PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Type, (PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F2 (PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F1 (PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F2 y) = y. enum_solve H y. Qed.

Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__Type := Z.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__cond := (fun z => (0 <= z <= 1)%Z).
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__Type := list Z.

Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__helper1 : (0 <= 1 <= maxNrofSlots)%Z. unfold maxNrofSlots.
 lia. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSlots - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSlots - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__cond (z : PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSlots)%Z /\ (list_and PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__cond z) .

Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__Type := Z.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__cond := (fun z => (0 <= z <= 1)%Z).
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__Type := list Z.

Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__helper1 : (0 <= 1 <= maxNrofSlots)%Z. unfold maxNrofSlots.
 lia. Qed.
Lemma PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSlots - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSlots - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__cond (z : PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSlots)%Z /\ (list_and PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__cond z) .

Inductive PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Type, (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F2 (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F1 (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Type, (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F2 (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F1 (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Type, (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F2 (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F1 (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Type, (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F2 (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F1 (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Type, (PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F2 (PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F1 (PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Type, (PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F2 (PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F1 (PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F2 y) = y. enum_solve H y. Qed.

Inductive PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__enabled
.
Definition PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__enabled
  | _ => PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Type, (PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F2 (PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F1 (PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.MulticastConfig_r17.
Definition PhysicalCellGroupConfig__ext4O__multicastConfig_r17__Type := SetupRelease__Type MulticastConfig_r17__Type.
Definition PhysicalCellGroupConfig__ext4O__multicastConfig_r17__cond := SetupRelease__cond _ MulticastConfig_r17__cond.
Definition PhysicalCellGroupConfig__ext4O__multicastConfig_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__multicastConfig_r17__Type PhysicalCellGroupConfig__ext4O__multicastConfig_r17__cond := SetupRelease__Format _ _ MulticastConfig_r17__Format.
Opaque PhysicalCellGroupConfig__ext4O__multicastConfig_r17__cond PhysicalCellGroupConfig__ext4O__multicastConfig_r17__Format.

Require Import NR.SetupRelease.
Require Import NR.PDCCH_BlindDetectionCA_CombIndicator_r17.
Definition PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__Type := SetupRelease__Type PDCCH_BlindDetectionCA_CombIndicator_r17__Type.
Definition PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__cond := SetupRelease__cond _ PDCCH_BlindDetectionCA_CombIndicator_r17__cond.
Definition PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__Type PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__cond := SetupRelease__Format _ _ PDCCH_BlindDetectionCA_CombIndicator_r17__Format.
Opaque PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__cond PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__Format.

Record PhysicalCellGroupConfig__ext4O__Type : Set :=
  make__PhysicalCellGroupConfig__ext4O__Type {
    PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17 : option PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17 : option PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17 : option PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17 : option PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17 : option PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17 : option PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17 : option PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17 : option PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pucch_sSCell_r17 : option SCellIndex__Type ;
    PhysicalCellGroupConfig__ext4O__pucch_sSCellSecondaryPUCCHgroup_r17 : option SCellIndex__Type ;
    PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17 : option PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17 : option PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17 : option PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17 : option PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__Type ;
    PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17 : option PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Type ;
    PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17 : option PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Type ;
    PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17 : option PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Type ;
    PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17 : option PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Type ;
    PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17 : option PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Type ;
    PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17 : option PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Type ;
    PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17 : option PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Type ;
    PhysicalCellGroupConfig__ext4O__multicastConfig_r17 : option PhysicalCellGroupConfig__ext4O__multicastConfig_r17__Type ;
    PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17 : option PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__Type ;
}.
Definition PhysicalCellGroupConfig__ext4O__list := (
 Opt PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__cond ::
 Opt SCellIndex__Type SCellIndex__cond ::
 Opt SCellIndex__Type SCellIndex__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Type PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Type PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__Type PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__Type PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Type PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Type PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Type PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Type PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Type PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Type PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Type PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__multicastConfig_r17__Type PhysicalCellGroupConfig__ext4O__multicastConfig_r17__cond ::
 Opt PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__Type PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__cond ::
 nil).
Definition PhysicalCellGroupConfig__ext4O__cond z := 
  opt_cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__cond (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__cond (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__cond (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__cond (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__cond (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__cond (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__cond (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__cond (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17 z) /\
  opt_cond SCellIndex__cond (PhysicalCellGroupConfig__ext4O__pucch_sSCell_r17 z) /\
  opt_cond SCellIndex__cond (PhysicalCellGroupConfig__ext4O__pucch_sSCellSecondaryPUCCHgroup_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__cond (PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__cond (PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__cond (PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__cond (PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__cond (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__cond (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__cond (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__cond (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__cond (PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__cond (PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__cond (PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__multicastConfig_r17__cond (PhysicalCellGroupConfig__ext4O__multicastConfig_r17 z) /\
  opt_cond PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__cond (PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17 z) /\
  True.

Definition PhysicalCellGroupConfig__ext4__Type := PhysicalCellGroupConfig__ext4O__Type.
Definition PhysicalCellGroupConfig__ext4__cond := PhysicalCellGroupConfig__ext4O__cond.

Inductive PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__enabled
.
Definition PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__enabled
  | _ => PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Type, (PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F2 (PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F1 (PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F2 y) = y. enum_solve H y. Qed.

Record PhysicalCellGroupConfig__ext5O__Type : Set :=
  make__PhysicalCellGroupConfig__ext5O__Type {
    PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17 : option PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Type ;
}.
Definition PhysicalCellGroupConfig__ext5O__list := (
 Opt PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Type PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__cond ::
 nil).
Definition PhysicalCellGroupConfig__ext5O__cond z := 
  opt_cond PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__cond (PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17 z) /\
  True.

Definition PhysicalCellGroupConfig__ext5__Type := PhysicalCellGroupConfig__ext5O__Type.
Definition PhysicalCellGroupConfig__ext5__cond := PhysicalCellGroupConfig__ext5O__cond.

Inductive PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Type : Set :=
 | PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__enabled
.
Definition PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__cond := (fun (_ : PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Type) => True).
Lemma PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__nat__helper.

Definition PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F1 t :=
  match t with
  | PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__enabled => 0
  end.
Definition PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F2 n :=
  match n with
  | 0 => PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__enabled
  | _ => PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__enabled
  end.
Lemma PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F1F2 : forall x : PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Type, (PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F1 x <= 0) /\ PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F2 (PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F1 x) = x. imp_solve. Qed.
Lemma PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F2F1 : forall (y : nat) (H : y <= 0), PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F1 (PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F2 y) = y. enum_solve H y. Qed.

Record PhysicalCellGroupConfig__ext6O__Type : Set :=
  make__PhysicalCellGroupConfig__ext6O__Type {
    PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17 : option PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Type ;
}.
Definition PhysicalCellGroupConfig__ext6O__list := (
 Opt PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Type PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__cond ::
 nil).
Definition PhysicalCellGroupConfig__ext6O__cond z := 
  opt_cond PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__cond (PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17 z) /\
  True.

Definition PhysicalCellGroupConfig__ext6__Type := PhysicalCellGroupConfig__ext6O__Type.
Definition PhysicalCellGroupConfig__ext6__cond := PhysicalCellGroupConfig__ext6O__cond.

Record PhysicalCellGroupConfig__Type : Set :=
  make__PhysicalCellGroupConfig__Type {
    PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH : option PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Type ;
    PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH : option PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Type ;
    PhysicalCellGroupConfig__p_NR_FR1 : option P_Max__Type ;
    PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook : PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Type ;
    PhysicalCellGroupConfig__tpc_SRS_RNTI : option RNTI_Value__Type ;
    PhysicalCellGroupConfig__tpc_PUCCH_RNTI : option RNTI_Value__Type ;
    PhysicalCellGroupConfig__tpc_PUSCH_RNTI : option RNTI_Value__Type ;
    PhysicalCellGroupConfig__sp_CSI_RNTI : option RNTI_Value__Type ;
    PhysicalCellGroupConfig__cs_RNTI : option PhysicalCellGroupConfig__cs_RNTI__Type ;
    PhysicalCellGroupConfig__ext0 : option PhysicalCellGroupConfig__ext0__Type ;
    PhysicalCellGroupConfig__ext1 : option PhysicalCellGroupConfig__ext1__Type ;
    PhysicalCellGroupConfig__ext2 : option PhysicalCellGroupConfig__ext2__Type ;
    PhysicalCellGroupConfig__ext3 : option PhysicalCellGroupConfig__ext3__Type ;
    PhysicalCellGroupConfig__ext4 : option PhysicalCellGroupConfig__ext4__Type ;
    PhysicalCellGroupConfig__ext5 : option PhysicalCellGroupConfig__ext5__Type ;
    PhysicalCellGroupConfig__ext6 : option PhysicalCellGroupConfig__ext6__Type ;
}.
Definition PhysicalCellGroupConfig__root_list : list seq_elem := (
 Opt PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Type PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__cond ::
 Opt PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Type PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__cond ::
 Opt P_Max__Type P_Max__cond ::
 Nor PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Type PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__cond ::
 Opt RNTI_Value__Type RNTI_Value__cond ::
 Opt RNTI_Value__Type RNTI_Value__cond ::
 Opt RNTI_Value__Type RNTI_Value__cond ::
 Opt RNTI_Value__Type RNTI_Value__cond ::
 Opt PhysicalCellGroupConfig__cs_RNTI__Type PhysicalCellGroupConfig__cs_RNTI__cond ::
 nil).
Definition PhysicalCellGroupConfig__ext_list : list typ := (
  typ_cons PhysicalCellGroupConfig__ext0__Type PhysicalCellGroupConfig__ext0__cond ::
  typ_cons PhysicalCellGroupConfig__ext1__Type PhysicalCellGroupConfig__ext1__cond ::
  typ_cons PhysicalCellGroupConfig__ext2__Type PhysicalCellGroupConfig__ext2__cond ::
  typ_cons PhysicalCellGroupConfig__ext3__Type PhysicalCellGroupConfig__ext3__cond ::
  typ_cons PhysicalCellGroupConfig__ext4__Type PhysicalCellGroupConfig__ext4__cond ::
  typ_cons PhysicalCellGroupConfig__ext5__Type PhysicalCellGroupConfig__ext5__cond ::
  typ_cons PhysicalCellGroupConfig__ext6__Type PhysicalCellGroupConfig__ext6__cond ::
  nil).
Definition PhysicalCellGroupConfig__cond (z : PhysicalCellGroupConfig__Type) := 
(  opt_cond PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__cond (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH z) /\
  opt_cond PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__cond (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH z) /\
  opt_cond P_Max__cond (PhysicalCellGroupConfig__p_NR_FR1 z) /\
  PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__cond (PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook z) /\
  opt_cond RNTI_Value__cond (PhysicalCellGroupConfig__tpc_SRS_RNTI z) /\
  opt_cond RNTI_Value__cond (PhysicalCellGroupConfig__tpc_PUCCH_RNTI z) /\
  opt_cond RNTI_Value__cond (PhysicalCellGroupConfig__tpc_PUSCH_RNTI z) /\
  opt_cond RNTI_Value__cond (PhysicalCellGroupConfig__sp_CSI_RNTI z) /\
  opt_cond PhysicalCellGroupConfig__cs_RNTI__cond (PhysicalCellGroupConfig__cs_RNTI z) /\
  True) /\ 
(  opt_cond PhysicalCellGroupConfig__ext0__cond (PhysicalCellGroupConfig__ext0 z) /\
  opt_cond PhysicalCellGroupConfig__ext1__cond (PhysicalCellGroupConfig__ext1 z) /\
  opt_cond PhysicalCellGroupConfig__ext2__cond (PhysicalCellGroupConfig__ext2 z) /\
  opt_cond PhysicalCellGroupConfig__ext3__cond (PhysicalCellGroupConfig__ext3 z) /\
  opt_cond PhysicalCellGroupConfig__ext4__cond (PhysicalCellGroupConfig__ext4 z) /\
  opt_cond PhysicalCellGroupConfig__ext5__cond (PhysicalCellGroupConfig__ext5 z) /\
  opt_cond PhysicalCellGroupConfig__ext6__cond (PhysicalCellGroupConfig__ext6 z) /\
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
Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Format : T_Format PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__nat__Format PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F1 PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F2 PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F1F2 PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__F2F1.

Opaque PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__cond PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Format.

Definition PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Format : T_Format PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__nat__Format PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F1 PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F2 PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F1F2 PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__F2F1.

Opaque PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__cond PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Format.

Definition PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Format : T_Format PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__nat__Format PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F1 PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F2 PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F1F2 PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__F2F1.

Opaque PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__cond PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Format.

Opaque PhysicalCellGroupConfig__cs_RNTI__cond PhysicalCellGroupConfig__cs_RNTI__Format.


Definition PhysicalCellGroupConfig__ext0O__Format_Type := Eval cbn in seq_format_prod PhysicalCellGroupConfig__ext0O__list.
Definition PhysicalCellGroupConfig__ext0O__Format_list : PhysicalCellGroupConfig__ext0O__Format_Type :=
  (RNTI_Value__Format, (P_Max__Format, unit_format)).
Definition PhysicalCellGroupConfig__ext0O__list__Format := (*Eval compute in *) seq_format PhysicalCellGroupConfig__ext0O__list PhysicalCellGroupConfig__ext0O__Format_list.
Definition PhysicalCellGroupConfig__ext0O__F1 z :=
  (PhysicalCellGroupConfig__ext0O__mcs_C_RNTI z, (PhysicalCellGroupConfig__ext0O__p_UE_FR1 z, tt)).
Definition PhysicalCellGroupConfig__ext0O__F2 (y : seq_type PhysicalCellGroupConfig__ext0O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__PhysicalCellGroupConfig__ext0O__Type i0 i1
  end.
Lemma PhysicalCellGroupConfig__ext0O__F1F2_cond (z : PhysicalCellGroupConfig__ext0O__Type)
  : PhysicalCellGroupConfig__ext0O__cond z ->
  (seq_cond PhysicalCellGroupConfig__ext0O__list (PhysicalCellGroupConfig__ext0O__F1 z)).
intro H. unfold PhysicalCellGroupConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext0O__F1F2_cond2 (z : PhysicalCellGroupConfig__ext0O__Type)
 : PhysicalCellGroupConfig__ext0O__F2 (PhysicalCellGroupConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext0O__F2F1_cond (y : seq_type PhysicalCellGroupConfig__ext0O__list)
  : seq_cond PhysicalCellGroupConfig__ext0O__list y ->
 (PhysicalCellGroupConfig__ext0O__cond (PhysicalCellGroupConfig__ext0O__F2 y)) /\  PhysicalCellGroupConfig__ext0O__F1 (PhysicalCellGroupConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PhysicalCellGroupConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold PhysicalCellGroupConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PhysicalCellGroupConfig__ext0O__Format : T_Format PhysicalCellGroupConfig__ext0O__Type PhysicalCellGroupConfig__ext0O__cond :=
        proj2_format  PhysicalCellGroupConfig__ext0O__cond PhysicalCellGroupConfig__ext0O__list__Format
    PhysicalCellGroupConfig__ext0O__F1 PhysicalCellGroupConfig__ext0O__F2 PhysicalCellGroupConfig__ext0O__F1F2_cond  PhysicalCellGroupConfig__ext0O__F1F2_cond2 PhysicalCellGroupConfig__ext0O__F2F1_cond.
Opaque PhysicalCellGroupConfig__ext0O__cond PhysicalCellGroupConfig__ext0O__Format.

Definition PhysicalCellGroupConfig__ext0__check_all_none (b : PhysicalCellGroupConfig__ext0O__Type) : bool :=
match b with 
  | make__PhysicalCellGroupConfig__ext0O__Type None None  => false 
  | _ => true 
 end.
Definition PhysicalCellGroupConfig__ext0__Format : T_Format PhysicalCellGroupConfig__ext0__Type PhysicalCellGroupConfig__ext0__cond :=
  restrict_add_format PhysicalCellGroupConfig__ext0__check_all_none PhysicalCellGroupConfig__ext0O__Format.

Opaque PhysicalCellGroupConfig__ext0__cond PhysicalCellGroupConfig__ext0__Format.

Definition PhysicalCellGroupConfig__ext1O__xScale__Format : T_Format PhysicalCellGroupConfig__ext1O__xScale__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext1O__xScale__nat__Format PhysicalCellGroupConfig__ext1O__xScale__F1 PhysicalCellGroupConfig__ext1O__xScale__F2 PhysicalCellGroupConfig__ext1O__xScale__F1F2 PhysicalCellGroupConfig__ext1O__xScale__F2F1.

Opaque PhysicalCellGroupConfig__ext1O__xScale__cond PhysicalCellGroupConfig__ext1O__xScale__Format.


Definition PhysicalCellGroupConfig__ext1O__Format_Type := Eval cbn in seq_format_prod PhysicalCellGroupConfig__ext1O__list.
Definition PhysicalCellGroupConfig__ext1O__Format_list : PhysicalCellGroupConfig__ext1O__Format_Type :=
  (PhysicalCellGroupConfig__ext1O__xScale__Format, unit_format).
Definition PhysicalCellGroupConfig__ext1O__list__Format := (*Eval compute in *) seq_format PhysicalCellGroupConfig__ext1O__list PhysicalCellGroupConfig__ext1O__Format_list.
Definition PhysicalCellGroupConfig__ext1O__F1 z :=
  (PhysicalCellGroupConfig__ext1O__xScale z, tt).
Definition PhysicalCellGroupConfig__ext1O__F2 (y : seq_type PhysicalCellGroupConfig__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__PhysicalCellGroupConfig__ext1O__Type i0
  end.
Lemma PhysicalCellGroupConfig__ext1O__F1F2_cond (z : PhysicalCellGroupConfig__ext1O__Type)
  : PhysicalCellGroupConfig__ext1O__cond z ->
  (seq_cond PhysicalCellGroupConfig__ext1O__list (PhysicalCellGroupConfig__ext1O__F1 z)).
intro H. unfold PhysicalCellGroupConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext1O__F1F2_cond2 (z : PhysicalCellGroupConfig__ext1O__Type)
 : PhysicalCellGroupConfig__ext1O__F2 (PhysicalCellGroupConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext1O__F2F1_cond (y : seq_type PhysicalCellGroupConfig__ext1O__list)
  : seq_cond PhysicalCellGroupConfig__ext1O__list y ->
 (PhysicalCellGroupConfig__ext1O__cond (PhysicalCellGroupConfig__ext1O__F2 y)) /\  PhysicalCellGroupConfig__ext1O__F1 (PhysicalCellGroupConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PhysicalCellGroupConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold PhysicalCellGroupConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PhysicalCellGroupConfig__ext1O__Format : T_Format PhysicalCellGroupConfig__ext1O__Type PhysicalCellGroupConfig__ext1O__cond :=
        proj2_format  PhysicalCellGroupConfig__ext1O__cond PhysicalCellGroupConfig__ext1O__list__Format
    PhysicalCellGroupConfig__ext1O__F1 PhysicalCellGroupConfig__ext1O__F2 PhysicalCellGroupConfig__ext1O__F1F2_cond  PhysicalCellGroupConfig__ext1O__F1F2_cond2 PhysicalCellGroupConfig__ext1O__F2F1_cond.
Opaque PhysicalCellGroupConfig__ext1O__cond PhysicalCellGroupConfig__ext1O__Format.

Definition PhysicalCellGroupConfig__ext1__check_all_none (b : PhysicalCellGroupConfig__ext1O__Type) : bool :=
match b with 
  | make__PhysicalCellGroupConfig__ext1O__Type None  => false 
  | _ => true 
 end.
Definition PhysicalCellGroupConfig__ext1__Format : T_Format PhysicalCellGroupConfig__ext1__Type PhysicalCellGroupConfig__ext1__cond :=
  restrict_add_format PhysicalCellGroupConfig__ext1__check_all_none PhysicalCellGroupConfig__ext1O__Format.

Opaque PhysicalCellGroupConfig__ext1__cond PhysicalCellGroupConfig__ext1__Format.

Opaque PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__cond PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__Format.


Definition PhysicalCellGroupConfig__ext2O__Format_Type := Eval cbn in seq_format_prod PhysicalCellGroupConfig__ext2O__list.
Definition PhysicalCellGroupConfig__ext2O__Format_list : PhysicalCellGroupConfig__ext2O__Format_Type :=
  (PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection__Format, unit_format).
Definition PhysicalCellGroupConfig__ext2O__list__Format := (*Eval compute in *) seq_format PhysicalCellGroupConfig__ext2O__list PhysicalCellGroupConfig__ext2O__Format_list.
Definition PhysicalCellGroupConfig__ext2O__F1 z :=
  (PhysicalCellGroupConfig__ext2O__pdcch_BlindDetection z, tt).
Definition PhysicalCellGroupConfig__ext2O__F2 (y : seq_type PhysicalCellGroupConfig__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__PhysicalCellGroupConfig__ext2O__Type i0
  end.
Lemma PhysicalCellGroupConfig__ext2O__F1F2_cond (z : PhysicalCellGroupConfig__ext2O__Type)
  : PhysicalCellGroupConfig__ext2O__cond z ->
  (seq_cond PhysicalCellGroupConfig__ext2O__list (PhysicalCellGroupConfig__ext2O__F1 z)).
intro H. unfold PhysicalCellGroupConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext2O__F1F2_cond2 (z : PhysicalCellGroupConfig__ext2O__Type)
 : PhysicalCellGroupConfig__ext2O__F2 (PhysicalCellGroupConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext2O__F2F1_cond (y : seq_type PhysicalCellGroupConfig__ext2O__list)
  : seq_cond PhysicalCellGroupConfig__ext2O__list y ->
 (PhysicalCellGroupConfig__ext2O__cond (PhysicalCellGroupConfig__ext2O__F2 y)) /\  PhysicalCellGroupConfig__ext2O__F1 (PhysicalCellGroupConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PhysicalCellGroupConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold PhysicalCellGroupConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PhysicalCellGroupConfig__ext2O__Format : T_Format PhysicalCellGroupConfig__ext2O__Type PhysicalCellGroupConfig__ext2O__cond :=
        proj2_format  PhysicalCellGroupConfig__ext2O__cond PhysicalCellGroupConfig__ext2O__list__Format
    PhysicalCellGroupConfig__ext2O__F1 PhysicalCellGroupConfig__ext2O__F2 PhysicalCellGroupConfig__ext2O__F1F2_cond  PhysicalCellGroupConfig__ext2O__F1F2_cond2 PhysicalCellGroupConfig__ext2O__F2F1_cond.
Opaque PhysicalCellGroupConfig__ext2O__cond PhysicalCellGroupConfig__ext2O__Format.

Definition PhysicalCellGroupConfig__ext2__check_all_none (b : PhysicalCellGroupConfig__ext2O__Type) : bool :=
match b with 
  | make__PhysicalCellGroupConfig__ext2O__Type None  => false 
  | _ => true 
 end.
Definition PhysicalCellGroupConfig__ext2__Format : T_Format PhysicalCellGroupConfig__ext2__Type PhysicalCellGroupConfig__ext2__cond :=
  restrict_add_format PhysicalCellGroupConfig__ext2__check_all_none PhysicalCellGroupConfig__ext2O__Format.

Opaque PhysicalCellGroupConfig__ext2__cond PhysicalCellGroupConfig__ext2__Format.

Opaque PhysicalCellGroupConfig__ext3O__dcp_Config_r16__cond PhysicalCellGroupConfig__ext3O__dcp_Config_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__nat__Format PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F1 PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F2 PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F1F2 PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__cond PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__nat__Format PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F1 PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F2 PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F1F2 PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__cond PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__nat__Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F1 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F1F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__nat__Format PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F1 PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F2 PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F1F2 PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__cond PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__nat__Format PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F1 PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F2 PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F1F2 PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__cond PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__nat__Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F1 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F1F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__nat__Format PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F1 PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F2 PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F1F2 PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__cond PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__nat__Format PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F1 PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F2 PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F1F2 PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__cond PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__nat__Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F1 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F1F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__nat__Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F1 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F1F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__nat__Format PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F1 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F1F2 PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__nat__Format PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F1 PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F2 PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F1F2 PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__cond PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__nat__Format PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F1 PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F2 PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F1F2 PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__cond PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Format.

Opaque PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__cond PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__nat__Format PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F1 PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F2 PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F1F2 PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__cond PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Format.

Opaque PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__Format.

Opaque PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__Format.

Opaque PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__cond PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__Format.

Definition PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Format : T_Format PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext3O__bdFactorR_r16__nat__Format PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F1 PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F2 PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F1F2 PhysicalCellGroupConfig__ext3O__bdFactorR_r16__F2F1.

Opaque PhysicalCellGroupConfig__ext3O__bdFactorR_r16__cond PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Format.


Definition PhysicalCellGroupConfig__ext3O__Format_Type := Eval cbn in seq_format_prod PhysicalCellGroupConfig__ext3O__list.
Definition PhysicalCellGroupConfig__ext3O__Format_list : PhysicalCellGroupConfig__ext3O__Format_Type :=
  (PhysicalCellGroupConfig__ext3O__dcp_Config_r16__Format, (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16__Format, (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16__Format, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16__Format, (P_Max__Format, (P_Max__Format, (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16__Format, (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16__Format, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16__Format, (PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16__Format, (PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16__Format, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16__Format, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16__Format, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16__Format, (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16__Format, (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16__Format, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16__Format, (PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16__Format, (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16__Format, (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16__Format, (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16__Format, (PhysicalCellGroupConfig__ext3O__bdFactorR_r16__Format, unit_format)))))))))))))))))))))).
Definition PhysicalCellGroupConfig__ext3O__list__Format := (*Eval compute in *) seq_format PhysicalCellGroupConfig__ext3O__list PhysicalCellGroupConfig__ext3O__Format_list.
Definition PhysicalCellGroupConfig__ext3O__F1 z :=
  (PhysicalCellGroupConfig__ext3O__dcp_Config_r16 z, (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUCCH_secondaryPUCCHgroup_r16 z, (PhysicalCellGroupConfig__ext3O__harq_ACK_SpatialBundlingPUSCH_secondaryPUCCHgroup_r16 z, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_secondaryPUCCHgroup_r16 z, (PhysicalCellGroupConfig__ext3O__p_NR_FR2_r16 z, (PhysicalCellGroupConfig__ext3O__p_UE_FR2_r16 z, (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR1_r16 z, (PhysicalCellGroupConfig__ext3O__nrdc_PCmode_FR2_r16 z, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_Codebook_r16 z, (PhysicalCellGroupConfig__ext3O__nfi_TotalDAI_Included_r16 z, (PhysicalCellGroupConfig__ext3O__ul_TotalDAI_Included_r16 z, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedback_r16 z, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackNDI_r16 z, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_OneShotFeedbackCBG_r16 z, (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_0_2_r16 z, (PhysicalCellGroupConfig__ext3O__downlinkAssignmentIndexDCI_1_2_r16 z, (PhysicalCellGroupConfig__ext3O__pdsch_HARQ_ACK_CodebookList_r16 z, (PhysicalCellGroupConfig__ext3O__ackNackFeedbackMode_r16 z, (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetectionCA_CombIndicator_r16 z, (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection2_r16 z, (PhysicalCellGroupConfig__ext3O__pdcch_BlindDetection3_r16 z, (PhysicalCellGroupConfig__ext3O__bdFactorR_r16 z, tt)))))))))))))))))))))).
Definition PhysicalCellGroupConfig__ext3O__F2 (y : seq_type PhysicalCellGroupConfig__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, _))))))))))))))))))))))=>
    make__PhysicalCellGroupConfig__ext3O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21
  end.
Lemma PhysicalCellGroupConfig__ext3O__F1F2_cond (z : PhysicalCellGroupConfig__ext3O__Type)
  : PhysicalCellGroupConfig__ext3O__cond z ->
  (seq_cond PhysicalCellGroupConfig__ext3O__list (PhysicalCellGroupConfig__ext3O__F1 z)).
intro H. unfold PhysicalCellGroupConfig__ext3O__cond in H. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext3O__F1F2_cond2 (z : PhysicalCellGroupConfig__ext3O__Type)
 : PhysicalCellGroupConfig__ext3O__F2 (PhysicalCellGroupConfig__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext3O__F2F1_cond (y : seq_type PhysicalCellGroupConfig__ext3O__list)
  : seq_cond PhysicalCellGroupConfig__ext3O__list y ->
 (PhysicalCellGroupConfig__ext3O__cond (PhysicalCellGroupConfig__ext3O__F2 y)) /\  PhysicalCellGroupConfig__ext3O__F1 (PhysicalCellGroupConfig__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PhysicalCellGroupConfig__ext3O__cond. simpl in *. auto.
 - simpl. unfold PhysicalCellGroupConfig__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PhysicalCellGroupConfig__ext3O__Format : T_Format PhysicalCellGroupConfig__ext3O__Type PhysicalCellGroupConfig__ext3O__cond :=
        proj2_format  PhysicalCellGroupConfig__ext3O__cond PhysicalCellGroupConfig__ext3O__list__Format
    PhysicalCellGroupConfig__ext3O__F1 PhysicalCellGroupConfig__ext3O__F2 PhysicalCellGroupConfig__ext3O__F1F2_cond  PhysicalCellGroupConfig__ext3O__F1F2_cond2 PhysicalCellGroupConfig__ext3O__F2F1_cond.
Opaque PhysicalCellGroupConfig__ext3O__cond PhysicalCellGroupConfig__ext3O__Format.

Definition PhysicalCellGroupConfig__ext3__check_all_none (b : PhysicalCellGroupConfig__ext3O__Type) : bool :=
match b with 
  | make__PhysicalCellGroupConfig__ext3O__Type None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition PhysicalCellGroupConfig__ext3__Format : T_Format PhysicalCellGroupConfig__ext3__Type PhysicalCellGroupConfig__ext3__cond :=
  restrict_add_format PhysicalCellGroupConfig__ext3__check_all_none PhysicalCellGroupConfig__ext3O__Format.

Opaque PhysicalCellGroupConfig__ext3__cond PhysicalCellGroupConfig__ext3__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__cond := seq_of_format PDSCH_HARQ_ACK_EnhType3_r17__Format 1 maxNrofEnhType3HARQ_ACK_r17 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__helper1 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__helper2.

Opaque PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__cond := seq_of_format PDSCH_HARQ_ACK_EnhType3Index_r17__Format 1 maxNrofEnhType3HARQ_ACK_r17 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__helper1 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__helper2.

Opaque PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__cond := seq_of_format PDSCH_HARQ_ACK_EnhType3_r17__Format 1 maxNrofEnhType3HARQ_ACK_r17 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__helper1 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__helper2.

Opaque PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__Type PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__cond := seq_of_format PDSCH_HARQ_ACK_EnhType3Index_r17__Format 1 maxNrofEnhType3HARQ_ACK_r17 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__helper1 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__helper2.

Opaque PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__nat__Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F1 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F2 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F1F2 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__nat__Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F1 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F2 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F1F2 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__nat__Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F1 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F2 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F1F2 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__nat__Format PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F1 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F2 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F1F2 PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__cond PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__nat__Format PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F1 PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F2 PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F1F2 PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__cond PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__nat__Format PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F1 PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F2 PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F1F2 PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__cond PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__Format : T_Format Z PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__cond :=
 ranged_int_format (0) (1) PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__helper1 PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__helper2.

Opaque PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__cond PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__Format.

Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__Type PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__cond := seq_of_format PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__seq_of__Format 1 maxNrofSlots PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__helper1 PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__helper2.

Opaque PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__cond PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__Format : T_Format Z PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__cond :=
 ranged_int_format (0) (1) PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__helper1 PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__helper2.

Opaque PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__cond PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__Format.

Definition PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__Type PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__cond := seq_of_format PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__seq_of__Format 1 maxNrofSlots PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__helper1 PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__helper2.

Opaque PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__cond PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__nat__Format PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F1 PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F2 PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F1F2 PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__cond PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__nat__Format PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F1 PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F2 PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F1F2 PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__cond PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__nat__Format PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F1 PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F2 PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F1F2 PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__cond PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__nat__Format PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F1 PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F2 PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F1F2 PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__cond PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__nat__Format PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F1 PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F2 PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F1F2 PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__cond PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__nat__Format PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F1 PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F2 PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F1F2 PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__cond PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Format.

Definition PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Format : T_Format PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__nat__Format PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F1 PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F2 PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F1F2 PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__cond PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Format.

Opaque PhysicalCellGroupConfig__ext4O__multicastConfig_r17__cond PhysicalCellGroupConfig__ext4O__multicastConfig_r17__Format.

Opaque PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__cond PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__Format.


Definition PhysicalCellGroupConfig__ext4O__Format_Type := Eval cbn in seq_format_prod PhysicalCellGroupConfig__ext4O__list.
Definition PhysicalCellGroupConfig__ext4O__Format_list : PhysicalCellGroupConfig__ext4O__Format_Type :=
  (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17__Format, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17__Format, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17__Format, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17__Format, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17__Format, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17__Format, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17__Format, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17__Format, (SCellIndex__Format, (SCellIndex__Format, (PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17__Format, (PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17__Format, (PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17__Format, (PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17__Format, (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17__Format, (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17__Format, (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17__Format, (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17__Format, (PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17__Format, (PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17__Format, (PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17__Format, (PhysicalCellGroupConfig__ext4O__multicastConfig_r17__Format, (PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17__Format, unit_format))))))))))))))))))))))).
Definition PhysicalCellGroupConfig__ext4O__list__Format := (*Eval compute in *) seq_format PhysicalCellGroupConfig__ext4O__list PhysicalCellGroupConfig__ext4O__Format_list.
Definition PhysicalCellGroupConfig__ext4O__F1 z :=
  (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToAddModList_r17 z, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3ToReleaseList_r17 z, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToAddModList_r17 z, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3SecondaryToReleaseList_r17 z, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_FieldSecondaryPUCCHgroup_r17 z, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_EnhType3DCI_Field_r17 z, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_Retx_r17 z, (PhysicalCellGroupConfig__ext4O__pdsch_HARQ_ACK_RetxSecondaryPUCCHgroup_r17 z, (PhysicalCellGroupConfig__ext4O__pucch_sSCell_r17 z, (PhysicalCellGroupConfig__ext4O__pucch_sSCellSecondaryPUCCHgroup_r17 z, (PhysicalCellGroupConfig__ext4O__pucch_sSCellDyn_r17 z, (PhysicalCellGroupConfig__ext4O__pucch_sSCellDynSecondaryPUCCHgroup_r17 z, (PhysicalCellGroupConfig__ext4O__pucch_sSCellPattern_r17 z, (PhysicalCellGroupConfig__ext4O__pucch_sSCellPatternSecondaryPUCCHgroup_r17 z, (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrio_r17 z, (PhysicalCellGroupConfig__ext4O__uci_MuxWithDiffPrioSecondaryPUCCHgroup_r17 z, (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_r17 z, (PhysicalCellGroupConfig__ext4O__simultaneousPUCCH_PUSCH_SecondaryPUCCHgroup_r17 z, (PhysicalCellGroupConfig__ext4O__prioLowDG_HighCG_r17 z, (PhysicalCellGroupConfig__ext4O__prioHighDG_LowCG_r17 z, (PhysicalCellGroupConfig__ext4O__twoQCLTypeDforPDCCHRepetition_r17 z, (PhysicalCellGroupConfig__ext4O__multicastConfig_r17 z, (PhysicalCellGroupConfig__ext4O__pdcch_BlindDetectionCA_CombIndicator_r17 z, tt))))))))))))))))))))))).
Definition PhysicalCellGroupConfig__ext4O__F2 (y : seq_type PhysicalCellGroupConfig__ext4O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, _)))))))))))))))))))))))=>
    make__PhysicalCellGroupConfig__ext4O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22
  end.
Lemma PhysicalCellGroupConfig__ext4O__F1F2_cond (z : PhysicalCellGroupConfig__ext4O__Type)
  : PhysicalCellGroupConfig__ext4O__cond z ->
  (seq_cond PhysicalCellGroupConfig__ext4O__list (PhysicalCellGroupConfig__ext4O__F1 z)).
intro H. unfold PhysicalCellGroupConfig__ext4O__cond in H. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext4O__F1F2_cond2 (z : PhysicalCellGroupConfig__ext4O__Type)
 : PhysicalCellGroupConfig__ext4O__F2 (PhysicalCellGroupConfig__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext4O__F2F1_cond (y : seq_type PhysicalCellGroupConfig__ext4O__list)
  : seq_cond PhysicalCellGroupConfig__ext4O__list y ->
 (PhysicalCellGroupConfig__ext4O__cond (PhysicalCellGroupConfig__ext4O__F2 y)) /\  PhysicalCellGroupConfig__ext4O__F1 (PhysicalCellGroupConfig__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PhysicalCellGroupConfig__ext4O__cond. simpl in *. auto.
 - simpl. unfold PhysicalCellGroupConfig__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PhysicalCellGroupConfig__ext4O__Format : T_Format PhysicalCellGroupConfig__ext4O__Type PhysicalCellGroupConfig__ext4O__cond :=
        proj2_format  PhysicalCellGroupConfig__ext4O__cond PhysicalCellGroupConfig__ext4O__list__Format
    PhysicalCellGroupConfig__ext4O__F1 PhysicalCellGroupConfig__ext4O__F2 PhysicalCellGroupConfig__ext4O__F1F2_cond  PhysicalCellGroupConfig__ext4O__F1F2_cond2 PhysicalCellGroupConfig__ext4O__F2F1_cond.
Opaque PhysicalCellGroupConfig__ext4O__cond PhysicalCellGroupConfig__ext4O__Format.

Definition PhysicalCellGroupConfig__ext4__check_all_none (b : PhysicalCellGroupConfig__ext4O__Type) : bool :=
match b with 
  | make__PhysicalCellGroupConfig__ext4O__Type None None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition PhysicalCellGroupConfig__ext4__Format : T_Format PhysicalCellGroupConfig__ext4__Type PhysicalCellGroupConfig__ext4__cond :=
  restrict_add_format PhysicalCellGroupConfig__ext4__check_all_none PhysicalCellGroupConfig__ext4O__Format.

Opaque PhysicalCellGroupConfig__ext4__cond PhysicalCellGroupConfig__ext4__Format.

Definition PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Format : T_Format PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__nat__Format PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F1 PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F2 PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F1F2 PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__cond PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Format.


Definition PhysicalCellGroupConfig__ext5O__Format_Type := Eval cbn in seq_format_prod PhysicalCellGroupConfig__ext5O__list.
Definition PhysicalCellGroupConfig__ext5O__Format_list : PhysicalCellGroupConfig__ext5O__Format_Type :=
  (PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17__Format, unit_format).
Definition PhysicalCellGroupConfig__ext5O__list__Format := (*Eval compute in *) seq_format PhysicalCellGroupConfig__ext5O__list PhysicalCellGroupConfig__ext5O__Format_list.
Definition PhysicalCellGroupConfig__ext5O__F1 z :=
  (PhysicalCellGroupConfig__ext5O__simultaneousSR_PUSCH_diffPUCCH_Groups_r17 z, tt).
Definition PhysicalCellGroupConfig__ext5O__F2 (y : seq_type PhysicalCellGroupConfig__ext5O__list) :=
  match y with
  | (i0, _)=>
    make__PhysicalCellGroupConfig__ext5O__Type i0
  end.
Lemma PhysicalCellGroupConfig__ext5O__F1F2_cond (z : PhysicalCellGroupConfig__ext5O__Type)
  : PhysicalCellGroupConfig__ext5O__cond z ->
  (seq_cond PhysicalCellGroupConfig__ext5O__list (PhysicalCellGroupConfig__ext5O__F1 z)).
intro H. unfold PhysicalCellGroupConfig__ext5O__cond in H. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext5O__F1F2_cond2 (z : PhysicalCellGroupConfig__ext5O__Type)
 : PhysicalCellGroupConfig__ext5O__F2 (PhysicalCellGroupConfig__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext5O__F2F1_cond (y : seq_type PhysicalCellGroupConfig__ext5O__list)
  : seq_cond PhysicalCellGroupConfig__ext5O__list y ->
 (PhysicalCellGroupConfig__ext5O__cond (PhysicalCellGroupConfig__ext5O__F2 y)) /\  PhysicalCellGroupConfig__ext5O__F1 (PhysicalCellGroupConfig__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PhysicalCellGroupConfig__ext5O__cond. simpl in *. auto.
 - simpl. unfold PhysicalCellGroupConfig__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PhysicalCellGroupConfig__ext5O__Format : T_Format PhysicalCellGroupConfig__ext5O__Type PhysicalCellGroupConfig__ext5O__cond :=
        proj2_format  PhysicalCellGroupConfig__ext5O__cond PhysicalCellGroupConfig__ext5O__list__Format
    PhysicalCellGroupConfig__ext5O__F1 PhysicalCellGroupConfig__ext5O__F2 PhysicalCellGroupConfig__ext5O__F1F2_cond  PhysicalCellGroupConfig__ext5O__F1F2_cond2 PhysicalCellGroupConfig__ext5O__F2F1_cond.
Opaque PhysicalCellGroupConfig__ext5O__cond PhysicalCellGroupConfig__ext5O__Format.

Definition PhysicalCellGroupConfig__ext5__check_all_none (b : PhysicalCellGroupConfig__ext5O__Type) : bool :=
match b with 
  | make__PhysicalCellGroupConfig__ext5O__Type None  => false 
  | _ => true 
 end.
Definition PhysicalCellGroupConfig__ext5__Format : T_Format PhysicalCellGroupConfig__ext5__Type PhysicalCellGroupConfig__ext5__cond :=
  restrict_add_format PhysicalCellGroupConfig__ext5__check_all_none PhysicalCellGroupConfig__ext5O__Format.

Opaque PhysicalCellGroupConfig__ext5__cond PhysicalCellGroupConfig__ext5__Format.

Definition PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Format : T_Format PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__nat__Format PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F1 PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F2 PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F1F2 PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__F2F1.

Opaque PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__cond PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Format.


Definition PhysicalCellGroupConfig__ext6O__Format_Type := Eval cbn in seq_format_prod PhysicalCellGroupConfig__ext6O__list.
Definition PhysicalCellGroupConfig__ext6O__Format_list : PhysicalCellGroupConfig__ext6O__Format_Type :=
  (PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17__Format, unit_format).
Definition PhysicalCellGroupConfig__ext6O__list__Format := (*Eval compute in *) seq_format PhysicalCellGroupConfig__ext6O__list PhysicalCellGroupConfig__ext6O__Format_list.
Definition PhysicalCellGroupConfig__ext6O__F1 z :=
  (PhysicalCellGroupConfig__ext6O__intraBandNC_PRACH_simulTx_r17 z, tt).
Definition PhysicalCellGroupConfig__ext6O__F2 (y : seq_type PhysicalCellGroupConfig__ext6O__list) :=
  match y with
  | (i0, _)=>
    make__PhysicalCellGroupConfig__ext6O__Type i0
  end.
Lemma PhysicalCellGroupConfig__ext6O__F1F2_cond (z : PhysicalCellGroupConfig__ext6O__Type)
  : PhysicalCellGroupConfig__ext6O__cond z ->
  (seq_cond PhysicalCellGroupConfig__ext6O__list (PhysicalCellGroupConfig__ext6O__F1 z)).
intro H. unfold PhysicalCellGroupConfig__ext6O__cond in H. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext6O__F1F2_cond2 (z : PhysicalCellGroupConfig__ext6O__Type)
 : PhysicalCellGroupConfig__ext6O__F2 (PhysicalCellGroupConfig__ext6O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PhysicalCellGroupConfig__ext6O__F2F1_cond (y : seq_type PhysicalCellGroupConfig__ext6O__list)
  : seq_cond PhysicalCellGroupConfig__ext6O__list y ->
 (PhysicalCellGroupConfig__ext6O__cond (PhysicalCellGroupConfig__ext6O__F2 y)) /\  PhysicalCellGroupConfig__ext6O__F1 (PhysicalCellGroupConfig__ext6O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PhysicalCellGroupConfig__ext6O__cond. simpl in *. auto.
 - simpl. unfold PhysicalCellGroupConfig__ext6O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PhysicalCellGroupConfig__ext6O__Format : T_Format PhysicalCellGroupConfig__ext6O__Type PhysicalCellGroupConfig__ext6O__cond :=
        proj2_format  PhysicalCellGroupConfig__ext6O__cond PhysicalCellGroupConfig__ext6O__list__Format
    PhysicalCellGroupConfig__ext6O__F1 PhysicalCellGroupConfig__ext6O__F2 PhysicalCellGroupConfig__ext6O__F1F2_cond  PhysicalCellGroupConfig__ext6O__F1F2_cond2 PhysicalCellGroupConfig__ext6O__F2F1_cond.
Opaque PhysicalCellGroupConfig__ext6O__cond PhysicalCellGroupConfig__ext6O__Format.

Definition PhysicalCellGroupConfig__ext6__check_all_none (b : PhysicalCellGroupConfig__ext6O__Type) : bool :=
match b with 
  | make__PhysicalCellGroupConfig__ext6O__Type None  => false 
  | _ => true 
 end.
Definition PhysicalCellGroupConfig__ext6__Format : T_Format PhysicalCellGroupConfig__ext6__Type PhysicalCellGroupConfig__ext6__cond :=
  restrict_add_format PhysicalCellGroupConfig__ext6__check_all_none PhysicalCellGroupConfig__ext6O__Format.

Opaque PhysicalCellGroupConfig__ext6__cond PhysicalCellGroupConfig__ext6__Format.


Definition PhysicalCellGroupConfig__root_Format_Type := Eval cbn in seq_format_prod PhysicalCellGroupConfig__root_list.
Definition PhysicalCellGroupConfig__root_Format_list : PhysicalCellGroupConfig__root_Format_Type :=
  (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH__Format, (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH__Format, (P_Max__Format, (PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook__Format, (RNTI_Value__Format, (RNTI_Value__Format, (RNTI_Value__Format, (RNTI_Value__Format, (PhysicalCellGroupConfig__cs_RNTI__Format, unit_format))))))))).

Definition PhysicalCellGroupConfig__ext_Format_Type := Eval cbn in get_formats PhysicalCellGroupConfig__ext_list.
Definition PhysicalCellGroupConfig__ext_Format_list : PhysicalCellGroupConfig__ext_Format_Type :=
  (PhysicalCellGroupConfig__ext0__Format, (PhysicalCellGroupConfig__ext1__Format, (PhysicalCellGroupConfig__ext2__Format, (PhysicalCellGroupConfig__ext3__Format, (PhysicalCellGroupConfig__ext4__Format, (PhysicalCellGroupConfig__ext5__Format, (PhysicalCellGroupConfig__ext6__Format, unit__Format))))))).

Definition PhysicalCellGroupConfig__list_type : Set := (seq_type PhysicalCellGroupConfig__root_list) * (seq_ext_type PhysicalCellGroupConfig__ext_list).
Definition PhysicalCellGroupConfig__list_cond (z : PhysicalCellGroupConfig__list_type) : Prop :=
        (seq_cond PhysicalCellGroupConfig__root_list (fst z)) /\ (seq_ext_cond PhysicalCellGroupConfig__ext_list (snd z)).
Definition PhysicalCellGroupConfig__list_format : T_Format PhysicalCellGroupConfig__list_type PhysicalCellGroupConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PhysicalCellGroupConfig__root_list PhysicalCellGroupConfig__root_Format_list PhysicalCellGroupConfig__ext_list PhysicalCellGroupConfig__ext_Format_list.

Opaque PhysicalCellGroupConfig__list_format.
Definition PhysicalCellGroupConfig__F1 (z : PhysicalCellGroupConfig__Type) : PhysicalCellGroupConfig__list_type :=
  (((PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUCCH z, (PhysicalCellGroupConfig__harq_ACK_SpatialBundlingPUSCH z, (PhysicalCellGroupConfig__p_NR_FR1 z, (PhysicalCellGroupConfig__pdsch_HARQ_ACK_Codebook z, (PhysicalCellGroupConfig__tpc_SRS_RNTI z, (PhysicalCellGroupConfig__tpc_PUCCH_RNTI z, (PhysicalCellGroupConfig__tpc_PUSCH_RNTI z, (PhysicalCellGroupConfig__sp_CSI_RNTI z, (PhysicalCellGroupConfig__cs_RNTI z, tt)))))))))), (
(PhysicalCellGroupConfig__ext0 z, (PhysicalCellGroupConfig__ext1 z, (PhysicalCellGroupConfig__ext2 z, (PhysicalCellGroupConfig__ext3 z, (PhysicalCellGroupConfig__ext4 z, (PhysicalCellGroupConfig__ext5 z, (PhysicalCellGroupConfig__ext6 z, tt))))))))).
Definition PhysicalCellGroupConfig__F2 (y : PhysicalCellGroupConfig__list_type) : PhysicalCellGroupConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), (i0, (i1, (i2, (i3, (i4, (i5, (i6, _))))))))=>
    make__PhysicalCellGroupConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 i0 i1 i2 i3 i4 i5 i6
  end.
Definition PhysicalCellGroupConfig__helper1 : (forall a : PhysicalCellGroupConfig__Type, PhysicalCellGroupConfig__cond a -> PhysicalCellGroupConfig__list_cond (PhysicalCellGroupConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PhysicalCellGroupConfig__helper2 : (forall a : PhysicalCellGroupConfig__Type, PhysicalCellGroupConfig__F2 (PhysicalCellGroupConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PhysicalCellGroupConfig__helper3 : (forall b : PhysicalCellGroupConfig__list_type, PhysicalCellGroupConfig__list_cond b -> PhysicalCellGroupConfig__cond (PhysicalCellGroupConfig__F2 b) /\ PhysicalCellGroupConfig__F1 (PhysicalCellGroupConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PhysicalCellGroupConfig__cond, PhysicalCellGroupConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PhysicalCellGroupConfig__Format : T_Format PhysicalCellGroupConfig__Type PhysicalCellGroupConfig__cond :=
 proj2_format PhysicalCellGroupConfig__cond PhysicalCellGroupConfig__list_format  PhysicalCellGroupConfig__F1 PhysicalCellGroupConfig__F2 PhysicalCellGroupConfig__helper1 PhysicalCellGroupConfig__helper2 PhysicalCellGroupConfig__helper3.

Opaque PhysicalCellGroupConfig__cond PhysicalCellGroupConfig__Format.

