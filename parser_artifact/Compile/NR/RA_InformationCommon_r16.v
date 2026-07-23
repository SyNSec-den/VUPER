Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Lemma RA_InformationCommon_r16__locationAndBandwidth_r16__helper1 : (0 <= 37949)%Z.  lia. Qed.
Lemma RA_InformationCommon_r16__locationAndBandwidth_r16__helper2 : to_bit_sz (Z.to_nat (37949 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (37949 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__locationAndBandwidth_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__locationAndBandwidth_r16__Type := Z.
Definition RA_InformationCommon_r16__locationAndBandwidth_r16__cond := (fun z => (0 <= z <= 37949)%Z).
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Lemma RA_InformationCommon_r16__msg1_FrequencyStart_r16__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma RA_InformationCommon_r16__msg1_FrequencyStart_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__msg1_FrequencyStart_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__msg1_FrequencyStart_r16__Type := Z.
Definition RA_InformationCommon_r16__msg1_FrequencyStart_r16__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Lemma RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__Type := Z.
Definition RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Inductive RA_InformationCommon_r16__msg1_FDM_r16__Type : Set :=
 | RA_InformationCommon_r16__msg1_FDM_r16__one
 | RA_InformationCommon_r16__msg1_FDM_r16__two
 | RA_InformationCommon_r16__msg1_FDM_r16__four
 | RA_InformationCommon_r16__msg1_FDM_r16__eight
.
Definition RA_InformationCommon_r16__msg1_FDM_r16__cond := (fun (_ : RA_InformationCommon_r16__msg1_FDM_r16__Type) => True).
Lemma RA_InformationCommon_r16__msg1_FDM_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__msg1_FDM_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_InformationCommon_r16__msg1_FDM_r16__nat__helper.

Definition RA_InformationCommon_r16__msg1_FDM_r16__F1 t :=
  match t with
  | RA_InformationCommon_r16__msg1_FDM_r16__one => 0
  | RA_InformationCommon_r16__msg1_FDM_r16__two => 1
  | RA_InformationCommon_r16__msg1_FDM_r16__four => 2
  | RA_InformationCommon_r16__msg1_FDM_r16__eight => 3
  end.
Definition RA_InformationCommon_r16__msg1_FDM_r16__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__msg1_FDM_r16__one
  | 1 => RA_InformationCommon_r16__msg1_FDM_r16__two
  | 2 => RA_InformationCommon_r16__msg1_FDM_r16__four
  | 3 => RA_InformationCommon_r16__msg1_FDM_r16__eight
  | _ => RA_InformationCommon_r16__msg1_FDM_r16__one
  end.
Lemma RA_InformationCommon_r16__msg1_FDM_r16__F1F2 : forall x : RA_InformationCommon_r16__msg1_FDM_r16__Type, (RA_InformationCommon_r16__msg1_FDM_r16__F1 x <= 3) /\ RA_InformationCommon_r16__msg1_FDM_r16__F2 (RA_InformationCommon_r16__msg1_FDM_r16__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__msg1_FDM_r16__F2F1 : forall (y : nat) (H : y <= 3), RA_InformationCommon_r16__msg1_FDM_r16__F1 (RA_InformationCommon_r16__msg1_FDM_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RA_InformationCommon_r16__msg1_FDMCFRA_r16__Type : Set :=
 | RA_InformationCommon_r16__msg1_FDMCFRA_r16__one
 | RA_InformationCommon_r16__msg1_FDMCFRA_r16__two
 | RA_InformationCommon_r16__msg1_FDMCFRA_r16__four
 | RA_InformationCommon_r16__msg1_FDMCFRA_r16__eight
.
Definition RA_InformationCommon_r16__msg1_FDMCFRA_r16__cond := (fun (_ : RA_InformationCommon_r16__msg1_FDMCFRA_r16__Type) => True).
Lemma RA_InformationCommon_r16__msg1_FDMCFRA_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__msg1_FDMCFRA_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_InformationCommon_r16__msg1_FDMCFRA_r16__nat__helper.

Definition RA_InformationCommon_r16__msg1_FDMCFRA_r16__F1 t :=
  match t with
  | RA_InformationCommon_r16__msg1_FDMCFRA_r16__one => 0
  | RA_InformationCommon_r16__msg1_FDMCFRA_r16__two => 1
  | RA_InformationCommon_r16__msg1_FDMCFRA_r16__four => 2
  | RA_InformationCommon_r16__msg1_FDMCFRA_r16__eight => 3
  end.
Definition RA_InformationCommon_r16__msg1_FDMCFRA_r16__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__msg1_FDMCFRA_r16__one
  | 1 => RA_InformationCommon_r16__msg1_FDMCFRA_r16__two
  | 2 => RA_InformationCommon_r16__msg1_FDMCFRA_r16__four
  | 3 => RA_InformationCommon_r16__msg1_FDMCFRA_r16__eight
  | _ => RA_InformationCommon_r16__msg1_FDMCFRA_r16__one
  end.
Lemma RA_InformationCommon_r16__msg1_FDMCFRA_r16__F1F2 : forall x : RA_InformationCommon_r16__msg1_FDMCFRA_r16__Type, (RA_InformationCommon_r16__msg1_FDMCFRA_r16__F1 x <= 3) /\ RA_InformationCommon_r16__msg1_FDMCFRA_r16__F2 (RA_InformationCommon_r16__msg1_FDMCFRA_r16__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__msg1_FDMCFRA_r16__F2F1 : forall (y : nat) (H : y <= 3), RA_InformationCommon_r16__msg1_FDMCFRA_r16__F1 (RA_InformationCommon_r16__msg1_FDMCFRA_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PerRAInfoList_r16.

Opaque PerRAInfoList_r16__cond PerRAInfoList_r16__Format.

Require Import NR.PerRAInfoList_v1660.

Opaque PerRAInfoList_v1660__cond PerRAInfoList_v1660__Format.

Record RA_InformationCommon_r16__ext0O__Type : Set :=
  make__RA_InformationCommon_r16__ext0O__Type {
    RA_InformationCommon_r16__ext0O__perRAInfoList_v1660 : option PerRAInfoList_v1660__Type ;
}.
Definition RA_InformationCommon_r16__ext0O__list := (
 Opt PerRAInfoList_v1660__Type PerRAInfoList_v1660__cond ::
 nil).
Definition RA_InformationCommon_r16__ext0O__cond z := 
  opt_cond PerRAInfoList_v1660__cond (RA_InformationCommon_r16__ext0O__perRAInfoList_v1660 z) /\
  True.

Definition RA_InformationCommon_r16__ext0__Type := RA_InformationCommon_r16__ext0O__Type.
Definition RA_InformationCommon_r16__ext0__cond := RA_InformationCommon_r16__ext0O__cond.

Inductive RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type : Set :=
 | RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz1dot25
 | RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz5
 | RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__spare2
 | RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__spare1
.
Definition RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__cond := (fun (_ : RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type) => True).
Lemma RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__nat__helper.

Definition RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F1 t :=
  match t with
  | RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz1dot25 => 0
  | RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz5 => 1
  | RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__spare2 => 2
  | RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__spare1 => 3
  end.
Definition RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz1dot25
  | 1 => RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz5
  | 2 => RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__spare2
  | 3 => RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__spare1
  | _ => RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__kHz1dot25
  end.
Lemma RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F1F2 : forall x : RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type, (RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F1 x <= 3) /\ RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F2 (RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F2F1 : forall (y : nat) (H : y <= 3), RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F1 (RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F2 y) = y. enum_solve H y. Qed.

Record RA_InformationCommon_r16__ext1O__Type : Set :=
  make__RA_InformationCommon_r16__ext1O__Type {
    RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16 : option RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type ;
}.
Definition RA_InformationCommon_r16__ext1O__list := (
 Opt RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__cond ::
 nil).
Definition RA_InformationCommon_r16__ext1O__cond z := 
  opt_cond RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__cond (RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16 z) /\
  True.

Definition RA_InformationCommon_r16__ext1__Type := RA_InformationCommon_r16__ext1O__Type.
Definition RA_InformationCommon_r16__ext1__cond := RA_InformationCommon_r16__ext1O__cond.

Inductive RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type : Set :=
 | RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz1dot25
 | RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz5
 | RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__spare2
 | RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__spare1
.
Definition RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__cond := (fun (_ : RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type) => True).
Lemma RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__nat__helper.

Definition RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F1 t :=
  match t with
  | RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz1dot25 => 0
  | RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz5 => 1
  | RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__spare2 => 2
  | RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__spare1 => 3
  end.
Definition RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz1dot25
  | 1 => RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz5
  | 2 => RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__spare2
  | 3 => RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__spare1
  | _ => RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__kHz1dot25
  end.
Lemma RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F1F2 : forall x : RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type, (RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F1 x <= 3) /\ RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F2 (RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F2F1 : forall (y : nat) (H : y <= 3), RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F1 (RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F2 y) = y. enum_solve H y. Qed.

Record RA_InformationCommon_r16__ext2O__Type : Set :=
  make__RA_InformationCommon_r16__ext2O__Type {
    RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16 : option RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type ;
}.
Definition RA_InformationCommon_r16__ext2O__list := (
 Opt RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__cond ::
 nil).
Definition RA_InformationCommon_r16__ext2O__cond z := 
  opt_cond RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__cond (RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16 z) /\
  True.

Definition RA_InformationCommon_r16__ext2__Type := RA_InformationCommon_r16__ext2O__Type.
Definition RA_InformationCommon_r16__ext2__cond := RA_InformationCommon_r16__ext2O__cond.

Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__Type := Z.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__Type := Z.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Inductive RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type : Set :=
 | RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__one
 | RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__two
 | RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__four
 | RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__eight
.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__cond := (fun (_ : RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type) => True).
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__nat__helper.

Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F1 t :=
  match t with
  | RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__one => 0
  | RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__two => 1
  | RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__four => 2
  | RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__eight => 3
  end.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__one
  | 1 => RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__two
  | 2 => RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__four
  | 3 => RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__eight
  | _ => RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__one
  end.
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F1F2 : forall x : RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type, (RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F1 x <= 3) /\ RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F2 (RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F2F1 : forall (y : nat) (H : y <= 3), RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F1 (RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F2 y) = y. enum_solve H y. Qed.

Inductive RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type : Set :=
 | RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__one
 | RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__two
 | RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__four
 | RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__eight
.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__cond := (fun (_ : RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type) => True).
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__nat__helper.

Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F1 t :=
  match t with
  | RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__one => 0
  | RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__two => 1
  | RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__four => 2
  | RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__eight => 3
  end.
Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__one
  | 1 => RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__two
  | 2 => RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__four
  | 3 => RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__eight
  | _ => RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__one
  end.
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F1F2 : forall x : RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type, (RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F1 x <= 3) /\ RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F2 (RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F2F1 : forall (y : nat) (H : y <= 3), RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F1 (RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type : Set :=
 | RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz1dot25
 | RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz5
 | RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__spare2
 | RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__spare1
.
Definition RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__cond := (fun (_ : RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type) => True).
Lemma RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__nat__helper.

Definition RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F1 t :=
  match t with
  | RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz1dot25 => 0
  | RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz5 => 1
  | RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__spare2 => 2
  | RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__spare1 => 3
  end.
Definition RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz1dot25
  | 1 => RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz5
  | 2 => RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__spare2
  | 3 => RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__spare1
  | _ => RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__kHz1dot25
  end.
Lemma RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F1F2 : forall x : RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type, (RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F1 x <= 3) /\ RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F2 (RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F2F1 : forall (y : nat) (H : y <= 3), RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F1 (RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F2 y) = y. enum_solve H y. Qed.

Inductive RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type : Set :=
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n1
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n2
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n4
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n6
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n8
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n10
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n20
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n50
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n100
 | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n200
.
Definition RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__cond := (fun (_ : RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type) => True).
Lemma RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__nat__helper.

Definition RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F1 t :=
  match t with
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n1 => 0
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n2 => 1
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n4 => 2
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n6 => 3
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n8 => 4
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n10 => 5
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n20 => 6
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n50 => 7
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n100 => 8
  | RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n200 => 9
  end.
Definition RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n1
  | 1 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n2
  | 2 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n4
  | 3 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n6
  | 4 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n8
  | 5 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n10
  | 6 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n20
  | 7 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n50
  | 8 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n100
  | 9 => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n200
  | _ => RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__n1
  end.
Lemma RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F1F2 : forall x : RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type, (RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F1 x <= 9) /\ RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F2 (RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F2F1 : forall (y : nat) (H : y <= 9), RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F1 (RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F2 y) = y. enum_solve H y. Qed.

Lemma RA_InformationCommon_r16__ext3O__msgA_MCS_r17__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma RA_InformationCommon_r16__ext3O__msgA_MCS_r17__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__ext3O__msgA_MCS_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__ext3O__msgA_MCS_r17__Type := Z.
Definition RA_InformationCommon_r16__ext3O__msgA_MCS_r17__cond := (fun z => (0 <= z <= 15)%Z).
Lemma RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__Type := Z.
Definition RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__cond := (fun z => (1 <= z <= 32)%Z).
Lemma RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__helper1 : (1 <= maxNrofUL_Allocations)%Z. unfold maxNrofUL_Allocations.
 lia. Qed.
Lemma RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__Type := Z.
Definition RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__cond := (fun z => (1 <= z <= maxNrofUL_Allocations)%Z).
Lemma RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__Type := Z.
Definition RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Inductive RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type : Set :=
 | RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__one
 | RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__two
 | RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__four
 | RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__eight
.
Definition RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__cond := (fun (_ : RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type) => True).
Lemma RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__nat__helper.

Definition RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F1 t :=
  match t with
  | RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__one => 0
  | RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__two => 1
  | RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__four => 2
  | RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__eight => 3
  end.
Definition RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__one
  | 1 => RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__two
  | 2 => RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__four
  | 3 => RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__eight
  | _ => RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__one
  end.
Lemma RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F1F2 : forall x : RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type, (RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F1 x <= 3) /\ RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F2 (RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F2F1 : forall (y : nat) (H : y <= 3), RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F1 (RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RSRP_Range.

Opaque RSRP_Range__cond RSRP_Range__Format.

Require Import NR.SIB_Type_r17.

Opaque SIB_Type_r17__cond SIB_Type_r17__Format.

Definition RA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type := list SIB_Type_r17__Type.

Lemma RA_InformationCommon_r16__ext3O__intendedSIBs_r17__helper1 : (0 <= 1 <= maxSIB)%Z. unfold maxSIB.
 lia. Qed.
Lemma RA_InformationCommon_r16__ext3O__intendedSIBs_r17__helper2 : to_bit_sz (Z.to_nat (maxSIB - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSIB - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__ext3O__intendedSIBs_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__ext3O__intendedSIBs_r17__cond (z : RA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxSIB)%Z /\ (list_and SIB_Type_r17__cond z) .

Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Definition RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type := list SSB_Index__Type.

Lemma RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__helper1 : (0 <= 1 <= maxNrofSSBs_r16)%Z. unfold maxNrofSSBs_r16.
 lia. Qed.
Lemma RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofSSBs_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSSBs_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__cond (z : RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSSBs_r16)%Z /\ (list_and SSB_Index__cond z) .

Definition RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Type := bit_string_fixed.
Definition RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 5 /\ bit_string_len_prop (fst z) (snd z)).
Inductive RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type : Set :=
 | RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__true
.
Definition RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__cond := (fun (_ : RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type) => True).
Lemma RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__nat__helper.

Definition RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F1 t :=
  match t with
  | RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__true => 0
  end.
Definition RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F2 n :=
  match n with
  | 0 => RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__true
  | _ => RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__true
  end.
Lemma RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F1F2 : forall x : RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type, (RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F1 x <= 0) /\ RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F2 (RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F1 x) = x. imp_solve. Qed.
Lemma RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F2F1 : forall (y : nat) (H : y <= 0), RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F1 (RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F2 y) = y. enum_solve H y. Qed.

Record RA_InformationCommon_r16__ext3O__Type : Set :=
  make__RA_InformationCommon_r16__ext3O__Type {
    RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17 : option Z ;
    RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17 : option Z ;
    RA_InformationCommon_r16__ext3O__msgA_SubcarrierSpacing_r17 : option SubcarrierSpacing__Type ;
    RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17 : option RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type ;
    RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17 : option RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type ;
    RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17 : option RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type ;
    RA_InformationCommon_r16__ext3O__msgA_TransMax_r17 : option RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type ;
    RA_InformationCommon_r16__ext3O__msgA_MCS_r17 : option Z ;
    RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17 : option Z ;
    RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17 : option Z ;
    RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17 : option Z ;
    RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17 : option RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type ;
    RA_InformationCommon_r16__ext3O__dlPathlossRSRP_r17 : option RSRP_Range__Type ;
    RA_InformationCommon_r16__ext3O__intendedSIBs_r17 : option RA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type ;
    RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17 : option RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type ;
    RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17 : option RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Type ;
    RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17 : option RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type ;
}.
Definition RA_InformationCommon_r16__ext3O__list := (
 Opt Z RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__cond ::
 Opt Z RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__cond ::
 Opt RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__cond ::
 Opt RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__cond ::
 Opt RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__cond ::
 Opt Z RA_InformationCommon_r16__ext3O__msgA_MCS_r17__cond ::
 Opt Z RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__cond ::
 Opt Z RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__cond ::
 Opt Z RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__cond ::
 Opt RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__cond ::
 Opt RSRP_Range__Type RSRP_Range__cond ::
 Opt RA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type RA_InformationCommon_r16__ext3O__intendedSIBs_r17__cond ::
 Opt RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__cond ::
 Opt RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Type RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__cond ::
 Opt RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__cond ::
 nil).
Definition RA_InformationCommon_r16__ext3O__cond z := 
  opt_cond RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__cond (RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__cond (RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17 z) /\
  opt_cond SubcarrierSpacing__cond (RA_InformationCommon_r16__ext3O__msgA_SubcarrierSpacing_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__cond (RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__cond (RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__cond (RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__cond (RA_InformationCommon_r16__ext3O__msgA_TransMax_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__msgA_MCS_r17__cond (RA_InformationCommon_r16__ext3O__msgA_MCS_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__cond (RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__cond (RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__cond (RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__cond (RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17 z) /\
  opt_cond RSRP_Range__cond (RA_InformationCommon_r16__ext3O__dlPathlossRSRP_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__intendedSIBs_r17__cond (RA_InformationCommon_r16__ext3O__intendedSIBs_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__cond (RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__cond (RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17 z) /\
  opt_cond RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__cond (RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17 z) /\
  True.

Definition RA_InformationCommon_r16__ext3__Type := RA_InformationCommon_r16__ext3O__Type.
Definition RA_InformationCommon_r16__ext3__cond := RA_InformationCommon_r16__ext3O__cond.

Record RA_InformationCommon_r16__Type : Set :=
  make__RA_InformationCommon_r16__Type {
    RA_InformationCommon_r16__absoluteFrequencyPointA_r16 : ARFCN_ValueNR__Type ;
    RA_InformationCommon_r16__locationAndBandwidth_r16 : Z ;
    RA_InformationCommon_r16__subcarrierSpacing_r16 : SubcarrierSpacing__Type ;
    RA_InformationCommon_r16__msg1_FrequencyStart_r16 : option Z ;
    RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16 : option Z ;
    RA_InformationCommon_r16__msg1_SubcarrierSpacing_r16 : option SubcarrierSpacing__Type ;
    RA_InformationCommon_r16__msg1_SubcarrierSpacingCFRA_r16 : option SubcarrierSpacing__Type ;
    RA_InformationCommon_r16__msg1_FDM_r16 : option RA_InformationCommon_r16__msg1_FDM_r16__Type ;
    RA_InformationCommon_r16__msg1_FDMCFRA_r16 : option RA_InformationCommon_r16__msg1_FDMCFRA_r16__Type ;
    RA_InformationCommon_r16__perRAInfoList_r16 : PerRAInfoList_r16__Type ;
    RA_InformationCommon_r16__ext0 : option RA_InformationCommon_r16__ext0__Type ;
    RA_InformationCommon_r16__ext1 : option RA_InformationCommon_r16__ext1__Type ;
    RA_InformationCommon_r16__ext2 : option RA_InformationCommon_r16__ext2__Type ;
    RA_InformationCommon_r16__ext3 : option RA_InformationCommon_r16__ext3__Type ;
}.
Definition RA_InformationCommon_r16__root_list : list seq_elem := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor Z RA_InformationCommon_r16__locationAndBandwidth_r16__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt Z RA_InformationCommon_r16__msg1_FrequencyStart_r16__cond ::
 Opt Z RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt RA_InformationCommon_r16__msg1_FDM_r16__Type RA_InformationCommon_r16__msg1_FDM_r16__cond ::
 Opt RA_InformationCommon_r16__msg1_FDMCFRA_r16__Type RA_InformationCommon_r16__msg1_FDMCFRA_r16__cond ::
 Nor PerRAInfoList_r16__Type PerRAInfoList_r16__cond ::
 nil).
Definition RA_InformationCommon_r16__ext_list : list typ := (
  typ_cons RA_InformationCommon_r16__ext0__Type RA_InformationCommon_r16__ext0__cond ::
  typ_cons RA_InformationCommon_r16__ext1__Type RA_InformationCommon_r16__ext1__cond ::
  typ_cons RA_InformationCommon_r16__ext2__Type RA_InformationCommon_r16__ext2__cond ::
  typ_cons RA_InformationCommon_r16__ext3__Type RA_InformationCommon_r16__ext3__cond ::
  nil).
Definition RA_InformationCommon_r16__cond (z : RA_InformationCommon_r16__Type) := 
(  ARFCN_ValueNR__cond (RA_InformationCommon_r16__absoluteFrequencyPointA_r16 z) /\
  RA_InformationCommon_r16__locationAndBandwidth_r16__cond (RA_InformationCommon_r16__locationAndBandwidth_r16 z) /\
  SubcarrierSpacing__cond (RA_InformationCommon_r16__subcarrierSpacing_r16 z) /\
  opt_cond RA_InformationCommon_r16__msg1_FrequencyStart_r16__cond (RA_InformationCommon_r16__msg1_FrequencyStart_r16 z) /\
  opt_cond RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__cond (RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16 z) /\
  opt_cond SubcarrierSpacing__cond (RA_InformationCommon_r16__msg1_SubcarrierSpacing_r16 z) /\
  opt_cond SubcarrierSpacing__cond (RA_InformationCommon_r16__msg1_SubcarrierSpacingCFRA_r16 z) /\
  opt_cond RA_InformationCommon_r16__msg1_FDM_r16__cond (RA_InformationCommon_r16__msg1_FDM_r16 z) /\
  opt_cond RA_InformationCommon_r16__msg1_FDMCFRA_r16__cond (RA_InformationCommon_r16__msg1_FDMCFRA_r16 z) /\
  PerRAInfoList_r16__cond (RA_InformationCommon_r16__perRAInfoList_r16 z) /\
  True) /\ 
(  opt_cond RA_InformationCommon_r16__ext0__cond (RA_InformationCommon_r16__ext0 z) /\
  opt_cond RA_InformationCommon_r16__ext1__cond (RA_InformationCommon_r16__ext1 z) /\
  opt_cond RA_InformationCommon_r16__ext2__cond (RA_InformationCommon_r16__ext2 z) /\
  opt_cond RA_InformationCommon_r16__ext3__cond (RA_InformationCommon_r16__ext3 z) /\
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
Definition RA_InformationCommon_r16__locationAndBandwidth_r16__Format : T_Format Z RA_InformationCommon_r16__locationAndBandwidth_r16__cond :=
 ranged_int_format (0) (37949) RA_InformationCommon_r16__locationAndBandwidth_r16__helper1 RA_InformationCommon_r16__locationAndBandwidth_r16__helper2.

Opaque RA_InformationCommon_r16__locationAndBandwidth_r16__cond RA_InformationCommon_r16__locationAndBandwidth_r16__Format.

Definition RA_InformationCommon_r16__msg1_FrequencyStart_r16__Format : T_Format Z RA_InformationCommon_r16__msg1_FrequencyStart_r16__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) RA_InformationCommon_r16__msg1_FrequencyStart_r16__helper1 RA_InformationCommon_r16__msg1_FrequencyStart_r16__helper2.

Opaque RA_InformationCommon_r16__msg1_FrequencyStart_r16__cond RA_InformationCommon_r16__msg1_FrequencyStart_r16__Format.

Definition RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__Format : T_Format Z RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__helper1 RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__helper2.

Opaque RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__cond RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__Format.

Definition RA_InformationCommon_r16__msg1_FDM_r16__Format : T_Format RA_InformationCommon_r16__msg1_FDM_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__msg1_FDM_r16__nat__Format RA_InformationCommon_r16__msg1_FDM_r16__F1 RA_InformationCommon_r16__msg1_FDM_r16__F2 RA_InformationCommon_r16__msg1_FDM_r16__F1F2 RA_InformationCommon_r16__msg1_FDM_r16__F2F1.

Opaque RA_InformationCommon_r16__msg1_FDM_r16__cond RA_InformationCommon_r16__msg1_FDM_r16__Format.

Definition RA_InformationCommon_r16__msg1_FDMCFRA_r16__Format : T_Format RA_InformationCommon_r16__msg1_FDMCFRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__msg1_FDMCFRA_r16__nat__Format RA_InformationCommon_r16__msg1_FDMCFRA_r16__F1 RA_InformationCommon_r16__msg1_FDMCFRA_r16__F2 RA_InformationCommon_r16__msg1_FDMCFRA_r16__F1F2 RA_InformationCommon_r16__msg1_FDMCFRA_r16__F2F1.

Opaque RA_InformationCommon_r16__msg1_FDMCFRA_r16__cond RA_InformationCommon_r16__msg1_FDMCFRA_r16__Format.


Definition RA_InformationCommon_r16__ext0O__Format_Type := Eval cbn in seq_format_prod RA_InformationCommon_r16__ext0O__list.
Definition RA_InformationCommon_r16__ext0O__Format_list : RA_InformationCommon_r16__ext0O__Format_Type :=
  (PerRAInfoList_v1660__Format, unit_format).
Definition RA_InformationCommon_r16__ext0O__list__Format := (*Eval compute in *) seq_format RA_InformationCommon_r16__ext0O__list RA_InformationCommon_r16__ext0O__Format_list.
Definition RA_InformationCommon_r16__ext0O__F1 z :=
  (RA_InformationCommon_r16__ext0O__perRAInfoList_v1660 z, tt).
Definition RA_InformationCommon_r16__ext0O__F2 (y : seq_type RA_InformationCommon_r16__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__RA_InformationCommon_r16__ext0O__Type i0
  end.
Lemma RA_InformationCommon_r16__ext0O__F1F2_cond (z : RA_InformationCommon_r16__ext0O__Type)
  : RA_InformationCommon_r16__ext0O__cond z ->
  (seq_cond RA_InformationCommon_r16__ext0O__list (RA_InformationCommon_r16__ext0O__F1 z)).
intro H. unfold RA_InformationCommon_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma RA_InformationCommon_r16__ext0O__F1F2_cond2 (z : RA_InformationCommon_r16__ext0O__Type)
 : RA_InformationCommon_r16__ext0O__F2 (RA_InformationCommon_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RA_InformationCommon_r16__ext0O__F2F1_cond (y : seq_type RA_InformationCommon_r16__ext0O__list)
  : seq_cond RA_InformationCommon_r16__ext0O__list y ->
 (RA_InformationCommon_r16__ext0O__cond (RA_InformationCommon_r16__ext0O__F2 y)) /\  RA_InformationCommon_r16__ext0O__F1 (RA_InformationCommon_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RA_InformationCommon_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold RA_InformationCommon_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RA_InformationCommon_r16__ext0O__Format : T_Format RA_InformationCommon_r16__ext0O__Type RA_InformationCommon_r16__ext0O__cond :=
        proj2_format  RA_InformationCommon_r16__ext0O__cond RA_InformationCommon_r16__ext0O__list__Format
    RA_InformationCommon_r16__ext0O__F1 RA_InformationCommon_r16__ext0O__F2 RA_InformationCommon_r16__ext0O__F1F2_cond  RA_InformationCommon_r16__ext0O__F1F2_cond2 RA_InformationCommon_r16__ext0O__F2F1_cond.
Opaque RA_InformationCommon_r16__ext0O__cond RA_InformationCommon_r16__ext0O__Format.

Definition RA_InformationCommon_r16__ext0__check_all_none (b : RA_InformationCommon_r16__ext0O__Type) : bool :=
match b with 
  | make__RA_InformationCommon_r16__ext0O__Type None  => false 
  | _ => true 
 end.
Definition RA_InformationCommon_r16__ext0__Format : T_Format RA_InformationCommon_r16__ext0__Type RA_InformationCommon_r16__ext0__cond :=
  restrict_add_format RA_InformationCommon_r16__ext0__check_all_none RA_InformationCommon_r16__ext0O__Format.

Opaque RA_InformationCommon_r16__ext0__cond RA_InformationCommon_r16__ext0__Format.

Definition RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Format : T_Format RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__nat__Format RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F1 RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F2 RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F1F2 RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__F2F1.

Opaque RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__cond RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Format.


Definition RA_InformationCommon_r16__ext1O__Format_Type := Eval cbn in seq_format_prod RA_InformationCommon_r16__ext1O__list.
Definition RA_InformationCommon_r16__ext1O__Format_list : RA_InformationCommon_r16__ext1O__Format_Type :=
  (RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16__Format, unit_format).
Definition RA_InformationCommon_r16__ext1O__list__Format := (*Eval compute in *) seq_format RA_InformationCommon_r16__ext1O__list RA_InformationCommon_r16__ext1O__Format_list.
Definition RA_InformationCommon_r16__ext1O__F1 z :=
  (RA_InformationCommon_r16__ext1O__msg1_SCS_From_prach_ConfigurationIndex_r16 z, tt).
Definition RA_InformationCommon_r16__ext1O__F2 (y : seq_type RA_InformationCommon_r16__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__RA_InformationCommon_r16__ext1O__Type i0
  end.
Lemma RA_InformationCommon_r16__ext1O__F1F2_cond (z : RA_InformationCommon_r16__ext1O__Type)
  : RA_InformationCommon_r16__ext1O__cond z ->
  (seq_cond RA_InformationCommon_r16__ext1O__list (RA_InformationCommon_r16__ext1O__F1 z)).
intro H. unfold RA_InformationCommon_r16__ext1O__cond in H. simpl. auto. Qed.
Lemma RA_InformationCommon_r16__ext1O__F1F2_cond2 (z : RA_InformationCommon_r16__ext1O__Type)
 : RA_InformationCommon_r16__ext1O__F2 (RA_InformationCommon_r16__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RA_InformationCommon_r16__ext1O__F2F1_cond (y : seq_type RA_InformationCommon_r16__ext1O__list)
  : seq_cond RA_InformationCommon_r16__ext1O__list y ->
 (RA_InformationCommon_r16__ext1O__cond (RA_InformationCommon_r16__ext1O__F2 y)) /\  RA_InformationCommon_r16__ext1O__F1 (RA_InformationCommon_r16__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RA_InformationCommon_r16__ext1O__cond. simpl in *. auto.
 - simpl. unfold RA_InformationCommon_r16__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RA_InformationCommon_r16__ext1O__Format : T_Format RA_InformationCommon_r16__ext1O__Type RA_InformationCommon_r16__ext1O__cond :=
        proj2_format  RA_InformationCommon_r16__ext1O__cond RA_InformationCommon_r16__ext1O__list__Format
    RA_InformationCommon_r16__ext1O__F1 RA_InformationCommon_r16__ext1O__F2 RA_InformationCommon_r16__ext1O__F1F2_cond  RA_InformationCommon_r16__ext1O__F1F2_cond2 RA_InformationCommon_r16__ext1O__F2F1_cond.
Opaque RA_InformationCommon_r16__ext1O__cond RA_InformationCommon_r16__ext1O__Format.

Definition RA_InformationCommon_r16__ext1__check_all_none (b : RA_InformationCommon_r16__ext1O__Type) : bool :=
match b with 
  | make__RA_InformationCommon_r16__ext1O__Type None  => false 
  | _ => true 
 end.
Definition RA_InformationCommon_r16__ext1__Format : T_Format RA_InformationCommon_r16__ext1__Type RA_InformationCommon_r16__ext1__cond :=
  restrict_add_format RA_InformationCommon_r16__ext1__check_all_none RA_InformationCommon_r16__ext1O__Format.

Opaque RA_InformationCommon_r16__ext1__cond RA_InformationCommon_r16__ext1__Format.

Definition RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Format : T_Format RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__nat__Format RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F1 RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F2 RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F1F2 RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__F2F1.

Opaque RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__cond RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Format.


Definition RA_InformationCommon_r16__ext2O__Format_Type := Eval cbn in seq_format_prod RA_InformationCommon_r16__ext2O__list.
Definition RA_InformationCommon_r16__ext2O__Format_list : RA_InformationCommon_r16__ext2O__Format_Type :=
  (RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16__Format, unit_format).
Definition RA_InformationCommon_r16__ext2O__list__Format := (*Eval compute in *) seq_format RA_InformationCommon_r16__ext2O__list RA_InformationCommon_r16__ext2O__Format_list.
Definition RA_InformationCommon_r16__ext2O__F1 z :=
  (RA_InformationCommon_r16__ext2O__msg1_SCS_From_prach_ConfigurationIndexCFRA_r16 z, tt).
Definition RA_InformationCommon_r16__ext2O__F2 (y : seq_type RA_InformationCommon_r16__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__RA_InformationCommon_r16__ext2O__Type i0
  end.
Lemma RA_InformationCommon_r16__ext2O__F1F2_cond (z : RA_InformationCommon_r16__ext2O__Type)
  : RA_InformationCommon_r16__ext2O__cond z ->
  (seq_cond RA_InformationCommon_r16__ext2O__list (RA_InformationCommon_r16__ext2O__F1 z)).
intro H. unfold RA_InformationCommon_r16__ext2O__cond in H. simpl. auto. Qed.
Lemma RA_InformationCommon_r16__ext2O__F1F2_cond2 (z : RA_InformationCommon_r16__ext2O__Type)
 : RA_InformationCommon_r16__ext2O__F2 (RA_InformationCommon_r16__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RA_InformationCommon_r16__ext2O__F2F1_cond (y : seq_type RA_InformationCommon_r16__ext2O__list)
  : seq_cond RA_InformationCommon_r16__ext2O__list y ->
 (RA_InformationCommon_r16__ext2O__cond (RA_InformationCommon_r16__ext2O__F2 y)) /\  RA_InformationCommon_r16__ext2O__F1 (RA_InformationCommon_r16__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RA_InformationCommon_r16__ext2O__cond. simpl in *. auto.
 - simpl. unfold RA_InformationCommon_r16__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RA_InformationCommon_r16__ext2O__Format : T_Format RA_InformationCommon_r16__ext2O__Type RA_InformationCommon_r16__ext2O__cond :=
        proj2_format  RA_InformationCommon_r16__ext2O__cond RA_InformationCommon_r16__ext2O__list__Format
    RA_InformationCommon_r16__ext2O__F1 RA_InformationCommon_r16__ext2O__F2 RA_InformationCommon_r16__ext2O__F1F2_cond  RA_InformationCommon_r16__ext2O__F1F2_cond2 RA_InformationCommon_r16__ext2O__F2F1_cond.
Opaque RA_InformationCommon_r16__ext2O__cond RA_InformationCommon_r16__ext2O__Format.

Definition RA_InformationCommon_r16__ext2__check_all_none (b : RA_InformationCommon_r16__ext2O__Type) : bool :=
match b with 
  | make__RA_InformationCommon_r16__ext2O__Type None  => false 
  | _ => true 
 end.
Definition RA_InformationCommon_r16__ext2__Format : T_Format RA_InformationCommon_r16__ext2__Type RA_InformationCommon_r16__ext2__cond :=
  restrict_add_format RA_InformationCommon_r16__ext2__check_all_none RA_InformationCommon_r16__ext2O__Format.

Opaque RA_InformationCommon_r16__ext2__cond RA_InformationCommon_r16__ext2__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__Format : T_Format Z RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__helper1 RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__helper2.

Opaque RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__cond RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__Format : T_Format Z RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__helper1 RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__helper2.

Opaque RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__cond RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Format : T_Format RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__nat__Format RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F1 RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F2 RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F1F2 RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__F2F1.

Opaque RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__cond RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Format : T_Format RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__nat__Format RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F1 RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F2 RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F1F2 RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__F2F1.

Opaque RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__cond RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Format : T_Format RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__nat__Format RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F1 RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F2 RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F1F2 RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__F2F1.

Opaque RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__cond RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Format : T_Format RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__nat__Format RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F1 RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F2 RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F1F2 RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__F2F1.

Opaque RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__cond RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_MCS_r17__Format : T_Format Z RA_InformationCommon_r16__ext3O__msgA_MCS_r17__cond :=
 ranged_int_format (0) (15) RA_InformationCommon_r16__ext3O__msgA_MCS_r17__helper1 RA_InformationCommon_r16__ext3O__msgA_MCS_r17__helper2.

Opaque RA_InformationCommon_r16__ext3O__msgA_MCS_r17__cond RA_InformationCommon_r16__ext3O__msgA_MCS_r17__Format.

Definition RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__Format : T_Format Z RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__cond :=
 ranged_int_format (1) (32) RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__helper1 RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__helper2.

Opaque RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__cond RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__Format : T_Format Z RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__cond :=
 ranged_int_format (1) (maxNrofUL_Allocations) RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__helper1 RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__helper2.

Opaque RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__cond RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__Format.

Definition RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__Format : T_Format Z RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__helper1 RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__helper2.

Opaque RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__cond RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__Format.

Definition RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Format : T_Format RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__nat__Format RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F1 RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F2 RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F1F2 RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__F2F1.

Opaque RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__cond RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Format.

Definition RA_InformationCommon_r16__ext3O__intendedSIBs_r17__Format : T_Format RA_InformationCommon_r16__ext3O__intendedSIBs_r17__Type RA_InformationCommon_r16__ext3O__intendedSIBs_r17__cond := seq_of_format SIB_Type_r17__Format 1 maxSIB RA_InformationCommon_r16__ext3O__intendedSIBs_r17__helper1 RA_InformationCommon_r16__ext3O__intendedSIBs_r17__helper2.

Opaque RA_InformationCommon_r16__ext3O__intendedSIBs_r17__cond RA_InformationCommon_r16__ext3O__intendedSIBs_r17__Format.

Definition RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Format : T_Format RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Type RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__cond := seq_of_format SSB_Index__Format 1 maxNrofSSBs_r16 RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__helper1 RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__helper2.

Opaque RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__cond RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Format.

Definition RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Format : T_Format RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Type RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__cond := (* Eval compute in *) bit_string_fixed_format 5.
Opaque RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__cond RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Format.

Definition RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Format : T_Format RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__nat__Format RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F1 RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F2 RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F1F2 RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__F2F1.

Opaque RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__cond RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Format.


Definition RA_InformationCommon_r16__ext3O__Format_Type := Eval cbn in seq_format_prod RA_InformationCommon_r16__ext3O__list.
Definition RA_InformationCommon_r16__ext3O__Format_list : RA_InformationCommon_r16__ext3O__Format_Type :=
  (RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17__Format, (RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17__Format, (SubcarrierSpacing__Format, (RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17__Format, (RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17__Format, (RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17__Format, (RA_InformationCommon_r16__ext3O__msgA_TransMax_r17__Format, (RA_InformationCommon_r16__ext3O__msgA_MCS_r17__Format, (RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17__Format, (RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17__Format, (RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17__Format, (RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17__Format, (RSRP_Range__Format, (RA_InformationCommon_r16__ext3O__intendedSIBs_r17__Format, (RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17__Format, (RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17__Format, (RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17__Format, unit_format))))))))))))))))).
Definition RA_InformationCommon_r16__ext3O__list__Format := (*Eval compute in *) seq_format RA_InformationCommon_r16__ext3O__list RA_InformationCommon_r16__ext3O__Format_list.
Definition RA_InformationCommon_r16__ext3O__F1 z :=
  (RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStart_r17 z, (RA_InformationCommon_r16__ext3O__msgA_RO_FrequencyStartCFRA_r17 z, (RA_InformationCommon_r16__ext3O__msgA_SubcarrierSpacing_r17 z, (RA_InformationCommon_r16__ext3O__msgA_RO_FDM_r17 z, (RA_InformationCommon_r16__ext3O__msgA_RO_FDMCFRA_r17 z, (RA_InformationCommon_r16__ext3O__msgA_SCS_From_prach_ConfigurationIndex_r17 z, (RA_InformationCommon_r16__ext3O__msgA_TransMax_r17 z, (RA_InformationCommon_r16__ext3O__msgA_MCS_r17 z, (RA_InformationCommon_r16__ext3O__nrofPRBs_PerMsgA_PO_r17 z, (RA_InformationCommon_r16__ext3O__msgA_PUSCH_TimeDomainAllocation_r17 z, (RA_InformationCommon_r16__ext3O__frequencyStartMsgA_PUSCH_r17 z, (RA_InformationCommon_r16__ext3O__nrofMsgA_PO_FDM_r17 z, (RA_InformationCommon_r16__ext3O__dlPathlossRSRP_r17 z, (RA_InformationCommon_r16__ext3O__intendedSIBs_r17 z, (RA_InformationCommon_r16__ext3O__ssbsForSI_Acquisition_r17 z, (RA_InformationCommon_r16__ext3O__msgA_PUSCH_PayloadSize_r17 z, (RA_InformationCommon_r16__ext3O__onDemandSISuccess_r17 z, tt))))))))))))))))).
Definition RA_InformationCommon_r16__ext3O__F2 (y : seq_type RA_InformationCommon_r16__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, _)))))))))))))))))=>
    make__RA_InformationCommon_r16__ext3O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16
  end.
Lemma RA_InformationCommon_r16__ext3O__F1F2_cond (z : RA_InformationCommon_r16__ext3O__Type)
  : RA_InformationCommon_r16__ext3O__cond z ->
  (seq_cond RA_InformationCommon_r16__ext3O__list (RA_InformationCommon_r16__ext3O__F1 z)).
intro H. unfold RA_InformationCommon_r16__ext3O__cond in H. simpl. auto. Qed.
Lemma RA_InformationCommon_r16__ext3O__F1F2_cond2 (z : RA_InformationCommon_r16__ext3O__Type)
 : RA_InformationCommon_r16__ext3O__F2 (RA_InformationCommon_r16__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RA_InformationCommon_r16__ext3O__F2F1_cond (y : seq_type RA_InformationCommon_r16__ext3O__list)
  : seq_cond RA_InformationCommon_r16__ext3O__list y ->
 (RA_InformationCommon_r16__ext3O__cond (RA_InformationCommon_r16__ext3O__F2 y)) /\  RA_InformationCommon_r16__ext3O__F1 (RA_InformationCommon_r16__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RA_InformationCommon_r16__ext3O__cond. simpl in *. auto.
 - simpl. unfold RA_InformationCommon_r16__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RA_InformationCommon_r16__ext3O__Format : T_Format RA_InformationCommon_r16__ext3O__Type RA_InformationCommon_r16__ext3O__cond :=
        proj2_format  RA_InformationCommon_r16__ext3O__cond RA_InformationCommon_r16__ext3O__list__Format
    RA_InformationCommon_r16__ext3O__F1 RA_InformationCommon_r16__ext3O__F2 RA_InformationCommon_r16__ext3O__F1F2_cond  RA_InformationCommon_r16__ext3O__F1F2_cond2 RA_InformationCommon_r16__ext3O__F2F1_cond.
Opaque RA_InformationCommon_r16__ext3O__cond RA_InformationCommon_r16__ext3O__Format.

Definition RA_InformationCommon_r16__ext3__check_all_none (b : RA_InformationCommon_r16__ext3O__Type) : bool :=
match b with 
  | make__RA_InformationCommon_r16__ext3O__Type None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition RA_InformationCommon_r16__ext3__Format : T_Format RA_InformationCommon_r16__ext3__Type RA_InformationCommon_r16__ext3__cond :=
  restrict_add_format RA_InformationCommon_r16__ext3__check_all_none RA_InformationCommon_r16__ext3O__Format.

Opaque RA_InformationCommon_r16__ext3__cond RA_InformationCommon_r16__ext3__Format.


Definition RA_InformationCommon_r16__root_Format_Type := Eval cbn in seq_format_prod RA_InformationCommon_r16__root_list.
Definition RA_InformationCommon_r16__root_Format_list : RA_InformationCommon_r16__root_Format_Type :=
  (ARFCN_ValueNR__Format, (RA_InformationCommon_r16__locationAndBandwidth_r16__Format, (SubcarrierSpacing__Format, (RA_InformationCommon_r16__msg1_FrequencyStart_r16__Format, (RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16__Format, (SubcarrierSpacing__Format, (SubcarrierSpacing__Format, (RA_InformationCommon_r16__msg1_FDM_r16__Format, (RA_InformationCommon_r16__msg1_FDMCFRA_r16__Format, (PerRAInfoList_r16__Format, unit_format)))))))))).

Definition RA_InformationCommon_r16__ext_Format_Type := Eval cbn in get_formats RA_InformationCommon_r16__ext_list.
Definition RA_InformationCommon_r16__ext_Format_list : RA_InformationCommon_r16__ext_Format_Type :=
  (RA_InformationCommon_r16__ext0__Format, (RA_InformationCommon_r16__ext1__Format, (RA_InformationCommon_r16__ext2__Format, (RA_InformationCommon_r16__ext3__Format, unit__Format)))).

Definition RA_InformationCommon_r16__list_type : Set := (seq_type RA_InformationCommon_r16__root_list) * (seq_ext_type RA_InformationCommon_r16__ext_list).
Definition RA_InformationCommon_r16__list_cond (z : RA_InformationCommon_r16__list_type) : Prop :=
        (seq_cond RA_InformationCommon_r16__root_list (fst z)) /\ (seq_ext_cond RA_InformationCommon_r16__ext_list (snd z)).
Definition RA_InformationCommon_r16__list_format : T_Format RA_InformationCommon_r16__list_type RA_InformationCommon_r16__list_cond :=
 (* Eval compute in *) seq_ext_format RA_InformationCommon_r16__root_list RA_InformationCommon_r16__root_Format_list RA_InformationCommon_r16__ext_list RA_InformationCommon_r16__ext_Format_list.

Opaque RA_InformationCommon_r16__list_format.
Definition RA_InformationCommon_r16__F1 (z : RA_InformationCommon_r16__Type) : RA_InformationCommon_r16__list_type :=
  (((RA_InformationCommon_r16__absoluteFrequencyPointA_r16 z, (RA_InformationCommon_r16__locationAndBandwidth_r16 z, (RA_InformationCommon_r16__subcarrierSpacing_r16 z, (RA_InformationCommon_r16__msg1_FrequencyStart_r16 z, (RA_InformationCommon_r16__msg1_FrequencyStartCFRA_r16 z, (RA_InformationCommon_r16__msg1_SubcarrierSpacing_r16 z, (RA_InformationCommon_r16__msg1_SubcarrierSpacingCFRA_r16 z, (RA_InformationCommon_r16__msg1_FDM_r16 z, (RA_InformationCommon_r16__msg1_FDMCFRA_r16 z, (RA_InformationCommon_r16__perRAInfoList_r16 z, tt))))))))))), (
(RA_InformationCommon_r16__ext0 z, (RA_InformationCommon_r16__ext1 z, (RA_InformationCommon_r16__ext2 z, (RA_InformationCommon_r16__ext3 z, tt)))))).
Definition RA_InformationCommon_r16__F2 (y : RA_InformationCommon_r16__list_type) : RA_InformationCommon_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, _)))))))))), (i0, (i1, (i2, (i3, _)))))=>
    make__RA_InformationCommon_r16__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i0 i1 i2 i3
  end.
Definition RA_InformationCommon_r16__helper1 : (forall a : RA_InformationCommon_r16__Type, RA_InformationCommon_r16__cond a -> RA_InformationCommon_r16__list_cond (RA_InformationCommon_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RA_InformationCommon_r16__helper2 : (forall a : RA_InformationCommon_r16__Type, RA_InformationCommon_r16__F2 (RA_InformationCommon_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RA_InformationCommon_r16__helper3 : (forall b : RA_InformationCommon_r16__list_type, RA_InformationCommon_r16__list_cond b -> RA_InformationCommon_r16__cond (RA_InformationCommon_r16__F2 b) /\ RA_InformationCommon_r16__F1 (RA_InformationCommon_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RA_InformationCommon_r16__cond, RA_InformationCommon_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RA_InformationCommon_r16__Format : T_Format RA_InformationCommon_r16__Type RA_InformationCommon_r16__cond :=
 proj2_format RA_InformationCommon_r16__cond RA_InformationCommon_r16__list_format  RA_InformationCommon_r16__F1 RA_InformationCommon_r16__F2 RA_InformationCommon_r16__helper1 RA_InformationCommon_r16__helper2 RA_InformationCommon_r16__helper3.

Opaque RA_InformationCommon_r16__cond RA_InformationCommon_r16__Format.

