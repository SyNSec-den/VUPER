Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.CSI_ReportConfigId.

Opaque CSI_ReportConfigId__cond CSI_ReportConfigId__Format.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.CSI_ResourceConfigId.

Opaque CSI_ResourceConfigId__cond CSI_ResourceConfigId__Format.

Require Import NR.CSI_ResourceConfigId.

Opaque CSI_ResourceConfigId__cond CSI_ResourceConfigId__Format.

Require Import NR.CSI_ResourceConfigId.

Opaque CSI_ResourceConfigId__cond CSI_ResourceConfigId__Format.

Require Import NR.CSI_ReportPeriodicityAndOffset.

Opaque CSI_ReportPeriodicityAndOffset__cond CSI_ReportPeriodicityAndOffset__Format.

Require Import NR.PUCCH_CSI_Resource.

Opaque PUCCH_CSI_Resource__cond PUCCH_CSI_Resource__Format.

Definition CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__Type := list PUCCH_CSI_Resource__Type.

Lemma CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__helper1 : (0 <= 1 <= maxNrofBWPs)%Z. unfold maxNrofBWPs.
 lia. Qed.
Lemma CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxNrofBWPs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofBWPs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__cond (z : CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofBWPs)%Z /\ (list_and PUCCH_CSI_Resource__cond z) .

Record CSI_ReportConfig__reportConfigType__periodic__Type : Set :=
  make__CSI_ReportConfig__reportConfigType__periodic__Type {
    CSI_ReportConfig__reportConfigType__periodic__reportSlotConfig : CSI_ReportPeriodicityAndOffset__Type ;
    CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList : CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__Type ;
}.
Definition CSI_ReportConfig__reportConfigType__periodic__list := (
 Nor CSI_ReportPeriodicityAndOffset__Type CSI_ReportPeriodicityAndOffset__cond ::
 Nor CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__Type CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__cond ::
 nil).
Definition CSI_ReportConfig__reportConfigType__periodic__cond z := 
  CSI_ReportPeriodicityAndOffset__cond (CSI_ReportConfig__reportConfigType__periodic__reportSlotConfig z) /\
  CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__cond (CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList z) /\
  True.

Require Import NR.CSI_ReportPeriodicityAndOffset.

Opaque CSI_ReportPeriodicityAndOffset__cond CSI_ReportPeriodicityAndOffset__Format.

Require Import NR.PUCCH_CSI_Resource.

Opaque PUCCH_CSI_Resource__cond PUCCH_CSI_Resource__Format.

Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__Type := list PUCCH_CSI_Resource__Type.

Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__helper1 : (0 <= 1 <= maxNrofBWPs)%Z. unfold maxNrofBWPs.
 lia. Qed.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__helper2 : to_bit_sz (Z.to_nat (maxNrofBWPs - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofBWPs - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__cond (z : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofBWPs)%Z /\ (list_and PUCCH_CSI_Resource__cond z) .

Record CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type : Set :=
  make__CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type {
    CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__reportSlotConfig : CSI_ReportPeriodicityAndOffset__Type ;
    CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__Type ;
}.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list := (
 Nor CSI_ReportPeriodicityAndOffset__Type CSI_ReportPeriodicityAndOffset__cond ::
 Nor CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__cond ::
 nil).
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond z := 
  CSI_ReportPeriodicityAndOffset__cond (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__reportSlotConfig z) /\
  CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__cond (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList z) /\
  True.

Inductive CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Type : Set :=
 | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl5
 | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl10
 | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl20
 | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl40
 | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl80
 | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl160
 | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl320
.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__cond := (fun (_ : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Type) => True).
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__nat__helper.

Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F1 t :=
  match t with
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl5 => 0
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl10 => 1
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl20 => 2
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl40 => 3
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl80 => 4
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl160 => 5
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl320 => 6
  end.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl5
  | 1 => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl10
  | 2 => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl20
  | 3 => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl40
  | 4 => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl80
  | 5 => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl160
  | 6 => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl320
  | _ => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__sl5
  end.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F1F2 : forall x : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Type, (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F1 x <= 6) /\ CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F2 (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F2F1 : forall (y : nat) (H : y <= 6), CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F1 (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F2 y) = y. enum_solve H y. Qed.

Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__Type := Z.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__cond := (fun z => (0 <= z <= 32)%Z).
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__Type := list Z.

Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__helper1 : (0 <= 1 <= maxNrofUL_Allocations)%Z. unfold maxNrofUL_Allocations.
 lia. Qed.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__cond (z : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations)%Z /\ (list_and CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__cond z) .

Require Import NR.P0_PUSCH_AlphaSetId.

Opaque P0_PUSCH_AlphaSetId__cond P0_PUSCH_AlphaSetId__Format.

Record CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type : Set :=
  make__CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type {
    CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Type ;
    CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__Type ;
    CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__p0alpha : P0_PUSCH_AlphaSetId__Type ;
}.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list := (
 Nor CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__cond ::
 Nor CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__cond ::
 Nor P0_PUSCH_AlphaSetId__Type P0_PUSCH_AlphaSetId__cond ::
 nil).
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond z := 
  CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__cond (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig z) /\
  CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__cond (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList z) /\
  P0_PUSCH_AlphaSetId__cond (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__p0alpha z) /\
  True.

Lemma CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__Type := Z.
Definition CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__cond := (fun z => (0 <= z <= 32)%Z).
Definition CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__Type := list Z.

Lemma CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__helper1 : (0 <= 1 <= maxNrofUL_Allocations)%Z. unfold maxNrofUL_Allocations.
 lia. Qed.
Lemma CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__cond (z : CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations)%Z /\ (list_and CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__cond z) .

Record CSI_ReportConfig__reportConfigType__aperiodic__Type : Set :=
  make__CSI_ReportConfig__reportConfigType__aperiodic__Type {
    CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList : CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__Type ;
}.
Definition CSI_ReportConfig__reportConfigType__aperiodic__list := (
 Nor CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__Type CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__cond ::
 nil).
Definition CSI_ReportConfig__reportConfigType__aperiodic__cond z := 
  CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__cond (CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList z) /\
  True.


Inductive CSI_ReportConfig__reportConfigType__Type : Set :=
  | CSI_ReportConfig__reportConfigType__periodic : CSI_ReportConfig__reportConfigType__periodic__Type -> CSI_ReportConfig__reportConfigType__Type
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type -> CSI_ReportConfig__reportConfigType__Type
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type -> CSI_ReportConfig__reportConfigType__Type
  | CSI_ReportConfig__reportConfigType__aperiodic : CSI_ReportConfig__reportConfigType__aperiodic__Type -> CSI_ReportConfig__reportConfigType__Type
.
Definition CSI_ReportConfig__reportConfigType__list : list typ := (
typ_cons CSI_ReportConfig__reportConfigType__periodic__Type CSI_ReportConfig__reportConfigType__periodic__cond ::
typ_cons CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond ::
typ_cons CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond ::
typ_cons CSI_ReportConfig__reportConfigType__aperiodic__Type CSI_ReportConfig__reportConfigType__aperiodic__cond ::
 nil).
Definition CSI_ReportConfig__reportConfigType__cond (c : CSI_ReportConfig__reportConfigType__Type) := 
  match c with
  | CSI_ReportConfig__reportConfigType__periodic t => CSI_ReportConfig__reportConfigType__periodic__cond t 
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH t => CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond t 
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH t => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond t 
  | CSI_ReportConfig__reportConfigType__aperiodic t => CSI_ReportConfig__reportConfigType__aperiodic__cond t 
  end.

Lemma CSI_ReportConfig__reportConfigType__len_helper1 : to_bit_sz (length CSI_ReportConfig__reportConfigType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_ReportConfig__reportConfigType__len_helper2 : 2 <= length2 CSI_ReportConfig__reportConfigType__list.
 simpl. lia. Qed.
Inductive CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Type : Set :=
 | CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__n2
 | CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__n4
.
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__cond := (fun (_ : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Type) => True).
Lemma CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__nat__helper.

Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F1 t :=
  match t with
  | CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__n2 => 0
  | CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__n4 => 1
  end.
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__n2
  | 1 => CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__n4
  | _ => CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__n2
  end.
Lemma CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F1F2 : forall x : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Type, (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F1 x <= 1) /\ CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F2 (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F2F1 : forall (y : nat) (H : y <= 1), CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F1 (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F2 y) = y. enum_solve H y. Qed.

Record CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type : Set :=
  make__CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type {
    CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI : option CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Type ;
}.
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list := (
 Opt CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Type CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__cond ::
 nil).
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond z := 
  opt_cond CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__cond (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI z) /\
  True.


Inductive CSI_ReportConfig__reportQuantity__Type : Set :=
  | CSI_ReportConfig__reportQuantity__none : unit -> CSI_ReportConfig__reportQuantity__Type
  | CSI_ReportConfig__reportQuantity__cri_RI_PMI_CQI : unit -> CSI_ReportConfig__reportQuantity__Type
  | CSI_ReportConfig__reportQuantity__cri_RI_i1 : unit -> CSI_ReportConfig__reportQuantity__Type
  | CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type -> CSI_ReportConfig__reportQuantity__Type
  | CSI_ReportConfig__reportQuantity__cri_RI_CQI : unit -> CSI_ReportConfig__reportQuantity__Type
  | CSI_ReportConfig__reportQuantity__cri_RSRP : unit -> CSI_ReportConfig__reportQuantity__Type
  | CSI_ReportConfig__reportQuantity__ssb_Index_RSRP : unit -> CSI_ReportConfig__reportQuantity__Type
  | CSI_ReportConfig__reportQuantity__cri_RI_LI_PMI_CQI : unit -> CSI_ReportConfig__reportQuantity__Type
.
Definition CSI_ReportConfig__reportQuantity__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition CSI_ReportConfig__reportQuantity__cond (c : CSI_ReportConfig__reportQuantity__Type) := 
  match c with
  | CSI_ReportConfig__reportQuantity__none t => (fun _ => True) t 
  | CSI_ReportConfig__reportQuantity__cri_RI_PMI_CQI t => (fun _ => True) t 
  | CSI_ReportConfig__reportQuantity__cri_RI_i1 t => (fun _ => True) t 
  | CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI t => CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond t 
  | CSI_ReportConfig__reportQuantity__cri_RI_CQI t => (fun _ => True) t 
  | CSI_ReportConfig__reportQuantity__cri_RSRP t => (fun _ => True) t 
  | CSI_ReportConfig__reportQuantity__ssb_Index_RSRP t => (fun _ => True) t 
  | CSI_ReportConfig__reportQuantity__cri_RI_LI_PMI_CQI t => (fun _ => True) t 
  end.

Lemma CSI_ReportConfig__reportQuantity__len_helper1 : to_bit_sz (length CSI_ReportConfig__reportQuantity__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_ReportConfig__reportQuantity__len_helper2 : 2 <= length2 CSI_ReportConfig__reportQuantity__list.
 simpl. lia. Qed.
Inductive CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Type : Set :=
 | CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__widebandCQI
 | CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__subbandCQI
.
Definition CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__cond := (fun (_ : CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Type) => True).
Lemma CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__nat__helper.

Definition CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F1 t :=
  match t with
  | CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__widebandCQI => 0
  | CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__subbandCQI => 1
  end.
Definition CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__widebandCQI
  | 1 => CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__subbandCQI
  | _ => CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__widebandCQI
  end.
Lemma CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F1F2 : forall x : CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Type, (CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F1 x <= 1) /\ CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F2 (CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F2F1 : forall (y : nat) (H : y <= 1), CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F1 (CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F2 y) = y. enum_solve H y. Qed.

Inductive CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Type : Set :=
 | CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__widebandPMI
 | CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__subbandPMI
.
Definition CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__cond := (fun (_ : CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Type) => True).
Lemma CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__nat__helper.

Definition CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F1 t :=
  match t with
  | CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__widebandPMI => 0
  | CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__subbandPMI => 1
  end.
Definition CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__widebandPMI
  | 1 => CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__subbandPMI
  | _ => CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__widebandPMI
  end.
Lemma CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F1F2 : forall x : CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Type, (CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F1 x <= 1) /\ CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F2 (CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F2F1 : forall (y : nat) (H : y <= 1), CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F1 (CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F2 y) = y. enum_solve H y. Qed.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 3 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 5 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 6 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 7 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 9 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 11 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 12 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 13 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 14 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 15 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 17 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 18 /\ bit_string_len_prop (fst z) (snd z)).

Inductive CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type : Set :=
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type
.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list : list typ := (
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__cond ::
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__cond ::
 nil).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__cond (c : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type) := 
  match c with
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__cond t 
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__cond t 
  end.

Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__len_helper1 : to_bit_sz (length CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__len_helper2 : 2 <= length2 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list.
 simpl. lia. Qed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__Type := bit_string_fixed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 19 /\ bit_string_len_prop (fst z) (snd z)).

Inductive CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type : Set :=
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530 : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__Type -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type
.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list : list typ := (
typ_cons CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__cond ::
 nil).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__cond (c : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type) := 
  match c with
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530 t => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__cond t 
  end.

Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__len_helper1 : to_bit_sz (length CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__Type : Set := CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type + CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__cond :=
  sum_cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__cond.
Record CSI_ReportConfig__reportFreqConfiguration__Type : Set :=
  make__CSI_ReportConfig__reportFreqConfiguration__Type {
    CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator : option CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Type ;
    CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator : option CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Type ;
    CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand : option CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__Type ;
}.
Definition CSI_ReportConfig__reportFreqConfiguration__list := (
 Opt CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Type CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__cond ::
 Opt CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Type CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__cond ::
 Opt CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__cond ::
 nil).
Definition CSI_ReportConfig__reportFreqConfiguration__cond z := 
  opt_cond CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__cond (CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator z) /\
  opt_cond CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__cond (CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator z) /\
  opt_cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__cond (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand z) /\
  True.

Inductive CSI_ReportConfig__timeRestrictionForChannelMeasurements__Type : Set :=
 | CSI_ReportConfig__timeRestrictionForChannelMeasurements__configured
 | CSI_ReportConfig__timeRestrictionForChannelMeasurements__notConfigured
.
Definition CSI_ReportConfig__timeRestrictionForChannelMeasurements__cond := (fun (_ : CSI_ReportConfig__timeRestrictionForChannelMeasurements__Type) => True).
Lemma CSI_ReportConfig__timeRestrictionForChannelMeasurements__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__timeRestrictionForChannelMeasurements__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_ReportConfig__timeRestrictionForChannelMeasurements__nat__helper.

Definition CSI_ReportConfig__timeRestrictionForChannelMeasurements__F1 t :=
  match t with
  | CSI_ReportConfig__timeRestrictionForChannelMeasurements__configured => 0
  | CSI_ReportConfig__timeRestrictionForChannelMeasurements__notConfigured => 1
  end.
Definition CSI_ReportConfig__timeRestrictionForChannelMeasurements__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__timeRestrictionForChannelMeasurements__configured
  | 1 => CSI_ReportConfig__timeRestrictionForChannelMeasurements__notConfigured
  | _ => CSI_ReportConfig__timeRestrictionForChannelMeasurements__configured
  end.
Lemma CSI_ReportConfig__timeRestrictionForChannelMeasurements__F1F2 : forall x : CSI_ReportConfig__timeRestrictionForChannelMeasurements__Type, (CSI_ReportConfig__timeRestrictionForChannelMeasurements__F1 x <= 1) /\ CSI_ReportConfig__timeRestrictionForChannelMeasurements__F2 (CSI_ReportConfig__timeRestrictionForChannelMeasurements__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__timeRestrictionForChannelMeasurements__F2F1 : forall (y : nat) (H : y <= 1), CSI_ReportConfig__timeRestrictionForChannelMeasurements__F1 (CSI_ReportConfig__timeRestrictionForChannelMeasurements__F2 y) = y. enum_solve H y. Qed.

Inductive CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Type : Set :=
 | CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__configured
 | CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__notConfigured
.
Definition CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__cond := (fun (_ : CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Type) => True).
Lemma CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__nat__helper.

Definition CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F1 t :=
  match t with
  | CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__configured => 0
  | CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__notConfigured => 1
  end.
Definition CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__configured
  | 1 => CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__notConfigured
  | _ => CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__configured
  end.
Lemma CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F1F2 : forall x : CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Type, (CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F1 x <= 1) /\ CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F2 (CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F2F1 : forall (y : nat) (H : y <= 1), CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F1 (CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F2 y) = y. enum_solve H y. Qed.

Require Import NR.CodebookConfig.

Opaque CodebookConfig__cond CodebookConfig__Format.

Inductive CSI_ReportConfig__dummy__Type : Set :=
 | CSI_ReportConfig__dummy__n1
 | CSI_ReportConfig__dummy__n2
.
Definition CSI_ReportConfig__dummy__cond := (fun (_ : CSI_ReportConfig__dummy__Type) => True).
Lemma CSI_ReportConfig__dummy__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__dummy__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_ReportConfig__dummy__nat__helper.

Definition CSI_ReportConfig__dummy__F1 t :=
  match t with
  | CSI_ReportConfig__dummy__n1 => 0
  | CSI_ReportConfig__dummy__n2 => 1
  end.
Definition CSI_ReportConfig__dummy__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__dummy__n1
  | 1 => CSI_ReportConfig__dummy__n2
  | _ => CSI_ReportConfig__dummy__n1
  end.
Lemma CSI_ReportConfig__dummy__F1F2 : forall x : CSI_ReportConfig__dummy__Type, (CSI_ReportConfig__dummy__F1 x <= 1) /\ CSI_ReportConfig__dummy__F2 (CSI_ReportConfig__dummy__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__dummy__F2F1 : forall (y : nat) (H : y <= 1), CSI_ReportConfig__dummy__F1 (CSI_ReportConfig__dummy__F2 y) = y. enum_solve H y. Qed.

Inductive CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Type : Set :=
 | CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n1
 | CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n2
 | CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n3
 | CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n4
.
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__cond := (fun (_ : CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Type) => True).
Lemma CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__nat__helper.

Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F1 t :=
  match t with
  | CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n1 => 0
  | CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n2 => 1
  | CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n3 => 2
  | CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n4 => 3
  end.
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n1
  | 1 => CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n2
  | 2 => CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n3
  | 3 => CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n4
  | _ => CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__n1
  end.
Lemma CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F1F2 : forall x : CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Type, (CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F1 x <= 3) /\ CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F2 (CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F2F1 : forall (y : nat) (H : y <= 3), CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F1 (CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F2 y) = y. enum_solve H y. Qed.

Record CSI_ReportConfig__groupBasedBeamReporting__disabled__Type : Set :=
  make__CSI_ReportConfig__groupBasedBeamReporting__disabled__Type {
    CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS : option CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Type ;
}.
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__list := (
 Opt CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Type CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__cond ::
 nil).
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__cond z := 
  opt_cond CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__cond (CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS z) /\
  True.


Inductive CSI_ReportConfig__groupBasedBeamReporting__Type : Set :=
  | CSI_ReportConfig__groupBasedBeamReporting__enabled : unit -> CSI_ReportConfig__groupBasedBeamReporting__Type
  | CSI_ReportConfig__groupBasedBeamReporting__disabled : CSI_ReportConfig__groupBasedBeamReporting__disabled__Type -> CSI_ReportConfig__groupBasedBeamReporting__Type
.
Definition CSI_ReportConfig__groupBasedBeamReporting__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons CSI_ReportConfig__groupBasedBeamReporting__disabled__Type CSI_ReportConfig__groupBasedBeamReporting__disabled__cond ::
 nil).
Definition CSI_ReportConfig__groupBasedBeamReporting__cond (c : CSI_ReportConfig__groupBasedBeamReporting__Type) := 
  match c with
  | CSI_ReportConfig__groupBasedBeamReporting__enabled t => (fun _ => True) t 
  | CSI_ReportConfig__groupBasedBeamReporting__disabled t => CSI_ReportConfig__groupBasedBeamReporting__disabled__cond t 
  end.

Lemma CSI_ReportConfig__groupBasedBeamReporting__len_helper1 : to_bit_sz (length CSI_ReportConfig__groupBasedBeamReporting__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_ReportConfig__groupBasedBeamReporting__len_helper2 : 2 <= length2 CSI_ReportConfig__groupBasedBeamReporting__list.
 simpl. lia. Qed.
Inductive CSI_ReportConfig__cqi_Table__Type : Set :=
 | CSI_ReportConfig__cqi_Table__table1
 | CSI_ReportConfig__cqi_Table__table2
 | CSI_ReportConfig__cqi_Table__table3
 | CSI_ReportConfig__cqi_Table__table4_r17
.
Definition CSI_ReportConfig__cqi_Table__cond := (fun (_ : CSI_ReportConfig__cqi_Table__Type) => True).
Lemma CSI_ReportConfig__cqi_Table__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__cqi_Table__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 CSI_ReportConfig__cqi_Table__nat__helper.

Definition CSI_ReportConfig__cqi_Table__F1 t :=
  match t with
  | CSI_ReportConfig__cqi_Table__table1 => 0
  | CSI_ReportConfig__cqi_Table__table2 => 1
  | CSI_ReportConfig__cqi_Table__table3 => 2
  | CSI_ReportConfig__cqi_Table__table4_r17 => 3
  end.
Definition CSI_ReportConfig__cqi_Table__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__cqi_Table__table1
  | 1 => CSI_ReportConfig__cqi_Table__table2
  | 2 => CSI_ReportConfig__cqi_Table__table3
  | 3 => CSI_ReportConfig__cqi_Table__table4_r17
  | _ => CSI_ReportConfig__cqi_Table__table1
  end.
Lemma CSI_ReportConfig__cqi_Table__F1F2 : forall x : CSI_ReportConfig__cqi_Table__Type, (CSI_ReportConfig__cqi_Table__F1 x <= 3) /\ CSI_ReportConfig__cqi_Table__F2 (CSI_ReportConfig__cqi_Table__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__cqi_Table__F2F1 : forall (y : nat) (H : y <= 3), CSI_ReportConfig__cqi_Table__F1 (CSI_ReportConfig__cqi_Table__F2 y) = y. enum_solve H y. Qed.

Inductive CSI_ReportConfig__subbandSize__Type : Set :=
 | CSI_ReportConfig__subbandSize__value1
 | CSI_ReportConfig__subbandSize__value2
.
Definition CSI_ReportConfig__subbandSize__cond := (fun (_ : CSI_ReportConfig__subbandSize__Type) => True).
Lemma CSI_ReportConfig__subbandSize__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__subbandSize__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_ReportConfig__subbandSize__nat__helper.

Definition CSI_ReportConfig__subbandSize__F1 t :=
  match t with
  | CSI_ReportConfig__subbandSize__value1 => 0
  | CSI_ReportConfig__subbandSize__value2 => 1
  end.
Definition CSI_ReportConfig__subbandSize__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__subbandSize__value1
  | 1 => CSI_ReportConfig__subbandSize__value2
  | _ => CSI_ReportConfig__subbandSize__value1
  end.
Lemma CSI_ReportConfig__subbandSize__F1F2 : forall x : CSI_ReportConfig__subbandSize__Type, (CSI_ReportConfig__subbandSize__F1 x <= 1) /\ CSI_ReportConfig__subbandSize__F2 (CSI_ReportConfig__subbandSize__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__subbandSize__F2F1 : forall (y : nat) (H : y <= 1), CSI_ReportConfig__subbandSize__F1 (CSI_ReportConfig__subbandSize__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PortIndexFor8Ranks.

Opaque PortIndexFor8Ranks__cond PortIndexFor8Ranks__Format.

Definition CSI_ReportConfig__non_PMI_PortIndication__Type := list PortIndexFor8Ranks__Type.

Lemma CSI_ReportConfig__non_PMI_PortIndication__helper1 : (0 <= 1 <= maxNrofNZP_CSI_RS_ResourcesPerConfig)%Z. unfold maxNrofNZP_CSI_RS_ResourcesPerConfig.
 lia. Qed.
Lemma CSI_ReportConfig__non_PMI_PortIndication__helper2 : to_bit_sz (Z.to_nat (maxNrofNZP_CSI_RS_ResourcesPerConfig - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofNZP_CSI_RS_ResourcesPerConfig - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__non_PMI_PortIndication__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__non_PMI_PortIndication__cond (z : CSI_ReportConfig__non_PMI_PortIndication__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofNZP_CSI_RS_ResourcesPerConfig)%Z /\ (list_and PortIndexFor8Ranks__cond z) .

Inductive CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Type : Set :=
 | CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl4
 | CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl8
 | CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl16
.
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__cond := (fun (_ : CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Type) => True).
Lemma CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__nat__helper.

Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F1 t :=
  match t with
  | CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl4 => 0
  | CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl8 => 1
  | CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl16 => 2
  end.
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl4
  | 1 => CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl8
  | 2 => CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl16
  | _ => CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__sl4
  end.
Lemma CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F1F2 : forall x : CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Type, (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F1 x <= 2) /\ CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F2 (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F2F1 : forall (y : nat) (H : y <= 2), CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F1 (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F2 y) = y. enum_solve H y. Qed.

Record CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Type : Set :=
  make__CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Type {
    CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530 : CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Type ;
}.
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list := (
 Nor CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Type CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__cond ::
 nil).
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond z := 
  CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__cond (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530 z) /\
  True.

Record CSI_ReportConfig__ext0O__Type : Set :=
  make__CSI_ReportConfig__ext0O__Type {
    CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530 : option CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Type ;
}.
Definition CSI_ReportConfig__ext0O__list := (
 Opt CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Type CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond ::
 nil).
Definition CSI_ReportConfig__ext0O__cond z := 
  opt_cond CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530 z) /\
  True.

Definition CSI_ReportConfig__ext0__Type := CSI_ReportConfig__ext0O__Type.
Definition CSI_ReportConfig__ext0__cond := CSI_ReportConfig__ext0O__cond.

Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__Type := Z.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__cond := (fun z => (0 <= z <= 32)%Z).
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__Type := list Z.

Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__cond (z : CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__cond z) .

Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__Type := Z.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__cond := (fun z => (0 <= z <= 32)%Z).
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__Type := list Z.

Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__cond (z : CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__cond z) .

Record CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Type : Set :=
  make__CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Type {
    CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16 : option CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__Type ;
    CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16 : option CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__Type ;
}.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list := (
 Opt CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__Type CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__cond ::
 Opt CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__Type CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__cond ::
 nil).
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond z := 
  opt_cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__cond (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16 z) /\
  opt_cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__cond (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16 z) /\
  True.

Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__Type := Z.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__cond := (fun z => (0 <= z <= 32)%Z).
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__Type := list Z.

Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__cond (z : CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__cond z) .

Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper1 : (0 <= 32)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper2 : to_bit_sz (Z.to_nat (32 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__Type := Z.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__cond := (fun z => (0 <= z <= 32)%Z).
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__Type := list Z.

Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__cond (z : CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__cond z) .

Record CSI_ReportConfig__ext1O__aperiodic_v1610__Type : Set :=
  make__CSI_ReportConfig__ext1O__aperiodic_v1610__Type {
    CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16 : option CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__Type ;
    CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16 : option CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__Type ;
}.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__list := (
 Opt CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__Type CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__cond ::
 Opt CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__Type CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__cond ::
 nil).
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__cond z := 
  opt_cond CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__cond (CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16 z) /\
  opt_cond CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__cond (CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16 z) /\
  True.


Inductive CSI_ReportConfig__ext1O__reportQuantity_r16__Type : Set :=
  | CSI_ReportConfig__ext1O__reportQuantity_r16__cri_SINR_r16 : unit -> CSI_ReportConfig__ext1O__reportQuantity_r16__Type
  | CSI_ReportConfig__ext1O__reportQuantity_r16__ssb_Index_SINR_r16 : unit -> CSI_ReportConfig__ext1O__reportQuantity_r16__Type
.
Definition CSI_ReportConfig__ext1O__reportQuantity_r16__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition CSI_ReportConfig__ext1O__reportQuantity_r16__cond (c : CSI_ReportConfig__ext1O__reportQuantity_r16__Type) := 
  match c with
  | CSI_ReportConfig__ext1O__reportQuantity_r16__cri_SINR_r16 t => (fun _ => True) t 
  | CSI_ReportConfig__ext1O__reportQuantity_r16__ssb_Index_SINR_r16 t => (fun _ => True) t 
  end.

Lemma CSI_ReportConfig__ext1O__reportQuantity_r16__len_helper1 : to_bit_sz (length CSI_ReportConfig__ext1O__reportQuantity_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_ReportConfig__ext1O__reportQuantity_r16__len_helper2 : 2 <= length2 CSI_ReportConfig__ext1O__reportQuantity_r16__list.
 simpl. lia. Qed.
Require Import NR.CodebookConfig_r16.

Opaque CodebookConfig_r16__cond CodebookConfig_r16__Format.

Record CSI_ReportConfig__ext1O__Type : Set :=
  make__CSI_ReportConfig__ext1O__Type {
    CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610 : option CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Type ;
    CSI_ReportConfig__ext1O__aperiodic_v1610 : option CSI_ReportConfig__ext1O__aperiodic_v1610__Type ;
    CSI_ReportConfig__ext1O__reportQuantity_r16 : option CSI_ReportConfig__ext1O__reportQuantity_r16__Type ;
    CSI_ReportConfig__ext1O__codebookConfig_r16 : option CodebookConfig_r16__Type ;
}.
Definition CSI_ReportConfig__ext1O__list := (
 Opt CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Type CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond ::
 Opt CSI_ReportConfig__ext1O__aperiodic_v1610__Type CSI_ReportConfig__ext1O__aperiodic_v1610__cond ::
 Opt CSI_ReportConfig__ext1O__reportQuantity_r16__Type CSI_ReportConfig__ext1O__reportQuantity_r16__cond ::
 Opt CodebookConfig_r16__Type CodebookConfig_r16__cond ::
 nil).
Definition CSI_ReportConfig__ext1O__cond z := 
  opt_cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610 z) /\
  opt_cond CSI_ReportConfig__ext1O__aperiodic_v1610__cond (CSI_ReportConfig__ext1O__aperiodic_v1610 z) /\
  opt_cond CSI_ReportConfig__ext1O__reportQuantity_r16__cond (CSI_ReportConfig__ext1O__reportQuantity_r16 z) /\
  opt_cond CodebookConfig_r16__cond (CSI_ReportConfig__ext1O__codebookConfig_r16 z) /\
  True.

Definition CSI_ReportConfig__ext1__Type := CSI_ReportConfig__ext1O__Type.
Definition CSI_ReportConfig__ext1__cond := CSI_ReportConfig__ext1O__cond.

Inductive CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Type : Set :=
 | CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__bits4
.
Definition CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__cond := (fun (_ : CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Type) => True).
Lemma CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__nat__helper.

Definition CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F1 t :=
  match t with
  | CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__bits4 => 0
  end.
Definition CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__bits4
  | _ => CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__bits4
  end.
Lemma CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F1F2 : forall x : CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Type, (CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F1 x <= 0) /\ CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F2 (CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F2F1 : forall (y : nat) (H : y <= 0), CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F1 (CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Type : Set :=
 | CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n1
 | CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n2
 | CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n3
 | CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n4
.
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__cond := (fun (_ : CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Type) => True).
Lemma CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__nat__helper.

Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F1 t :=
  match t with
  | CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n1 => 0
  | CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n2 => 1
  | CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n3 => 2
  | CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n4 => 3
  end.
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n1
  | 1 => CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n2
  | 2 => CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n3
  | 3 => CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n4
  | _ => CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__n1
  end.
Lemma CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F1F2 : forall x : CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Type, (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F1 x <= 3) /\ CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F2 (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F2F1 : forall (y : nat) (H : y <= 3), CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F1 (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F2 y) = y. enum_solve H y. Qed.

Record CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Type : Set :=
  make__CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Type {
    CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17 : CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Type ;
}.
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list := (
 Nor CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Type CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__cond ::
 nil).
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond z := 
  CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__cond (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17 z) /\
  True.

Require Import NR.CodebookConfig_r17.

Opaque CodebookConfig_r17__cond CodebookConfig_r17__Format.

Inductive CSI_ReportConfig__ext2O__sharedCMR_r17__Type : Set :=
 | CSI_ReportConfig__ext2O__sharedCMR_r17__enable
.
Definition CSI_ReportConfig__ext2O__sharedCMR_r17__cond := (fun (_ : CSI_ReportConfig__ext2O__sharedCMR_r17__Type) => True).
Lemma CSI_ReportConfig__ext2O__sharedCMR_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__ext2O__sharedCMR_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CSI_ReportConfig__ext2O__sharedCMR_r17__nat__helper.

Definition CSI_ReportConfig__ext2O__sharedCMR_r17__F1 t :=
  match t with
  | CSI_ReportConfig__ext2O__sharedCMR_r17__enable => 0
  end.
Definition CSI_ReportConfig__ext2O__sharedCMR_r17__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__ext2O__sharedCMR_r17__enable
  | _ => CSI_ReportConfig__ext2O__sharedCMR_r17__enable
  end.
Lemma CSI_ReportConfig__ext2O__sharedCMR_r17__F1F2 : forall x : CSI_ReportConfig__ext2O__sharedCMR_r17__Type, (CSI_ReportConfig__ext2O__sharedCMR_r17__F1 x <= 0) /\ CSI_ReportConfig__ext2O__sharedCMR_r17__F2 (CSI_ReportConfig__ext2O__sharedCMR_r17__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__ext2O__sharedCMR_r17__F2F1 : forall (y : nat) (H : y <= 0), CSI_ReportConfig__ext2O__sharedCMR_r17__F1 (CSI_ReportConfig__ext2O__sharedCMR_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CSI_ReportConfig__ext2O__csi_ReportMode_r17__Type : Set :=
 | CSI_ReportConfig__ext2O__csi_ReportMode_r17__mode1
 | CSI_ReportConfig__ext2O__csi_ReportMode_r17__mode2
.
Definition CSI_ReportConfig__ext2O__csi_ReportMode_r17__cond := (fun (_ : CSI_ReportConfig__ext2O__csi_ReportMode_r17__Type) => True).
Lemma CSI_ReportConfig__ext2O__csi_ReportMode_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__ext2O__csi_ReportMode_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_ReportConfig__ext2O__csi_ReportMode_r17__nat__helper.

Definition CSI_ReportConfig__ext2O__csi_ReportMode_r17__F1 t :=
  match t with
  | CSI_ReportConfig__ext2O__csi_ReportMode_r17__mode1 => 0
  | CSI_ReportConfig__ext2O__csi_ReportMode_r17__mode2 => 1
  end.
Definition CSI_ReportConfig__ext2O__csi_ReportMode_r17__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__ext2O__csi_ReportMode_r17__mode1
  | 1 => CSI_ReportConfig__ext2O__csi_ReportMode_r17__mode2
  | _ => CSI_ReportConfig__ext2O__csi_ReportMode_r17__mode1
  end.
Lemma CSI_ReportConfig__ext2O__csi_ReportMode_r17__F1F2 : forall x : CSI_ReportConfig__ext2O__csi_ReportMode_r17__Type, (CSI_ReportConfig__ext2O__csi_ReportMode_r17__F1 x <= 1) /\ CSI_ReportConfig__ext2O__csi_ReportMode_r17__F2 (CSI_ReportConfig__ext2O__csi_ReportMode_r17__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__ext2O__csi_ReportMode_r17__F2F1 : forall (y : nat) (H : y <= 1), CSI_ReportConfig__ext2O__csi_ReportMode_r17__F1 (CSI_ReportConfig__ext2O__csi_ReportMode_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Type : Set :=
 | CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n0
 | CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n1
 | CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n2
.
Definition CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__cond := (fun (_ : CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Type) => True).
Lemma CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__nat__helper.

Definition CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F1 t :=
  match t with
  | CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n0 => 0
  | CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n1 => 1
  | CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n2 => 2
  end.
Definition CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F2 n :=
  match n with
  | 0 => CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n0
  | 1 => CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n1
  | 2 => CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n2
  | _ => CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__n0
  end.
Lemma CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F1F2 : forall x : CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Type, (CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F1 x <= 2) /\ CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F2 (CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F1 x) = x. imp_solve. Qed.
Lemma CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F2F1 : forall (y : nat) (H : y <= 2), CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F1 (CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F2 y) = y. enum_solve H y. Qed.


Inductive CSI_ReportConfig__ext2O__reportQuantity_r17__Type : Set :=
  | CSI_ReportConfig__ext2O__reportQuantity_r17__cri_RSRP_Index_r17 : unit -> CSI_ReportConfig__ext2O__reportQuantity_r17__Type
  | CSI_ReportConfig__ext2O__reportQuantity_r17__ssb_Index_RSRP_Index_r17 : unit -> CSI_ReportConfig__ext2O__reportQuantity_r17__Type
  | CSI_ReportConfig__ext2O__reportQuantity_r17__cri_SINR_Index_r17 : unit -> CSI_ReportConfig__ext2O__reportQuantity_r17__Type
  | CSI_ReportConfig__ext2O__reportQuantity_r17__ssb_Index_SINR_Index_r17 : unit -> CSI_ReportConfig__ext2O__reportQuantity_r17__Type
.
Definition CSI_ReportConfig__ext2O__reportQuantity_r17__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition CSI_ReportConfig__ext2O__reportQuantity_r17__cond (c : CSI_ReportConfig__ext2O__reportQuantity_r17__Type) := 
  match c with
  | CSI_ReportConfig__ext2O__reportQuantity_r17__cri_RSRP_Index_r17 t => (fun _ => True) t 
  | CSI_ReportConfig__ext2O__reportQuantity_r17__ssb_Index_RSRP_Index_r17 t => (fun _ => True) t 
  | CSI_ReportConfig__ext2O__reportQuantity_r17__cri_SINR_Index_r17 t => (fun _ => True) t 
  | CSI_ReportConfig__ext2O__reportQuantity_r17__ssb_Index_SINR_Index_r17 t => (fun _ => True) t 
  end.

Lemma CSI_ReportConfig__ext2O__reportQuantity_r17__len_helper1 : to_bit_sz (length CSI_ReportConfig__ext2O__reportQuantity_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_ReportConfig__ext2O__reportQuantity_r17__len_helper2 : 2 <= length2 CSI_ReportConfig__ext2O__reportQuantity_r17__list.
 simpl. lia. Qed.
Record CSI_ReportConfig__ext2O__Type : Set :=
  make__CSI_ReportConfig__ext2O__Type {
    CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17 : option CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Type ;
    CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710 : option CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Type ;
    CSI_ReportConfig__ext2O__codebookConfig_r17 : option CodebookConfig_r17__Type ;
    CSI_ReportConfig__ext2O__sharedCMR_r17 : option CSI_ReportConfig__ext2O__sharedCMR_r17__Type ;
    CSI_ReportConfig__ext2O__csi_ReportMode_r17 : option CSI_ReportConfig__ext2O__csi_ReportMode_r17__Type ;
    CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17 : option CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Type ;
    CSI_ReportConfig__ext2O__reportQuantity_r17 : option CSI_ReportConfig__ext2O__reportQuantity_r17__Type ;
}.
Definition CSI_ReportConfig__ext2O__list := (
 Opt CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Type CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__cond ::
 Opt CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Type CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond ::
 Opt CodebookConfig_r17__Type CodebookConfig_r17__cond ::
 Opt CSI_ReportConfig__ext2O__sharedCMR_r17__Type CSI_ReportConfig__ext2O__sharedCMR_r17__cond ::
 Opt CSI_ReportConfig__ext2O__csi_ReportMode_r17__Type CSI_ReportConfig__ext2O__csi_ReportMode_r17__cond ::
 Opt CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Type CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__cond ::
 Opt CSI_ReportConfig__ext2O__reportQuantity_r17__Type CSI_ReportConfig__ext2O__reportQuantity_r17__cond ::
 nil).
Definition CSI_ReportConfig__ext2O__cond z := 
  opt_cond CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__cond (CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17 z) /\
  opt_cond CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710 z) /\
  opt_cond CodebookConfig_r17__cond (CSI_ReportConfig__ext2O__codebookConfig_r17 z) /\
  opt_cond CSI_ReportConfig__ext2O__sharedCMR_r17__cond (CSI_ReportConfig__ext2O__sharedCMR_r17 z) /\
  opt_cond CSI_ReportConfig__ext2O__csi_ReportMode_r17__cond (CSI_ReportConfig__ext2O__csi_ReportMode_r17 z) /\
  opt_cond CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__cond (CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17 z) /\
  opt_cond CSI_ReportConfig__ext2O__reportQuantity_r17__cond (CSI_ReportConfig__ext2O__reportQuantity_r17 z) /\
  True.

Definition CSI_ReportConfig__ext2__Type := CSI_ReportConfig__ext2O__Type.
Definition CSI_ReportConfig__ext2__cond := CSI_ReportConfig__ext2O__cond.

Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__helper1 : (0 <= 128)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (128 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__Type := Z.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__cond := (fun z => (0 <= z <= 128)%Z).
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__Type := list Z.

Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__cond (z : CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__cond z) .

Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper1 : (0 <= 128)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (128 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__Type := Z.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__cond := (fun z => (0 <= z <= 128)%Z).
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__Type := list Z.

Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__cond (z : CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__cond z) .

Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper1 : (0 <= 128)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (128 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__Type := Z.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__cond := (fun z => (0 <= z <= 128)%Z).
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__Type := list Z.

Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__cond (z : CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__cond z) .

Record CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Type : Set :=
  make__CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Type {
    CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17 : option CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__Type ;
    CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17 : option CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__Type ;
    CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17 : option CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__Type ;
}.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list := (
 Opt CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__Type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__cond ::
 Opt CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__Type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__cond ::
 Opt CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__Type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__cond ::
 nil).
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond z := 
  opt_cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__cond (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17 z) /\
  opt_cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__cond (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17 z) /\
  opt_cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__cond (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17 z) /\
  True.

Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__helper1 : (0 <= 128)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (128 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__Type := Z.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__cond := (fun z => (0 <= z <= 128)%Z).
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__Type := list Z.

Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__cond (z : CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__cond z) .

Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper1 : (0 <= 128)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (128 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__Type := Z.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__cond := (fun z => (0 <= z <= 128)%Z).
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__Type := list Z.

Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__cond (z : CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__cond z) .

Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper1 : (0 <= 128)%Z.  lia. Qed.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper2 : to_bit_sz (Z.to_nat (128 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (128 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__Type := Z.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__cond := (fun z => (0 <= z <= 128)%Z).
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__Type := list Z.

Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__helper1 : (0 <= 1 <= maxNrofUL_Allocations_r16)%Z. unfold maxNrofUL_Allocations_r16.
 lia. Qed.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofUL_Allocations_r16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofUL_Allocations_r16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__cond (z : CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofUL_Allocations_r16)%Z /\ (list_and CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__cond z) .

Record CSI_ReportConfig__ext3O__aperiodic_v1720__Type : Set :=
  make__CSI_ReportConfig__ext3O__aperiodic_v1720__Type {
    CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17 : option CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__Type ;
    CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17 : option CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__Type ;
    CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17 : option CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__Type ;
}.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__list := (
 Opt CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__Type CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__cond ::
 Opt CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__Type CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__cond ::
 Opt CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__Type CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__cond ::
 nil).
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__cond z := 
  opt_cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__cond (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17 z) /\
  opt_cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__cond (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17 z) /\
  opt_cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__cond (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17 z) /\
  True.

Record CSI_ReportConfig__ext3O__Type : Set :=
  make__CSI_ReportConfig__ext3O__Type {
    CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720 : option CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Type ;
    CSI_ReportConfig__ext3O__aperiodic_v1720 : option CSI_ReportConfig__ext3O__aperiodic_v1720__Type ;
}.
Definition CSI_ReportConfig__ext3O__list := (
 Opt CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond ::
 Opt CSI_ReportConfig__ext3O__aperiodic_v1720__Type CSI_ReportConfig__ext3O__aperiodic_v1720__cond ::
 nil).
Definition CSI_ReportConfig__ext3O__cond z := 
  opt_cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720 z) /\
  opt_cond CSI_ReportConfig__ext3O__aperiodic_v1720__cond (CSI_ReportConfig__ext3O__aperiodic_v1720 z) /\
  True.

Definition CSI_ReportConfig__ext3__Type := CSI_ReportConfig__ext3O__Type.
Definition CSI_ReportConfig__ext3__cond := CSI_ReportConfig__ext3O__cond.

Require Import NR.CodebookConfig_v1730.

Opaque CodebookConfig_v1730__cond CodebookConfig_v1730__Format.

Record CSI_ReportConfig__ext4O__Type : Set :=
  make__CSI_ReportConfig__ext4O__Type {
    CSI_ReportConfig__ext4O__codebookConfig_v1730 : option CodebookConfig_v1730__Type ;
}.
Definition CSI_ReportConfig__ext4O__list := (
 Opt CodebookConfig_v1730__Type CodebookConfig_v1730__cond ::
 nil).
Definition CSI_ReportConfig__ext4O__cond z := 
  opt_cond CodebookConfig_v1730__cond (CSI_ReportConfig__ext4O__codebookConfig_v1730 z) /\
  True.

Definition CSI_ReportConfig__ext4__Type := CSI_ReportConfig__ext4O__Type.
Definition CSI_ReportConfig__ext4__cond := CSI_ReportConfig__ext4O__cond.

Record CSI_ReportConfig__Type : Set :=
  make__CSI_ReportConfig__Type {
    CSI_ReportConfig__reportConfigId : CSI_ReportConfigId__Type ;
    CSI_ReportConfig__carrier : option ServCellIndex__Type ;
    CSI_ReportConfig__resourcesForChannelMeasurement : CSI_ResourceConfigId__Type ;
    CSI_ReportConfig__csi_IM_ResourcesForInterference : option CSI_ResourceConfigId__Type ;
    CSI_ReportConfig__nzp_CSI_RS_ResourcesForInterference : option CSI_ResourceConfigId__Type ;
    CSI_ReportConfig__reportConfigType : CSI_ReportConfig__reportConfigType__Type ;
    CSI_ReportConfig__reportQuantity : CSI_ReportConfig__reportQuantity__Type ;
    CSI_ReportConfig__reportFreqConfiguration : option CSI_ReportConfig__reportFreqConfiguration__Type ;
    CSI_ReportConfig__timeRestrictionForChannelMeasurements : CSI_ReportConfig__timeRestrictionForChannelMeasurements__Type ;
    CSI_ReportConfig__timeRestrictionForInterferenceMeasurements : CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Type ;
    CSI_ReportConfig__codebookConfig : option CodebookConfig__Type ;
    CSI_ReportConfig__dummy : option CSI_ReportConfig__dummy__Type ;
    CSI_ReportConfig__groupBasedBeamReporting : CSI_ReportConfig__groupBasedBeamReporting__Type ;
    CSI_ReportConfig__cqi_Table : option CSI_ReportConfig__cqi_Table__Type ;
    CSI_ReportConfig__subbandSize : CSI_ReportConfig__subbandSize__Type ;
    CSI_ReportConfig__non_PMI_PortIndication : option CSI_ReportConfig__non_PMI_PortIndication__Type ;
    CSI_ReportConfig__ext0 : option CSI_ReportConfig__ext0__Type ;
    CSI_ReportConfig__ext1 : option CSI_ReportConfig__ext1__Type ;
    CSI_ReportConfig__ext2 : option CSI_ReportConfig__ext2__Type ;
    CSI_ReportConfig__ext3 : option CSI_ReportConfig__ext3__Type ;
    CSI_ReportConfig__ext4 : option CSI_ReportConfig__ext4__Type ;
}.
Definition CSI_ReportConfig__root_list : list seq_elem := (
 Nor CSI_ReportConfigId__Type CSI_ReportConfigId__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 Nor CSI_ResourceConfigId__Type CSI_ResourceConfigId__cond ::
 Opt CSI_ResourceConfigId__Type CSI_ResourceConfigId__cond ::
 Opt CSI_ResourceConfigId__Type CSI_ResourceConfigId__cond ::
 Nor CSI_ReportConfig__reportConfigType__Type CSI_ReportConfig__reportConfigType__cond ::
 Nor CSI_ReportConfig__reportQuantity__Type CSI_ReportConfig__reportQuantity__cond ::
 Opt CSI_ReportConfig__reportFreqConfiguration__Type CSI_ReportConfig__reportFreqConfiguration__cond ::
 Nor CSI_ReportConfig__timeRestrictionForChannelMeasurements__Type CSI_ReportConfig__timeRestrictionForChannelMeasurements__cond ::
 Nor CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Type CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__cond ::
 Opt CodebookConfig__Type CodebookConfig__cond ::
 Opt CSI_ReportConfig__dummy__Type CSI_ReportConfig__dummy__cond ::
 Nor CSI_ReportConfig__groupBasedBeamReporting__Type CSI_ReportConfig__groupBasedBeamReporting__cond ::
 Opt CSI_ReportConfig__cqi_Table__Type CSI_ReportConfig__cqi_Table__cond ::
 Nor CSI_ReportConfig__subbandSize__Type CSI_ReportConfig__subbandSize__cond ::
 Opt CSI_ReportConfig__non_PMI_PortIndication__Type CSI_ReportConfig__non_PMI_PortIndication__cond ::
 nil).
Definition CSI_ReportConfig__ext_list : list typ := (
  typ_cons CSI_ReportConfig__ext0__Type CSI_ReportConfig__ext0__cond ::
  typ_cons CSI_ReportConfig__ext1__Type CSI_ReportConfig__ext1__cond ::
  typ_cons CSI_ReportConfig__ext2__Type CSI_ReportConfig__ext2__cond ::
  typ_cons CSI_ReportConfig__ext3__Type CSI_ReportConfig__ext3__cond ::
  typ_cons CSI_ReportConfig__ext4__Type CSI_ReportConfig__ext4__cond ::
  nil).
Definition CSI_ReportConfig__cond (z : CSI_ReportConfig__Type) := 
(  CSI_ReportConfigId__cond (CSI_ReportConfig__reportConfigId z) /\
  opt_cond ServCellIndex__cond (CSI_ReportConfig__carrier z) /\
  CSI_ResourceConfigId__cond (CSI_ReportConfig__resourcesForChannelMeasurement z) /\
  opt_cond CSI_ResourceConfigId__cond (CSI_ReportConfig__csi_IM_ResourcesForInterference z) /\
  opt_cond CSI_ResourceConfigId__cond (CSI_ReportConfig__nzp_CSI_RS_ResourcesForInterference z) /\
  CSI_ReportConfig__reportConfigType__cond (CSI_ReportConfig__reportConfigType z) /\
  CSI_ReportConfig__reportQuantity__cond (CSI_ReportConfig__reportQuantity z) /\
  opt_cond CSI_ReportConfig__reportFreqConfiguration__cond (CSI_ReportConfig__reportFreqConfiguration z) /\
  CSI_ReportConfig__timeRestrictionForChannelMeasurements__cond (CSI_ReportConfig__timeRestrictionForChannelMeasurements z) /\
  CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__cond (CSI_ReportConfig__timeRestrictionForInterferenceMeasurements z) /\
  opt_cond CodebookConfig__cond (CSI_ReportConfig__codebookConfig z) /\
  opt_cond CSI_ReportConfig__dummy__cond (CSI_ReportConfig__dummy z) /\
  CSI_ReportConfig__groupBasedBeamReporting__cond (CSI_ReportConfig__groupBasedBeamReporting z) /\
  opt_cond CSI_ReportConfig__cqi_Table__cond (CSI_ReportConfig__cqi_Table z) /\
  CSI_ReportConfig__subbandSize__cond (CSI_ReportConfig__subbandSize z) /\
  opt_cond CSI_ReportConfig__non_PMI_PortIndication__cond (CSI_ReportConfig__non_PMI_PortIndication z) /\
  True) /\ 
(  opt_cond CSI_ReportConfig__ext0__cond (CSI_ReportConfig__ext0 z) /\
  opt_cond CSI_ReportConfig__ext1__cond (CSI_ReportConfig__ext1 z) /\
  opt_cond CSI_ReportConfig__ext2__cond (CSI_ReportConfig__ext2 z) /\
  opt_cond CSI_ReportConfig__ext3__cond (CSI_ReportConfig__ext3 z) /\
  opt_cond CSI_ReportConfig__ext4__cond (CSI_ReportConfig__ext4 z) /\
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
Definition CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__Format : T_Format CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__Type CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__cond := seq_of_format PUCCH_CSI_Resource__Format 1 maxNrofBWPs CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__helper1 CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__helper2.

Opaque CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__cond CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__Format.


Definition CSI_ReportConfig__reportConfigType__periodic__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__reportConfigType__periodic__list.
Definition CSI_ReportConfig__reportConfigType__periodic__Format_list : CSI_ReportConfig__reportConfigType__periodic__Format_Type :=
  (CSI_ReportPeriodicityAndOffset__Format, (CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList__Format, unit_format)).
Definition CSI_ReportConfig__reportConfigType__periodic__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__reportConfigType__periodic__list CSI_ReportConfig__reportConfigType__periodic__Format_list.
Definition CSI_ReportConfig__reportConfigType__periodic__F1 z :=
  (CSI_ReportConfig__reportConfigType__periodic__reportSlotConfig z, (CSI_ReportConfig__reportConfigType__periodic__pucch_CSI_ResourceList z, tt)).
Definition CSI_ReportConfig__reportConfigType__periodic__F2 (y : seq_type CSI_ReportConfig__reportConfigType__periodic__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_ReportConfig__reportConfigType__periodic__Type i0 i1
  end.
Lemma CSI_ReportConfig__reportConfigType__periodic__F1F2_cond (z : CSI_ReportConfig__reportConfigType__periodic__Type)
  : CSI_ReportConfig__reportConfigType__periodic__cond z ->
  (seq_cond CSI_ReportConfig__reportConfigType__periodic__list (CSI_ReportConfig__reportConfigType__periodic__F1 z)).
intro H. unfold CSI_ReportConfig__reportConfigType__periodic__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportConfigType__periodic__F1F2_cond2 (z : CSI_ReportConfig__reportConfigType__periodic__Type)
 : CSI_ReportConfig__reportConfigType__periodic__F2 (CSI_ReportConfig__reportConfigType__periodic__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportConfigType__periodic__F2F1_cond (y : seq_type CSI_ReportConfig__reportConfigType__periodic__list)
  : seq_cond CSI_ReportConfig__reportConfigType__periodic__list y ->
 (CSI_ReportConfig__reportConfigType__periodic__cond (CSI_ReportConfig__reportConfigType__periodic__F2 y)) /\  CSI_ReportConfig__reportConfigType__periodic__F1 (CSI_ReportConfig__reportConfigType__periodic__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__reportConfigType__periodic__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__reportConfigType__periodic__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__reportConfigType__periodic__Format : T_Format CSI_ReportConfig__reportConfigType__periodic__Type CSI_ReportConfig__reportConfigType__periodic__cond :=
        proj2_format  CSI_ReportConfig__reportConfigType__periodic__cond CSI_ReportConfig__reportConfigType__periodic__list__Format
    CSI_ReportConfig__reportConfigType__periodic__F1 CSI_ReportConfig__reportConfigType__periodic__F2 CSI_ReportConfig__reportConfigType__periodic__F1F2_cond  CSI_ReportConfig__reportConfigType__periodic__F1F2_cond2 CSI_ReportConfig__reportConfigType__periodic__F2F1_cond.
Opaque CSI_ReportConfig__reportConfigType__periodic__cond CSI_ReportConfig__reportConfigType__periodic__Format.

Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__Format : T_Format CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__cond := seq_of_format PUCCH_CSI_Resource__Format 1 maxNrofBWPs CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__helper1 CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__helper2.

Opaque CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__Format.


Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Format_list : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Format_Type :=
  (CSI_ReportPeriodicityAndOffset__Format, (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList__Format, unit_format)).
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Format_list.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1 z :=
  (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__reportSlotConfig z, (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__pucch_CSI_ResourceList z, tt)).
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F2 (y : seq_type CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type i0 i1
  end.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1F2_cond (z : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type)
  : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond z ->
  (seq_cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1 z)).
intro H. unfold CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1F2_cond2 (z : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type)
 : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F2 (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F2F1_cond (y : seq_type CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list)
  : seq_cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list y ->
 (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F2 y)) /\  CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1 (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Format : T_Format CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond :=
        proj2_format  CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__list__Format
    CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1 CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F2 CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1F2_cond  CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F1F2_cond2 CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__F2F1_cond.
Opaque CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Format.

Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Format : T_Format CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__nat__Format CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F1 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F2 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F1F2 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__F2F1.

Opaque CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Format.

Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__Format : T_Format Z CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__cond :=
 ranged_int_format (0) (32) CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__helper1 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__helper2.

Opaque CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__Format.

Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__Format : T_Format CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__cond := seq_of_format CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__seq_of__Format 1 maxNrofUL_Allocations CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__helper1 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__helper2.

Opaque CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__Format.


Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Format_list : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Format_Type :=
  (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig__Format, (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList__Format, (P0_PUSCH_AlphaSetId__Format, unit_format))).
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Format_list.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1 z :=
  (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotConfig z, (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__reportSlotOffsetList z, (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__p0alpha z, tt))).
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F2 (y : seq_type CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type i0 i1 i2
  end.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1F2_cond (z : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type)
  : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond z ->
  (seq_cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1 z)).
intro H. unfold CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1F2_cond2 (z : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type)
 : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F2 (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F2F1_cond (y : seq_type CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list)
  : seq_cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list y ->
 (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F2 y)) /\  CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1 (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Format : T_Format CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond :=
        proj2_format  CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__list__Format
    CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F2 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1F2_cond  CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F1F2_cond2 CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__F2F1_cond.
Opaque CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__cond CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Format.

Definition CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__Format : T_Format Z CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__cond :=
 ranged_int_format (0) (32) CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__helper1 CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__helper2.

Opaque CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__cond CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__Format.

Definition CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__Format : T_Format CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__Type CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__cond := seq_of_format CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__seq_of__Format 1 maxNrofUL_Allocations CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__helper1 CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__helper2.

Opaque CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__cond CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__Format.


Definition CSI_ReportConfig__reportConfigType__aperiodic__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__reportConfigType__aperiodic__list.
Definition CSI_ReportConfig__reportConfigType__aperiodic__Format_list : CSI_ReportConfig__reportConfigType__aperiodic__Format_Type :=
  (CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList__Format, unit_format).
Definition CSI_ReportConfig__reportConfigType__aperiodic__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__reportConfigType__aperiodic__list CSI_ReportConfig__reportConfigType__aperiodic__Format_list.
Definition CSI_ReportConfig__reportConfigType__aperiodic__F1 z :=
  (CSI_ReportConfig__reportConfigType__aperiodic__reportSlotOffsetList z, tt).
Definition CSI_ReportConfig__reportConfigType__aperiodic__F2 (y : seq_type CSI_ReportConfig__reportConfigType__aperiodic__list) :=
  match y with
  | (i0, _)=>
    make__CSI_ReportConfig__reportConfigType__aperiodic__Type i0
  end.
Lemma CSI_ReportConfig__reportConfigType__aperiodic__F1F2_cond (z : CSI_ReportConfig__reportConfigType__aperiodic__Type)
  : CSI_ReportConfig__reportConfigType__aperiodic__cond z ->
  (seq_cond CSI_ReportConfig__reportConfigType__aperiodic__list (CSI_ReportConfig__reportConfigType__aperiodic__F1 z)).
intro H. unfold CSI_ReportConfig__reportConfigType__aperiodic__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportConfigType__aperiodic__F1F2_cond2 (z : CSI_ReportConfig__reportConfigType__aperiodic__Type)
 : CSI_ReportConfig__reportConfigType__aperiodic__F2 (CSI_ReportConfig__reportConfigType__aperiodic__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportConfigType__aperiodic__F2F1_cond (y : seq_type CSI_ReportConfig__reportConfigType__aperiodic__list)
  : seq_cond CSI_ReportConfig__reportConfigType__aperiodic__list y ->
 (CSI_ReportConfig__reportConfigType__aperiodic__cond (CSI_ReportConfig__reportConfigType__aperiodic__F2 y)) /\  CSI_ReportConfig__reportConfigType__aperiodic__F1 (CSI_ReportConfig__reportConfigType__aperiodic__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__reportConfigType__aperiodic__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__reportConfigType__aperiodic__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__reportConfigType__aperiodic__Format : T_Format CSI_ReportConfig__reportConfigType__aperiodic__Type CSI_ReportConfig__reportConfigType__aperiodic__cond :=
        proj2_format  CSI_ReportConfig__reportConfigType__aperiodic__cond CSI_ReportConfig__reportConfigType__aperiodic__list__Format
    CSI_ReportConfig__reportConfigType__aperiodic__F1 CSI_ReportConfig__reportConfigType__aperiodic__F2 CSI_ReportConfig__reportConfigType__aperiodic__F1F2_cond  CSI_ReportConfig__reportConfigType__aperiodic__F1F2_cond2 CSI_ReportConfig__reportConfigType__aperiodic__F2F1_cond.
Opaque CSI_ReportConfig__reportConfigType__aperiodic__cond CSI_ReportConfig__reportConfigType__aperiodic__Format.


Definition CSI_ReportConfig__reportConfigType__Format_Type := Eval cbn in get_formats CSI_ReportConfig__reportConfigType__list.
Definition CSI_ReportConfig__reportConfigType__Format_list : CSI_ReportConfig__reportConfigType__Format_Type :=
  (CSI_ReportConfig__reportConfigType__periodic__Format, (CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Format, (CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Format, (CSI_ReportConfig__reportConfigType__aperiodic__Format, unit__Format)))).
Definition CSI_ReportConfig__reportConfigType__list__Format := Eval compute in choice_format CSI_ReportConfig__reportConfigType__list CSI_ReportConfig__reportConfigType__len_helper1 CSI_ReportConfig__reportConfigType__len_helper2  CSI_ReportConfig__reportConfigType__Format_list.
Definition CSI_ReportConfig__reportConfigType__F1 (z : CSI_ReportConfig__reportConfigType__Type) : (choice CSI_ReportConfig__reportConfigType__list) :=
  match z with
   | CSI_ReportConfig__reportConfigType__periodic t => existT _ 0 t
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH t => existT _ 1 t
  | CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH t => existT _ 2 t
  | CSI_ReportConfig__reportConfigType__aperiodic t => existT _ 3 t
  end.
Definition CSI_ReportConfig__reportConfigType__g := (fun n => typ_set (get_nth_typ CSI_ReportConfig__reportConfigType__list n)).
Definition CSI_ReportConfig__reportConfigType__F2 (y : choice CSI_ReportConfig__reportConfigType__list) : CSI_ReportConfig__reportConfigType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ReportConfig__reportConfigType__g n -> CSI_ReportConfig__reportConfigType__Type) with
    | 0 => fun (t : CSI_ReportConfig__reportConfigType__periodic__Type) => CSI_ReportConfig__reportConfigType__periodic t 
    | 1 => fun (t : CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH__Type) => CSI_ReportConfig__reportConfigType__semiPersistentOnPUCCH t 
    | 2 => fun (t : CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH__Type) => CSI_ReportConfig__reportConfigType__semiPersistentOnPUSCH t 
    | 3 => fun (t : CSI_ReportConfig__reportConfigType__aperiodic__Type) => CSI_ReportConfig__reportConfigType__aperiodic t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : CSI_ReportConfig__reportConfigType__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ CSI_ReportConfig__reportConfigType__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_ReportConfig__reportConfigType__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return CSI_ReportConfig__reportConfigType__Type with end) n0
           end t0).

Lemma CSI_ReportConfig__reportConfigType__helper2 :  forall (y : CSI_ReportConfig__reportConfigType__Type), CSI_ReportConfig__reportConfigType__cond y -> choice_cond CSI_ReportConfig__reportConfigType__list (CSI_ReportConfig__reportConfigType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ReportConfig__reportConfigType__helper3 :  forall (y : CSI_ReportConfig__reportConfigType__Type), CSI_ReportConfig__reportConfigType__F2 (CSI_ReportConfig__reportConfigType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ReportConfig__reportConfigType__helper4 : (forall b : choice CSI_ReportConfig__reportConfigType__list, choice_cond CSI_ReportConfig__reportConfigType__list b -> CSI_ReportConfig__reportConfigType__cond (CSI_ReportConfig__reportConfigType__F2 b) /\ CSI_ReportConfig__reportConfigType__F1 (CSI_ReportConfig__reportConfigType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ReportConfig__reportConfigType__F1 CSI_ReportConfig__reportConfigType__F2.
Definition CSI_ReportConfig__reportConfigType__Format : T_Format CSI_ReportConfig__reportConfigType__Type CSI_ReportConfig__reportConfigType__cond :=
  (* Eval compute in *) proj2_format CSI_ReportConfig__reportConfigType__cond CSI_ReportConfig__reportConfigType__list__Format CSI_ReportConfig__reportConfigType__F1 CSI_ReportConfig__reportConfigType__F2 CSI_ReportConfig__reportConfigType__helper2 CSI_ReportConfig__reportConfigType__helper3 CSI_ReportConfig__reportConfigType__helper4.
Opaque CSI_ReportConfig__reportConfigType__cond CSI_ReportConfig__reportConfigType__Format.

Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Format : T_Format CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__nat__Format CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F1 CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F2 CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F1F2 CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__F2F1.

Opaque CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__cond CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Format.


Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list.
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Format_list : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Format_Type :=
  (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI__Format, unit_format).
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Format_list.
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1 z :=
  (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__pdsch_BundleSizeForCSI z, tt).
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F2 (y : seq_type CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list) :=
  match y with
  | (i0, _)=>
    make__CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type i0
  end.
Lemma CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1F2_cond (z : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type)
  : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond z ->
  (seq_cond CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1 z)).
intro H. unfold CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1F2_cond2 (z : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type)
 : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F2 (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F2F1_cond (y : seq_type CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list)
  : seq_cond CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list y ->
 (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F2 y)) /\  CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1 (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Format : T_Format CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond :=
        proj2_format  CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__list__Format
    CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1 CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F2 CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1F2_cond  CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F1F2_cond2 CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__F2F1_cond.
Opaque CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__cond CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Format.


Definition CSI_ReportConfig__reportQuantity__Format_Type := Eval cbn in get_formats CSI_ReportConfig__reportQuantity__list.
Definition CSI_ReportConfig__reportQuantity__Format_list : CSI_ReportConfig__reportQuantity__Format_Type :=
  (unit__Format, (unit__Format, (unit__Format, (CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Format, (unit__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))))))).
Definition CSI_ReportConfig__reportQuantity__list__Format := Eval compute in choice_format CSI_ReportConfig__reportQuantity__list CSI_ReportConfig__reportQuantity__len_helper1 CSI_ReportConfig__reportQuantity__len_helper2  CSI_ReportConfig__reportQuantity__Format_list.
Definition CSI_ReportConfig__reportQuantity__F1 (z : CSI_ReportConfig__reportQuantity__Type) : (choice CSI_ReportConfig__reportQuantity__list) :=
  match z with
   | CSI_ReportConfig__reportQuantity__none t => existT _ 0 t
  | CSI_ReportConfig__reportQuantity__cri_RI_PMI_CQI t => existT _ 1 t
  | CSI_ReportConfig__reportQuantity__cri_RI_i1 t => existT _ 2 t
  | CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI t => existT _ 3 t
  | CSI_ReportConfig__reportQuantity__cri_RI_CQI t => existT _ 4 t
  | CSI_ReportConfig__reportQuantity__cri_RSRP t => existT _ 5 t
  | CSI_ReportConfig__reportQuantity__ssb_Index_RSRP t => existT _ 6 t
  | CSI_ReportConfig__reportQuantity__cri_RI_LI_PMI_CQI t => existT _ 7 t
  end.
Definition CSI_ReportConfig__reportQuantity__g := (fun n => typ_set (get_nth_typ CSI_ReportConfig__reportQuantity__list n)).
Definition CSI_ReportConfig__reportQuantity__F2 (y : choice CSI_ReportConfig__reportQuantity__list) : CSI_ReportConfig__reportQuantity__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ReportConfig__reportQuantity__g n -> CSI_ReportConfig__reportQuantity__Type) with
    | 0 => fun (t : unit) => CSI_ReportConfig__reportQuantity__none t 
    | 1 => fun (t : unit) => CSI_ReportConfig__reportQuantity__cri_RI_PMI_CQI t 
    | 2 => fun (t : unit) => CSI_ReportConfig__reportQuantity__cri_RI_i1 t 
    | 3 => fun (t : CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI__Type) => CSI_ReportConfig__reportQuantity__cri_RI_i1_CQI t 
    | 4 => fun (t : unit) => CSI_ReportConfig__reportQuantity__cri_RI_CQI t 
    | 5 => fun (t : unit) => CSI_ReportConfig__reportQuantity__cri_RSRP t 
    | 6 => fun (t : unit) => CSI_ReportConfig__reportQuantity__ssb_Index_RSRP t 
    | 7 => fun (t : unit) => CSI_ReportConfig__reportQuantity__cri_RI_LI_PMI_CQI t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : CSI_ReportConfig__reportQuantity__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ CSI_ReportConfig__reportQuantity__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_ReportConfig__reportQuantity__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return CSI_ReportConfig__reportQuantity__Type with end) n0
           end t0).

Lemma CSI_ReportConfig__reportQuantity__helper2 :  forall (y : CSI_ReportConfig__reportQuantity__Type), CSI_ReportConfig__reportQuantity__cond y -> choice_cond CSI_ReportConfig__reportQuantity__list (CSI_ReportConfig__reportQuantity__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ReportConfig__reportQuantity__helper3 :  forall (y : CSI_ReportConfig__reportQuantity__Type), CSI_ReportConfig__reportQuantity__F2 (CSI_ReportConfig__reportQuantity__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ReportConfig__reportQuantity__helper4 : (forall b : choice CSI_ReportConfig__reportQuantity__list, choice_cond CSI_ReportConfig__reportQuantity__list b -> CSI_ReportConfig__reportQuantity__cond (CSI_ReportConfig__reportQuantity__F2 b) /\ CSI_ReportConfig__reportQuantity__F1 (CSI_ReportConfig__reportQuantity__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ReportConfig__reportQuantity__F1 CSI_ReportConfig__reportQuantity__F2.
Definition CSI_ReportConfig__reportQuantity__Format : T_Format CSI_ReportConfig__reportQuantity__Type CSI_ReportConfig__reportQuantity__cond :=
  (* Eval compute in *) proj2_format CSI_ReportConfig__reportQuantity__cond CSI_ReportConfig__reportQuantity__list__Format CSI_ReportConfig__reportQuantity__F1 CSI_ReportConfig__reportQuantity__F2 CSI_ReportConfig__reportQuantity__helper2 CSI_ReportConfig__reportQuantity__helper3 CSI_ReportConfig__reportQuantity__helper4.
Opaque CSI_ReportConfig__reportQuantity__cond CSI_ReportConfig__reportQuantity__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__nat__Format CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F1 CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F2 CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F1F2 CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__F2F1.

Opaque CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__cond CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__nat__Format CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F1 CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F2 CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F1F2 CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__F2F1.

Opaque CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__cond CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__cond := (* Eval compute in *) bit_string_fixed_format 3.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__cond := (* Eval compute in *) bit_string_fixed_format 5.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__cond := (* Eval compute in *) bit_string_fixed_format 6.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__cond := (* Eval compute in *) bit_string_fixed_format 7.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__cond := (* Eval compute in *) bit_string_fixed_format 9.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__cond := (* Eval compute in *) bit_string_fixed_format 11.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__cond := (* Eval compute in *) bit_string_fixed_format 12.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__cond := (* Eval compute in *) bit_string_fixed_format 13.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__cond := (* Eval compute in *) bit_string_fixed_format 14.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__cond := (* Eval compute in *) bit_string_fixed_format 15.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__cond := (* Eval compute in *) bit_string_fixed_format 17.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__cond := (* Eval compute in *) bit_string_fixed_format 18.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__Format.


Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Format_Type := Eval cbn in get_formats CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Format_list : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Format_Type :=
  (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__Format, unit__Format)))))))))))))))).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list__Format := Eval compute in choice_format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__len_helper1 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__len_helper2  CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Format_list.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F1 (z : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type) : (choice CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list) :=
  match z with
   | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3 t => existT _ 0 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4 t => existT _ 1 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5 t => existT _ 2 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6 t => existT _ 3 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7 t => existT _ 4 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8 t => existT _ 5 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9 t => existT _ 6 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10 t => existT _ 7 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11 t => existT _ 8 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12 t => existT _ 9 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13 t => existT _ 10 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14 t => existT _ 11 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15 t => existT _ 12 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16 t => existT _ 13 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17 t => existT _ 14 t
  | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18 t => existT _ 15 t
  end.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__g := (fun n => typ_set (get_nth_typ CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list n)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F2 (y : choice CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list) : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__g n -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type) with
    | 0 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands3 t 
    | 1 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands4 t 
    | 2 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands5 t 
    | 3 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands6 t 
    | 4 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands7 t 
    | 5 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands8 t 
    | 6 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands9 t 
    | 7 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands10 t 
    | 8 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands11 t 
    | 9 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands12 t 
    | 10 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands13 t 
    | 11 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands14 t 
    | 12 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands15 t 
    | 13 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands16 t 
    | 14 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands17 t 
    | 15 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__subbands18 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0)))))))))))))))) => (fun (x' : nat) (t'' : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))))))))) in match t' return CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type with end) n0
           end t0).

Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__helper2 :  forall (y : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type), CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__cond y -> choice_cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__helper3 :  forall (y : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type), CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F2 (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__helper4 : (forall b : choice CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list, choice_cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list b -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__cond (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F2 b) /\ CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F1 (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F1 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F2.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__cond :=
  (* Eval compute in *) proj2_format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__list__Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F1 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__F2 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__helper2 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__helper3 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__helper4.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__cond := (* Eval compute in *) bit_string_fixed_format 19.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__Format.


Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Format_Type := Eval cbn in get_formats CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Format_list : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Format_Type :=
  (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__Format, unit__Format).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list__Format := Eval compute in choice_ext_format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Format_list.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F1 (z : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type) : (choice CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list) :=
  match z with
   | CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530 t => existT _ 0 t
  end.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__g := (fun n => typ_set (get_nth_typ CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list n)).
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F2 (y : choice CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list) : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__g n -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type) with
    | 0 => fun (t : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530__Type) => CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__subbands19_v1530 t 
 | (S n0) => (fun (x' : nat) (t'' : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__g (S x')) =>let t' :=
                       eq_rect (get_nth_typ CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list (S x'))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list (S x')
                       (le_n_S _ _ (le_0_n x'))) in match t' return CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type with end) n0
                       end t0).

Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__helper2 :  forall (y : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type), CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__cond y -> choice_cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__helper3 :  forall (y : CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type), CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F2 (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__helper4 : (forall b : choice CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list, choice_cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list b -> CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__cond (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F2 b) /\ CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F1 (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F1 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F2.
Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__cond :=
          proj2_format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__list__Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F1 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__F2 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__helper2 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__helper3 CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__helper4.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Format.

Definition CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__Type CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__cond := sum_format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__root__Format CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__ext__Format.
Opaque CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__cond CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__Format.


Definition CSI_ReportConfig__reportFreqConfiguration__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__reportFreqConfiguration__list.
Definition CSI_ReportConfig__reportFreqConfiguration__Format_list : CSI_ReportConfig__reportFreqConfiguration__Format_Type :=
  (CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator__Format, (CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator__Format, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand__Format, unit_format))).
Definition CSI_ReportConfig__reportFreqConfiguration__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__reportFreqConfiguration__list CSI_ReportConfig__reportFreqConfiguration__Format_list.
Definition CSI_ReportConfig__reportFreqConfiguration__F1 z :=
  (CSI_ReportConfig__reportFreqConfiguration__cqi_FormatIndicator z, (CSI_ReportConfig__reportFreqConfiguration__pmi_FormatIndicator z, (CSI_ReportConfig__reportFreqConfiguration__csi_ReportingBand z, tt))).
Definition CSI_ReportConfig__reportFreqConfiguration__F2 (y : seq_type CSI_ReportConfig__reportFreqConfiguration__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CSI_ReportConfig__reportFreqConfiguration__Type i0 i1 i2
  end.
Lemma CSI_ReportConfig__reportFreqConfiguration__F1F2_cond (z : CSI_ReportConfig__reportFreqConfiguration__Type)
  : CSI_ReportConfig__reportFreqConfiguration__cond z ->
  (seq_cond CSI_ReportConfig__reportFreqConfiguration__list (CSI_ReportConfig__reportFreqConfiguration__F1 z)).
intro H. unfold CSI_ReportConfig__reportFreqConfiguration__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportFreqConfiguration__F1F2_cond2 (z : CSI_ReportConfig__reportFreqConfiguration__Type)
 : CSI_ReportConfig__reportFreqConfiguration__F2 (CSI_ReportConfig__reportFreqConfiguration__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__reportFreqConfiguration__F2F1_cond (y : seq_type CSI_ReportConfig__reportFreqConfiguration__list)
  : seq_cond CSI_ReportConfig__reportFreqConfiguration__list y ->
 (CSI_ReportConfig__reportFreqConfiguration__cond (CSI_ReportConfig__reportFreqConfiguration__F2 y)) /\  CSI_ReportConfig__reportFreqConfiguration__F1 (CSI_ReportConfig__reportFreqConfiguration__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__reportFreqConfiguration__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__reportFreqConfiguration__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__reportFreqConfiguration__Format : T_Format CSI_ReportConfig__reportFreqConfiguration__Type CSI_ReportConfig__reportFreqConfiguration__cond :=
        proj2_format  CSI_ReportConfig__reportFreqConfiguration__cond CSI_ReportConfig__reportFreqConfiguration__list__Format
    CSI_ReportConfig__reportFreqConfiguration__F1 CSI_ReportConfig__reportFreqConfiguration__F2 CSI_ReportConfig__reportFreqConfiguration__F1F2_cond  CSI_ReportConfig__reportFreqConfiguration__F1F2_cond2 CSI_ReportConfig__reportFreqConfiguration__F2F1_cond.
Opaque CSI_ReportConfig__reportFreqConfiguration__cond CSI_ReportConfig__reportFreqConfiguration__Format.

Definition CSI_ReportConfig__timeRestrictionForChannelMeasurements__Format : T_Format CSI_ReportConfig__timeRestrictionForChannelMeasurements__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__timeRestrictionForChannelMeasurements__nat__Format CSI_ReportConfig__timeRestrictionForChannelMeasurements__F1 CSI_ReportConfig__timeRestrictionForChannelMeasurements__F2 CSI_ReportConfig__timeRestrictionForChannelMeasurements__F1F2 CSI_ReportConfig__timeRestrictionForChannelMeasurements__F2F1.

Opaque CSI_ReportConfig__timeRestrictionForChannelMeasurements__cond CSI_ReportConfig__timeRestrictionForChannelMeasurements__Format.

Definition CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Format : T_Format CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__nat__Format CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F1 CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F2 CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F1F2 CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__F2F1.

Opaque CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__cond CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Format.

Definition CSI_ReportConfig__dummy__Format : T_Format CSI_ReportConfig__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__dummy__nat__Format CSI_ReportConfig__dummy__F1 CSI_ReportConfig__dummy__F2 CSI_ReportConfig__dummy__F1F2 CSI_ReportConfig__dummy__F2F1.

Opaque CSI_ReportConfig__dummy__cond CSI_ReportConfig__dummy__Format.

Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Format : T_Format CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__nat__Format CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F1 CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F2 CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F1F2 CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__F2F1.

Opaque CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__cond CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Format.


Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__groupBasedBeamReporting__disabled__list.
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__Format_list : CSI_ReportConfig__groupBasedBeamReporting__disabled__Format_Type :=
  (CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS__Format, unit_format).
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__groupBasedBeamReporting__disabled__list CSI_ReportConfig__groupBasedBeamReporting__disabled__Format_list.
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__F1 z :=
  (CSI_ReportConfig__groupBasedBeamReporting__disabled__nrofReportedRS z, tt).
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__F2 (y : seq_type CSI_ReportConfig__groupBasedBeamReporting__disabled__list) :=
  match y with
  | (i0, _)=>
    make__CSI_ReportConfig__groupBasedBeamReporting__disabled__Type i0
  end.
Lemma CSI_ReportConfig__groupBasedBeamReporting__disabled__F1F2_cond (z : CSI_ReportConfig__groupBasedBeamReporting__disabled__Type)
  : CSI_ReportConfig__groupBasedBeamReporting__disabled__cond z ->
  (seq_cond CSI_ReportConfig__groupBasedBeamReporting__disabled__list (CSI_ReportConfig__groupBasedBeamReporting__disabled__F1 z)).
intro H. unfold CSI_ReportConfig__groupBasedBeamReporting__disabled__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__groupBasedBeamReporting__disabled__F1F2_cond2 (z : CSI_ReportConfig__groupBasedBeamReporting__disabled__Type)
 : CSI_ReportConfig__groupBasedBeamReporting__disabled__F2 (CSI_ReportConfig__groupBasedBeamReporting__disabled__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__groupBasedBeamReporting__disabled__F2F1_cond (y : seq_type CSI_ReportConfig__groupBasedBeamReporting__disabled__list)
  : seq_cond CSI_ReportConfig__groupBasedBeamReporting__disabled__list y ->
 (CSI_ReportConfig__groupBasedBeamReporting__disabled__cond (CSI_ReportConfig__groupBasedBeamReporting__disabled__F2 y)) /\  CSI_ReportConfig__groupBasedBeamReporting__disabled__F1 (CSI_ReportConfig__groupBasedBeamReporting__disabled__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__groupBasedBeamReporting__disabled__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__groupBasedBeamReporting__disabled__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__groupBasedBeamReporting__disabled__Format : T_Format CSI_ReportConfig__groupBasedBeamReporting__disabled__Type CSI_ReportConfig__groupBasedBeamReporting__disabled__cond :=
        proj2_format  CSI_ReportConfig__groupBasedBeamReporting__disabled__cond CSI_ReportConfig__groupBasedBeamReporting__disabled__list__Format
    CSI_ReportConfig__groupBasedBeamReporting__disabled__F1 CSI_ReportConfig__groupBasedBeamReporting__disabled__F2 CSI_ReportConfig__groupBasedBeamReporting__disabled__F1F2_cond  CSI_ReportConfig__groupBasedBeamReporting__disabled__F1F2_cond2 CSI_ReportConfig__groupBasedBeamReporting__disabled__F2F1_cond.
Opaque CSI_ReportConfig__groupBasedBeamReporting__disabled__cond CSI_ReportConfig__groupBasedBeamReporting__disabled__Format.


Definition CSI_ReportConfig__groupBasedBeamReporting__Format_Type := Eval cbn in get_formats CSI_ReportConfig__groupBasedBeamReporting__list.
Definition CSI_ReportConfig__groupBasedBeamReporting__Format_list : CSI_ReportConfig__groupBasedBeamReporting__Format_Type :=
  (unit__Format, (CSI_ReportConfig__groupBasedBeamReporting__disabled__Format, unit__Format)).
Definition CSI_ReportConfig__groupBasedBeamReporting__list__Format := Eval compute in choice_format CSI_ReportConfig__groupBasedBeamReporting__list CSI_ReportConfig__groupBasedBeamReporting__len_helper1 CSI_ReportConfig__groupBasedBeamReporting__len_helper2  CSI_ReportConfig__groupBasedBeamReporting__Format_list.
Definition CSI_ReportConfig__groupBasedBeamReporting__F1 (z : CSI_ReportConfig__groupBasedBeamReporting__Type) : (choice CSI_ReportConfig__groupBasedBeamReporting__list) :=
  match z with
   | CSI_ReportConfig__groupBasedBeamReporting__enabled t => existT _ 0 t
  | CSI_ReportConfig__groupBasedBeamReporting__disabled t => existT _ 1 t
  end.
Definition CSI_ReportConfig__groupBasedBeamReporting__g := (fun n => typ_set (get_nth_typ CSI_ReportConfig__groupBasedBeamReporting__list n)).
Definition CSI_ReportConfig__groupBasedBeamReporting__F2 (y : choice CSI_ReportConfig__groupBasedBeamReporting__list) : CSI_ReportConfig__groupBasedBeamReporting__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ReportConfig__groupBasedBeamReporting__g n -> CSI_ReportConfig__groupBasedBeamReporting__Type) with
    | 0 => fun (t : unit) => CSI_ReportConfig__groupBasedBeamReporting__enabled t 
    | 1 => fun (t : CSI_ReportConfig__groupBasedBeamReporting__disabled__Type) => CSI_ReportConfig__groupBasedBeamReporting__disabled t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CSI_ReportConfig__groupBasedBeamReporting__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CSI_ReportConfig__groupBasedBeamReporting__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_ReportConfig__groupBasedBeamReporting__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CSI_ReportConfig__groupBasedBeamReporting__Type with end) n0
           end t0).

Lemma CSI_ReportConfig__groupBasedBeamReporting__helper2 :  forall (y : CSI_ReportConfig__groupBasedBeamReporting__Type), CSI_ReportConfig__groupBasedBeamReporting__cond y -> choice_cond CSI_ReportConfig__groupBasedBeamReporting__list (CSI_ReportConfig__groupBasedBeamReporting__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ReportConfig__groupBasedBeamReporting__helper3 :  forall (y : CSI_ReportConfig__groupBasedBeamReporting__Type), CSI_ReportConfig__groupBasedBeamReporting__F2 (CSI_ReportConfig__groupBasedBeamReporting__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ReportConfig__groupBasedBeamReporting__helper4 : (forall b : choice CSI_ReportConfig__groupBasedBeamReporting__list, choice_cond CSI_ReportConfig__groupBasedBeamReporting__list b -> CSI_ReportConfig__groupBasedBeamReporting__cond (CSI_ReportConfig__groupBasedBeamReporting__F2 b) /\ CSI_ReportConfig__groupBasedBeamReporting__F1 (CSI_ReportConfig__groupBasedBeamReporting__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ReportConfig__groupBasedBeamReporting__F1 CSI_ReportConfig__groupBasedBeamReporting__F2.
Definition CSI_ReportConfig__groupBasedBeamReporting__Format : T_Format CSI_ReportConfig__groupBasedBeamReporting__Type CSI_ReportConfig__groupBasedBeamReporting__cond :=
  (* Eval compute in *) proj2_format CSI_ReportConfig__groupBasedBeamReporting__cond CSI_ReportConfig__groupBasedBeamReporting__list__Format CSI_ReportConfig__groupBasedBeamReporting__F1 CSI_ReportConfig__groupBasedBeamReporting__F2 CSI_ReportConfig__groupBasedBeamReporting__helper2 CSI_ReportConfig__groupBasedBeamReporting__helper3 CSI_ReportConfig__groupBasedBeamReporting__helper4.
Opaque CSI_ReportConfig__groupBasedBeamReporting__cond CSI_ReportConfig__groupBasedBeamReporting__Format.

Definition CSI_ReportConfig__cqi_Table__Format : T_Format CSI_ReportConfig__cqi_Table__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__cqi_Table__nat__Format CSI_ReportConfig__cqi_Table__F1 CSI_ReportConfig__cqi_Table__F2 CSI_ReportConfig__cqi_Table__F1F2 CSI_ReportConfig__cqi_Table__F2F1.

Opaque CSI_ReportConfig__cqi_Table__cond CSI_ReportConfig__cqi_Table__Format.

Definition CSI_ReportConfig__subbandSize__Format : T_Format CSI_ReportConfig__subbandSize__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__subbandSize__nat__Format CSI_ReportConfig__subbandSize__F1 CSI_ReportConfig__subbandSize__F2 CSI_ReportConfig__subbandSize__F1F2 CSI_ReportConfig__subbandSize__F2F1.

Opaque CSI_ReportConfig__subbandSize__cond CSI_ReportConfig__subbandSize__Format.

Definition CSI_ReportConfig__non_PMI_PortIndication__Format : T_Format CSI_ReportConfig__non_PMI_PortIndication__Type CSI_ReportConfig__non_PMI_PortIndication__cond := seq_of_format PortIndexFor8Ranks__Format 1 maxNrofNZP_CSI_RS_ResourcesPerConfig CSI_ReportConfig__non_PMI_PortIndication__helper1 CSI_ReportConfig__non_PMI_PortIndication__helper2.

Opaque CSI_ReportConfig__non_PMI_PortIndication__cond CSI_ReportConfig__non_PMI_PortIndication__Format.

Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Format : T_Format CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__nat__Format CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F1 CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F2 CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F1F2 CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__F2F1.

Opaque CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__cond CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Format.


Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list.
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Format_list : CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Format_Type :=
  (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530__Format, unit_format).
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Format_list.
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1 z :=
  (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__reportSlotConfig_v1530 z, tt).
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F2 (y : seq_type CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list) :=
  match y with
  | (i0, _)=>
    make__CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Type i0
  end.
Lemma CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1F2_cond (z : CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Type)
  : CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond z ->
  (seq_cond CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1 z)).
intro H. unfold CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1F2_cond2 (z : CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Type)
 : CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F2 (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F2F1_cond (y : seq_type CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list)
  : seq_cond CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list y ->
 (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F2 y)) /\  CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1 (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Format : T_Format CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Type CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond :=
        proj2_format  CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__list__Format
    CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1 CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F2 CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1F2_cond  CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F1F2_cond2 CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__F2F1_cond.
Opaque CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__cond CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Format.


Definition CSI_ReportConfig__ext0O__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext0O__list.
Definition CSI_ReportConfig__ext0O__Format_list : CSI_ReportConfig__ext0O__Format_Type :=
  (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530__Format, unit_format).
Definition CSI_ReportConfig__ext0O__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext0O__list CSI_ReportConfig__ext0O__Format_list.
Definition CSI_ReportConfig__ext0O__F1 z :=
  (CSI_ReportConfig__ext0O__semiPersistentOnPUSCH_v1530 z, tt).
Definition CSI_ReportConfig__ext0O__F2 (y : seq_type CSI_ReportConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CSI_ReportConfig__ext0O__Type i0
  end.
Lemma CSI_ReportConfig__ext0O__F1F2_cond (z : CSI_ReportConfig__ext0O__Type)
  : CSI_ReportConfig__ext0O__cond z ->
  (seq_cond CSI_ReportConfig__ext0O__list (CSI_ReportConfig__ext0O__F1 z)).
intro H. unfold CSI_ReportConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext0O__F1F2_cond2 (z : CSI_ReportConfig__ext0O__Type)
 : CSI_ReportConfig__ext0O__F2 (CSI_ReportConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext0O__F2F1_cond (y : seq_type CSI_ReportConfig__ext0O__list)
  : seq_cond CSI_ReportConfig__ext0O__list y ->
 (CSI_ReportConfig__ext0O__cond (CSI_ReportConfig__ext0O__F2 y)) /\  CSI_ReportConfig__ext0O__F1 (CSI_ReportConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext0O__Format : T_Format CSI_ReportConfig__ext0O__Type CSI_ReportConfig__ext0O__cond :=
        proj2_format  CSI_ReportConfig__ext0O__cond CSI_ReportConfig__ext0O__list__Format
    CSI_ReportConfig__ext0O__F1 CSI_ReportConfig__ext0O__F2 CSI_ReportConfig__ext0O__F1F2_cond  CSI_ReportConfig__ext0O__F1F2_cond2 CSI_ReportConfig__ext0O__F2F1_cond.
Opaque CSI_ReportConfig__ext0O__cond CSI_ReportConfig__ext0O__Format.

Definition CSI_ReportConfig__ext0__check_all_none (b : CSI_ReportConfig__ext0O__Type) : bool :=
match b with 
  | make__CSI_ReportConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CSI_ReportConfig__ext0__Format : T_Format CSI_ReportConfig__ext0__Type CSI_ReportConfig__ext0__cond :=
  restrict_add_format CSI_ReportConfig__ext0__check_all_none CSI_ReportConfig__ext0O__Format.

Opaque CSI_ReportConfig__ext0__cond CSI_ReportConfig__ext0__Format.

Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__Format : T_Format Z CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__cond :=
 ranged_int_format (0) (32) CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper1 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper2.

Opaque CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__Format.

Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__Format : T_Format CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__Type CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__cond := seq_of_format CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__helper1 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__helper2.

Opaque CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__Format.

Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__Format : T_Format Z CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__cond :=
 ranged_int_format (0) (32) CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper1 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper2.

Opaque CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__Format.

Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__Format : T_Format CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__Type CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__cond := seq_of_format CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__helper1 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__helper2.

Opaque CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__Format.


Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Format_list : CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Format_Type :=
  (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16__Format, (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16__Format, unit_format)).
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Format_list.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1 z :=
  (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_2_r16 z, (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__reportSlotOffsetListDCI_0_1_r16 z, tt)).
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F2 (y : seq_type CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Type i0 i1
  end.
Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1F2_cond (z : CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Type)
  : CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond z ->
  (seq_cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1 z)).
intro H. unfold CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1F2_cond2 (z : CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Type)
 : CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F2 (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F2F1_cond (y : seq_type CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list)
  : seq_cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list y ->
 (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F2 y)) /\  CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1 (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Format : T_Format CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Type CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond :=
        proj2_format  CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__list__Format
    CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F2 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1F2_cond  CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F1F2_cond2 CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__F2F1_cond.
Opaque CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__cond CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Format.

Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__Format : T_Format Z CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__cond :=
 ranged_int_format (0) (32) CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper1 CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__helper2.

Opaque CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__cond CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__Format.

Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__Format : T_Format CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__Type CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__cond := seq_of_format CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__helper1 CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__helper2.

Opaque CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__cond CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__Format.

Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__Format : T_Format Z CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__cond :=
 ranged_int_format (0) (32) CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper1 CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__helper2.

Opaque CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__cond CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__Format.

Definition CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__Format : T_Format CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__Type CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__cond := seq_of_format CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__helper1 CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__helper2.

Opaque CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__cond CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__Format.


Definition CSI_ReportConfig__ext1O__aperiodic_v1610__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext1O__aperiodic_v1610__list.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__Format_list : CSI_ReportConfig__ext1O__aperiodic_v1610__Format_Type :=
  (CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16__Format, (CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16__Format, unit_format)).
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext1O__aperiodic_v1610__list CSI_ReportConfig__ext1O__aperiodic_v1610__Format_list.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__F1 z :=
  (CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_2_r16 z, (CSI_ReportConfig__ext1O__aperiodic_v1610__reportSlotOffsetListDCI_0_1_r16 z, tt)).
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__F2 (y : seq_type CSI_ReportConfig__ext1O__aperiodic_v1610__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_ReportConfig__ext1O__aperiodic_v1610__Type i0 i1
  end.
Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__F1F2_cond (z : CSI_ReportConfig__ext1O__aperiodic_v1610__Type)
  : CSI_ReportConfig__ext1O__aperiodic_v1610__cond z ->
  (seq_cond CSI_ReportConfig__ext1O__aperiodic_v1610__list (CSI_ReportConfig__ext1O__aperiodic_v1610__F1 z)).
intro H. unfold CSI_ReportConfig__ext1O__aperiodic_v1610__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__F1F2_cond2 (z : CSI_ReportConfig__ext1O__aperiodic_v1610__Type)
 : CSI_ReportConfig__ext1O__aperiodic_v1610__F2 (CSI_ReportConfig__ext1O__aperiodic_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext1O__aperiodic_v1610__F2F1_cond (y : seq_type CSI_ReportConfig__ext1O__aperiodic_v1610__list)
  : seq_cond CSI_ReportConfig__ext1O__aperiodic_v1610__list y ->
 (CSI_ReportConfig__ext1O__aperiodic_v1610__cond (CSI_ReportConfig__ext1O__aperiodic_v1610__F2 y)) /\  CSI_ReportConfig__ext1O__aperiodic_v1610__F1 (CSI_ReportConfig__ext1O__aperiodic_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext1O__aperiodic_v1610__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext1O__aperiodic_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext1O__aperiodic_v1610__Format : T_Format CSI_ReportConfig__ext1O__aperiodic_v1610__Type CSI_ReportConfig__ext1O__aperiodic_v1610__cond :=
        proj2_format  CSI_ReportConfig__ext1O__aperiodic_v1610__cond CSI_ReportConfig__ext1O__aperiodic_v1610__list__Format
    CSI_ReportConfig__ext1O__aperiodic_v1610__F1 CSI_ReportConfig__ext1O__aperiodic_v1610__F2 CSI_ReportConfig__ext1O__aperiodic_v1610__F1F2_cond  CSI_ReportConfig__ext1O__aperiodic_v1610__F1F2_cond2 CSI_ReportConfig__ext1O__aperiodic_v1610__F2F1_cond.
Opaque CSI_ReportConfig__ext1O__aperiodic_v1610__cond CSI_ReportConfig__ext1O__aperiodic_v1610__Format.


Definition CSI_ReportConfig__ext1O__reportQuantity_r16__Format_Type := Eval cbn in get_formats CSI_ReportConfig__ext1O__reportQuantity_r16__list.
Definition CSI_ReportConfig__ext1O__reportQuantity_r16__Format_list : CSI_ReportConfig__ext1O__reportQuantity_r16__Format_Type :=
  (unit__Format, (unit__Format, unit__Format)).
Definition CSI_ReportConfig__ext1O__reportQuantity_r16__list__Format := Eval compute in choice_format CSI_ReportConfig__ext1O__reportQuantity_r16__list CSI_ReportConfig__ext1O__reportQuantity_r16__len_helper1 CSI_ReportConfig__ext1O__reportQuantity_r16__len_helper2  CSI_ReportConfig__ext1O__reportQuantity_r16__Format_list.
Definition CSI_ReportConfig__ext1O__reportQuantity_r16__F1 (z : CSI_ReportConfig__ext1O__reportQuantity_r16__Type) : (choice CSI_ReportConfig__ext1O__reportQuantity_r16__list) :=
  match z with
   | CSI_ReportConfig__ext1O__reportQuantity_r16__cri_SINR_r16 t => existT _ 0 t
  | CSI_ReportConfig__ext1O__reportQuantity_r16__ssb_Index_SINR_r16 t => existT _ 1 t
  end.
Definition CSI_ReportConfig__ext1O__reportQuantity_r16__g := (fun n => typ_set (get_nth_typ CSI_ReportConfig__ext1O__reportQuantity_r16__list n)).
Definition CSI_ReportConfig__ext1O__reportQuantity_r16__F2 (y : choice CSI_ReportConfig__ext1O__reportQuantity_r16__list) : CSI_ReportConfig__ext1O__reportQuantity_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ReportConfig__ext1O__reportQuantity_r16__g n -> CSI_ReportConfig__ext1O__reportQuantity_r16__Type) with
    | 0 => fun (t : unit) => CSI_ReportConfig__ext1O__reportQuantity_r16__cri_SINR_r16 t 
    | 1 => fun (t : unit) => CSI_ReportConfig__ext1O__reportQuantity_r16__ssb_Index_SINR_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : CSI_ReportConfig__ext1O__reportQuantity_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ CSI_ReportConfig__ext1O__reportQuantity_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_ReportConfig__ext1O__reportQuantity_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return CSI_ReportConfig__ext1O__reportQuantity_r16__Type with end) n0
           end t0).

Lemma CSI_ReportConfig__ext1O__reportQuantity_r16__helper2 :  forall (y : CSI_ReportConfig__ext1O__reportQuantity_r16__Type), CSI_ReportConfig__ext1O__reportQuantity_r16__cond y -> choice_cond CSI_ReportConfig__ext1O__reportQuantity_r16__list (CSI_ReportConfig__ext1O__reportQuantity_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ReportConfig__ext1O__reportQuantity_r16__helper3 :  forall (y : CSI_ReportConfig__ext1O__reportQuantity_r16__Type), CSI_ReportConfig__ext1O__reportQuantity_r16__F2 (CSI_ReportConfig__ext1O__reportQuantity_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ReportConfig__ext1O__reportQuantity_r16__helper4 : (forall b : choice CSI_ReportConfig__ext1O__reportQuantity_r16__list, choice_cond CSI_ReportConfig__ext1O__reportQuantity_r16__list b -> CSI_ReportConfig__ext1O__reportQuantity_r16__cond (CSI_ReportConfig__ext1O__reportQuantity_r16__F2 b) /\ CSI_ReportConfig__ext1O__reportQuantity_r16__F1 (CSI_ReportConfig__ext1O__reportQuantity_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ReportConfig__ext1O__reportQuantity_r16__F1 CSI_ReportConfig__ext1O__reportQuantity_r16__F2.
Definition CSI_ReportConfig__ext1O__reportQuantity_r16__Format : T_Format CSI_ReportConfig__ext1O__reportQuantity_r16__Type CSI_ReportConfig__ext1O__reportQuantity_r16__cond :=
  (* Eval compute in *) proj2_format CSI_ReportConfig__ext1O__reportQuantity_r16__cond CSI_ReportConfig__ext1O__reportQuantity_r16__list__Format CSI_ReportConfig__ext1O__reportQuantity_r16__F1 CSI_ReportConfig__ext1O__reportQuantity_r16__F2 CSI_ReportConfig__ext1O__reportQuantity_r16__helper2 CSI_ReportConfig__ext1O__reportQuantity_r16__helper3 CSI_ReportConfig__ext1O__reportQuantity_r16__helper4.
Opaque CSI_ReportConfig__ext1O__reportQuantity_r16__cond CSI_ReportConfig__ext1O__reportQuantity_r16__Format.


Definition CSI_ReportConfig__ext1O__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext1O__list.
Definition CSI_ReportConfig__ext1O__Format_list : CSI_ReportConfig__ext1O__Format_Type :=
  (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610__Format, (CSI_ReportConfig__ext1O__aperiodic_v1610__Format, (CSI_ReportConfig__ext1O__reportQuantity_r16__Format, (CodebookConfig_r16__Format, unit_format)))).
Definition CSI_ReportConfig__ext1O__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext1O__list CSI_ReportConfig__ext1O__Format_list.
Definition CSI_ReportConfig__ext1O__F1 z :=
  (CSI_ReportConfig__ext1O__semiPersistentOnPUSCH_v1610 z, (CSI_ReportConfig__ext1O__aperiodic_v1610 z, (CSI_ReportConfig__ext1O__reportQuantity_r16 z, (CSI_ReportConfig__ext1O__codebookConfig_r16 z, tt)))).
Definition CSI_ReportConfig__ext1O__F2 (y : seq_type CSI_ReportConfig__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__CSI_ReportConfig__ext1O__Type i0 i1 i2 i3
  end.
Lemma CSI_ReportConfig__ext1O__F1F2_cond (z : CSI_ReportConfig__ext1O__Type)
  : CSI_ReportConfig__ext1O__cond z ->
  (seq_cond CSI_ReportConfig__ext1O__list (CSI_ReportConfig__ext1O__F1 z)).
intro H. unfold CSI_ReportConfig__ext1O__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext1O__F1F2_cond2 (z : CSI_ReportConfig__ext1O__Type)
 : CSI_ReportConfig__ext1O__F2 (CSI_ReportConfig__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext1O__F2F1_cond (y : seq_type CSI_ReportConfig__ext1O__list)
  : seq_cond CSI_ReportConfig__ext1O__list y ->
 (CSI_ReportConfig__ext1O__cond (CSI_ReportConfig__ext1O__F2 y)) /\  CSI_ReportConfig__ext1O__F1 (CSI_ReportConfig__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext1O__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext1O__Format : T_Format CSI_ReportConfig__ext1O__Type CSI_ReportConfig__ext1O__cond :=
        proj2_format  CSI_ReportConfig__ext1O__cond CSI_ReportConfig__ext1O__list__Format
    CSI_ReportConfig__ext1O__F1 CSI_ReportConfig__ext1O__F2 CSI_ReportConfig__ext1O__F1F2_cond  CSI_ReportConfig__ext1O__F1F2_cond2 CSI_ReportConfig__ext1O__F2F1_cond.
Opaque CSI_ReportConfig__ext1O__cond CSI_ReportConfig__ext1O__Format.

Definition CSI_ReportConfig__ext1__check_all_none (b : CSI_ReportConfig__ext1O__Type) : bool :=
match b with 
  | make__CSI_ReportConfig__ext1O__Type None None None None  => false 
  | _ => true 
 end.
Definition CSI_ReportConfig__ext1__Format : T_Format CSI_ReportConfig__ext1__Type CSI_ReportConfig__ext1__cond :=
  restrict_add_format CSI_ReportConfig__ext1__check_all_none CSI_ReportConfig__ext1O__Format.

Opaque CSI_ReportConfig__ext1__cond CSI_ReportConfig__ext1__Format.

Definition CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Format : T_Format CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__nat__Format CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F1 CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F2 CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F1F2 CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__F2F1.

Opaque CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__cond CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Format.

Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Format : T_Format CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__nat__Format CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F1 CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F2 CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F1F2 CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__F2F1.

Opaque CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__cond CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Format.


Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list.
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Format_list : CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Format_Type :=
  (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17__Format, unit_format).
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Format_list.
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1 z :=
  (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__nrofReportedGroups_r17 z, tt).
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F2 (y : seq_type CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list) :=
  match y with
  | (i0, _)=>
    make__CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Type i0
  end.
Lemma CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1F2_cond (z : CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Type)
  : CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond z ->
  (seq_cond CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1 z)).
intro H. unfold CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1F2_cond2 (z : CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Type)
 : CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F2 (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F2F1_cond (y : seq_type CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list)
  : seq_cond CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list y ->
 (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F2 y)) /\  CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1 (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Format : T_Format CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Type CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond :=
        proj2_format  CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__list__Format
    CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1 CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F2 CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1F2_cond  CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F1F2_cond2 CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__F2F1_cond.
Opaque CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__cond CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Format.

Definition CSI_ReportConfig__ext2O__sharedCMR_r17__Format : T_Format CSI_ReportConfig__ext2O__sharedCMR_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__ext2O__sharedCMR_r17__nat__Format CSI_ReportConfig__ext2O__sharedCMR_r17__F1 CSI_ReportConfig__ext2O__sharedCMR_r17__F2 CSI_ReportConfig__ext2O__sharedCMR_r17__F1F2 CSI_ReportConfig__ext2O__sharedCMR_r17__F2F1.

Opaque CSI_ReportConfig__ext2O__sharedCMR_r17__cond CSI_ReportConfig__ext2O__sharedCMR_r17__Format.

Definition CSI_ReportConfig__ext2O__csi_ReportMode_r17__Format : T_Format CSI_ReportConfig__ext2O__csi_ReportMode_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__ext2O__csi_ReportMode_r17__nat__Format CSI_ReportConfig__ext2O__csi_ReportMode_r17__F1 CSI_ReportConfig__ext2O__csi_ReportMode_r17__F2 CSI_ReportConfig__ext2O__csi_ReportMode_r17__F1F2 CSI_ReportConfig__ext2O__csi_ReportMode_r17__F2F1.

Opaque CSI_ReportConfig__ext2O__csi_ReportMode_r17__cond CSI_ReportConfig__ext2O__csi_ReportMode_r17__Format.

Definition CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Format : T_Format CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__nat__Format CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F1 CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F2 CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F1F2 CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__F2F1.

Opaque CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__cond CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Format.


Definition CSI_ReportConfig__ext2O__reportQuantity_r17__Format_Type := Eval cbn in get_formats CSI_ReportConfig__ext2O__reportQuantity_r17__list.
Definition CSI_ReportConfig__ext2O__reportQuantity_r17__Format_list : CSI_ReportConfig__ext2O__reportQuantity_r17__Format_Type :=
  (unit__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))).
Definition CSI_ReportConfig__ext2O__reportQuantity_r17__list__Format := Eval compute in choice_format CSI_ReportConfig__ext2O__reportQuantity_r17__list CSI_ReportConfig__ext2O__reportQuantity_r17__len_helper1 CSI_ReportConfig__ext2O__reportQuantity_r17__len_helper2  CSI_ReportConfig__ext2O__reportQuantity_r17__Format_list.
Definition CSI_ReportConfig__ext2O__reportQuantity_r17__F1 (z : CSI_ReportConfig__ext2O__reportQuantity_r17__Type) : (choice CSI_ReportConfig__ext2O__reportQuantity_r17__list) :=
  match z with
   | CSI_ReportConfig__ext2O__reportQuantity_r17__cri_RSRP_Index_r17 t => existT _ 0 t
  | CSI_ReportConfig__ext2O__reportQuantity_r17__ssb_Index_RSRP_Index_r17 t => existT _ 1 t
  | CSI_ReportConfig__ext2O__reportQuantity_r17__cri_SINR_Index_r17 t => existT _ 2 t
  | CSI_ReportConfig__ext2O__reportQuantity_r17__ssb_Index_SINR_Index_r17 t => existT _ 3 t
  end.
Definition CSI_ReportConfig__ext2O__reportQuantity_r17__g := (fun n => typ_set (get_nth_typ CSI_ReportConfig__ext2O__reportQuantity_r17__list n)).
Definition CSI_ReportConfig__ext2O__reportQuantity_r17__F2 (y : choice CSI_ReportConfig__ext2O__reportQuantity_r17__list) : CSI_ReportConfig__ext2O__reportQuantity_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_ReportConfig__ext2O__reportQuantity_r17__g n -> CSI_ReportConfig__ext2O__reportQuantity_r17__Type) with
    | 0 => fun (t : unit) => CSI_ReportConfig__ext2O__reportQuantity_r17__cri_RSRP_Index_r17 t 
    | 1 => fun (t : unit) => CSI_ReportConfig__ext2O__reportQuantity_r17__ssb_Index_RSRP_Index_r17 t 
    | 2 => fun (t : unit) => CSI_ReportConfig__ext2O__reportQuantity_r17__cri_SINR_Index_r17 t 
    | 3 => fun (t : unit) => CSI_ReportConfig__ext2O__reportQuantity_r17__ssb_Index_SINR_Index_r17 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : CSI_ReportConfig__ext2O__reportQuantity_r17__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ CSI_ReportConfig__ext2O__reportQuantity_r17__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_ReportConfig__ext2O__reportQuantity_r17__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return CSI_ReportConfig__ext2O__reportQuantity_r17__Type with end) n0
           end t0).

Lemma CSI_ReportConfig__ext2O__reportQuantity_r17__helper2 :  forall (y : CSI_ReportConfig__ext2O__reportQuantity_r17__Type), CSI_ReportConfig__ext2O__reportQuantity_r17__cond y -> choice_cond CSI_ReportConfig__ext2O__reportQuantity_r17__list (CSI_ReportConfig__ext2O__reportQuantity_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_ReportConfig__ext2O__reportQuantity_r17__helper3 :  forall (y : CSI_ReportConfig__ext2O__reportQuantity_r17__Type), CSI_ReportConfig__ext2O__reportQuantity_r17__F2 (CSI_ReportConfig__ext2O__reportQuantity_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_ReportConfig__ext2O__reportQuantity_r17__helper4 : (forall b : choice CSI_ReportConfig__ext2O__reportQuantity_r17__list, choice_cond CSI_ReportConfig__ext2O__reportQuantity_r17__list b -> CSI_ReportConfig__ext2O__reportQuantity_r17__cond (CSI_ReportConfig__ext2O__reportQuantity_r17__F2 b) /\ CSI_ReportConfig__ext2O__reportQuantity_r17__F1 (CSI_ReportConfig__ext2O__reportQuantity_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_ReportConfig__ext2O__reportQuantity_r17__F1 CSI_ReportConfig__ext2O__reportQuantity_r17__F2.
Definition CSI_ReportConfig__ext2O__reportQuantity_r17__Format : T_Format CSI_ReportConfig__ext2O__reportQuantity_r17__Type CSI_ReportConfig__ext2O__reportQuantity_r17__cond :=
  (* Eval compute in *) proj2_format CSI_ReportConfig__ext2O__reportQuantity_r17__cond CSI_ReportConfig__ext2O__reportQuantity_r17__list__Format CSI_ReportConfig__ext2O__reportQuantity_r17__F1 CSI_ReportConfig__ext2O__reportQuantity_r17__F2 CSI_ReportConfig__ext2O__reportQuantity_r17__helper2 CSI_ReportConfig__ext2O__reportQuantity_r17__helper3 CSI_ReportConfig__ext2O__reportQuantity_r17__helper4.
Opaque CSI_ReportConfig__ext2O__reportQuantity_r17__cond CSI_ReportConfig__ext2O__reportQuantity_r17__Format.


Definition CSI_ReportConfig__ext2O__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext2O__list.
Definition CSI_ReportConfig__ext2O__Format_list : CSI_ReportConfig__ext2O__Format_Type :=
  (CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17__Format, (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710__Format, (CodebookConfig_r17__Format, (CSI_ReportConfig__ext2O__sharedCMR_r17__Format, (CSI_ReportConfig__ext2O__csi_ReportMode_r17__Format, (CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17__Format, (CSI_ReportConfig__ext2O__reportQuantity_r17__Format, unit_format))))))).
Definition CSI_ReportConfig__ext2O__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext2O__list CSI_ReportConfig__ext2O__Format_list.
Definition CSI_ReportConfig__ext2O__F1 z :=
  (CSI_ReportConfig__ext2O__cqi_BitsPerSubband_r17 z, (CSI_ReportConfig__ext2O__groupBasedBeamReporting_v1710 z, (CSI_ReportConfig__ext2O__codebookConfig_r17 z, (CSI_ReportConfig__ext2O__sharedCMR_r17 z, (CSI_ReportConfig__ext2O__csi_ReportMode_r17 z, (CSI_ReportConfig__ext2O__numberOfSingleTRP_CSI_Mode1_r17 z, (CSI_ReportConfig__ext2O__reportQuantity_r17 z, tt))))))).
Definition CSI_ReportConfig__ext2O__F2 (y : seq_type CSI_ReportConfig__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__CSI_ReportConfig__ext2O__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma CSI_ReportConfig__ext2O__F1F2_cond (z : CSI_ReportConfig__ext2O__Type)
  : CSI_ReportConfig__ext2O__cond z ->
  (seq_cond CSI_ReportConfig__ext2O__list (CSI_ReportConfig__ext2O__F1 z)).
intro H. unfold CSI_ReportConfig__ext2O__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext2O__F1F2_cond2 (z : CSI_ReportConfig__ext2O__Type)
 : CSI_ReportConfig__ext2O__F2 (CSI_ReportConfig__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext2O__F2F1_cond (y : seq_type CSI_ReportConfig__ext2O__list)
  : seq_cond CSI_ReportConfig__ext2O__list y ->
 (CSI_ReportConfig__ext2O__cond (CSI_ReportConfig__ext2O__F2 y)) /\  CSI_ReportConfig__ext2O__F1 (CSI_ReportConfig__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext2O__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext2O__Format : T_Format CSI_ReportConfig__ext2O__Type CSI_ReportConfig__ext2O__cond :=
        proj2_format  CSI_ReportConfig__ext2O__cond CSI_ReportConfig__ext2O__list__Format
    CSI_ReportConfig__ext2O__F1 CSI_ReportConfig__ext2O__F2 CSI_ReportConfig__ext2O__F1F2_cond  CSI_ReportConfig__ext2O__F1F2_cond2 CSI_ReportConfig__ext2O__F2F1_cond.
Opaque CSI_ReportConfig__ext2O__cond CSI_ReportConfig__ext2O__Format.

Definition CSI_ReportConfig__ext2__check_all_none (b : CSI_ReportConfig__ext2O__Type) : bool :=
match b with 
  | make__CSI_ReportConfig__ext2O__Type None None None None None None None  => false 
  | _ => true 
 end.
Definition CSI_ReportConfig__ext2__Format : T_Format CSI_ReportConfig__ext2__Type CSI_ReportConfig__ext2__cond :=
  restrict_add_format CSI_ReportConfig__ext2__check_all_none CSI_ReportConfig__ext2O__Format.

Opaque CSI_ReportConfig__ext2__cond CSI_ReportConfig__ext2__Format.

Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__Format : T_Format Z CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__cond :=
 ranged_int_format (0) (128) CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__helper1 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__helper2.

Opaque CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__Format.

Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__Format : T_Format CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__Type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__cond := seq_of_format CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__helper1 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__helper2.

Opaque CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__Format.

Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__Format : T_Format Z CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__cond :=
 ranged_int_format (0) (128) CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper1 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper2.

Opaque CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__Format.

Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__Format : T_Format CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__Type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__cond := seq_of_format CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__helper1 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__helper2.

Opaque CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__Format.

Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__Format : T_Format Z CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__cond :=
 ranged_int_format (0) (128) CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper1 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper2.

Opaque CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__Format.

Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__Format : T_Format CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__Type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__cond := seq_of_format CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__helper1 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__helper2.

Opaque CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__Format.


Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Format_list : CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Format_Type :=
  (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17__Format, (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17__Format, (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17__Format, unit_format))).
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Format_list.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1 z :=
  (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetList_r17 z, (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_2_r17 z, (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__reportSlotOffsetListDCI_0_1_r17 z, tt))).
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F2 (y : seq_type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Type i0 i1 i2
  end.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1F2_cond (z : CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Type)
  : CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond z ->
  (seq_cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1 z)).
intro H. unfold CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1F2_cond2 (z : CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Type)
 : CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F2 (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F2F1_cond (y : seq_type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list)
  : seq_cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list y ->
 (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F2 y)) /\  CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1 (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Format : T_Format CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Type CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond :=
        proj2_format  CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__list__Format
    CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F2 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1F2_cond  CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F1F2_cond2 CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__F2F1_cond.
Opaque CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__cond CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Format.

Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__Format : T_Format Z CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__cond :=
 ranged_int_format (0) (128) CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__helper1 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__helper2.

Opaque CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__Format.

Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__Format : T_Format CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__Type CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__cond := seq_of_format CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__helper1 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__helper2.

Opaque CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__Format.

Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__Format : T_Format Z CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__cond :=
 ranged_int_format (0) (128) CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper1 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__helper2.

Opaque CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__Format.

Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__Format : T_Format CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__Type CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__cond := seq_of_format CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__helper1 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__helper2.

Opaque CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__Format.

Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__Format : T_Format Z CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__cond :=
 ranged_int_format (0) (128) CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper1 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__helper2.

Opaque CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__Format.

Definition CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__Format : T_Format CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__Type CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__cond := seq_of_format CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__seq_of__Format 1 maxNrofUL_Allocations_r16 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__helper1 CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__helper2.

Opaque CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__cond CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__Format.


Definition CSI_ReportConfig__ext3O__aperiodic_v1720__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext3O__aperiodic_v1720__list.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__Format_list : CSI_ReportConfig__ext3O__aperiodic_v1720__Format_Type :=
  (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17__Format, (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17__Format, (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17__Format, unit_format))).
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext3O__aperiodic_v1720__list CSI_ReportConfig__ext3O__aperiodic_v1720__Format_list.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__F1 z :=
  (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetList_r17 z, (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_2_r17 z, (CSI_ReportConfig__ext3O__aperiodic_v1720__reportSlotOffsetListDCI_0_1_r17 z, tt))).
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__F2 (y : seq_type CSI_ReportConfig__ext3O__aperiodic_v1720__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CSI_ReportConfig__ext3O__aperiodic_v1720__Type i0 i1 i2
  end.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__F1F2_cond (z : CSI_ReportConfig__ext3O__aperiodic_v1720__Type)
  : CSI_ReportConfig__ext3O__aperiodic_v1720__cond z ->
  (seq_cond CSI_ReportConfig__ext3O__aperiodic_v1720__list (CSI_ReportConfig__ext3O__aperiodic_v1720__F1 z)).
intro H. unfold CSI_ReportConfig__ext3O__aperiodic_v1720__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__F1F2_cond2 (z : CSI_ReportConfig__ext3O__aperiodic_v1720__Type)
 : CSI_ReportConfig__ext3O__aperiodic_v1720__F2 (CSI_ReportConfig__ext3O__aperiodic_v1720__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext3O__aperiodic_v1720__F2F1_cond (y : seq_type CSI_ReportConfig__ext3O__aperiodic_v1720__list)
  : seq_cond CSI_ReportConfig__ext3O__aperiodic_v1720__list y ->
 (CSI_ReportConfig__ext3O__aperiodic_v1720__cond (CSI_ReportConfig__ext3O__aperiodic_v1720__F2 y)) /\  CSI_ReportConfig__ext3O__aperiodic_v1720__F1 (CSI_ReportConfig__ext3O__aperiodic_v1720__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext3O__aperiodic_v1720__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext3O__aperiodic_v1720__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext3O__aperiodic_v1720__Format : T_Format CSI_ReportConfig__ext3O__aperiodic_v1720__Type CSI_ReportConfig__ext3O__aperiodic_v1720__cond :=
        proj2_format  CSI_ReportConfig__ext3O__aperiodic_v1720__cond CSI_ReportConfig__ext3O__aperiodic_v1720__list__Format
    CSI_ReportConfig__ext3O__aperiodic_v1720__F1 CSI_ReportConfig__ext3O__aperiodic_v1720__F2 CSI_ReportConfig__ext3O__aperiodic_v1720__F1F2_cond  CSI_ReportConfig__ext3O__aperiodic_v1720__F1F2_cond2 CSI_ReportConfig__ext3O__aperiodic_v1720__F2F1_cond.
Opaque CSI_ReportConfig__ext3O__aperiodic_v1720__cond CSI_ReportConfig__ext3O__aperiodic_v1720__Format.


Definition CSI_ReportConfig__ext3O__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext3O__list.
Definition CSI_ReportConfig__ext3O__Format_list : CSI_ReportConfig__ext3O__Format_Type :=
  (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720__Format, (CSI_ReportConfig__ext3O__aperiodic_v1720__Format, unit_format)).
Definition CSI_ReportConfig__ext3O__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext3O__list CSI_ReportConfig__ext3O__Format_list.
Definition CSI_ReportConfig__ext3O__F1 z :=
  (CSI_ReportConfig__ext3O__semiPersistentOnPUSCH_v1720 z, (CSI_ReportConfig__ext3O__aperiodic_v1720 z, tt)).
Definition CSI_ReportConfig__ext3O__F2 (y : seq_type CSI_ReportConfig__ext3O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__CSI_ReportConfig__ext3O__Type i0 i1
  end.
Lemma CSI_ReportConfig__ext3O__F1F2_cond (z : CSI_ReportConfig__ext3O__Type)
  : CSI_ReportConfig__ext3O__cond z ->
  (seq_cond CSI_ReportConfig__ext3O__list (CSI_ReportConfig__ext3O__F1 z)).
intro H. unfold CSI_ReportConfig__ext3O__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext3O__F1F2_cond2 (z : CSI_ReportConfig__ext3O__Type)
 : CSI_ReportConfig__ext3O__F2 (CSI_ReportConfig__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext3O__F2F1_cond (y : seq_type CSI_ReportConfig__ext3O__list)
  : seq_cond CSI_ReportConfig__ext3O__list y ->
 (CSI_ReportConfig__ext3O__cond (CSI_ReportConfig__ext3O__F2 y)) /\  CSI_ReportConfig__ext3O__F1 (CSI_ReportConfig__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext3O__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext3O__Format : T_Format CSI_ReportConfig__ext3O__Type CSI_ReportConfig__ext3O__cond :=
        proj2_format  CSI_ReportConfig__ext3O__cond CSI_ReportConfig__ext3O__list__Format
    CSI_ReportConfig__ext3O__F1 CSI_ReportConfig__ext3O__F2 CSI_ReportConfig__ext3O__F1F2_cond  CSI_ReportConfig__ext3O__F1F2_cond2 CSI_ReportConfig__ext3O__F2F1_cond.
Opaque CSI_ReportConfig__ext3O__cond CSI_ReportConfig__ext3O__Format.

Definition CSI_ReportConfig__ext3__check_all_none (b : CSI_ReportConfig__ext3O__Type) : bool :=
match b with 
  | make__CSI_ReportConfig__ext3O__Type None None  => false 
  | _ => true 
 end.
Definition CSI_ReportConfig__ext3__Format : T_Format CSI_ReportConfig__ext3__Type CSI_ReportConfig__ext3__cond :=
  restrict_add_format CSI_ReportConfig__ext3__check_all_none CSI_ReportConfig__ext3O__Format.

Opaque CSI_ReportConfig__ext3__cond CSI_ReportConfig__ext3__Format.


Definition CSI_ReportConfig__ext4O__Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__ext4O__list.
Definition CSI_ReportConfig__ext4O__Format_list : CSI_ReportConfig__ext4O__Format_Type :=
  (CodebookConfig_v1730__Format, unit_format).
Definition CSI_ReportConfig__ext4O__list__Format := (*Eval compute in *) seq_format CSI_ReportConfig__ext4O__list CSI_ReportConfig__ext4O__Format_list.
Definition CSI_ReportConfig__ext4O__F1 z :=
  (CSI_ReportConfig__ext4O__codebookConfig_v1730 z, tt).
Definition CSI_ReportConfig__ext4O__F2 (y : seq_type CSI_ReportConfig__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__CSI_ReportConfig__ext4O__Type i0
  end.
Lemma CSI_ReportConfig__ext4O__F1F2_cond (z : CSI_ReportConfig__ext4O__Type)
  : CSI_ReportConfig__ext4O__cond z ->
  (seq_cond CSI_ReportConfig__ext4O__list (CSI_ReportConfig__ext4O__F1 z)).
intro H. unfold CSI_ReportConfig__ext4O__cond in H. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext4O__F1F2_cond2 (z : CSI_ReportConfig__ext4O__Type)
 : CSI_ReportConfig__ext4O__F2 (CSI_ReportConfig__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_ReportConfig__ext4O__F2F1_cond (y : seq_type CSI_ReportConfig__ext4O__list)
  : seq_cond CSI_ReportConfig__ext4O__list y ->
 (CSI_ReportConfig__ext4O__cond (CSI_ReportConfig__ext4O__F2 y)) /\  CSI_ReportConfig__ext4O__F1 (CSI_ReportConfig__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_ReportConfig__ext4O__cond. simpl in *. auto.
 - simpl. unfold CSI_ReportConfig__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_ReportConfig__ext4O__Format : T_Format CSI_ReportConfig__ext4O__Type CSI_ReportConfig__ext4O__cond :=
        proj2_format  CSI_ReportConfig__ext4O__cond CSI_ReportConfig__ext4O__list__Format
    CSI_ReportConfig__ext4O__F1 CSI_ReportConfig__ext4O__F2 CSI_ReportConfig__ext4O__F1F2_cond  CSI_ReportConfig__ext4O__F1F2_cond2 CSI_ReportConfig__ext4O__F2F1_cond.
Opaque CSI_ReportConfig__ext4O__cond CSI_ReportConfig__ext4O__Format.

Definition CSI_ReportConfig__ext4__check_all_none (b : CSI_ReportConfig__ext4O__Type) : bool :=
match b with 
  | make__CSI_ReportConfig__ext4O__Type None  => false 
  | _ => true 
 end.
Definition CSI_ReportConfig__ext4__Format : T_Format CSI_ReportConfig__ext4__Type CSI_ReportConfig__ext4__cond :=
  restrict_add_format CSI_ReportConfig__ext4__check_all_none CSI_ReportConfig__ext4O__Format.

Opaque CSI_ReportConfig__ext4__cond CSI_ReportConfig__ext4__Format.


Definition CSI_ReportConfig__root_Format_Type := Eval cbn in seq_format_prod CSI_ReportConfig__root_list.
Definition CSI_ReportConfig__root_Format_list : CSI_ReportConfig__root_Format_Type :=
  (CSI_ReportConfigId__Format, (ServCellIndex__Format, (CSI_ResourceConfigId__Format, (CSI_ResourceConfigId__Format, (CSI_ResourceConfigId__Format, (CSI_ReportConfig__reportConfigType__Format, (CSI_ReportConfig__reportQuantity__Format, (CSI_ReportConfig__reportFreqConfiguration__Format, (CSI_ReportConfig__timeRestrictionForChannelMeasurements__Format, (CSI_ReportConfig__timeRestrictionForInterferenceMeasurements__Format, (CodebookConfig__Format, (CSI_ReportConfig__dummy__Format, (CSI_ReportConfig__groupBasedBeamReporting__Format, (CSI_ReportConfig__cqi_Table__Format, (CSI_ReportConfig__subbandSize__Format, (CSI_ReportConfig__non_PMI_PortIndication__Format, unit_format)))))))))))))))).

Definition CSI_ReportConfig__ext_Format_Type := Eval cbn in get_formats CSI_ReportConfig__ext_list.
Definition CSI_ReportConfig__ext_Format_list : CSI_ReportConfig__ext_Format_Type :=
  (CSI_ReportConfig__ext0__Format, (CSI_ReportConfig__ext1__Format, (CSI_ReportConfig__ext2__Format, (CSI_ReportConfig__ext3__Format, (CSI_ReportConfig__ext4__Format, unit__Format))))).

Definition CSI_ReportConfig__list_type : Set := (seq_type CSI_ReportConfig__root_list) * (seq_ext_type CSI_ReportConfig__ext_list).
Definition CSI_ReportConfig__list_cond (z : CSI_ReportConfig__list_type) : Prop :=
        (seq_cond CSI_ReportConfig__root_list (fst z)) /\ (seq_ext_cond CSI_ReportConfig__ext_list (snd z)).
Definition CSI_ReportConfig__list_format : T_Format CSI_ReportConfig__list_type CSI_ReportConfig__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_ReportConfig__root_list CSI_ReportConfig__root_Format_list CSI_ReportConfig__ext_list CSI_ReportConfig__ext_Format_list.

Opaque CSI_ReportConfig__list_format.
Definition CSI_ReportConfig__F1 (z : CSI_ReportConfig__Type) : CSI_ReportConfig__list_type :=
  (((CSI_ReportConfig__reportConfigId z, (CSI_ReportConfig__carrier z, (CSI_ReportConfig__resourcesForChannelMeasurement z, (CSI_ReportConfig__csi_IM_ResourcesForInterference z, (CSI_ReportConfig__nzp_CSI_RS_ResourcesForInterference z, (CSI_ReportConfig__reportConfigType z, (CSI_ReportConfig__reportQuantity z, (CSI_ReportConfig__reportFreqConfiguration z, (CSI_ReportConfig__timeRestrictionForChannelMeasurements z, (CSI_ReportConfig__timeRestrictionForInterferenceMeasurements z, (CSI_ReportConfig__codebookConfig z, (CSI_ReportConfig__dummy z, (CSI_ReportConfig__groupBasedBeamReporting z, (CSI_ReportConfig__cqi_Table z, (CSI_ReportConfig__subbandSize z, (CSI_ReportConfig__non_PMI_PortIndication z, tt))))))))))))))))), (
(CSI_ReportConfig__ext0 z, (CSI_ReportConfig__ext1 z, (CSI_ReportConfig__ext2 z, (CSI_ReportConfig__ext3 z, (CSI_ReportConfig__ext4 z, tt))))))).
Definition CSI_ReportConfig__F2 (y : CSI_ReportConfig__list_type) : CSI_ReportConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, (j15, _)))))))))))))))), (i0, (i1, (i2, (i3, (i4, _))))))=>
    make__CSI_ReportConfig__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 i0 i1 i2 i3 i4
  end.
Definition CSI_ReportConfig__helper1 : (forall a : CSI_ReportConfig__Type, CSI_ReportConfig__cond a -> CSI_ReportConfig__list_cond (CSI_ReportConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_ReportConfig__helper2 : (forall a : CSI_ReportConfig__Type, CSI_ReportConfig__F2 (CSI_ReportConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_ReportConfig__helper3 : (forall b : CSI_ReportConfig__list_type, CSI_ReportConfig__list_cond b -> CSI_ReportConfig__cond (CSI_ReportConfig__F2 b) /\ CSI_ReportConfig__F1 (CSI_ReportConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_ReportConfig__cond, CSI_ReportConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_ReportConfig__Format : T_Format CSI_ReportConfig__Type CSI_ReportConfig__cond :=
 proj2_format CSI_ReportConfig__cond CSI_ReportConfig__list_format  CSI_ReportConfig__F1 CSI_ReportConfig__F2 CSI_ReportConfig__helper1 CSI_ReportConfig__helper2 CSI_ReportConfig__helper3.

Opaque CSI_ReportConfig__cond CSI_ReportConfig__Format.

