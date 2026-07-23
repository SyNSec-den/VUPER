Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SRS_ResourceSetId.

Opaque SRS_ResourceSetId__cond SRS_ResourceSetId__Format.

Require Import NR.SRS_ResourceId.

Opaque SRS_ResourceId__cond SRS_ResourceId__Format.

Definition SRS_ResourceSet__srs_ResourceIdList__Type := list SRS_ResourceId__Type.

Lemma SRS_ResourceSet__srs_ResourceIdList__helper1 : (0 <= 1 <= maxNrofSRS_ResourcesPerSet)%Z. unfold maxNrofSRS_ResourcesPerSet.
 lia. Qed.
Lemma SRS_ResourceSet__srs_ResourceIdList__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_ResourcesPerSet - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_ResourcesPerSet - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_ResourceSet__srs_ResourceIdList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_ResourceSet__srs_ResourceIdList__cond (z : SRS_ResourceSet__srs_ResourceIdList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_ResourcesPerSet)%Z /\ (list_and SRS_ResourceId__cond z) .

Lemma SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__helper1 : (1 <= maxNrofSRS_TriggerStates_1)%Z. unfold maxNrofSRS_TriggerStates_1.
 lia. Qed.
Lemma SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_TriggerStates_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_TriggerStates_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__Type := Z.
Definition SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__cond := (fun z => (1 <= z <= maxNrofSRS_TriggerStates_1)%Z).
Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Lemma SRS_ResourceSet__resourceType__aperiodic__slotOffset__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma SRS_ResourceSet__resourceType__aperiodic__slotOffset__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_ResourceSet__resourceType__aperiodic__slotOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_ResourceSet__resourceType__aperiodic__slotOffset__Type := Z.
Definition SRS_ResourceSet__resourceType__aperiodic__slotOffset__cond := (fun z => (1 <= z <= 32)%Z).
Lemma SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__helper1 : (1 <= maxNrofSRS_TriggerStates_1)%Z. unfold maxNrofSRS_TriggerStates_1.
 lia. Qed.
Lemma SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_TriggerStates_1 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_TriggerStates_1 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__Type := Z.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__cond := (fun z => (1 <= z <= maxNrofSRS_TriggerStates_1)%Z).
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__Type := list Z.

Lemma SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__helper1 : (0 <= 1 <= maxNrofSRS_TriggerStates_2)%Z. unfold maxNrofSRS_TriggerStates_2.
 lia. Qed.
Lemma SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__helper2 : to_bit_sz (Z.to_nat (maxNrofSRS_TriggerStates_2 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofSRS_TriggerStates_2 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__cond (z : SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofSRS_TriggerStates_2)%Z /\ (list_and SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__cond z) .

Record SRS_ResourceSet__resourceType__aperiodic__ext0O__Type : Set :=
  make__SRS_ResourceSet__resourceType__aperiodic__ext0O__Type {
    SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList : option SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__Type ;
}.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__list := (
 Opt SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__Type SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__cond ::
 nil).
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__cond z := 
  opt_cond SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__cond (SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList z) /\
  True.

Definition SRS_ResourceSet__resourceType__aperiodic__ext0__Type := SRS_ResourceSet__resourceType__aperiodic__ext0O__Type.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0__cond := SRS_ResourceSet__resourceType__aperiodic__ext0O__cond.

Record SRS_ResourceSet__resourceType__aperiodic__Type : Set :=
  make__SRS_ResourceSet__resourceType__aperiodic__Type {
    SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger : Z ;
    SRS_ResourceSet__resourceType__aperiodic__csi_RS : option NZP_CSI_RS_ResourceId__Type ;
    SRS_ResourceSet__resourceType__aperiodic__slotOffset : option Z ;
    SRS_ResourceSet__resourceType__aperiodic__ext0 : option SRS_ResourceSet__resourceType__aperiodic__ext0__Type ;
}.
Definition SRS_ResourceSet__resourceType__aperiodic__root_list : list seq_elem := (
 Nor Z SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__cond ::
 Opt NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 Opt Z SRS_ResourceSet__resourceType__aperiodic__slotOffset__cond ::
 nil).
Definition SRS_ResourceSet__resourceType__aperiodic__ext_list : list typ := (
  typ_cons SRS_ResourceSet__resourceType__aperiodic__ext0__Type SRS_ResourceSet__resourceType__aperiodic__ext0__cond ::
  nil).
Definition SRS_ResourceSet__resourceType__aperiodic__cond (z : SRS_ResourceSet__resourceType__aperiodic__Type) := 
(  SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__cond (SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger z) /\
  opt_cond NZP_CSI_RS_ResourceId__cond (SRS_ResourceSet__resourceType__aperiodic__csi_RS z) /\
  opt_cond SRS_ResourceSet__resourceType__aperiodic__slotOffset__cond (SRS_ResourceSet__resourceType__aperiodic__slotOffset z) /\
  True) /\ 
(  opt_cond SRS_ResourceSet__resourceType__aperiodic__ext0__cond (SRS_ResourceSet__resourceType__aperiodic__ext0 z) /\
  True).

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Record SRS_ResourceSet__resourceType__semi_persistent__Type : Set :=
  make__SRS_ResourceSet__resourceType__semi_persistent__Type {
    SRS_ResourceSet__resourceType__semi_persistent__associatedCSI_RS : option NZP_CSI_RS_ResourceId__Type ;
}.
Definition SRS_ResourceSet__resourceType__semi_persistent__root_list : list seq_elem := (
 Opt NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 nil).
Definition SRS_ResourceSet__resourceType__semi_persistent__ext_list : list typ := (
  nil).
Definition SRS_ResourceSet__resourceType__semi_persistent__cond (z : SRS_ResourceSet__resourceType__semi_persistent__Type) := 
(  opt_cond NZP_CSI_RS_ResourceId__cond (SRS_ResourceSet__resourceType__semi_persistent__associatedCSI_RS z) /\
  True) /\ 
(  True).

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Record SRS_ResourceSet__resourceType__periodic__Type : Set :=
  make__SRS_ResourceSet__resourceType__periodic__Type {
    SRS_ResourceSet__resourceType__periodic__associatedCSI_RS : option NZP_CSI_RS_ResourceId__Type ;
}.
Definition SRS_ResourceSet__resourceType__periodic__root_list : list seq_elem := (
 Opt NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 nil).
Definition SRS_ResourceSet__resourceType__periodic__ext_list : list typ := (
  nil).
Definition SRS_ResourceSet__resourceType__periodic__cond (z : SRS_ResourceSet__resourceType__periodic__Type) := 
(  opt_cond NZP_CSI_RS_ResourceId__cond (SRS_ResourceSet__resourceType__periodic__associatedCSI_RS z) /\
  True) /\ 
(  True).


Inductive SRS_ResourceSet__resourceType__Type : Set :=
  | SRS_ResourceSet__resourceType__aperiodic : SRS_ResourceSet__resourceType__aperiodic__Type -> SRS_ResourceSet__resourceType__Type
  | SRS_ResourceSet__resourceType__semi_persistent : SRS_ResourceSet__resourceType__semi_persistent__Type -> SRS_ResourceSet__resourceType__Type
  | SRS_ResourceSet__resourceType__periodic : SRS_ResourceSet__resourceType__periodic__Type -> SRS_ResourceSet__resourceType__Type
.
Definition SRS_ResourceSet__resourceType__list : list typ := (
typ_cons SRS_ResourceSet__resourceType__aperiodic__Type SRS_ResourceSet__resourceType__aperiodic__cond ::
typ_cons SRS_ResourceSet__resourceType__semi_persistent__Type SRS_ResourceSet__resourceType__semi_persistent__cond ::
typ_cons SRS_ResourceSet__resourceType__periodic__Type SRS_ResourceSet__resourceType__periodic__cond ::
 nil).
Definition SRS_ResourceSet__resourceType__cond (c : SRS_ResourceSet__resourceType__Type) := 
  match c with
  | SRS_ResourceSet__resourceType__aperiodic t => SRS_ResourceSet__resourceType__aperiodic__cond t 
  | SRS_ResourceSet__resourceType__semi_persistent t => SRS_ResourceSet__resourceType__semi_persistent__cond t 
  | SRS_ResourceSet__resourceType__periodic t => SRS_ResourceSet__resourceType__periodic__cond t 
  end.

Lemma SRS_ResourceSet__resourceType__len_helper1 : to_bit_sz (length SRS_ResourceSet__resourceType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_ResourceSet__resourceType__len_helper2 : 2 <= length2 SRS_ResourceSet__resourceType__list.
 simpl. lia. Qed.
Inductive SRS_ResourceSet__usage__Type : Set :=
 | SRS_ResourceSet__usage__beamManagement
 | SRS_ResourceSet__usage__codebook
 | SRS_ResourceSet__usage__nonCodebook
 | SRS_ResourceSet__usage__antennaSwitching
.
Definition SRS_ResourceSet__usage__cond := (fun (_ : SRS_ResourceSet__usage__Type) => True).
Lemma SRS_ResourceSet__usage__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_ResourceSet__usage__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 SRS_ResourceSet__usage__nat__helper.

Definition SRS_ResourceSet__usage__F1 t :=
  match t with
  | SRS_ResourceSet__usage__beamManagement => 0
  | SRS_ResourceSet__usage__codebook => 1
  | SRS_ResourceSet__usage__nonCodebook => 2
  | SRS_ResourceSet__usage__antennaSwitching => 3
  end.
Definition SRS_ResourceSet__usage__F2 n :=
  match n with
  | 0 => SRS_ResourceSet__usage__beamManagement
  | 1 => SRS_ResourceSet__usage__codebook
  | 2 => SRS_ResourceSet__usage__nonCodebook
  | 3 => SRS_ResourceSet__usage__antennaSwitching
  | _ => SRS_ResourceSet__usage__beamManagement
  end.
Lemma SRS_ResourceSet__usage__F1F2 : forall x : SRS_ResourceSet__usage__Type, (SRS_ResourceSet__usage__F1 x <= 3) /\ SRS_ResourceSet__usage__F2 (SRS_ResourceSet__usage__F1 x) = x. imp_solve. Qed.
Lemma SRS_ResourceSet__usage__F2F1 : forall (y : nat) (H : y <= 3), SRS_ResourceSet__usage__F1 (SRS_ResourceSet__usage__F2 y) = y. enum_solve H y. Qed.

Require Import NR.Alpha.

Opaque Alpha__cond Alpha__Format.

Lemma SRS_ResourceSet__p0__helper1 : (-202 <= 24)%Z.  lia. Qed.
Lemma SRS_ResourceSet__p0__helper2 : to_bit_sz (Z.to_nat (24 - -202)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (24 - -202))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_ResourceSet__p0__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_ResourceSet__p0__Type := Z.
Definition SRS_ResourceSet__p0__cond := (fun z => (-202 <= z <= 24)%Z).
Require Import NR.PathlossReferenceRS_Config.

Opaque PathlossReferenceRS_Config__cond PathlossReferenceRS_Config__Format.

Inductive SRS_ResourceSet__srs_PowerControlAdjustmentStates__Type : Set :=
 | SRS_ResourceSet__srs_PowerControlAdjustmentStates__sameAsFci2
 | SRS_ResourceSet__srs_PowerControlAdjustmentStates__separateClosedLoop
.
Definition SRS_ResourceSet__srs_PowerControlAdjustmentStates__cond := (fun (_ : SRS_ResourceSet__srs_PowerControlAdjustmentStates__Type) => True).
Lemma SRS_ResourceSet__srs_PowerControlAdjustmentStates__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_ResourceSet__srs_PowerControlAdjustmentStates__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SRS_ResourceSet__srs_PowerControlAdjustmentStates__nat__helper.

Definition SRS_ResourceSet__srs_PowerControlAdjustmentStates__F1 t :=
  match t with
  | SRS_ResourceSet__srs_PowerControlAdjustmentStates__sameAsFci2 => 0
  | SRS_ResourceSet__srs_PowerControlAdjustmentStates__separateClosedLoop => 1
  end.
Definition SRS_ResourceSet__srs_PowerControlAdjustmentStates__F2 n :=
  match n with
  | 0 => SRS_ResourceSet__srs_PowerControlAdjustmentStates__sameAsFci2
  | 1 => SRS_ResourceSet__srs_PowerControlAdjustmentStates__separateClosedLoop
  | _ => SRS_ResourceSet__srs_PowerControlAdjustmentStates__sameAsFci2
  end.
Lemma SRS_ResourceSet__srs_PowerControlAdjustmentStates__F1F2 : forall x : SRS_ResourceSet__srs_PowerControlAdjustmentStates__Type, (SRS_ResourceSet__srs_PowerControlAdjustmentStates__F1 x <= 1) /\ SRS_ResourceSet__srs_PowerControlAdjustmentStates__F2 (SRS_ResourceSet__srs_PowerControlAdjustmentStates__F1 x) = x. imp_solve. Qed.
Lemma SRS_ResourceSet__srs_PowerControlAdjustmentStates__F2F1 : forall (y : nat) (H : y <= 1), SRS_ResourceSet__srs_PowerControlAdjustmentStates__F1 (SRS_ResourceSet__srs_PowerControlAdjustmentStates__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SetupRelease.
Require Import NR.PathlossReferenceRSList_r16.
Definition SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__Type := SetupRelease__Type PathlossReferenceRSList_r16__Type.
Definition SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__cond := SetupRelease__cond _ PathlossReferenceRSList_r16__cond.
Definition SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__Format : T_Format SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__Type SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__cond := SetupRelease__Format _ _ PathlossReferenceRSList_r16__Format.
Opaque SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__cond SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__Format.

Record SRS_ResourceSet__ext0O__Type : Set :=
  make__SRS_ResourceSet__ext0O__Type {
    SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16 : option SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__Type ;
}.
Definition SRS_ResourceSet__ext0O__list := (
 Opt SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__Type SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__cond ::
 nil).
Definition SRS_ResourceSet__ext0O__cond z := 
  opt_cond SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__cond (SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16 z) /\
  True.

Definition SRS_ResourceSet__ext0__Type := SRS_ResourceSet__ext0O__Type.
Definition SRS_ResourceSet__ext0__cond := SRS_ResourceSet__ext0O__cond.

Inductive SRS_ResourceSet__ext1O__usagePDC_r17__Type : Set :=
 | SRS_ResourceSet__ext1O__usagePDC_r17__true
.
Definition SRS_ResourceSet__ext1O__usagePDC_r17__cond := (fun (_ : SRS_ResourceSet__ext1O__usagePDC_r17__Type) => True).
Lemma SRS_ResourceSet__ext1O__usagePDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_ResourceSet__ext1O__usagePDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SRS_ResourceSet__ext1O__usagePDC_r17__nat__helper.

Definition SRS_ResourceSet__ext1O__usagePDC_r17__F1 t :=
  match t with
  | SRS_ResourceSet__ext1O__usagePDC_r17__true => 0
  end.
Definition SRS_ResourceSet__ext1O__usagePDC_r17__F2 n :=
  match n with
  | 0 => SRS_ResourceSet__ext1O__usagePDC_r17__true
  | _ => SRS_ResourceSet__ext1O__usagePDC_r17__true
  end.
Lemma SRS_ResourceSet__ext1O__usagePDC_r17__F1F2 : forall x : SRS_ResourceSet__ext1O__usagePDC_r17__Type, (SRS_ResourceSet__ext1O__usagePDC_r17__F1 x <= 0) /\ SRS_ResourceSet__ext1O__usagePDC_r17__F2 (SRS_ResourceSet__ext1O__usagePDC_r17__F1 x) = x. imp_solve. Qed.
Lemma SRS_ResourceSet__ext1O__usagePDC_r17__F2F1 : forall (y : nat) (H : y <= 0), SRS_ResourceSet__ext1O__usagePDC_r17__F1 (SRS_ResourceSet__ext1O__usagePDC_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.AvailableSlotOffset_r17.

Opaque AvailableSlotOffset_r17__cond AvailableSlotOffset_r17__Format.

Definition SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__Type := list AvailableSlotOffset_r17__Type.

Lemma SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__helper1 : (0 <= 1 <= 4)%Z.  lia. Qed.
Lemma SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__helper2 : to_bit_sz (Z.to_nat (4 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__cond (z : SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__Type) :=  (1 <= Z.of_nat (length z) <= 4)%Z /\ (list_and AvailableSlotOffset_r17__cond z) .

Inductive SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Type : Set :=
 | SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__enabled
.
Definition SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__cond := (fun (_ : SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Type) => True).
Lemma SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__nat__helper.

Definition SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F1 t :=
  match t with
  | SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__enabled => 0
  end.
Definition SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F2 n :=
  match n with
  | 0 => SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__enabled
  | _ => SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__enabled
  end.
Lemma SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F1F2 : forall x : SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Type, (SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F1 x <= 0) /\ SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F2 (SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F1 x) = x. imp_solve. Qed.
Lemma SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F2F1 : forall (y : nat) (H : y <= 0), SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F1 (SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F2 y) = y. enum_solve H y. Qed.

Record SRS_ResourceSet__ext1O__Type : Set :=
  make__SRS_ResourceSet__ext1O__Type {
    SRS_ResourceSet__ext1O__usagePDC_r17 : option SRS_ResourceSet__ext1O__usagePDC_r17__Type ;
    SRS_ResourceSet__ext1O__availableSlotOffsetList_r17 : option SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__Type ;
    SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17 : option SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Type ;
}.
Definition SRS_ResourceSet__ext1O__list := (
 Opt SRS_ResourceSet__ext1O__usagePDC_r17__Type SRS_ResourceSet__ext1O__usagePDC_r17__cond ::
 Opt SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__Type SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__cond ::
 Opt SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Type SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__cond ::
 nil).
Definition SRS_ResourceSet__ext1O__cond z := 
  opt_cond SRS_ResourceSet__ext1O__usagePDC_r17__cond (SRS_ResourceSet__ext1O__usagePDC_r17 z) /\
  opt_cond SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__cond (SRS_ResourceSet__ext1O__availableSlotOffsetList_r17 z) /\
  opt_cond SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__cond (SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17 z) /\
  True.

Definition SRS_ResourceSet__ext1__Type := SRS_ResourceSet__ext1O__Type.
Definition SRS_ResourceSet__ext1__cond := SRS_ResourceSet__ext1O__cond.

Record SRS_ResourceSet__Type : Set :=
  make__SRS_ResourceSet__Type {
    SRS_ResourceSet__srs_ResourceSetId : SRS_ResourceSetId__Type ;
    SRS_ResourceSet__srs_ResourceIdList : option SRS_ResourceSet__srs_ResourceIdList__Type ;
    SRS_ResourceSet__resourceType : SRS_ResourceSet__resourceType__Type ;
    SRS_ResourceSet__usage : SRS_ResourceSet__usage__Type ;
    SRS_ResourceSet__alpha : option Alpha__Type ;
    SRS_ResourceSet__p0 : option Z ;
    SRS_ResourceSet__pathlossReferenceRS : option PathlossReferenceRS_Config__Type ;
    SRS_ResourceSet__srs_PowerControlAdjustmentStates : option SRS_ResourceSet__srs_PowerControlAdjustmentStates__Type ;
    SRS_ResourceSet__ext0 : option SRS_ResourceSet__ext0__Type ;
    SRS_ResourceSet__ext1 : option SRS_ResourceSet__ext1__Type ;
}.
Definition SRS_ResourceSet__root_list : list seq_elem := (
 Nor SRS_ResourceSetId__Type SRS_ResourceSetId__cond ::
 Opt SRS_ResourceSet__srs_ResourceIdList__Type SRS_ResourceSet__srs_ResourceIdList__cond ::
 Nor SRS_ResourceSet__resourceType__Type SRS_ResourceSet__resourceType__cond ::
 Nor SRS_ResourceSet__usage__Type SRS_ResourceSet__usage__cond ::
 Opt Alpha__Type Alpha__cond ::
 Opt Z SRS_ResourceSet__p0__cond ::
 Opt PathlossReferenceRS_Config__Type PathlossReferenceRS_Config__cond ::
 Opt SRS_ResourceSet__srs_PowerControlAdjustmentStates__Type SRS_ResourceSet__srs_PowerControlAdjustmentStates__cond ::
 nil).
Definition SRS_ResourceSet__ext_list : list typ := (
  typ_cons SRS_ResourceSet__ext0__Type SRS_ResourceSet__ext0__cond ::
  typ_cons SRS_ResourceSet__ext1__Type SRS_ResourceSet__ext1__cond ::
  nil).
Definition SRS_ResourceSet__cond (z : SRS_ResourceSet__Type) := 
(  SRS_ResourceSetId__cond (SRS_ResourceSet__srs_ResourceSetId z) /\
  opt_cond SRS_ResourceSet__srs_ResourceIdList__cond (SRS_ResourceSet__srs_ResourceIdList z) /\
  SRS_ResourceSet__resourceType__cond (SRS_ResourceSet__resourceType z) /\
  SRS_ResourceSet__usage__cond (SRS_ResourceSet__usage z) /\
  opt_cond Alpha__cond (SRS_ResourceSet__alpha z) /\
  opt_cond SRS_ResourceSet__p0__cond (SRS_ResourceSet__p0 z) /\
  opt_cond PathlossReferenceRS_Config__cond (SRS_ResourceSet__pathlossReferenceRS z) /\
  opt_cond SRS_ResourceSet__srs_PowerControlAdjustmentStates__cond (SRS_ResourceSet__srs_PowerControlAdjustmentStates z) /\
  True) /\ 
(  opt_cond SRS_ResourceSet__ext0__cond (SRS_ResourceSet__ext0 z) /\
  opt_cond SRS_ResourceSet__ext1__cond (SRS_ResourceSet__ext1 z) /\
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
Definition SRS_ResourceSet__srs_ResourceIdList__Format : T_Format SRS_ResourceSet__srs_ResourceIdList__Type SRS_ResourceSet__srs_ResourceIdList__cond := seq_of_format SRS_ResourceId__Format 1 maxNrofSRS_ResourcesPerSet SRS_ResourceSet__srs_ResourceIdList__helper1 SRS_ResourceSet__srs_ResourceIdList__helper2.

Opaque SRS_ResourceSet__srs_ResourceIdList__cond SRS_ResourceSet__srs_ResourceIdList__Format.

Definition SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__Format : T_Format Z SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__cond :=
 ranged_int_format (1) (maxNrofSRS_TriggerStates_1) SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__helper1 SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__helper2.

Opaque SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__cond SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__Format.

Definition SRS_ResourceSet__resourceType__aperiodic__slotOffset__Format : T_Format Z SRS_ResourceSet__resourceType__aperiodic__slotOffset__cond :=
 ranged_int_format (1) (32) SRS_ResourceSet__resourceType__aperiodic__slotOffset__helper1 SRS_ResourceSet__resourceType__aperiodic__slotOffset__helper2.

Opaque SRS_ResourceSet__resourceType__aperiodic__slotOffset__cond SRS_ResourceSet__resourceType__aperiodic__slotOffset__Format.

Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__Format : T_Format Z SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__cond :=
 ranged_int_format (1) (maxNrofSRS_TriggerStates_1) SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__helper1 SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__helper2.

Opaque SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__cond SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__Format.

Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__Format : T_Format SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__Type SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__cond := seq_of_format SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__seq_of__Format 1 maxNrofSRS_TriggerStates_2 SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__helper1 SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__helper2.

Opaque SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__cond SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__Format.


Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__Format_Type := Eval cbn in seq_format_prod SRS_ResourceSet__resourceType__aperiodic__ext0O__list.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__Format_list : SRS_ResourceSet__resourceType__aperiodic__ext0O__Format_Type :=
  (SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList__Format, unit_format).
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__list__Format := (*Eval compute in *) seq_format SRS_ResourceSet__resourceType__aperiodic__ext0O__list SRS_ResourceSet__resourceType__aperiodic__ext0O__Format_list.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__F1 z :=
  (SRS_ResourceSet__resourceType__aperiodic__ext0O__aperiodicSRS_ResourceTriggerList z, tt).
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__F2 (y : seq_type SRS_ResourceSet__resourceType__aperiodic__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SRS_ResourceSet__resourceType__aperiodic__ext0O__Type i0
  end.
Lemma SRS_ResourceSet__resourceType__aperiodic__ext0O__F1F2_cond (z : SRS_ResourceSet__resourceType__aperiodic__ext0O__Type)
  : SRS_ResourceSet__resourceType__aperiodic__ext0O__cond z ->
  (seq_cond SRS_ResourceSet__resourceType__aperiodic__ext0O__list (SRS_ResourceSet__resourceType__aperiodic__ext0O__F1 z)).
intro H. unfold SRS_ResourceSet__resourceType__aperiodic__ext0O__cond in H. simpl. auto. Qed.
Lemma SRS_ResourceSet__resourceType__aperiodic__ext0O__F1F2_cond2 (z : SRS_ResourceSet__resourceType__aperiodic__ext0O__Type)
 : SRS_ResourceSet__resourceType__aperiodic__ext0O__F2 (SRS_ResourceSet__resourceType__aperiodic__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_ResourceSet__resourceType__aperiodic__ext0O__F2F1_cond (y : seq_type SRS_ResourceSet__resourceType__aperiodic__ext0O__list)
  : seq_cond SRS_ResourceSet__resourceType__aperiodic__ext0O__list y ->
 (SRS_ResourceSet__resourceType__aperiodic__ext0O__cond (SRS_ResourceSet__resourceType__aperiodic__ext0O__F2 y)) /\  SRS_ResourceSet__resourceType__aperiodic__ext0O__F1 (SRS_ResourceSet__resourceType__aperiodic__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_ResourceSet__resourceType__aperiodic__ext0O__cond. simpl in *. auto.
 - simpl. unfold SRS_ResourceSet__resourceType__aperiodic__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0O__Format : T_Format SRS_ResourceSet__resourceType__aperiodic__ext0O__Type SRS_ResourceSet__resourceType__aperiodic__ext0O__cond :=
        proj2_format  SRS_ResourceSet__resourceType__aperiodic__ext0O__cond SRS_ResourceSet__resourceType__aperiodic__ext0O__list__Format
    SRS_ResourceSet__resourceType__aperiodic__ext0O__F1 SRS_ResourceSet__resourceType__aperiodic__ext0O__F2 SRS_ResourceSet__resourceType__aperiodic__ext0O__F1F2_cond  SRS_ResourceSet__resourceType__aperiodic__ext0O__F1F2_cond2 SRS_ResourceSet__resourceType__aperiodic__ext0O__F2F1_cond.
Opaque SRS_ResourceSet__resourceType__aperiodic__ext0O__cond SRS_ResourceSet__resourceType__aperiodic__ext0O__Format.

Definition SRS_ResourceSet__resourceType__aperiodic__ext0__check_all_none (b : SRS_ResourceSet__resourceType__aperiodic__ext0O__Type) : bool :=
match b with 
  | make__SRS_ResourceSet__resourceType__aperiodic__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SRS_ResourceSet__resourceType__aperiodic__ext0__Format : T_Format SRS_ResourceSet__resourceType__aperiodic__ext0__Type SRS_ResourceSet__resourceType__aperiodic__ext0__cond :=
  restrict_add_format SRS_ResourceSet__resourceType__aperiodic__ext0__check_all_none SRS_ResourceSet__resourceType__aperiodic__ext0O__Format.

Opaque SRS_ResourceSet__resourceType__aperiodic__ext0__cond SRS_ResourceSet__resourceType__aperiodic__ext0__Format.


Definition SRS_ResourceSet__resourceType__aperiodic__root_Format_Type := Eval cbn in seq_format_prod SRS_ResourceSet__resourceType__aperiodic__root_list.
Definition SRS_ResourceSet__resourceType__aperiodic__root_Format_list : SRS_ResourceSet__resourceType__aperiodic__root_Format_Type :=
  (SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger__Format, (NZP_CSI_RS_ResourceId__Format, (SRS_ResourceSet__resourceType__aperiodic__slotOffset__Format, unit_format))).

Definition SRS_ResourceSet__resourceType__aperiodic__ext_Format_Type := Eval cbn in get_formats SRS_ResourceSet__resourceType__aperiodic__ext_list.
Definition SRS_ResourceSet__resourceType__aperiodic__ext_Format_list : SRS_ResourceSet__resourceType__aperiodic__ext_Format_Type :=
  (SRS_ResourceSet__resourceType__aperiodic__ext0__Format, unit__Format).

Definition SRS_ResourceSet__resourceType__aperiodic__list_type : Set := (seq_type SRS_ResourceSet__resourceType__aperiodic__root_list) * (seq_ext_type SRS_ResourceSet__resourceType__aperiodic__ext_list).
Definition SRS_ResourceSet__resourceType__aperiodic__list_cond (z : SRS_ResourceSet__resourceType__aperiodic__list_type) : Prop :=
        (seq_cond SRS_ResourceSet__resourceType__aperiodic__root_list (fst z)) /\ (seq_ext_cond SRS_ResourceSet__resourceType__aperiodic__ext_list (snd z)).
Definition SRS_ResourceSet__resourceType__aperiodic__list_format : T_Format SRS_ResourceSet__resourceType__aperiodic__list_type SRS_ResourceSet__resourceType__aperiodic__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_ResourceSet__resourceType__aperiodic__root_list SRS_ResourceSet__resourceType__aperiodic__root_Format_list SRS_ResourceSet__resourceType__aperiodic__ext_list SRS_ResourceSet__resourceType__aperiodic__ext_Format_list.

Opaque SRS_ResourceSet__resourceType__aperiodic__list_format.
Definition SRS_ResourceSet__resourceType__aperiodic__F1 (z : SRS_ResourceSet__resourceType__aperiodic__Type) : SRS_ResourceSet__resourceType__aperiodic__list_type :=
  (((SRS_ResourceSet__resourceType__aperiodic__aperiodicSRS_ResourceTrigger z, (SRS_ResourceSet__resourceType__aperiodic__csi_RS z, (SRS_ResourceSet__resourceType__aperiodic__slotOffset z, tt)))), (
(SRS_ResourceSet__resourceType__aperiodic__ext0 z, tt))).
Definition SRS_ResourceSet__resourceType__aperiodic__F2 (y : SRS_ResourceSet__resourceType__aperiodic__list_type) : SRS_ResourceSet__resourceType__aperiodic__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__SRS_ResourceSet__resourceType__aperiodic__Type j0 j1 j2 i0
  end.
Definition SRS_ResourceSet__resourceType__aperiodic__helper1 : (forall a : SRS_ResourceSet__resourceType__aperiodic__Type, SRS_ResourceSet__resourceType__aperiodic__cond a -> SRS_ResourceSet__resourceType__aperiodic__list_cond (SRS_ResourceSet__resourceType__aperiodic__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceSet__resourceType__aperiodic__helper2 : (forall a : SRS_ResourceSet__resourceType__aperiodic__Type, SRS_ResourceSet__resourceType__aperiodic__F2 (SRS_ResourceSet__resourceType__aperiodic__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceSet__resourceType__aperiodic__helper3 : (forall b : SRS_ResourceSet__resourceType__aperiodic__list_type, SRS_ResourceSet__resourceType__aperiodic__list_cond b -> SRS_ResourceSet__resourceType__aperiodic__cond (SRS_ResourceSet__resourceType__aperiodic__F2 b) /\ SRS_ResourceSet__resourceType__aperiodic__F1 (SRS_ResourceSet__resourceType__aperiodic__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_ResourceSet__resourceType__aperiodic__cond, SRS_ResourceSet__resourceType__aperiodic__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_ResourceSet__resourceType__aperiodic__Format : T_Format SRS_ResourceSet__resourceType__aperiodic__Type SRS_ResourceSet__resourceType__aperiodic__cond :=
 proj2_format SRS_ResourceSet__resourceType__aperiodic__cond SRS_ResourceSet__resourceType__aperiodic__list_format  SRS_ResourceSet__resourceType__aperiodic__F1 SRS_ResourceSet__resourceType__aperiodic__F2 SRS_ResourceSet__resourceType__aperiodic__helper1 SRS_ResourceSet__resourceType__aperiodic__helper2 SRS_ResourceSet__resourceType__aperiodic__helper3.

Opaque SRS_ResourceSet__resourceType__aperiodic__cond SRS_ResourceSet__resourceType__aperiodic__Format.


Definition SRS_ResourceSet__resourceType__semi_persistent__root_Format_Type := Eval cbn in seq_format_prod SRS_ResourceSet__resourceType__semi_persistent__root_list.
Definition SRS_ResourceSet__resourceType__semi_persistent__root_Format_list : SRS_ResourceSet__resourceType__semi_persistent__root_Format_Type :=
  (NZP_CSI_RS_ResourceId__Format, unit_format).

Definition SRS_ResourceSet__resourceType__semi_persistent__ext_Format_Type := Eval cbn in get_formats SRS_ResourceSet__resourceType__semi_persistent__ext_list.
Definition SRS_ResourceSet__resourceType__semi_persistent__ext_Format_list : SRS_ResourceSet__resourceType__semi_persistent__ext_Format_Type :=
  unit__Format.

Definition SRS_ResourceSet__resourceType__semi_persistent__list_type : Set := (seq_type SRS_ResourceSet__resourceType__semi_persistent__root_list) * (seq_ext_type SRS_ResourceSet__resourceType__semi_persistent__ext_list).
Definition SRS_ResourceSet__resourceType__semi_persistent__list_cond (z : SRS_ResourceSet__resourceType__semi_persistent__list_type) : Prop :=
        (seq_cond SRS_ResourceSet__resourceType__semi_persistent__root_list (fst z)) /\ (seq_ext_cond SRS_ResourceSet__resourceType__semi_persistent__ext_list (snd z)).
Definition SRS_ResourceSet__resourceType__semi_persistent__list_format : T_Format SRS_ResourceSet__resourceType__semi_persistent__list_type SRS_ResourceSet__resourceType__semi_persistent__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_ResourceSet__resourceType__semi_persistent__root_list SRS_ResourceSet__resourceType__semi_persistent__root_Format_list SRS_ResourceSet__resourceType__semi_persistent__ext_list SRS_ResourceSet__resourceType__semi_persistent__ext_Format_list.

Opaque SRS_ResourceSet__resourceType__semi_persistent__list_format.
Definition SRS_ResourceSet__resourceType__semi_persistent__F1 (z : SRS_ResourceSet__resourceType__semi_persistent__Type) : SRS_ResourceSet__resourceType__semi_persistent__list_type :=
  (((SRS_ResourceSet__resourceType__semi_persistent__associatedCSI_RS z, tt)), (
tt)).
Definition SRS_ResourceSet__resourceType__semi_persistent__F2 (y : SRS_ResourceSet__resourceType__semi_persistent__list_type) : SRS_ResourceSet__resourceType__semi_persistent__Type :=
  match y with
  | ((j0, _), _)=>
    make__SRS_ResourceSet__resourceType__semi_persistent__Type j0
  end.
Definition SRS_ResourceSet__resourceType__semi_persistent__helper1 : (forall a : SRS_ResourceSet__resourceType__semi_persistent__Type, SRS_ResourceSet__resourceType__semi_persistent__cond a -> SRS_ResourceSet__resourceType__semi_persistent__list_cond (SRS_ResourceSet__resourceType__semi_persistent__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceSet__resourceType__semi_persistent__helper2 : (forall a : SRS_ResourceSet__resourceType__semi_persistent__Type, SRS_ResourceSet__resourceType__semi_persistent__F2 (SRS_ResourceSet__resourceType__semi_persistent__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceSet__resourceType__semi_persistent__helper3 : (forall b : SRS_ResourceSet__resourceType__semi_persistent__list_type, SRS_ResourceSet__resourceType__semi_persistent__list_cond b -> SRS_ResourceSet__resourceType__semi_persistent__cond (SRS_ResourceSet__resourceType__semi_persistent__F2 b) /\ SRS_ResourceSet__resourceType__semi_persistent__F1 (SRS_ResourceSet__resourceType__semi_persistent__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_ResourceSet__resourceType__semi_persistent__cond, SRS_ResourceSet__resourceType__semi_persistent__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_ResourceSet__resourceType__semi_persistent__Format : T_Format SRS_ResourceSet__resourceType__semi_persistent__Type SRS_ResourceSet__resourceType__semi_persistent__cond :=
 proj2_format SRS_ResourceSet__resourceType__semi_persistent__cond SRS_ResourceSet__resourceType__semi_persistent__list_format  SRS_ResourceSet__resourceType__semi_persistent__F1 SRS_ResourceSet__resourceType__semi_persistent__F2 SRS_ResourceSet__resourceType__semi_persistent__helper1 SRS_ResourceSet__resourceType__semi_persistent__helper2 SRS_ResourceSet__resourceType__semi_persistent__helper3.

Opaque SRS_ResourceSet__resourceType__semi_persistent__cond SRS_ResourceSet__resourceType__semi_persistent__Format.


Definition SRS_ResourceSet__resourceType__periodic__root_Format_Type := Eval cbn in seq_format_prod SRS_ResourceSet__resourceType__periodic__root_list.
Definition SRS_ResourceSet__resourceType__periodic__root_Format_list : SRS_ResourceSet__resourceType__periodic__root_Format_Type :=
  (NZP_CSI_RS_ResourceId__Format, unit_format).

Definition SRS_ResourceSet__resourceType__periodic__ext_Format_Type := Eval cbn in get_formats SRS_ResourceSet__resourceType__periodic__ext_list.
Definition SRS_ResourceSet__resourceType__periodic__ext_Format_list : SRS_ResourceSet__resourceType__periodic__ext_Format_Type :=
  unit__Format.

Definition SRS_ResourceSet__resourceType__periodic__list_type : Set := (seq_type SRS_ResourceSet__resourceType__periodic__root_list) * (seq_ext_type SRS_ResourceSet__resourceType__periodic__ext_list).
Definition SRS_ResourceSet__resourceType__periodic__list_cond (z : SRS_ResourceSet__resourceType__periodic__list_type) : Prop :=
        (seq_cond SRS_ResourceSet__resourceType__periodic__root_list (fst z)) /\ (seq_ext_cond SRS_ResourceSet__resourceType__periodic__ext_list (snd z)).
Definition SRS_ResourceSet__resourceType__periodic__list_format : T_Format SRS_ResourceSet__resourceType__periodic__list_type SRS_ResourceSet__resourceType__periodic__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_ResourceSet__resourceType__periodic__root_list SRS_ResourceSet__resourceType__periodic__root_Format_list SRS_ResourceSet__resourceType__periodic__ext_list SRS_ResourceSet__resourceType__periodic__ext_Format_list.

Opaque SRS_ResourceSet__resourceType__periodic__list_format.
Definition SRS_ResourceSet__resourceType__periodic__F1 (z : SRS_ResourceSet__resourceType__periodic__Type) : SRS_ResourceSet__resourceType__periodic__list_type :=
  (((SRS_ResourceSet__resourceType__periodic__associatedCSI_RS z, tt)), (
tt)).
Definition SRS_ResourceSet__resourceType__periodic__F2 (y : SRS_ResourceSet__resourceType__periodic__list_type) : SRS_ResourceSet__resourceType__periodic__Type :=
  match y with
  | ((j0, _), _)=>
    make__SRS_ResourceSet__resourceType__periodic__Type j0
  end.
Definition SRS_ResourceSet__resourceType__periodic__helper1 : (forall a : SRS_ResourceSet__resourceType__periodic__Type, SRS_ResourceSet__resourceType__periodic__cond a -> SRS_ResourceSet__resourceType__periodic__list_cond (SRS_ResourceSet__resourceType__periodic__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceSet__resourceType__periodic__helper2 : (forall a : SRS_ResourceSet__resourceType__periodic__Type, SRS_ResourceSet__resourceType__periodic__F2 (SRS_ResourceSet__resourceType__periodic__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceSet__resourceType__periodic__helper3 : (forall b : SRS_ResourceSet__resourceType__periodic__list_type, SRS_ResourceSet__resourceType__periodic__list_cond b -> SRS_ResourceSet__resourceType__periodic__cond (SRS_ResourceSet__resourceType__periodic__F2 b) /\ SRS_ResourceSet__resourceType__periodic__F1 (SRS_ResourceSet__resourceType__periodic__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_ResourceSet__resourceType__periodic__cond, SRS_ResourceSet__resourceType__periodic__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_ResourceSet__resourceType__periodic__Format : T_Format SRS_ResourceSet__resourceType__periodic__Type SRS_ResourceSet__resourceType__periodic__cond :=
 proj2_format SRS_ResourceSet__resourceType__periodic__cond SRS_ResourceSet__resourceType__periodic__list_format  SRS_ResourceSet__resourceType__periodic__F1 SRS_ResourceSet__resourceType__periodic__F2 SRS_ResourceSet__resourceType__periodic__helper1 SRS_ResourceSet__resourceType__periodic__helper2 SRS_ResourceSet__resourceType__periodic__helper3.

Opaque SRS_ResourceSet__resourceType__periodic__cond SRS_ResourceSet__resourceType__periodic__Format.


Definition SRS_ResourceSet__resourceType__Format_Type := Eval cbn in get_formats SRS_ResourceSet__resourceType__list.
Definition SRS_ResourceSet__resourceType__Format_list : SRS_ResourceSet__resourceType__Format_Type :=
  (SRS_ResourceSet__resourceType__aperiodic__Format, (SRS_ResourceSet__resourceType__semi_persistent__Format, (SRS_ResourceSet__resourceType__periodic__Format, unit__Format))).
Definition SRS_ResourceSet__resourceType__list__Format := Eval compute in choice_format SRS_ResourceSet__resourceType__list SRS_ResourceSet__resourceType__len_helper1 SRS_ResourceSet__resourceType__len_helper2  SRS_ResourceSet__resourceType__Format_list.
Definition SRS_ResourceSet__resourceType__F1 (z : SRS_ResourceSet__resourceType__Type) : (choice SRS_ResourceSet__resourceType__list) :=
  match z with
   | SRS_ResourceSet__resourceType__aperiodic t => existT _ 0 t
  | SRS_ResourceSet__resourceType__semi_persistent t => existT _ 1 t
  | SRS_ResourceSet__resourceType__periodic t => existT _ 2 t
  end.
Definition SRS_ResourceSet__resourceType__g := (fun n => typ_set (get_nth_typ SRS_ResourceSet__resourceType__list n)).
Definition SRS_ResourceSet__resourceType__F2 (y : choice SRS_ResourceSet__resourceType__list) : SRS_ResourceSet__resourceType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_ResourceSet__resourceType__g n -> SRS_ResourceSet__resourceType__Type) with
    | 0 => fun (t : SRS_ResourceSet__resourceType__aperiodic__Type) => SRS_ResourceSet__resourceType__aperiodic t 
    | 1 => fun (t : SRS_ResourceSet__resourceType__semi_persistent__Type) => SRS_ResourceSet__resourceType__semi_persistent t 
    | 2 => fun (t : SRS_ResourceSet__resourceType__periodic__Type) => SRS_ResourceSet__resourceType__periodic t 
 | (S (S (S n0))) => (fun (x' : nat) (t'' : SRS_ResourceSet__resourceType__g (S (S (S x')))) =>let t' :=
           eq_rect (get_nth_typ SRS_ResourceSet__resourceType__list (S (S (S x'))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_ResourceSet__resourceType__list (S (S (S x')))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))) in match t' return SRS_ResourceSet__resourceType__Type with end) n0
           end t0).

Lemma SRS_ResourceSet__resourceType__helper2 :  forall (y : SRS_ResourceSet__resourceType__Type), SRS_ResourceSet__resourceType__cond y -> choice_cond SRS_ResourceSet__resourceType__list (SRS_ResourceSet__resourceType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_ResourceSet__resourceType__helper3 :  forall (y : SRS_ResourceSet__resourceType__Type), SRS_ResourceSet__resourceType__F2 (SRS_ResourceSet__resourceType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_ResourceSet__resourceType__helper4 : (forall b : choice SRS_ResourceSet__resourceType__list, choice_cond SRS_ResourceSet__resourceType__list b -> SRS_ResourceSet__resourceType__cond (SRS_ResourceSet__resourceType__F2 b) /\ SRS_ResourceSet__resourceType__F1 (SRS_ResourceSet__resourceType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_ResourceSet__resourceType__F1 SRS_ResourceSet__resourceType__F2.
Definition SRS_ResourceSet__resourceType__Format : T_Format SRS_ResourceSet__resourceType__Type SRS_ResourceSet__resourceType__cond :=
  (* Eval compute in *) proj2_format SRS_ResourceSet__resourceType__cond SRS_ResourceSet__resourceType__list__Format SRS_ResourceSet__resourceType__F1 SRS_ResourceSet__resourceType__F2 SRS_ResourceSet__resourceType__helper2 SRS_ResourceSet__resourceType__helper3 SRS_ResourceSet__resourceType__helper4.
Opaque SRS_ResourceSet__resourceType__cond SRS_ResourceSet__resourceType__Format.

Definition SRS_ResourceSet__usage__Format : T_Format SRS_ResourceSet__usage__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_ResourceSet__usage__nat__Format SRS_ResourceSet__usage__F1 SRS_ResourceSet__usage__F2 SRS_ResourceSet__usage__F1F2 SRS_ResourceSet__usage__F2F1.

Opaque SRS_ResourceSet__usage__cond SRS_ResourceSet__usage__Format.

Definition SRS_ResourceSet__p0__Format : T_Format Z SRS_ResourceSet__p0__cond :=
 ranged_int_format (-202) (24) SRS_ResourceSet__p0__helper1 SRS_ResourceSet__p0__helper2.

Opaque SRS_ResourceSet__p0__cond SRS_ResourceSet__p0__Format.

Definition SRS_ResourceSet__srs_PowerControlAdjustmentStates__Format : T_Format SRS_ResourceSet__srs_PowerControlAdjustmentStates__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_ResourceSet__srs_PowerControlAdjustmentStates__nat__Format SRS_ResourceSet__srs_PowerControlAdjustmentStates__F1 SRS_ResourceSet__srs_PowerControlAdjustmentStates__F2 SRS_ResourceSet__srs_PowerControlAdjustmentStates__F1F2 SRS_ResourceSet__srs_PowerControlAdjustmentStates__F2F1.

Opaque SRS_ResourceSet__srs_PowerControlAdjustmentStates__cond SRS_ResourceSet__srs_PowerControlAdjustmentStates__Format.

Opaque SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__cond SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__Format.


Definition SRS_ResourceSet__ext0O__Format_Type := Eval cbn in seq_format_prod SRS_ResourceSet__ext0O__list.
Definition SRS_ResourceSet__ext0O__Format_list : SRS_ResourceSet__ext0O__Format_Type :=
  (SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16__Format, unit_format).
Definition SRS_ResourceSet__ext0O__list__Format := (*Eval compute in *) seq_format SRS_ResourceSet__ext0O__list SRS_ResourceSet__ext0O__Format_list.
Definition SRS_ResourceSet__ext0O__F1 z :=
  (SRS_ResourceSet__ext0O__pathlossReferenceRSList_r16 z, tt).
Definition SRS_ResourceSet__ext0O__F2 (y : seq_type SRS_ResourceSet__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__SRS_ResourceSet__ext0O__Type i0
  end.
Lemma SRS_ResourceSet__ext0O__F1F2_cond (z : SRS_ResourceSet__ext0O__Type)
  : SRS_ResourceSet__ext0O__cond z ->
  (seq_cond SRS_ResourceSet__ext0O__list (SRS_ResourceSet__ext0O__F1 z)).
intro H. unfold SRS_ResourceSet__ext0O__cond in H. simpl. auto. Qed.
Lemma SRS_ResourceSet__ext0O__F1F2_cond2 (z : SRS_ResourceSet__ext0O__Type)
 : SRS_ResourceSet__ext0O__F2 (SRS_ResourceSet__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_ResourceSet__ext0O__F2F1_cond (y : seq_type SRS_ResourceSet__ext0O__list)
  : seq_cond SRS_ResourceSet__ext0O__list y ->
 (SRS_ResourceSet__ext0O__cond (SRS_ResourceSet__ext0O__F2 y)) /\  SRS_ResourceSet__ext0O__F1 (SRS_ResourceSet__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_ResourceSet__ext0O__cond. simpl in *. auto.
 - simpl. unfold SRS_ResourceSet__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_ResourceSet__ext0O__Format : T_Format SRS_ResourceSet__ext0O__Type SRS_ResourceSet__ext0O__cond :=
        proj2_format  SRS_ResourceSet__ext0O__cond SRS_ResourceSet__ext0O__list__Format
    SRS_ResourceSet__ext0O__F1 SRS_ResourceSet__ext0O__F2 SRS_ResourceSet__ext0O__F1F2_cond  SRS_ResourceSet__ext0O__F1F2_cond2 SRS_ResourceSet__ext0O__F2F1_cond.
Opaque SRS_ResourceSet__ext0O__cond SRS_ResourceSet__ext0O__Format.

Definition SRS_ResourceSet__ext0__check_all_none (b : SRS_ResourceSet__ext0O__Type) : bool :=
match b with 
  | make__SRS_ResourceSet__ext0O__Type None  => false 
  | _ => true 
 end.
Definition SRS_ResourceSet__ext0__Format : T_Format SRS_ResourceSet__ext0__Type SRS_ResourceSet__ext0__cond :=
  restrict_add_format SRS_ResourceSet__ext0__check_all_none SRS_ResourceSet__ext0O__Format.

Opaque SRS_ResourceSet__ext0__cond SRS_ResourceSet__ext0__Format.

Definition SRS_ResourceSet__ext1O__usagePDC_r17__Format : T_Format SRS_ResourceSet__ext1O__usagePDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_ResourceSet__ext1O__usagePDC_r17__nat__Format SRS_ResourceSet__ext1O__usagePDC_r17__F1 SRS_ResourceSet__ext1O__usagePDC_r17__F2 SRS_ResourceSet__ext1O__usagePDC_r17__F1F2 SRS_ResourceSet__ext1O__usagePDC_r17__F2F1.

Opaque SRS_ResourceSet__ext1O__usagePDC_r17__cond SRS_ResourceSet__ext1O__usagePDC_r17__Format.

Definition SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__Format : T_Format SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__Type SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__cond := seq_of_format AvailableSlotOffset_r17__Format 1 4 SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__helper1 SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__helper2.

Opaque SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__cond SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__Format.

Definition SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Format : T_Format SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__nat__Format SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F1 SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F2 SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F1F2 SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__F2F1.

Opaque SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__cond SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Format.


Definition SRS_ResourceSet__ext1O__Format_Type := Eval cbn in seq_format_prod SRS_ResourceSet__ext1O__list.
Definition SRS_ResourceSet__ext1O__Format_list : SRS_ResourceSet__ext1O__Format_Type :=
  (SRS_ResourceSet__ext1O__usagePDC_r17__Format, (SRS_ResourceSet__ext1O__availableSlotOffsetList_r17__Format, (SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17__Format, unit_format))).
Definition SRS_ResourceSet__ext1O__list__Format := (*Eval compute in *) seq_format SRS_ResourceSet__ext1O__list SRS_ResourceSet__ext1O__Format_list.
Definition SRS_ResourceSet__ext1O__F1 z :=
  (SRS_ResourceSet__ext1O__usagePDC_r17 z, (SRS_ResourceSet__ext1O__availableSlotOffsetList_r17 z, (SRS_ResourceSet__ext1O__followUnifiedTCI_StateSRS_r17 z, tt))).
Definition SRS_ResourceSet__ext1O__F2 (y : seq_type SRS_ResourceSet__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SRS_ResourceSet__ext1O__Type i0 i1 i2
  end.
Lemma SRS_ResourceSet__ext1O__F1F2_cond (z : SRS_ResourceSet__ext1O__Type)
  : SRS_ResourceSet__ext1O__cond z ->
  (seq_cond SRS_ResourceSet__ext1O__list (SRS_ResourceSet__ext1O__F1 z)).
intro H. unfold SRS_ResourceSet__ext1O__cond in H. simpl. auto. Qed.
Lemma SRS_ResourceSet__ext1O__F1F2_cond2 (z : SRS_ResourceSet__ext1O__Type)
 : SRS_ResourceSet__ext1O__F2 (SRS_ResourceSet__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SRS_ResourceSet__ext1O__F2F1_cond (y : seq_type SRS_ResourceSet__ext1O__list)
  : seq_cond SRS_ResourceSet__ext1O__list y ->
 (SRS_ResourceSet__ext1O__cond (SRS_ResourceSet__ext1O__F2 y)) /\  SRS_ResourceSet__ext1O__F1 (SRS_ResourceSet__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SRS_ResourceSet__ext1O__cond. simpl in *. auto.
 - simpl. unfold SRS_ResourceSet__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SRS_ResourceSet__ext1O__Format : T_Format SRS_ResourceSet__ext1O__Type SRS_ResourceSet__ext1O__cond :=
        proj2_format  SRS_ResourceSet__ext1O__cond SRS_ResourceSet__ext1O__list__Format
    SRS_ResourceSet__ext1O__F1 SRS_ResourceSet__ext1O__F2 SRS_ResourceSet__ext1O__F1F2_cond  SRS_ResourceSet__ext1O__F1F2_cond2 SRS_ResourceSet__ext1O__F2F1_cond.
Opaque SRS_ResourceSet__ext1O__cond SRS_ResourceSet__ext1O__Format.

Definition SRS_ResourceSet__ext1__check_all_none (b : SRS_ResourceSet__ext1O__Type) : bool :=
match b with 
  | make__SRS_ResourceSet__ext1O__Type None None None  => false 
  | _ => true 
 end.
Definition SRS_ResourceSet__ext1__Format : T_Format SRS_ResourceSet__ext1__Type SRS_ResourceSet__ext1__cond :=
  restrict_add_format SRS_ResourceSet__ext1__check_all_none SRS_ResourceSet__ext1O__Format.

Opaque SRS_ResourceSet__ext1__cond SRS_ResourceSet__ext1__Format.


Definition SRS_ResourceSet__root_Format_Type := Eval cbn in seq_format_prod SRS_ResourceSet__root_list.
Definition SRS_ResourceSet__root_Format_list : SRS_ResourceSet__root_Format_Type :=
  (SRS_ResourceSetId__Format, (SRS_ResourceSet__srs_ResourceIdList__Format, (SRS_ResourceSet__resourceType__Format, (SRS_ResourceSet__usage__Format, (Alpha__Format, (SRS_ResourceSet__p0__Format, (PathlossReferenceRS_Config__Format, (SRS_ResourceSet__srs_PowerControlAdjustmentStates__Format, unit_format)))))))).

Definition SRS_ResourceSet__ext_Format_Type := Eval cbn in get_formats SRS_ResourceSet__ext_list.
Definition SRS_ResourceSet__ext_Format_list : SRS_ResourceSet__ext_Format_Type :=
  (SRS_ResourceSet__ext0__Format, (SRS_ResourceSet__ext1__Format, unit__Format)).

Definition SRS_ResourceSet__list_type : Set := (seq_type SRS_ResourceSet__root_list) * (seq_ext_type SRS_ResourceSet__ext_list).
Definition SRS_ResourceSet__list_cond (z : SRS_ResourceSet__list_type) : Prop :=
        (seq_cond SRS_ResourceSet__root_list (fst z)) /\ (seq_ext_cond SRS_ResourceSet__ext_list (snd z)).
Definition SRS_ResourceSet__list_format : T_Format SRS_ResourceSet__list_type SRS_ResourceSet__list_cond :=
 (* Eval compute in *) seq_ext_format SRS_ResourceSet__root_list SRS_ResourceSet__root_Format_list SRS_ResourceSet__ext_list SRS_ResourceSet__ext_Format_list.

Opaque SRS_ResourceSet__list_format.
Definition SRS_ResourceSet__F1 (z : SRS_ResourceSet__Type) : SRS_ResourceSet__list_type :=
  (((SRS_ResourceSet__srs_ResourceSetId z, (SRS_ResourceSet__srs_ResourceIdList z, (SRS_ResourceSet__resourceType z, (SRS_ResourceSet__usage z, (SRS_ResourceSet__alpha z, (SRS_ResourceSet__p0 z, (SRS_ResourceSet__pathlossReferenceRS z, (SRS_ResourceSet__srs_PowerControlAdjustmentStates z, tt))))))))), (
(SRS_ResourceSet__ext0 z, (SRS_ResourceSet__ext1 z, tt)))).
Definition SRS_ResourceSet__F2 (y : SRS_ResourceSet__list_type) : SRS_ResourceSet__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, _)))))))), (i0, (i1, _)))=>
    make__SRS_ResourceSet__Type j0 j1 j2 j3 j4 j5 j6 j7 i0 i1
  end.
Definition SRS_ResourceSet__helper1 : (forall a : SRS_ResourceSet__Type, SRS_ResourceSet__cond a -> SRS_ResourceSet__list_cond (SRS_ResourceSet__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceSet__helper2 : (forall a : SRS_ResourceSet__Type, SRS_ResourceSet__F2 (SRS_ResourceSet__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SRS_ResourceSet__helper3 : (forall b : SRS_ResourceSet__list_type, SRS_ResourceSet__list_cond b -> SRS_ResourceSet__cond (SRS_ResourceSet__F2 b) /\ SRS_ResourceSet__F1 (SRS_ResourceSet__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SRS_ResourceSet__cond, SRS_ResourceSet__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SRS_ResourceSet__Format : T_Format SRS_ResourceSet__Type SRS_ResourceSet__cond :=
 proj2_format SRS_ResourceSet__cond SRS_ResourceSet__list_format  SRS_ResourceSet__F1 SRS_ResourceSet__F2 SRS_ResourceSet__helper1 SRS_ResourceSet__helper2 SRS_ResourceSet__helper3.

Opaque SRS_ResourceSet__cond SRS_ResourceSet__Format.

