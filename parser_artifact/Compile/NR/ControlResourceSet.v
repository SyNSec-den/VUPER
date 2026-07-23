Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ControlResourceSetId.

Opaque ControlResourceSetId__cond ControlResourceSetId__Format.

Definition ControlResourceSet__frequencyDomainResources__Type := bit_string_fixed.
Definition ControlResourceSet__frequencyDomainResources__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 45 /\ bit_string_len_prop (fst z) (snd z)).
Lemma ControlResourceSet__duration__helper1 : (1 <= maxCoReSetDuration)%Z. unfold maxCoReSetDuration.
 lia. Qed.
Lemma ControlResourceSet__duration__helper2 : to_bit_sz (Z.to_nat (maxCoReSetDuration - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCoReSetDuration - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ControlResourceSet__duration__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ControlResourceSet__duration__Type := Z.
Definition ControlResourceSet__duration__cond := (fun z => (1 <= z <= maxCoReSetDuration)%Z).
Inductive ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Type : Set :=
 | ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n2
 | ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n3
 | ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n6
.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__cond := (fun (_ : ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Type) => True).
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__nat__helper.

Definition ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F1 t :=
  match t with
  | ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n2 => 0
  | ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n3 => 1
  | ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n6 => 2
  end.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F2 n :=
  match n with
  | 0 => ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n2
  | 1 => ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n3
  | 2 => ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n6
  | _ => ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__n2
  end.
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F1F2 : forall x : ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Type, (ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F1 x <= 2) /\ ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F2 (ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F1 x) = x. imp_solve. Qed.
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F2F1 : forall (y : nat) (H : y <= 2), ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F1 (ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F2 y) = y. enum_solve H y. Qed.

Inductive ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Type : Set :=
 | ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n2
 | ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n3
 | ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n6
.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__cond := (fun (_ : ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Type) => True).
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__nat__helper.

Definition ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F1 t :=
  match t with
  | ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n2 => 0
  | ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n3 => 1
  | ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n6 => 2
  end.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F2 n :=
  match n with
  | 0 => ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n2
  | 1 => ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n3
  | 2 => ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n6
  | _ => ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__n2
  end.
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F1F2 : forall x : ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Type, (ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F1 x <= 2) /\ ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F2 (ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F1 x) = x. imp_solve. Qed.
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F2F1 : forall (y : nat) (H : y <= 2), ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F1 (ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F2 y) = y. enum_solve H y. Qed.

Lemma ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__helper1 : (0 <= maxNrofPhysicalResourceBlocks_1)%Z. unfold maxNrofPhysicalResourceBlocks_1.
 lia. Qed.
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__helper2 : to_bit_sz (Z.to_nat (maxNrofPhysicalResourceBlocks_1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofPhysicalResourceBlocks_1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__Type := Z.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__cond := (fun z => (0 <= z <= maxNrofPhysicalResourceBlocks_1)%Z).
Record ControlResourceSet__cce_REG_MappingType__interleaved__Type : Set :=
  make__ControlResourceSet__cce_REG_MappingType__interleaved__Type {
    ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize : ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Type ;
    ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize : ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Type ;
    ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex : option Z ;
}.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__list := (
 Nor ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Type ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__cond ::
 Nor ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Type ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__cond ::
 Opt Z ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__cond ::
 nil).
Definition ControlResourceSet__cce_REG_MappingType__interleaved__cond z := 
  ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__cond (ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize z) /\
  ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__cond (ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize z) /\
  opt_cond ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__cond (ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex z) /\
  True.


Inductive ControlResourceSet__cce_REG_MappingType__Type : Set :=
  | ControlResourceSet__cce_REG_MappingType__interleaved : ControlResourceSet__cce_REG_MappingType__interleaved__Type -> ControlResourceSet__cce_REG_MappingType__Type
  | ControlResourceSet__cce_REG_MappingType__nonInterleaved : unit -> ControlResourceSet__cce_REG_MappingType__Type
.
Definition ControlResourceSet__cce_REG_MappingType__list : list typ := (
typ_cons ControlResourceSet__cce_REG_MappingType__interleaved__Type ControlResourceSet__cce_REG_MappingType__interleaved__cond ::
typ_cons unit (fun _ => True) ::
 nil).
Definition ControlResourceSet__cce_REG_MappingType__cond (c : ControlResourceSet__cce_REG_MappingType__Type) := 
  match c with
  | ControlResourceSet__cce_REG_MappingType__interleaved t => ControlResourceSet__cce_REG_MappingType__interleaved__cond t 
  | ControlResourceSet__cce_REG_MappingType__nonInterleaved t => (fun _ => True) t 
  end.

Lemma ControlResourceSet__cce_REG_MappingType__len_helper1 : to_bit_sz (length ControlResourceSet__cce_REG_MappingType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ControlResourceSet__cce_REG_MappingType__len_helper2 : 2 <= length2 ControlResourceSet__cce_REG_MappingType__list.
 simpl. lia. Qed.
Inductive ControlResourceSet__precoderGranularity__Type : Set :=
 | ControlResourceSet__precoderGranularity__sameAsREG_bundle
 | ControlResourceSet__precoderGranularity__allContiguousRBs
.
Definition ControlResourceSet__precoderGranularity__cond := (fun (_ : ControlResourceSet__precoderGranularity__Type) => True).
Lemma ControlResourceSet__precoderGranularity__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ControlResourceSet__precoderGranularity__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 ControlResourceSet__precoderGranularity__nat__helper.

Definition ControlResourceSet__precoderGranularity__F1 t :=
  match t with
  | ControlResourceSet__precoderGranularity__sameAsREG_bundle => 0
  | ControlResourceSet__precoderGranularity__allContiguousRBs => 1
  end.
Definition ControlResourceSet__precoderGranularity__F2 n :=
  match n with
  | 0 => ControlResourceSet__precoderGranularity__sameAsREG_bundle
  | 1 => ControlResourceSet__precoderGranularity__allContiguousRBs
  | _ => ControlResourceSet__precoderGranularity__sameAsREG_bundle
  end.
Lemma ControlResourceSet__precoderGranularity__F1F2 : forall x : ControlResourceSet__precoderGranularity__Type, (ControlResourceSet__precoderGranularity__F1 x <= 1) /\ ControlResourceSet__precoderGranularity__F2 (ControlResourceSet__precoderGranularity__F1 x) = x. imp_solve. Qed.
Lemma ControlResourceSet__precoderGranularity__F2F1 : forall (y : nat) (H : y <= 1), ControlResourceSet__precoderGranularity__F1 (ControlResourceSet__precoderGranularity__F2 y) = y. enum_solve H y. Qed.

Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Definition ControlResourceSet__tci_StatesPDCCH_ToAddList__Type := list TCI_StateId__Type.

Lemma ControlResourceSet__tci_StatesPDCCH_ToAddList__helper1 : (0 <= 1 <= maxNrofTCI_StatesPDCCH)%Z. unfold maxNrofTCI_StatesPDCCH.
 lia. Qed.
Lemma ControlResourceSet__tci_StatesPDCCH_ToAddList__helper2 : to_bit_sz (Z.to_nat (maxNrofTCI_StatesPDCCH - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTCI_StatesPDCCH - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ControlResourceSet__tci_StatesPDCCH_ToAddList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ControlResourceSet__tci_StatesPDCCH_ToAddList__cond (z : ControlResourceSet__tci_StatesPDCCH_ToAddList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofTCI_StatesPDCCH)%Z /\ (list_and TCI_StateId__cond z) .

Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Definition ControlResourceSet__tci_StatesPDCCH_ToReleaseList__Type := list TCI_StateId__Type.

Lemma ControlResourceSet__tci_StatesPDCCH_ToReleaseList__helper1 : (0 <= 1 <= maxNrofTCI_StatesPDCCH)%Z. unfold maxNrofTCI_StatesPDCCH.
 lia. Qed.
Lemma ControlResourceSet__tci_StatesPDCCH_ToReleaseList__helper2 : to_bit_sz (Z.to_nat (maxNrofTCI_StatesPDCCH - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofTCI_StatesPDCCH - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ControlResourceSet__tci_StatesPDCCH_ToReleaseList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ControlResourceSet__tci_StatesPDCCH_ToReleaseList__cond (z : ControlResourceSet__tci_StatesPDCCH_ToReleaseList__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofTCI_StatesPDCCH)%Z /\ (list_and TCI_StateId__cond z) .

Inductive ControlResourceSet__tci_PresentInDCI__Type : Set :=
 | ControlResourceSet__tci_PresentInDCI__enabled
.
Definition ControlResourceSet__tci_PresentInDCI__cond := (fun (_ : ControlResourceSet__tci_PresentInDCI__Type) => True).
Lemma ControlResourceSet__tci_PresentInDCI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ControlResourceSet__tci_PresentInDCI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ControlResourceSet__tci_PresentInDCI__nat__helper.

Definition ControlResourceSet__tci_PresentInDCI__F1 t :=
  match t with
  | ControlResourceSet__tci_PresentInDCI__enabled => 0
  end.
Definition ControlResourceSet__tci_PresentInDCI__F2 n :=
  match n with
  | 0 => ControlResourceSet__tci_PresentInDCI__enabled
  | _ => ControlResourceSet__tci_PresentInDCI__enabled
  end.
Lemma ControlResourceSet__tci_PresentInDCI__F1F2 : forall x : ControlResourceSet__tci_PresentInDCI__Type, (ControlResourceSet__tci_PresentInDCI__F1 x <= 0) /\ ControlResourceSet__tci_PresentInDCI__F2 (ControlResourceSet__tci_PresentInDCI__F1 x) = x. imp_solve. Qed.
Lemma ControlResourceSet__tci_PresentInDCI__F2F1 : forall (y : nat) (H : y <= 0), ControlResourceSet__tci_PresentInDCI__F1 (ControlResourceSet__tci_PresentInDCI__F2 y) = y. enum_solve H y. Qed.

Lemma ControlResourceSet__pdcch_DMRS_ScramblingID__helper1 : (0 <= 65535)%Z.  lia. Qed.
Lemma ControlResourceSet__pdcch_DMRS_ScramblingID__helper2 : to_bit_sz (Z.to_nat (65535 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65535 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ControlResourceSet__pdcch_DMRS_ScramblingID__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ControlResourceSet__pdcch_DMRS_ScramblingID__Type := Z.
Definition ControlResourceSet__pdcch_DMRS_ScramblingID__cond := (fun z => (0 <= z <= 65535)%Z).
Lemma ControlResourceSet__ext0O__rb_Offset_r16__helper1 : (0 <= 5)%Z.  lia. Qed.
Lemma ControlResourceSet__ext0O__rb_Offset_r16__helper2 : to_bit_sz (Z.to_nat (5 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ControlResourceSet__ext0O__rb_Offset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ControlResourceSet__ext0O__rb_Offset_r16__Type := Z.
Definition ControlResourceSet__ext0O__rb_Offset_r16__cond := (fun z => (0 <= z <= 5)%Z).
Lemma ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__helper1 : (1 <= 3)%Z.  lia. Qed.
Lemma ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__Type := Z.
Definition ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__cond := (fun z => (1 <= z <= 3)%Z).
Lemma ControlResourceSet__ext0O__coresetPoolIndex_r16__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma ControlResourceSet__ext0O__coresetPoolIndex_r16__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ControlResourceSet__ext0O__coresetPoolIndex_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ControlResourceSet__ext0O__coresetPoolIndex_r16__Type := Z.
Definition ControlResourceSet__ext0O__coresetPoolIndex_r16__cond := (fun z => (0 <= z <= 1)%Z).
Require Import NR.ControlResourceSetId_v1610.

Opaque ControlResourceSetId_v1610__cond ControlResourceSetId_v1610__Format.

Record ControlResourceSet__ext0O__Type : Set :=
  make__ControlResourceSet__ext0O__Type {
    ControlResourceSet__ext0O__rb_Offset_r16 : option Z ;
    ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16 : option Z ;
    ControlResourceSet__ext0O__coresetPoolIndex_r16 : option Z ;
    ControlResourceSet__ext0O__controlResourceSetId_v1610 : option ControlResourceSetId_v1610__Type ;
}.
Definition ControlResourceSet__ext0O__list := (
 Opt Z ControlResourceSet__ext0O__rb_Offset_r16__cond ::
 Opt Z ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__cond ::
 Opt Z ControlResourceSet__ext0O__coresetPoolIndex_r16__cond ::
 Opt ControlResourceSetId_v1610__Type ControlResourceSetId_v1610__cond ::
 nil).
Definition ControlResourceSet__ext0O__cond z := 
  opt_cond ControlResourceSet__ext0O__rb_Offset_r16__cond (ControlResourceSet__ext0O__rb_Offset_r16 z) /\
  opt_cond ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__cond (ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16 z) /\
  opt_cond ControlResourceSet__ext0O__coresetPoolIndex_r16__cond (ControlResourceSet__ext0O__coresetPoolIndex_r16 z) /\
  opt_cond ControlResourceSetId_v1610__cond (ControlResourceSet__ext0O__controlResourceSetId_v1610 z) /\
  True.

Definition ControlResourceSet__ext0__Type := ControlResourceSet__ext0O__Type.
Definition ControlResourceSet__ext0__cond := ControlResourceSet__ext0O__cond.

Inductive ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Type : Set :=
 | ControlResourceSet__ext1O__followUnifiedTCI_State_r17__enabled
.
Definition ControlResourceSet__ext1O__followUnifiedTCI_State_r17__cond := (fun (_ : ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Type) => True).
Lemma ControlResourceSet__ext1O__followUnifiedTCI_State_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ControlResourceSet__ext1O__followUnifiedTCI_State_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ControlResourceSet__ext1O__followUnifiedTCI_State_r17__nat__helper.

Definition ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F1 t :=
  match t with
  | ControlResourceSet__ext1O__followUnifiedTCI_State_r17__enabled => 0
  end.
Definition ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F2 n :=
  match n with
  | 0 => ControlResourceSet__ext1O__followUnifiedTCI_State_r17__enabled
  | _ => ControlResourceSet__ext1O__followUnifiedTCI_State_r17__enabled
  end.
Lemma ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F1F2 : forall x : ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Type, (ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F1 x <= 0) /\ ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F2 (ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F1 x) = x. imp_solve. Qed.
Lemma ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F2F1 : forall (y : nat) (H : y <= 0), ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F1 (ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F2 y) = y. enum_solve H y. Qed.

Record ControlResourceSet__ext1O__Type : Set :=
  make__ControlResourceSet__ext1O__Type {
    ControlResourceSet__ext1O__followUnifiedTCI_State_r17 : option ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Type ;
}.
Definition ControlResourceSet__ext1O__list := (
 Opt ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Type ControlResourceSet__ext1O__followUnifiedTCI_State_r17__cond ::
 nil).
Definition ControlResourceSet__ext1O__cond z := 
  opt_cond ControlResourceSet__ext1O__followUnifiedTCI_State_r17__cond (ControlResourceSet__ext1O__followUnifiedTCI_State_r17 z) /\
  True.

Definition ControlResourceSet__ext1__Type := ControlResourceSet__ext1O__Type.
Definition ControlResourceSet__ext1__cond := ControlResourceSet__ext1O__cond.

Record ControlResourceSet__Type : Set :=
  make__ControlResourceSet__Type {
    ControlResourceSet__controlResourceSetId : ControlResourceSetId__Type ;
    ControlResourceSet__frequencyDomainResources : ControlResourceSet__frequencyDomainResources__Type ;
    ControlResourceSet__duration : Z ;
    ControlResourceSet__cce_REG_MappingType : ControlResourceSet__cce_REG_MappingType__Type ;
    ControlResourceSet__precoderGranularity : ControlResourceSet__precoderGranularity__Type ;
    ControlResourceSet__tci_StatesPDCCH_ToAddList : option ControlResourceSet__tci_StatesPDCCH_ToAddList__Type ;
    ControlResourceSet__tci_StatesPDCCH_ToReleaseList : option ControlResourceSet__tci_StatesPDCCH_ToReleaseList__Type ;
    ControlResourceSet__tci_PresentInDCI : option ControlResourceSet__tci_PresentInDCI__Type ;
    ControlResourceSet__pdcch_DMRS_ScramblingID : option Z ;
    ControlResourceSet__ext0 : option ControlResourceSet__ext0__Type ;
    ControlResourceSet__ext1 : option ControlResourceSet__ext1__Type ;
}.
Definition ControlResourceSet__root_list : list seq_elem := (
 Nor ControlResourceSetId__Type ControlResourceSetId__cond ::
 Nor ControlResourceSet__frequencyDomainResources__Type ControlResourceSet__frequencyDomainResources__cond ::
 Nor Z ControlResourceSet__duration__cond ::
 Nor ControlResourceSet__cce_REG_MappingType__Type ControlResourceSet__cce_REG_MappingType__cond ::
 Nor ControlResourceSet__precoderGranularity__Type ControlResourceSet__precoderGranularity__cond ::
 Opt ControlResourceSet__tci_StatesPDCCH_ToAddList__Type ControlResourceSet__tci_StatesPDCCH_ToAddList__cond ::
 Opt ControlResourceSet__tci_StatesPDCCH_ToReleaseList__Type ControlResourceSet__tci_StatesPDCCH_ToReleaseList__cond ::
 Opt ControlResourceSet__tci_PresentInDCI__Type ControlResourceSet__tci_PresentInDCI__cond ::
 Opt Z ControlResourceSet__pdcch_DMRS_ScramblingID__cond ::
 nil).
Definition ControlResourceSet__ext_list : list typ := (
  typ_cons ControlResourceSet__ext0__Type ControlResourceSet__ext0__cond ::
  typ_cons ControlResourceSet__ext1__Type ControlResourceSet__ext1__cond ::
  nil).
Definition ControlResourceSet__cond (z : ControlResourceSet__Type) := 
(  ControlResourceSetId__cond (ControlResourceSet__controlResourceSetId z) /\
  ControlResourceSet__frequencyDomainResources__cond (ControlResourceSet__frequencyDomainResources z) /\
  ControlResourceSet__duration__cond (ControlResourceSet__duration z) /\
  ControlResourceSet__cce_REG_MappingType__cond (ControlResourceSet__cce_REG_MappingType z) /\
  ControlResourceSet__precoderGranularity__cond (ControlResourceSet__precoderGranularity z) /\
  opt_cond ControlResourceSet__tci_StatesPDCCH_ToAddList__cond (ControlResourceSet__tci_StatesPDCCH_ToAddList z) /\
  opt_cond ControlResourceSet__tci_StatesPDCCH_ToReleaseList__cond (ControlResourceSet__tci_StatesPDCCH_ToReleaseList z) /\
  opt_cond ControlResourceSet__tci_PresentInDCI__cond (ControlResourceSet__tci_PresentInDCI z) /\
  opt_cond ControlResourceSet__pdcch_DMRS_ScramblingID__cond (ControlResourceSet__pdcch_DMRS_ScramblingID z) /\
  True) /\ 
(  opt_cond ControlResourceSet__ext0__cond (ControlResourceSet__ext0 z) /\
  opt_cond ControlResourceSet__ext1__cond (ControlResourceSet__ext1 z) /\
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
Definition ControlResourceSet__frequencyDomainResources__Format : T_Format ControlResourceSet__frequencyDomainResources__Type ControlResourceSet__frequencyDomainResources__cond := (* Eval compute in *) bit_string_fixed_format 45.
Opaque ControlResourceSet__frequencyDomainResources__cond ControlResourceSet__frequencyDomainResources__Format.

Definition ControlResourceSet__duration__Format : T_Format Z ControlResourceSet__duration__cond :=
 ranged_int_format (1) (maxCoReSetDuration) ControlResourceSet__duration__helper1 ControlResourceSet__duration__helper2.

Opaque ControlResourceSet__duration__cond ControlResourceSet__duration__Format.

Definition ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Format : T_Format ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__nat__Format ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F1 ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F2 ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F1F2 ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__F2F1.

Opaque ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__cond ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Format.

Definition ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Format : T_Format ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__nat__Format ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F1 ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F2 ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F1F2 ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__F2F1.

Opaque ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__cond ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Format.

Definition ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__Format : T_Format Z ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__cond :=
 ranged_int_format (0) (maxNrofPhysicalResourceBlocks_1) ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__helper1 ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__helper2.

Opaque ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__cond ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__Format.


Definition ControlResourceSet__cce_REG_MappingType__interleaved__Format_Type := Eval cbn in seq_format_prod ControlResourceSet__cce_REG_MappingType__interleaved__list.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__Format_list : ControlResourceSet__cce_REG_MappingType__interleaved__Format_Type :=
  (ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize__Format, (ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize__Format, (ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex__Format, unit_format))).
Definition ControlResourceSet__cce_REG_MappingType__interleaved__list__Format := (*Eval compute in *) seq_format ControlResourceSet__cce_REG_MappingType__interleaved__list ControlResourceSet__cce_REG_MappingType__interleaved__Format_list.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__F1 z :=
  (ControlResourceSet__cce_REG_MappingType__interleaved__reg_BundleSize z, (ControlResourceSet__cce_REG_MappingType__interleaved__interleaverSize z, (ControlResourceSet__cce_REG_MappingType__interleaved__shiftIndex z, tt))).
Definition ControlResourceSet__cce_REG_MappingType__interleaved__F2 (y : seq_type ControlResourceSet__cce_REG_MappingType__interleaved__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ControlResourceSet__cce_REG_MappingType__interleaved__Type i0 i1 i2
  end.
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__F1F2_cond (z : ControlResourceSet__cce_REG_MappingType__interleaved__Type)
  : ControlResourceSet__cce_REG_MappingType__interleaved__cond z ->
  (seq_cond ControlResourceSet__cce_REG_MappingType__interleaved__list (ControlResourceSet__cce_REG_MappingType__interleaved__F1 z)).
intro H. unfold ControlResourceSet__cce_REG_MappingType__interleaved__cond in H. simpl. auto. Qed.
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__F1F2_cond2 (z : ControlResourceSet__cce_REG_MappingType__interleaved__Type)
 : ControlResourceSet__cce_REG_MappingType__interleaved__F2 (ControlResourceSet__cce_REG_MappingType__interleaved__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ControlResourceSet__cce_REG_MappingType__interleaved__F2F1_cond (y : seq_type ControlResourceSet__cce_REG_MappingType__interleaved__list)
  : seq_cond ControlResourceSet__cce_REG_MappingType__interleaved__list y ->
 (ControlResourceSet__cce_REG_MappingType__interleaved__cond (ControlResourceSet__cce_REG_MappingType__interleaved__F2 y)) /\  ControlResourceSet__cce_REG_MappingType__interleaved__F1 (ControlResourceSet__cce_REG_MappingType__interleaved__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ControlResourceSet__cce_REG_MappingType__interleaved__cond. simpl in *. auto.
 - simpl. unfold ControlResourceSet__cce_REG_MappingType__interleaved__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ControlResourceSet__cce_REG_MappingType__interleaved__Format : T_Format ControlResourceSet__cce_REG_MappingType__interleaved__Type ControlResourceSet__cce_REG_MappingType__interleaved__cond :=
        proj2_format  ControlResourceSet__cce_REG_MappingType__interleaved__cond ControlResourceSet__cce_REG_MappingType__interleaved__list__Format
    ControlResourceSet__cce_REG_MappingType__interleaved__F1 ControlResourceSet__cce_REG_MappingType__interleaved__F2 ControlResourceSet__cce_REG_MappingType__interleaved__F1F2_cond  ControlResourceSet__cce_REG_MappingType__interleaved__F1F2_cond2 ControlResourceSet__cce_REG_MappingType__interleaved__F2F1_cond.
Opaque ControlResourceSet__cce_REG_MappingType__interleaved__cond ControlResourceSet__cce_REG_MappingType__interleaved__Format.


Definition ControlResourceSet__cce_REG_MappingType__Format_Type := Eval cbn in get_formats ControlResourceSet__cce_REG_MappingType__list.
Definition ControlResourceSet__cce_REG_MappingType__Format_list : ControlResourceSet__cce_REG_MappingType__Format_Type :=
  (ControlResourceSet__cce_REG_MappingType__interleaved__Format, (unit__Format, unit__Format)).
Definition ControlResourceSet__cce_REG_MappingType__list__Format := Eval compute in choice_format ControlResourceSet__cce_REG_MappingType__list ControlResourceSet__cce_REG_MappingType__len_helper1 ControlResourceSet__cce_REG_MappingType__len_helper2  ControlResourceSet__cce_REG_MappingType__Format_list.
Definition ControlResourceSet__cce_REG_MappingType__F1 (z : ControlResourceSet__cce_REG_MappingType__Type) : (choice ControlResourceSet__cce_REG_MappingType__list) :=
  match z with
   | ControlResourceSet__cce_REG_MappingType__interleaved t => existT _ 0 t
  | ControlResourceSet__cce_REG_MappingType__nonInterleaved t => existT _ 1 t
  end.
Definition ControlResourceSet__cce_REG_MappingType__g := (fun n => typ_set (get_nth_typ ControlResourceSet__cce_REG_MappingType__list n)).
Definition ControlResourceSet__cce_REG_MappingType__F2 (y : choice ControlResourceSet__cce_REG_MappingType__list) : ControlResourceSet__cce_REG_MappingType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ControlResourceSet__cce_REG_MappingType__g n -> ControlResourceSet__cce_REG_MappingType__Type) with
    | 0 => fun (t : ControlResourceSet__cce_REG_MappingType__interleaved__Type) => ControlResourceSet__cce_REG_MappingType__interleaved t 
    | 1 => fun (t : unit) => ControlResourceSet__cce_REG_MappingType__nonInterleaved t 
 | (S (S n0)) => (fun (x' : nat) (t'' : ControlResourceSet__cce_REG_MappingType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ ControlResourceSet__cce_REG_MappingType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ControlResourceSet__cce_REG_MappingType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return ControlResourceSet__cce_REG_MappingType__Type with end) n0
           end t0).

Lemma ControlResourceSet__cce_REG_MappingType__helper2 :  forall (y : ControlResourceSet__cce_REG_MappingType__Type), ControlResourceSet__cce_REG_MappingType__cond y -> choice_cond ControlResourceSet__cce_REG_MappingType__list (ControlResourceSet__cce_REG_MappingType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ControlResourceSet__cce_REG_MappingType__helper3 :  forall (y : ControlResourceSet__cce_REG_MappingType__Type), ControlResourceSet__cce_REG_MappingType__F2 (ControlResourceSet__cce_REG_MappingType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ControlResourceSet__cce_REG_MappingType__helper4 : (forall b : choice ControlResourceSet__cce_REG_MappingType__list, choice_cond ControlResourceSet__cce_REG_MappingType__list b -> ControlResourceSet__cce_REG_MappingType__cond (ControlResourceSet__cce_REG_MappingType__F2 b) /\ ControlResourceSet__cce_REG_MappingType__F1 (ControlResourceSet__cce_REG_MappingType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ControlResourceSet__cce_REG_MappingType__F1 ControlResourceSet__cce_REG_MappingType__F2.
Definition ControlResourceSet__cce_REG_MappingType__Format : T_Format ControlResourceSet__cce_REG_MappingType__Type ControlResourceSet__cce_REG_MappingType__cond :=
  (* Eval compute in *) proj2_format ControlResourceSet__cce_REG_MappingType__cond ControlResourceSet__cce_REG_MappingType__list__Format ControlResourceSet__cce_REG_MappingType__F1 ControlResourceSet__cce_REG_MappingType__F2 ControlResourceSet__cce_REG_MappingType__helper2 ControlResourceSet__cce_REG_MappingType__helper3 ControlResourceSet__cce_REG_MappingType__helper4.
Opaque ControlResourceSet__cce_REG_MappingType__cond ControlResourceSet__cce_REG_MappingType__Format.

Definition ControlResourceSet__precoderGranularity__Format : T_Format ControlResourceSet__precoderGranularity__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ControlResourceSet__precoderGranularity__nat__Format ControlResourceSet__precoderGranularity__F1 ControlResourceSet__precoderGranularity__F2 ControlResourceSet__precoderGranularity__F1F2 ControlResourceSet__precoderGranularity__F2F1.

Opaque ControlResourceSet__precoderGranularity__cond ControlResourceSet__precoderGranularity__Format.

Definition ControlResourceSet__tci_StatesPDCCH_ToAddList__Format : T_Format ControlResourceSet__tci_StatesPDCCH_ToAddList__Type ControlResourceSet__tci_StatesPDCCH_ToAddList__cond := seq_of_format TCI_StateId__Format 1 maxNrofTCI_StatesPDCCH ControlResourceSet__tci_StatesPDCCH_ToAddList__helper1 ControlResourceSet__tci_StatesPDCCH_ToAddList__helper2.

Opaque ControlResourceSet__tci_StatesPDCCH_ToAddList__cond ControlResourceSet__tci_StatesPDCCH_ToAddList__Format.

Definition ControlResourceSet__tci_StatesPDCCH_ToReleaseList__Format : T_Format ControlResourceSet__tci_StatesPDCCH_ToReleaseList__Type ControlResourceSet__tci_StatesPDCCH_ToReleaseList__cond := seq_of_format TCI_StateId__Format 1 maxNrofTCI_StatesPDCCH ControlResourceSet__tci_StatesPDCCH_ToReleaseList__helper1 ControlResourceSet__tci_StatesPDCCH_ToReleaseList__helper2.

Opaque ControlResourceSet__tci_StatesPDCCH_ToReleaseList__cond ControlResourceSet__tci_StatesPDCCH_ToReleaseList__Format.

Definition ControlResourceSet__tci_PresentInDCI__Format : T_Format ControlResourceSet__tci_PresentInDCI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ControlResourceSet__tci_PresentInDCI__nat__Format ControlResourceSet__tci_PresentInDCI__F1 ControlResourceSet__tci_PresentInDCI__F2 ControlResourceSet__tci_PresentInDCI__F1F2 ControlResourceSet__tci_PresentInDCI__F2F1.

Opaque ControlResourceSet__tci_PresentInDCI__cond ControlResourceSet__tci_PresentInDCI__Format.

Definition ControlResourceSet__pdcch_DMRS_ScramblingID__Format : T_Format Z ControlResourceSet__pdcch_DMRS_ScramblingID__cond :=
 ranged_int_format (0) (65535) ControlResourceSet__pdcch_DMRS_ScramblingID__helper1 ControlResourceSet__pdcch_DMRS_ScramblingID__helper2.

Opaque ControlResourceSet__pdcch_DMRS_ScramblingID__cond ControlResourceSet__pdcch_DMRS_ScramblingID__Format.

Definition ControlResourceSet__ext0O__rb_Offset_r16__Format : T_Format Z ControlResourceSet__ext0O__rb_Offset_r16__cond :=
 ranged_int_format (0) (5) ControlResourceSet__ext0O__rb_Offset_r16__helper1 ControlResourceSet__ext0O__rb_Offset_r16__helper2.

Opaque ControlResourceSet__ext0O__rb_Offset_r16__cond ControlResourceSet__ext0O__rb_Offset_r16__Format.

Definition ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__Format : T_Format Z ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__cond :=
 ranged_int_format (1) (3) ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__helper1 ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__helper2.

Opaque ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__cond ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__Format.

Definition ControlResourceSet__ext0O__coresetPoolIndex_r16__Format : T_Format Z ControlResourceSet__ext0O__coresetPoolIndex_r16__cond :=
 ranged_int_format (0) (1) ControlResourceSet__ext0O__coresetPoolIndex_r16__helper1 ControlResourceSet__ext0O__coresetPoolIndex_r16__helper2.

Opaque ControlResourceSet__ext0O__coresetPoolIndex_r16__cond ControlResourceSet__ext0O__coresetPoolIndex_r16__Format.


Definition ControlResourceSet__ext0O__Format_Type := Eval cbn in seq_format_prod ControlResourceSet__ext0O__list.
Definition ControlResourceSet__ext0O__Format_list : ControlResourceSet__ext0O__Format_Type :=
  (ControlResourceSet__ext0O__rb_Offset_r16__Format, (ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16__Format, (ControlResourceSet__ext0O__coresetPoolIndex_r16__Format, (ControlResourceSetId_v1610__Format, unit_format)))).
Definition ControlResourceSet__ext0O__list__Format := (*Eval compute in *) seq_format ControlResourceSet__ext0O__list ControlResourceSet__ext0O__Format_list.
Definition ControlResourceSet__ext0O__F1 z :=
  (ControlResourceSet__ext0O__rb_Offset_r16 z, (ControlResourceSet__ext0O__tci_PresentDCI_1_2_r16 z, (ControlResourceSet__ext0O__coresetPoolIndex_r16 z, (ControlResourceSet__ext0O__controlResourceSetId_v1610 z, tt)))).
Definition ControlResourceSet__ext0O__F2 (y : seq_type ControlResourceSet__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ControlResourceSet__ext0O__Type i0 i1 i2 i3
  end.
Lemma ControlResourceSet__ext0O__F1F2_cond (z : ControlResourceSet__ext0O__Type)
  : ControlResourceSet__ext0O__cond z ->
  (seq_cond ControlResourceSet__ext0O__list (ControlResourceSet__ext0O__F1 z)).
intro H. unfold ControlResourceSet__ext0O__cond in H. simpl. auto. Qed.
Lemma ControlResourceSet__ext0O__F1F2_cond2 (z : ControlResourceSet__ext0O__Type)
 : ControlResourceSet__ext0O__F2 (ControlResourceSet__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ControlResourceSet__ext0O__F2F1_cond (y : seq_type ControlResourceSet__ext0O__list)
  : seq_cond ControlResourceSet__ext0O__list y ->
 (ControlResourceSet__ext0O__cond (ControlResourceSet__ext0O__F2 y)) /\  ControlResourceSet__ext0O__F1 (ControlResourceSet__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ControlResourceSet__ext0O__cond. simpl in *. auto.
 - simpl. unfold ControlResourceSet__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ControlResourceSet__ext0O__Format : T_Format ControlResourceSet__ext0O__Type ControlResourceSet__ext0O__cond :=
        proj2_format  ControlResourceSet__ext0O__cond ControlResourceSet__ext0O__list__Format
    ControlResourceSet__ext0O__F1 ControlResourceSet__ext0O__F2 ControlResourceSet__ext0O__F1F2_cond  ControlResourceSet__ext0O__F1F2_cond2 ControlResourceSet__ext0O__F2F1_cond.
Opaque ControlResourceSet__ext0O__cond ControlResourceSet__ext0O__Format.

Definition ControlResourceSet__ext0__check_all_none (b : ControlResourceSet__ext0O__Type) : bool :=
match b with 
  | make__ControlResourceSet__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition ControlResourceSet__ext0__Format : T_Format ControlResourceSet__ext0__Type ControlResourceSet__ext0__cond :=
  restrict_add_format ControlResourceSet__ext0__check_all_none ControlResourceSet__ext0O__Format.

Opaque ControlResourceSet__ext0__cond ControlResourceSet__ext0__Format.

Definition ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Format : T_Format ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ControlResourceSet__ext1O__followUnifiedTCI_State_r17__nat__Format ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F1 ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F2 ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F1F2 ControlResourceSet__ext1O__followUnifiedTCI_State_r17__F2F1.

Opaque ControlResourceSet__ext1O__followUnifiedTCI_State_r17__cond ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Format.


Definition ControlResourceSet__ext1O__Format_Type := Eval cbn in seq_format_prod ControlResourceSet__ext1O__list.
Definition ControlResourceSet__ext1O__Format_list : ControlResourceSet__ext1O__Format_Type :=
  (ControlResourceSet__ext1O__followUnifiedTCI_State_r17__Format, unit_format).
Definition ControlResourceSet__ext1O__list__Format := (*Eval compute in *) seq_format ControlResourceSet__ext1O__list ControlResourceSet__ext1O__Format_list.
Definition ControlResourceSet__ext1O__F1 z :=
  (ControlResourceSet__ext1O__followUnifiedTCI_State_r17 z, tt).
Definition ControlResourceSet__ext1O__F2 (y : seq_type ControlResourceSet__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__ControlResourceSet__ext1O__Type i0
  end.
Lemma ControlResourceSet__ext1O__F1F2_cond (z : ControlResourceSet__ext1O__Type)
  : ControlResourceSet__ext1O__cond z ->
  (seq_cond ControlResourceSet__ext1O__list (ControlResourceSet__ext1O__F1 z)).
intro H. unfold ControlResourceSet__ext1O__cond in H. simpl. auto. Qed.
Lemma ControlResourceSet__ext1O__F1F2_cond2 (z : ControlResourceSet__ext1O__Type)
 : ControlResourceSet__ext1O__F2 (ControlResourceSet__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ControlResourceSet__ext1O__F2F1_cond (y : seq_type ControlResourceSet__ext1O__list)
  : seq_cond ControlResourceSet__ext1O__list y ->
 (ControlResourceSet__ext1O__cond (ControlResourceSet__ext1O__F2 y)) /\  ControlResourceSet__ext1O__F1 (ControlResourceSet__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ControlResourceSet__ext1O__cond. simpl in *. auto.
 - simpl. unfold ControlResourceSet__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ControlResourceSet__ext1O__Format : T_Format ControlResourceSet__ext1O__Type ControlResourceSet__ext1O__cond :=
        proj2_format  ControlResourceSet__ext1O__cond ControlResourceSet__ext1O__list__Format
    ControlResourceSet__ext1O__F1 ControlResourceSet__ext1O__F2 ControlResourceSet__ext1O__F1F2_cond  ControlResourceSet__ext1O__F1F2_cond2 ControlResourceSet__ext1O__F2F1_cond.
Opaque ControlResourceSet__ext1O__cond ControlResourceSet__ext1O__Format.

Definition ControlResourceSet__ext1__check_all_none (b : ControlResourceSet__ext1O__Type) : bool :=
match b with 
  | make__ControlResourceSet__ext1O__Type None  => false 
  | _ => true 
 end.
Definition ControlResourceSet__ext1__Format : T_Format ControlResourceSet__ext1__Type ControlResourceSet__ext1__cond :=
  restrict_add_format ControlResourceSet__ext1__check_all_none ControlResourceSet__ext1O__Format.

Opaque ControlResourceSet__ext1__cond ControlResourceSet__ext1__Format.


Definition ControlResourceSet__root_Format_Type := Eval cbn in seq_format_prod ControlResourceSet__root_list.
Definition ControlResourceSet__root_Format_list : ControlResourceSet__root_Format_Type :=
  (ControlResourceSetId__Format, (ControlResourceSet__frequencyDomainResources__Format, (ControlResourceSet__duration__Format, (ControlResourceSet__cce_REG_MappingType__Format, (ControlResourceSet__precoderGranularity__Format, (ControlResourceSet__tci_StatesPDCCH_ToAddList__Format, (ControlResourceSet__tci_StatesPDCCH_ToReleaseList__Format, (ControlResourceSet__tci_PresentInDCI__Format, (ControlResourceSet__pdcch_DMRS_ScramblingID__Format, unit_format))))))))).

Definition ControlResourceSet__ext_Format_Type := Eval cbn in get_formats ControlResourceSet__ext_list.
Definition ControlResourceSet__ext_Format_list : ControlResourceSet__ext_Format_Type :=
  (ControlResourceSet__ext0__Format, (ControlResourceSet__ext1__Format, unit__Format)).

Definition ControlResourceSet__list_type : Set := (seq_type ControlResourceSet__root_list) * (seq_ext_type ControlResourceSet__ext_list).
Definition ControlResourceSet__list_cond (z : ControlResourceSet__list_type) : Prop :=
        (seq_cond ControlResourceSet__root_list (fst z)) /\ (seq_ext_cond ControlResourceSet__ext_list (snd z)).
Definition ControlResourceSet__list_format : T_Format ControlResourceSet__list_type ControlResourceSet__list_cond :=
 (* Eval compute in *) seq_ext_format ControlResourceSet__root_list ControlResourceSet__root_Format_list ControlResourceSet__ext_list ControlResourceSet__ext_Format_list.

Opaque ControlResourceSet__list_format.
Definition ControlResourceSet__F1 (z : ControlResourceSet__Type) : ControlResourceSet__list_type :=
  (((ControlResourceSet__controlResourceSetId z, (ControlResourceSet__frequencyDomainResources z, (ControlResourceSet__duration z, (ControlResourceSet__cce_REG_MappingType z, (ControlResourceSet__precoderGranularity z, (ControlResourceSet__tci_StatesPDCCH_ToAddList z, (ControlResourceSet__tci_StatesPDCCH_ToReleaseList z, (ControlResourceSet__tci_PresentInDCI z, (ControlResourceSet__pdcch_DMRS_ScramblingID z, tt)))))))))), (
(ControlResourceSet__ext0 z, (ControlResourceSet__ext1 z, tt)))).
Definition ControlResourceSet__F2 (y : ControlResourceSet__list_type) : ControlResourceSet__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, _))))))))), (i0, (i1, _)))=>
    make__ControlResourceSet__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 i0 i1
  end.
Definition ControlResourceSet__helper1 : (forall a : ControlResourceSet__Type, ControlResourceSet__cond a -> ControlResourceSet__list_cond (ControlResourceSet__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ControlResourceSet__helper2 : (forall a : ControlResourceSet__Type, ControlResourceSet__F2 (ControlResourceSet__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ControlResourceSet__helper3 : (forall b : ControlResourceSet__list_type, ControlResourceSet__list_cond b -> ControlResourceSet__cond (ControlResourceSet__F2 b) /\ ControlResourceSet__F1 (ControlResourceSet__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ControlResourceSet__cond, ControlResourceSet__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ControlResourceSet__Format : T_Format ControlResourceSet__Type ControlResourceSet__cond :=
 proj2_format ControlResourceSet__cond ControlResourceSet__list_format  ControlResourceSet__F1 ControlResourceSet__F2 ControlResourceSet__helper1 ControlResourceSet__helper2 ControlResourceSet__helper3.

Opaque ControlResourceSet__cond ControlResourceSet__Format.

