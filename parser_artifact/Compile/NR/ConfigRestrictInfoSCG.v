Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_InterNodeDefinitions.
Require Import NR.BandCombinationInfoList.

Opaque BandCombinationInfoList__cond BandCombinationInfoList__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Record ConfigRestrictInfoSCG__powerCoordination_FR1__Type : Set :=
  make__ConfigRestrictInfoSCG__powerCoordination_FR1__Type {
    ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxNR_FR1 : option P_Max__Type ;
    ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxEUTRA : option P_Max__Type ;
    ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxUE_FR1 : option P_Max__Type ;
}.
Definition ConfigRestrictInfoSCG__powerCoordination_FR1__list := (
 Opt P_Max__Type P_Max__cond ::
 Opt P_Max__Type P_Max__cond ::
 Opt P_Max__Type P_Max__cond ::
 nil).
Definition ConfigRestrictInfoSCG__powerCoordination_FR1__cond z := 
  opt_cond P_Max__cond (ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxNR_FR1 z) /\
  opt_cond P_Max__cond (ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxEUTRA z) /\
  opt_cond P_Max__cond (ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxUE_FR1 z) /\
  True.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Record ConfigRestrictInfoSCG__servCellIndexRangeSCG__Type : Set :=
  make__ConfigRestrictInfoSCG__servCellIndexRangeSCG__Type {
    ConfigRestrictInfoSCG__servCellIndexRangeSCG__lowBound : ServCellIndex__Type ;
    ConfigRestrictInfoSCG__servCellIndexRangeSCG__upBound : ServCellIndex__Type ;
}.
Definition ConfigRestrictInfoSCG__servCellIndexRangeSCG__list := (
 Nor ServCellIndex__Type ServCellIndex__cond ::
 Nor ServCellIndex__Type ServCellIndex__cond ::
 nil).
Definition ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond z := 
  ServCellIndex__cond (ConfigRestrictInfoSCG__servCellIndexRangeSCG__lowBound z) /\
  ServCellIndex__cond (ConfigRestrictInfoSCG__servCellIndexRangeSCG__upBound z) /\
  True.

Lemma ConfigRestrictInfoSCG__maxMeasFreqsSCG__helper1 : (1 <= maxMeasFreqsMN)%Z. unfold maxMeasFreqsMN.
 lia. Qed.
Lemma ConfigRestrictInfoSCG__maxMeasFreqsSCG__helper2 : to_bit_sz (Z.to_nat (maxMeasFreqsMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMeasFreqsMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__maxMeasFreqsSCG__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__maxMeasFreqsSCG__Type := Z.
Definition ConfigRestrictInfoSCG__maxMeasFreqsSCG__cond := (fun z => (1 <= z <= maxMeasFreqsMN)%Z).
Lemma ConfigRestrictInfoSCG__dummy__helper1 : (1 <= maxMeasIdentitiesMN)%Z. unfold maxMeasIdentitiesMN.
 lia. Qed.
Lemma ConfigRestrictInfoSCG__dummy__helper2 : to_bit_sz (Z.to_nat (maxMeasIdentitiesMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMeasIdentitiesMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__dummy__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__dummy__Type := Z.
Definition ConfigRestrictInfoSCG__dummy__cond := (fun z => (1 <= z <= maxMeasIdentitiesMN)%Z).
Require Import NR.SelectedBandEntriesMN.

Opaque SelectedBandEntriesMN__cond SelectedBandEntriesMN__Format.

Definition ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__Type := list SelectedBandEntriesMN__Type.

Lemma ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__helper1 : (0 <= 1 <= maxBandComb)%Z. unfold maxBandComb.
 lia. Qed.
Lemma ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__helper2 : to_bit_sz (Z.to_nat (maxBandComb - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxBandComb - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__cond (z : ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__Type) :=  (1 <= Z.of_nat (length z) <= maxBandComb)%Z /\ (list_and SelectedBandEntriesMN__cond z) .

Lemma ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__helper1 : (1 <= 15)%Z.  lia. Qed.
Lemma ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__helper2 : to_bit_sz (Z.to_nat (15 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__Type := Z.
Definition ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__cond := (fun z => (1 <= z <= 15)%Z).
Lemma ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__helper1 : (0 <= 16384)%Z.  lia. Qed.
Lemma ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__helper2 : to_bit_sz (Z.to_nat (16384 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16384 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__Type := Z.
Definition ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__cond := (fun z => (0 <= z <= 16384)%Z).
Record ConfigRestrictInfoSCG__ext0O__Type : Set :=
  make__ConfigRestrictInfoSCG__ext0O__Type {
    ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList : option ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__Type ;
    ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG : option Z ;
    ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN : option Z ;
}.
Definition ConfigRestrictInfoSCG__ext0O__list := (
 Opt ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__Type ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__cond ::
 Opt Z ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__cond ::
 Opt Z ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__cond ::
 nil).
Definition ConfigRestrictInfoSCG__ext0O__cond z := 
  opt_cond ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__cond (ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList z) /\
  opt_cond ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__cond (ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG z) /\
  opt_cond ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__cond (ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN z) /\
  True.

Definition ConfigRestrictInfoSCG__ext0__Type := ConfigRestrictInfoSCG__ext0O__Type.
Definition ConfigRestrictInfoSCG__ext0__cond := ConfigRestrictInfoSCG__ext0O__cond.

Lemma ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__helper1 : (1 <= maxMeasIdentitiesMN)%Z. unfold maxMeasIdentitiesMN.
 lia. Qed.
Lemma ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__helper2 : to_bit_sz (Z.to_nat (maxMeasIdentitiesMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMeasIdentitiesMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__Type := Z.
Definition ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__cond := (fun z => (1 <= z <= maxMeasIdentitiesMN)%Z).
Lemma ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__helper1 : (1 <= maxMeasIdentitiesMN)%Z. unfold maxMeasIdentitiesMN.
 lia. Qed.
Lemma ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__helper2 : to_bit_sz (Z.to_nat (maxMeasIdentitiesMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxMeasIdentitiesMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__Type := Z.
Definition ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__cond := (fun z => (1 <= z <= maxMeasIdentitiesMN)%Z).
Record ConfigRestrictInfoSCG__ext1O__Type : Set :=
  make__ConfigRestrictInfoSCG__ext1O__Type {
    ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG : option Z ;
    ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG : option Z ;
}.
Definition ConfigRestrictInfoSCG__ext1O__list := (
 Opt Z ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__cond ::
 Opt Z ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__cond ::
 nil).
Definition ConfigRestrictInfoSCG__ext1O__cond z := 
  opt_cond ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__cond (ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG z) /\
  opt_cond ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__cond (ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG z) /\
  True.

Definition ConfigRestrictInfoSCG__ext1__Type := ConfigRestrictInfoSCG__ext1O__Type.
Definition ConfigRestrictInfoSCG__ext1__cond := ConfigRestrictInfoSCG__ext1O__cond.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Require Import NR.P_Max.

Opaque P_Max__cond P_Max__Format.

Record ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Type : Set :=
  make__ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Type {
    ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxNR_FR2_MCG_r16 : option P_Max__Type ;
    ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxNR_FR2_SCG_r16 : option P_Max__Type ;
    ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxUE_FR2_r16 : option P_Max__Type ;
}.
Definition ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list := (
 Opt P_Max__Type P_Max__cond ::
 Opt P_Max__Type P_Max__cond ::
 Opt P_Max__Type P_Max__cond ::
 nil).
Definition ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond z := 
  opt_cond P_Max__cond (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxNR_FR2_MCG_r16 z) /\
  opt_cond P_Max__cond (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxNR_FR2_SCG_r16 z) /\
  opt_cond P_Max__cond (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxUE_FR2_r16 z) /\
  True.

Inductive ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Type : Set :=
 | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__semi_static_mode1
 | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__semi_static_mode2
 | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__dynamic
.
Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__cond := (fun (_ : ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Type) => True).
Lemma ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__nat__helper.

Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F1 t :=
  match t with
  | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__semi_static_mode1 => 0
  | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__semi_static_mode2 => 1
  | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__dynamic => 2
  end.
Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F2 n :=
  match n with
  | 0 => ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__semi_static_mode1
  | 1 => ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__semi_static_mode2
  | 2 => ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__dynamic
  | _ => ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__semi_static_mode1
  end.
Lemma ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F1F2 : forall x : ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Type, (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F1 x <= 2) /\ ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F2 (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F2F1 : forall (y : nat) (H : y <= 2), ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F1 (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Type : Set :=
 | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__semi_static_mode1
 | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__semi_static_mode2
 | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__dynamic
.
Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__cond := (fun (_ : ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Type) => True).
Lemma ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__nat__helper.

Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F1 t :=
  match t with
  | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__semi_static_mode1 => 0
  | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__semi_static_mode2 => 1
  | ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__dynamic => 2
  end.
Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F2 n :=
  match n with
  | 0 => ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__semi_static_mode1
  | 1 => ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__semi_static_mode2
  | 2 => ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__dynamic
  | _ => ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__semi_static_mode1
  end.
Lemma ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F1F2 : forall x : ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Type, (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F1 x <= 2) /\ ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F2 (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F1 x) = x. imp_solve. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F2F1 : forall (y : nat) (H : y <= 2), ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F1 (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F2 y) = y. enum_solve H y. Qed.

Lemma ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__helper1 : (0 <= maxNrofCLI_SRS_Resources_r16)%Z. unfold maxNrofCLI_SRS_Resources_r16.
 lia. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCLI_SRS_Resources_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCLI_SRS_Resources_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__Type := Z.
Definition ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__cond := (fun z => (0 <= z <= maxNrofCLI_SRS_Resources_r16)%Z).
Lemma ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__helper1 : (0 <= maxNrofCLI_RSSI_Resources_r16)%Z. unfold maxNrofCLI_RSSI_Resources_r16.
 lia. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__helper2 : to_bit_sz (Z.to_nat (maxNrofCLI_RSSI_Resources_r16 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCLI_RSSI_Resources_r16 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__Type := Z.
Definition ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__cond := (fun z => (0 <= z <= maxNrofCLI_RSSI_Resources_r16)%Z).
Lemma ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__helper1 : (0 <= 65536)%Z.  lia. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__helper2 : to_bit_sz (Z.to_nat (65536 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (65536 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__Type := Z.
Definition ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__cond := (fun z => (0 <= z <= 65536)%Z).
Require Import NR.OverheatingAssistance.

Opaque OverheatingAssistance__cond OverheatingAssistance__Format.

Require Import NR.T_Offset_r16.

Opaque T_Offset_r16__cond T_Offset_r16__Format.

Record ConfigRestrictInfoSCG__ext2O__Type : Set :=
  make__ConfigRestrictInfoSCG__ext2O__Type {
    ConfigRestrictInfoSCG__ext2O__p_maxNR_FR1_MCG_r16 : option P_Max__Type ;
    ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16 : option ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Type ;
    ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16 : option ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Type ;
    ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16 : option ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Type ;
    ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16 : option Z ;
    ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16 : option Z ;
    ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16 : option Z ;
    ConfigRestrictInfoSCG__ext2O__allowedReducedConfigForOverheating_r16 : option OverheatingAssistance__Type ;
    ConfigRestrictInfoSCG__ext2O__maxToffset_r16 : option T_Offset_r16__Type ;
}.
Definition ConfigRestrictInfoSCG__ext2O__list := (
 Opt P_Max__Type P_Max__cond ::
 Opt ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Type ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond ::
 Opt ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Type ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__cond ::
 Opt ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Type ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__cond ::
 Opt Z ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__cond ::
 Opt Z ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__cond ::
 Opt Z ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__cond ::
 Opt OverheatingAssistance__Type OverheatingAssistance__cond ::
 Opt T_Offset_r16__Type T_Offset_r16__cond ::
 nil).
Definition ConfigRestrictInfoSCG__ext2O__cond z := 
  opt_cond P_Max__cond (ConfigRestrictInfoSCG__ext2O__p_maxNR_FR1_MCG_r16 z) /\
  opt_cond ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16 z) /\
  opt_cond ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__cond (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16 z) /\
  opt_cond ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__cond (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16 z) /\
  opt_cond ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__cond (ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16 z) /\
  opt_cond ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__cond (ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16 z) /\
  opt_cond ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__cond (ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16 z) /\
  opt_cond OverheatingAssistance__cond (ConfigRestrictInfoSCG__ext2O__allowedReducedConfigForOverheating_r16 z) /\
  opt_cond T_Offset_r16__cond (ConfigRestrictInfoSCG__ext2O__maxToffset_r16 z) /\
  True.

Definition ConfigRestrictInfoSCG__ext2__Type := ConfigRestrictInfoSCG__ext2O__Type.
Definition ConfigRestrictInfoSCG__ext2__cond := ConfigRestrictInfoSCG__ext2O__cond.

Require Import NR.OverheatingAssistance_r17.

Opaque OverheatingAssistance_r17__cond OverheatingAssistance_r17__Format.

Lemma ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__helper1 : (0 <= 2)%Z.  lia. Qed.
Lemma ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__helper2 : to_bit_sz (Z.to_nat (2 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__Type := Z.
Definition ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__cond := (fun z => (0 <= z <= 2)%Z).
Lemma ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__helper1 : (0 <= maxNrofCondCells_1_r17)%Z. unfold maxNrofCondCells_1_r17.
 lia. Qed.
Lemma ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofCondCells_1_r17 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofCondCells_1_r17 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__Type := Z.
Definition ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__cond := (fun z => (0 <= z <= maxNrofCondCells_1_r17)%Z).
Record ConfigRestrictInfoSCG__ext3O__Type : Set :=
  make__ConfigRestrictInfoSCG__ext3O__Type {
    ConfigRestrictInfoSCG__ext3O__allowedReducedConfigForOverheating_r17 : option OverheatingAssistance_r17__Type ;
    ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17 : option Z ;
    ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17 : option Z ;
}.
Definition ConfigRestrictInfoSCG__ext3O__list := (
 Opt OverheatingAssistance_r17__Type OverheatingAssistance_r17__cond ::
 Opt Z ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__cond ::
 Opt Z ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__cond ::
 nil).
Definition ConfigRestrictInfoSCG__ext3O__cond z := 
  opt_cond OverheatingAssistance_r17__cond (ConfigRestrictInfoSCG__ext3O__allowedReducedConfigForOverheating_r17 z) /\
  opt_cond ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__cond (ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17 z) /\
  opt_cond ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__cond (ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17 z) /\
  True.

Definition ConfigRestrictInfoSCG__ext3__Type := ConfigRestrictInfoSCG__ext3O__Type.
Definition ConfigRestrictInfoSCG__ext3__cond := ConfigRestrictInfoSCG__ext3O__cond.

Record ConfigRestrictInfoSCG__Type : Set :=
  make__ConfigRestrictInfoSCG__Type {
    ConfigRestrictInfoSCG__allowedBC_ListMRDC : option BandCombinationInfoList__Type ;
    ConfigRestrictInfoSCG__powerCoordination_FR1 : option ConfigRestrictInfoSCG__powerCoordination_FR1__Type ;
    ConfigRestrictInfoSCG__servCellIndexRangeSCG : option ConfigRestrictInfoSCG__servCellIndexRangeSCG__Type ;
    ConfigRestrictInfoSCG__maxMeasFreqsSCG : option Z ;
    ConfigRestrictInfoSCG__dummy : option Z ;
    ConfigRestrictInfoSCG__ext0 : option ConfigRestrictInfoSCG__ext0__Type ;
    ConfigRestrictInfoSCG__ext1 : option ConfigRestrictInfoSCG__ext1__Type ;
    ConfigRestrictInfoSCG__ext2 : option ConfigRestrictInfoSCG__ext2__Type ;
    ConfigRestrictInfoSCG__ext3 : option ConfigRestrictInfoSCG__ext3__Type ;
}.
Definition ConfigRestrictInfoSCG__root_list : list seq_elem := (
 Opt BandCombinationInfoList__Type BandCombinationInfoList__cond ::
 Opt ConfigRestrictInfoSCG__powerCoordination_FR1__Type ConfigRestrictInfoSCG__powerCoordination_FR1__cond ::
 Opt ConfigRestrictInfoSCG__servCellIndexRangeSCG__Type ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond ::
 Opt Z ConfigRestrictInfoSCG__maxMeasFreqsSCG__cond ::
 Opt Z ConfigRestrictInfoSCG__dummy__cond ::
 nil).
Definition ConfigRestrictInfoSCG__ext_list : list typ := (
  typ_cons ConfigRestrictInfoSCG__ext0__Type ConfigRestrictInfoSCG__ext0__cond ::
  typ_cons ConfigRestrictInfoSCG__ext1__Type ConfigRestrictInfoSCG__ext1__cond ::
  typ_cons ConfigRestrictInfoSCG__ext2__Type ConfigRestrictInfoSCG__ext2__cond ::
  typ_cons ConfigRestrictInfoSCG__ext3__Type ConfigRestrictInfoSCG__ext3__cond ::
  nil).
Definition ConfigRestrictInfoSCG__cond (z : ConfigRestrictInfoSCG__Type) := 
(  opt_cond BandCombinationInfoList__cond (ConfigRestrictInfoSCG__allowedBC_ListMRDC z) /\
  opt_cond ConfigRestrictInfoSCG__powerCoordination_FR1__cond (ConfigRestrictInfoSCG__powerCoordination_FR1 z) /\
  opt_cond ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond (ConfigRestrictInfoSCG__servCellIndexRangeSCG z) /\
  opt_cond ConfigRestrictInfoSCG__maxMeasFreqsSCG__cond (ConfigRestrictInfoSCG__maxMeasFreqsSCG z) /\
  opt_cond ConfigRestrictInfoSCG__dummy__cond (ConfigRestrictInfoSCG__dummy z) /\
  True) /\ 
(  opt_cond ConfigRestrictInfoSCG__ext0__cond (ConfigRestrictInfoSCG__ext0 z) /\
  opt_cond ConfigRestrictInfoSCG__ext1__cond (ConfigRestrictInfoSCG__ext1 z) /\
  opt_cond ConfigRestrictInfoSCG__ext2__cond (ConfigRestrictInfoSCG__ext2 z) /\
  opt_cond ConfigRestrictInfoSCG__ext3__cond (ConfigRestrictInfoSCG__ext3 z) /\
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

Definition ConfigRestrictInfoSCG__powerCoordination_FR1__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoSCG__powerCoordination_FR1__list.
Definition ConfigRestrictInfoSCG__powerCoordination_FR1__Format_list : ConfigRestrictInfoSCG__powerCoordination_FR1__Format_Type :=
  (P_Max__Format, (P_Max__Format, (P_Max__Format, unit_format))).
Definition ConfigRestrictInfoSCG__powerCoordination_FR1__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoSCG__powerCoordination_FR1__list ConfigRestrictInfoSCG__powerCoordination_FR1__Format_list.
Definition ConfigRestrictInfoSCG__powerCoordination_FR1__F1 z :=
  (ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxNR_FR1 z, (ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxEUTRA z, (ConfigRestrictInfoSCG__powerCoordination_FR1__p_maxUE_FR1 z, tt))).
Definition ConfigRestrictInfoSCG__powerCoordination_FR1__F2 (y : seq_type ConfigRestrictInfoSCG__powerCoordination_FR1__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ConfigRestrictInfoSCG__powerCoordination_FR1__Type i0 i1 i2
  end.
Lemma ConfigRestrictInfoSCG__powerCoordination_FR1__F1F2_cond (z : ConfigRestrictInfoSCG__powerCoordination_FR1__Type)
  : ConfigRestrictInfoSCG__powerCoordination_FR1__cond z ->
  (seq_cond ConfigRestrictInfoSCG__powerCoordination_FR1__list (ConfigRestrictInfoSCG__powerCoordination_FR1__F1 z)).
intro H. unfold ConfigRestrictInfoSCG__powerCoordination_FR1__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__powerCoordination_FR1__F1F2_cond2 (z : ConfigRestrictInfoSCG__powerCoordination_FR1__Type)
 : ConfigRestrictInfoSCG__powerCoordination_FR1__F2 (ConfigRestrictInfoSCG__powerCoordination_FR1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__powerCoordination_FR1__F2F1_cond (y : seq_type ConfigRestrictInfoSCG__powerCoordination_FR1__list)
  : seq_cond ConfigRestrictInfoSCG__powerCoordination_FR1__list y ->
 (ConfigRestrictInfoSCG__powerCoordination_FR1__cond (ConfigRestrictInfoSCG__powerCoordination_FR1__F2 y)) /\  ConfigRestrictInfoSCG__powerCoordination_FR1__F1 (ConfigRestrictInfoSCG__powerCoordination_FR1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoSCG__powerCoordination_FR1__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoSCG__powerCoordination_FR1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoSCG__powerCoordination_FR1__Format : T_Format ConfigRestrictInfoSCG__powerCoordination_FR1__Type ConfigRestrictInfoSCG__powerCoordination_FR1__cond :=
        proj2_format  ConfigRestrictInfoSCG__powerCoordination_FR1__cond ConfigRestrictInfoSCG__powerCoordination_FR1__list__Format
    ConfigRestrictInfoSCG__powerCoordination_FR1__F1 ConfigRestrictInfoSCG__powerCoordination_FR1__F2 ConfigRestrictInfoSCG__powerCoordination_FR1__F1F2_cond  ConfigRestrictInfoSCG__powerCoordination_FR1__F1F2_cond2 ConfigRestrictInfoSCG__powerCoordination_FR1__F2F1_cond.
Opaque ConfigRestrictInfoSCG__powerCoordination_FR1__cond ConfigRestrictInfoSCG__powerCoordination_FR1__Format.


Definition ConfigRestrictInfoSCG__servCellIndexRangeSCG__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoSCG__servCellIndexRangeSCG__list.
Definition ConfigRestrictInfoSCG__servCellIndexRangeSCG__Format_list : ConfigRestrictInfoSCG__servCellIndexRangeSCG__Format_Type :=
  (ServCellIndex__Format, (ServCellIndex__Format, unit_format)).
Definition ConfigRestrictInfoSCG__servCellIndexRangeSCG__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoSCG__servCellIndexRangeSCG__list ConfigRestrictInfoSCG__servCellIndexRangeSCG__Format_list.
Definition ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1 z :=
  (ConfigRestrictInfoSCG__servCellIndexRangeSCG__lowBound z, (ConfigRestrictInfoSCG__servCellIndexRangeSCG__upBound z, tt)).
Definition ConfigRestrictInfoSCG__servCellIndexRangeSCG__F2 (y : seq_type ConfigRestrictInfoSCG__servCellIndexRangeSCG__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ConfigRestrictInfoSCG__servCellIndexRangeSCG__Type i0 i1
  end.
Lemma ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1F2_cond (z : ConfigRestrictInfoSCG__servCellIndexRangeSCG__Type)
  : ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond z ->
  (seq_cond ConfigRestrictInfoSCG__servCellIndexRangeSCG__list (ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1 z)).
intro H. unfold ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1F2_cond2 (z : ConfigRestrictInfoSCG__servCellIndexRangeSCG__Type)
 : ConfigRestrictInfoSCG__servCellIndexRangeSCG__F2 (ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__servCellIndexRangeSCG__F2F1_cond (y : seq_type ConfigRestrictInfoSCG__servCellIndexRangeSCG__list)
  : seq_cond ConfigRestrictInfoSCG__servCellIndexRangeSCG__list y ->
 (ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond (ConfigRestrictInfoSCG__servCellIndexRangeSCG__F2 y)) /\  ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1 (ConfigRestrictInfoSCG__servCellIndexRangeSCG__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoSCG__servCellIndexRangeSCG__Format : T_Format ConfigRestrictInfoSCG__servCellIndexRangeSCG__Type ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond :=
        proj2_format  ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond ConfigRestrictInfoSCG__servCellIndexRangeSCG__list__Format
    ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1 ConfigRestrictInfoSCG__servCellIndexRangeSCG__F2 ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1F2_cond  ConfigRestrictInfoSCG__servCellIndexRangeSCG__F1F2_cond2 ConfigRestrictInfoSCG__servCellIndexRangeSCG__F2F1_cond.
Opaque ConfigRestrictInfoSCG__servCellIndexRangeSCG__cond ConfigRestrictInfoSCG__servCellIndexRangeSCG__Format.

Definition ConfigRestrictInfoSCG__maxMeasFreqsSCG__Format : T_Format Z ConfigRestrictInfoSCG__maxMeasFreqsSCG__cond :=
 ranged_int_format (1) (maxMeasFreqsMN) ConfigRestrictInfoSCG__maxMeasFreqsSCG__helper1 ConfigRestrictInfoSCG__maxMeasFreqsSCG__helper2.

Opaque ConfigRestrictInfoSCG__maxMeasFreqsSCG__cond ConfigRestrictInfoSCG__maxMeasFreqsSCG__Format.

Definition ConfigRestrictInfoSCG__dummy__Format : T_Format Z ConfigRestrictInfoSCG__dummy__cond :=
 ranged_int_format (1) (maxMeasIdentitiesMN) ConfigRestrictInfoSCG__dummy__helper1 ConfigRestrictInfoSCG__dummy__helper2.

Opaque ConfigRestrictInfoSCG__dummy__cond ConfigRestrictInfoSCG__dummy__Format.

Definition ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__Format : T_Format ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__Type ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__cond := seq_of_format SelectedBandEntriesMN__Format 1 maxBandComb ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__helper1 ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__helper2.

Opaque ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__cond ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__Format.

Definition ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__Format : T_Format Z ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__cond :=
 ranged_int_format (1) (15) ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__helper1 ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__helper2.

Opaque ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__cond ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__Format.

Definition ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__Format : T_Format Z ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__cond :=
 ranged_int_format (0) (16384) ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__helper1 ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__helper2.

Opaque ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__cond ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__Format.


Definition ConfigRestrictInfoSCG__ext0O__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoSCG__ext0O__list.
Definition ConfigRestrictInfoSCG__ext0O__Format_list : ConfigRestrictInfoSCG__ext0O__Format_Type :=
  (ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList__Format, (ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG__Format, (ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN__Format, unit_format))).
Definition ConfigRestrictInfoSCG__ext0O__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoSCG__ext0O__list ConfigRestrictInfoSCG__ext0O__Format_list.
Definition ConfigRestrictInfoSCG__ext0O__F1 z :=
  (ConfigRestrictInfoSCG__ext0O__selectedBandEntriesMNList z, (ConfigRestrictInfoSCG__ext0O__pdcch_BlindDetectionSCG z, (ConfigRestrictInfoSCG__ext0O__maxNumberROHC_ContextSessionsSN z, tt))).
Definition ConfigRestrictInfoSCG__ext0O__F2 (y : seq_type ConfigRestrictInfoSCG__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ConfigRestrictInfoSCG__ext0O__Type i0 i1 i2
  end.
Lemma ConfigRestrictInfoSCG__ext0O__F1F2_cond (z : ConfigRestrictInfoSCG__ext0O__Type)
  : ConfigRestrictInfoSCG__ext0O__cond z ->
  (seq_cond ConfigRestrictInfoSCG__ext0O__list (ConfigRestrictInfoSCG__ext0O__F1 z)).
intro H. unfold ConfigRestrictInfoSCG__ext0O__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext0O__F1F2_cond2 (z : ConfigRestrictInfoSCG__ext0O__Type)
 : ConfigRestrictInfoSCG__ext0O__F2 (ConfigRestrictInfoSCG__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext0O__F2F1_cond (y : seq_type ConfigRestrictInfoSCG__ext0O__list)
  : seq_cond ConfigRestrictInfoSCG__ext0O__list y ->
 (ConfigRestrictInfoSCG__ext0O__cond (ConfigRestrictInfoSCG__ext0O__F2 y)) /\  ConfigRestrictInfoSCG__ext0O__F1 (ConfigRestrictInfoSCG__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoSCG__ext0O__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoSCG__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoSCG__ext0O__Format : T_Format ConfigRestrictInfoSCG__ext0O__Type ConfigRestrictInfoSCG__ext0O__cond :=
        proj2_format  ConfigRestrictInfoSCG__ext0O__cond ConfigRestrictInfoSCG__ext0O__list__Format
    ConfigRestrictInfoSCG__ext0O__F1 ConfigRestrictInfoSCG__ext0O__F2 ConfigRestrictInfoSCG__ext0O__F1F2_cond  ConfigRestrictInfoSCG__ext0O__F1F2_cond2 ConfigRestrictInfoSCG__ext0O__F2F1_cond.
Opaque ConfigRestrictInfoSCG__ext0O__cond ConfigRestrictInfoSCG__ext0O__Format.

Definition ConfigRestrictInfoSCG__ext0__check_all_none (b : ConfigRestrictInfoSCG__ext0O__Type) : bool :=
match b with 
  | make__ConfigRestrictInfoSCG__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition ConfigRestrictInfoSCG__ext0__Format : T_Format ConfigRestrictInfoSCG__ext0__Type ConfigRestrictInfoSCG__ext0__cond :=
  restrict_add_format ConfigRestrictInfoSCG__ext0__check_all_none ConfigRestrictInfoSCG__ext0O__Format.

Opaque ConfigRestrictInfoSCG__ext0__cond ConfigRestrictInfoSCG__ext0__Format.

Definition ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__Format : T_Format Z ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__cond :=
 ranged_int_format (1) (maxMeasIdentitiesMN) ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__helper1 ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__helper2.

Opaque ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__cond ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__Format.

Definition ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__Format : T_Format Z ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__cond :=
 ranged_int_format (1) (maxMeasIdentitiesMN) ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__helper1 ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__helper2.

Opaque ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__cond ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__Format.


Definition ConfigRestrictInfoSCG__ext1O__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoSCG__ext1O__list.
Definition ConfigRestrictInfoSCG__ext1O__Format_list : ConfigRestrictInfoSCG__ext1O__Format_Type :=
  (ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG__Format, (ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG__Format, unit_format)).
Definition ConfigRestrictInfoSCG__ext1O__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoSCG__ext1O__list ConfigRestrictInfoSCG__ext1O__Format_list.
Definition ConfigRestrictInfoSCG__ext1O__F1 z :=
  (ConfigRestrictInfoSCG__ext1O__maxIntraFreqMeasIdentitiesSCG z, (ConfigRestrictInfoSCG__ext1O__maxInterFreqMeasIdentitiesSCG z, tt)).
Definition ConfigRestrictInfoSCG__ext1O__F2 (y : seq_type ConfigRestrictInfoSCG__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ConfigRestrictInfoSCG__ext1O__Type i0 i1
  end.
Lemma ConfigRestrictInfoSCG__ext1O__F1F2_cond (z : ConfigRestrictInfoSCG__ext1O__Type)
  : ConfigRestrictInfoSCG__ext1O__cond z ->
  (seq_cond ConfigRestrictInfoSCG__ext1O__list (ConfigRestrictInfoSCG__ext1O__F1 z)).
intro H. unfold ConfigRestrictInfoSCG__ext1O__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext1O__F1F2_cond2 (z : ConfigRestrictInfoSCG__ext1O__Type)
 : ConfigRestrictInfoSCG__ext1O__F2 (ConfigRestrictInfoSCG__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext1O__F2F1_cond (y : seq_type ConfigRestrictInfoSCG__ext1O__list)
  : seq_cond ConfigRestrictInfoSCG__ext1O__list y ->
 (ConfigRestrictInfoSCG__ext1O__cond (ConfigRestrictInfoSCG__ext1O__F2 y)) /\  ConfigRestrictInfoSCG__ext1O__F1 (ConfigRestrictInfoSCG__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoSCG__ext1O__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoSCG__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoSCG__ext1O__Format : T_Format ConfigRestrictInfoSCG__ext1O__Type ConfigRestrictInfoSCG__ext1O__cond :=
        proj2_format  ConfigRestrictInfoSCG__ext1O__cond ConfigRestrictInfoSCG__ext1O__list__Format
    ConfigRestrictInfoSCG__ext1O__F1 ConfigRestrictInfoSCG__ext1O__F2 ConfigRestrictInfoSCG__ext1O__F1F2_cond  ConfigRestrictInfoSCG__ext1O__F1F2_cond2 ConfigRestrictInfoSCG__ext1O__F2F1_cond.
Opaque ConfigRestrictInfoSCG__ext1O__cond ConfigRestrictInfoSCG__ext1O__Format.

Definition ConfigRestrictInfoSCG__ext1__check_all_none (b : ConfigRestrictInfoSCG__ext1O__Type) : bool :=
match b with 
  | make__ConfigRestrictInfoSCG__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition ConfigRestrictInfoSCG__ext1__Format : T_Format ConfigRestrictInfoSCG__ext1__Type ConfigRestrictInfoSCG__ext1__cond :=
  restrict_add_format ConfigRestrictInfoSCG__ext1__check_all_none ConfigRestrictInfoSCG__ext1O__Format.

Opaque ConfigRestrictInfoSCG__ext1__cond ConfigRestrictInfoSCG__ext1__Format.


Definition ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list.
Definition ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Format_list : ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Format_Type :=
  (P_Max__Format, (P_Max__Format, (P_Max__Format, unit_format))).
Definition ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Format_list.
Definition ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1 z :=
  (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxNR_FR2_MCG_r16 z, (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxNR_FR2_SCG_r16 z, (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__p_maxUE_FR2_r16 z, tt))).
Definition ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F2 (y : seq_type ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Type i0 i1 i2
  end.
Lemma ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1F2_cond (z : ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Type)
  : ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond z ->
  (seq_cond ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1 z)).
intro H. unfold ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1F2_cond2 (z : ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Type)
 : ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F2 (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F2F1_cond (y : seq_type ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list)
  : seq_cond ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list y ->
 (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F2 y)) /\  ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1 (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Format : T_Format ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Type ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond :=
        proj2_format  ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__list__Format
    ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1 ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F2 ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1F2_cond  ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F1F2_cond2 ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__F2F1_cond.
Opaque ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__cond ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Format.

Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Format : T_Format ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__nat__Format ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F1 ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F2 ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F1F2 ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__F2F1.

Opaque ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__cond ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Format.

Definition ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Format : T_Format ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__nat__Format ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F1 ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F2 ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F1F2 ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__F2F1.

Opaque ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__cond ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Format.

Definition ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__Format : T_Format Z ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__cond :=
 ranged_int_format (0) (maxNrofCLI_SRS_Resources_r16) ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__helper1 ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__helper2.

Opaque ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__cond ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__Format.

Definition ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__Format : T_Format Z ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__cond :=
 ranged_int_format (0) (maxNrofCLI_RSSI_Resources_r16) ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__helper1 ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__helper2.

Opaque ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__cond ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__Format.

Definition ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__Format : T_Format Z ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__cond :=
 ranged_int_format (0) (65536) ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__helper1 ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__helper2.

Opaque ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__cond ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__Format.


Definition ConfigRestrictInfoSCG__ext2O__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoSCG__ext2O__list.
Definition ConfigRestrictInfoSCG__ext2O__Format_list : ConfigRestrictInfoSCG__ext2O__Format_Type :=
  (P_Max__Format, (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16__Format, (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16__Format, (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16__Format, (ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16__Format, (ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16__Format, (ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16__Format, (OverheatingAssistance__Format, (T_Offset_r16__Format, unit_format))))))))).
Definition ConfigRestrictInfoSCG__ext2O__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoSCG__ext2O__list ConfigRestrictInfoSCG__ext2O__Format_list.
Definition ConfigRestrictInfoSCG__ext2O__F1 z :=
  (ConfigRestrictInfoSCG__ext2O__p_maxNR_FR1_MCG_r16 z, (ConfigRestrictInfoSCG__ext2O__powerCoordination_FR2_r16 z, (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR1_r16 z, (ConfigRestrictInfoSCG__ext2O__nrdc_PC_mode_FR2_r16 z, (ConfigRestrictInfoSCG__ext2O__maxMeasSRS_ResourceSCG_r16 z, (ConfigRestrictInfoSCG__ext2O__maxMeasCLI_ResourceSCG_r16 z, (ConfigRestrictInfoSCG__ext2O__maxNumberEHC_ContextsSN_r16 z, (ConfigRestrictInfoSCG__ext2O__allowedReducedConfigForOverheating_r16 z, (ConfigRestrictInfoSCG__ext2O__maxToffset_r16 z, tt))))))))).
Definition ConfigRestrictInfoSCG__ext2O__F2 (y : seq_type ConfigRestrictInfoSCG__ext2O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, _)))))))))=>
    make__ConfigRestrictInfoSCG__ext2O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8
  end.
Lemma ConfigRestrictInfoSCG__ext2O__F1F2_cond (z : ConfigRestrictInfoSCG__ext2O__Type)
  : ConfigRestrictInfoSCG__ext2O__cond z ->
  (seq_cond ConfigRestrictInfoSCG__ext2O__list (ConfigRestrictInfoSCG__ext2O__F1 z)).
intro H. unfold ConfigRestrictInfoSCG__ext2O__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__F1F2_cond2 (z : ConfigRestrictInfoSCG__ext2O__Type)
 : ConfigRestrictInfoSCG__ext2O__F2 (ConfigRestrictInfoSCG__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext2O__F2F1_cond (y : seq_type ConfigRestrictInfoSCG__ext2O__list)
  : seq_cond ConfigRestrictInfoSCG__ext2O__list y ->
 (ConfigRestrictInfoSCG__ext2O__cond (ConfigRestrictInfoSCG__ext2O__F2 y)) /\  ConfigRestrictInfoSCG__ext2O__F1 (ConfigRestrictInfoSCG__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoSCG__ext2O__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoSCG__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoSCG__ext2O__Format : T_Format ConfigRestrictInfoSCG__ext2O__Type ConfigRestrictInfoSCG__ext2O__cond :=
        proj2_format  ConfigRestrictInfoSCG__ext2O__cond ConfigRestrictInfoSCG__ext2O__list__Format
    ConfigRestrictInfoSCG__ext2O__F1 ConfigRestrictInfoSCG__ext2O__F2 ConfigRestrictInfoSCG__ext2O__F1F2_cond  ConfigRestrictInfoSCG__ext2O__F1F2_cond2 ConfigRestrictInfoSCG__ext2O__F2F1_cond.
Opaque ConfigRestrictInfoSCG__ext2O__cond ConfigRestrictInfoSCG__ext2O__Format.

Definition ConfigRestrictInfoSCG__ext2__check_all_none (b : ConfigRestrictInfoSCG__ext2O__Type) : bool :=
match b with 
  | make__ConfigRestrictInfoSCG__ext2O__Type None None None None None None None None None  => false 
  | _ => true 
 end.
Definition ConfigRestrictInfoSCG__ext2__Format : T_Format ConfigRestrictInfoSCG__ext2__Type ConfigRestrictInfoSCG__ext2__cond :=
  restrict_add_format ConfigRestrictInfoSCG__ext2__check_all_none ConfigRestrictInfoSCG__ext2O__Format.

Opaque ConfigRestrictInfoSCG__ext2__cond ConfigRestrictInfoSCG__ext2__Format.

Definition ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__Format : T_Format Z ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__cond :=
 ranged_int_format (0) (2) ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__helper1 ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__helper2.

Opaque ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__cond ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__Format.

Definition ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__Format : T_Format Z ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__cond :=
 ranged_int_format (0) (maxNrofCondCells_1_r17) ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__helper1 ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__helper2.

Opaque ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__cond ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__Format.


Definition ConfigRestrictInfoSCG__ext3O__Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoSCG__ext3O__list.
Definition ConfigRestrictInfoSCG__ext3O__Format_list : ConfigRestrictInfoSCG__ext3O__Format_Type :=
  (OverheatingAssistance_r17__Format, (ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17__Format, (ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17__Format, unit_format))).
Definition ConfigRestrictInfoSCG__ext3O__list__Format := (*Eval compute in *) seq_format ConfigRestrictInfoSCG__ext3O__list ConfigRestrictInfoSCG__ext3O__Format_list.
Definition ConfigRestrictInfoSCG__ext3O__F1 z :=
  (ConfigRestrictInfoSCG__ext3O__allowedReducedConfigForOverheating_r17 z, (ConfigRestrictInfoSCG__ext3O__maxNumberUDC_DRB_r17 z, (ConfigRestrictInfoSCG__ext3O__maxNumberCPCCandidates_r17 z, tt))).
Definition ConfigRestrictInfoSCG__ext3O__F2 (y : seq_type ConfigRestrictInfoSCG__ext3O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ConfigRestrictInfoSCG__ext3O__Type i0 i1 i2
  end.
Lemma ConfigRestrictInfoSCG__ext3O__F1F2_cond (z : ConfigRestrictInfoSCG__ext3O__Type)
  : ConfigRestrictInfoSCG__ext3O__cond z ->
  (seq_cond ConfigRestrictInfoSCG__ext3O__list (ConfigRestrictInfoSCG__ext3O__F1 z)).
intro H. unfold ConfigRestrictInfoSCG__ext3O__cond in H. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext3O__F1F2_cond2 (z : ConfigRestrictInfoSCG__ext3O__Type)
 : ConfigRestrictInfoSCG__ext3O__F2 (ConfigRestrictInfoSCG__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ConfigRestrictInfoSCG__ext3O__F2F1_cond (y : seq_type ConfigRestrictInfoSCG__ext3O__list)
  : seq_cond ConfigRestrictInfoSCG__ext3O__list y ->
 (ConfigRestrictInfoSCG__ext3O__cond (ConfigRestrictInfoSCG__ext3O__F2 y)) /\  ConfigRestrictInfoSCG__ext3O__F1 (ConfigRestrictInfoSCG__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ConfigRestrictInfoSCG__ext3O__cond. simpl in *. auto.
 - simpl. unfold ConfigRestrictInfoSCG__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ConfigRestrictInfoSCG__ext3O__Format : T_Format ConfigRestrictInfoSCG__ext3O__Type ConfigRestrictInfoSCG__ext3O__cond :=
        proj2_format  ConfigRestrictInfoSCG__ext3O__cond ConfigRestrictInfoSCG__ext3O__list__Format
    ConfigRestrictInfoSCG__ext3O__F1 ConfigRestrictInfoSCG__ext3O__F2 ConfigRestrictInfoSCG__ext3O__F1F2_cond  ConfigRestrictInfoSCG__ext3O__F1F2_cond2 ConfigRestrictInfoSCG__ext3O__F2F1_cond.
Opaque ConfigRestrictInfoSCG__ext3O__cond ConfigRestrictInfoSCG__ext3O__Format.

Definition ConfigRestrictInfoSCG__ext3__check_all_none (b : ConfigRestrictInfoSCG__ext3O__Type) : bool :=
match b with 
  | make__ConfigRestrictInfoSCG__ext3O__Type None None None  => false 
  | _ => true 
 end.
Definition ConfigRestrictInfoSCG__ext3__Format : T_Format ConfigRestrictInfoSCG__ext3__Type ConfigRestrictInfoSCG__ext3__cond :=
  restrict_add_format ConfigRestrictInfoSCG__ext3__check_all_none ConfigRestrictInfoSCG__ext3O__Format.

Opaque ConfigRestrictInfoSCG__ext3__cond ConfigRestrictInfoSCG__ext3__Format.


Definition ConfigRestrictInfoSCG__root_Format_Type := Eval cbn in seq_format_prod ConfigRestrictInfoSCG__root_list.
Definition ConfigRestrictInfoSCG__root_Format_list : ConfigRestrictInfoSCG__root_Format_Type :=
  (BandCombinationInfoList__Format, (ConfigRestrictInfoSCG__powerCoordination_FR1__Format, (ConfigRestrictInfoSCG__servCellIndexRangeSCG__Format, (ConfigRestrictInfoSCG__maxMeasFreqsSCG__Format, (ConfigRestrictInfoSCG__dummy__Format, unit_format))))).

Definition ConfigRestrictInfoSCG__ext_Format_Type := Eval cbn in get_formats ConfigRestrictInfoSCG__ext_list.
Definition ConfigRestrictInfoSCG__ext_Format_list : ConfigRestrictInfoSCG__ext_Format_Type :=
  (ConfigRestrictInfoSCG__ext0__Format, (ConfigRestrictInfoSCG__ext1__Format, (ConfigRestrictInfoSCG__ext2__Format, (ConfigRestrictInfoSCG__ext3__Format, unit__Format)))).

Definition ConfigRestrictInfoSCG__list_type : Set := (seq_type ConfigRestrictInfoSCG__root_list) * (seq_ext_type ConfigRestrictInfoSCG__ext_list).
Definition ConfigRestrictInfoSCG__list_cond (z : ConfigRestrictInfoSCG__list_type) : Prop :=
        (seq_cond ConfigRestrictInfoSCG__root_list (fst z)) /\ (seq_ext_cond ConfigRestrictInfoSCG__ext_list (snd z)).
Definition ConfigRestrictInfoSCG__list_format : T_Format ConfigRestrictInfoSCG__list_type ConfigRestrictInfoSCG__list_cond :=
 (* Eval compute in *) seq_ext_format ConfigRestrictInfoSCG__root_list ConfigRestrictInfoSCG__root_Format_list ConfigRestrictInfoSCG__ext_list ConfigRestrictInfoSCG__ext_Format_list.

Opaque ConfigRestrictInfoSCG__list_format.
Definition ConfigRestrictInfoSCG__F1 (z : ConfigRestrictInfoSCG__Type) : ConfigRestrictInfoSCG__list_type :=
  (((ConfigRestrictInfoSCG__allowedBC_ListMRDC z, (ConfigRestrictInfoSCG__powerCoordination_FR1 z, (ConfigRestrictInfoSCG__servCellIndexRangeSCG z, (ConfigRestrictInfoSCG__maxMeasFreqsSCG z, (ConfigRestrictInfoSCG__dummy z, tt)))))), (
(ConfigRestrictInfoSCG__ext0 z, (ConfigRestrictInfoSCG__ext1 z, (ConfigRestrictInfoSCG__ext2 z, (ConfigRestrictInfoSCG__ext3 z, tt)))))).
Definition ConfigRestrictInfoSCG__F2 (y : ConfigRestrictInfoSCG__list_type) : ConfigRestrictInfoSCG__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, (i1, (i2, (i3, _)))))=>
    make__ConfigRestrictInfoSCG__Type j0 j1 j2 j3 j4 i0 i1 i2 i3
  end.
Definition ConfigRestrictInfoSCG__helper1 : (forall a : ConfigRestrictInfoSCG__Type, ConfigRestrictInfoSCG__cond a -> ConfigRestrictInfoSCG__list_cond (ConfigRestrictInfoSCG__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ConfigRestrictInfoSCG__helper2 : (forall a : ConfigRestrictInfoSCG__Type, ConfigRestrictInfoSCG__F2 (ConfigRestrictInfoSCG__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ConfigRestrictInfoSCG__helper3 : (forall b : ConfigRestrictInfoSCG__list_type, ConfigRestrictInfoSCG__list_cond b -> ConfigRestrictInfoSCG__cond (ConfigRestrictInfoSCG__F2 b) /\ ConfigRestrictInfoSCG__F1 (ConfigRestrictInfoSCG__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ConfigRestrictInfoSCG__cond, ConfigRestrictInfoSCG__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ConfigRestrictInfoSCG__Format : T_Format ConfigRestrictInfoSCG__Type ConfigRestrictInfoSCG__cond :=
 proj2_format ConfigRestrictInfoSCG__cond ConfigRestrictInfoSCG__list_format  ConfigRestrictInfoSCG__F1 ConfigRestrictInfoSCG__F2 ConfigRestrictInfoSCG__helper1 ConfigRestrictInfoSCG__helper2 ConfigRestrictInfoSCG__helper3.

Opaque ConfigRestrictInfoSCG__cond ConfigRestrictInfoSCG__Format.

