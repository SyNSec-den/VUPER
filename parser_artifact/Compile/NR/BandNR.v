Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Definition BandNR__modifiedMPR_Behaviour__Type := bit_string_fixed.
Definition BandNR__modifiedMPR_Behaviour__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Require Import NR.MIMO_ParametersPerBand.

Opaque MIMO_ParametersPerBand__cond MIMO_ParametersPerBand__Format.

Inductive BandNR__extendedCP__Type : Set :=
 | BandNR__extendedCP__supported
.
Definition BandNR__extendedCP__cond := (fun (_ : BandNR__extendedCP__Type) => True).
Lemma BandNR__extendedCP__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__extendedCP__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__extendedCP__nat__helper.

Definition BandNR__extendedCP__F1 t :=
  match t with
  | BandNR__extendedCP__supported => 0
  end.
Definition BandNR__extendedCP__F2 n :=
  match n with
  | 0 => BandNR__extendedCP__supported
  | _ => BandNR__extendedCP__supported
  end.
Lemma BandNR__extendedCP__F1F2 : forall x : BandNR__extendedCP__Type, (BandNR__extendedCP__F1 x <= 0) /\ BandNR__extendedCP__F2 (BandNR__extendedCP__F1 x) = x. imp_solve. Qed.
Lemma BandNR__extendedCP__F2F1 : forall (y : nat) (H : y <= 0), BandNR__extendedCP__F1 (BandNR__extendedCP__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__multipleTCI__Type : Set :=
 | BandNR__multipleTCI__supported
.
Definition BandNR__multipleTCI__cond := (fun (_ : BandNR__multipleTCI__Type) => True).
Lemma BandNR__multipleTCI__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__multipleTCI__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__multipleTCI__nat__helper.

Definition BandNR__multipleTCI__F1 t :=
  match t with
  | BandNR__multipleTCI__supported => 0
  end.
Definition BandNR__multipleTCI__F2 n :=
  match n with
  | 0 => BandNR__multipleTCI__supported
  | _ => BandNR__multipleTCI__supported
  end.
Lemma BandNR__multipleTCI__F1F2 : forall x : BandNR__multipleTCI__Type, (BandNR__multipleTCI__F1 x <= 0) /\ BandNR__multipleTCI__F2 (BandNR__multipleTCI__F1 x) = x. imp_solve. Qed.
Lemma BandNR__multipleTCI__F2F1 : forall (y : nat) (H : y <= 0), BandNR__multipleTCI__F1 (BandNR__multipleTCI__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__bwp_WithoutRestriction__Type : Set :=
 | BandNR__bwp_WithoutRestriction__supported
.
Definition BandNR__bwp_WithoutRestriction__cond := (fun (_ : BandNR__bwp_WithoutRestriction__Type) => True).
Lemma BandNR__bwp_WithoutRestriction__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__bwp_WithoutRestriction__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__bwp_WithoutRestriction__nat__helper.

Definition BandNR__bwp_WithoutRestriction__F1 t :=
  match t with
  | BandNR__bwp_WithoutRestriction__supported => 0
  end.
Definition BandNR__bwp_WithoutRestriction__F2 n :=
  match n with
  | 0 => BandNR__bwp_WithoutRestriction__supported
  | _ => BandNR__bwp_WithoutRestriction__supported
  end.
Lemma BandNR__bwp_WithoutRestriction__F1F2 : forall x : BandNR__bwp_WithoutRestriction__Type, (BandNR__bwp_WithoutRestriction__F1 x <= 0) /\ BandNR__bwp_WithoutRestriction__F2 (BandNR__bwp_WithoutRestriction__F1 x) = x. imp_solve. Qed.
Lemma BandNR__bwp_WithoutRestriction__F2F1 : forall (y : nat) (H : y <= 0), BandNR__bwp_WithoutRestriction__F1 (BandNR__bwp_WithoutRestriction__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__bwp_SameNumerology__Type : Set :=
 | BandNR__bwp_SameNumerology__upto2
 | BandNR__bwp_SameNumerology__upto4
.
Definition BandNR__bwp_SameNumerology__cond := (fun (_ : BandNR__bwp_SameNumerology__Type) => True).
Lemma BandNR__bwp_SameNumerology__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__bwp_SameNumerology__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandNR__bwp_SameNumerology__nat__helper.

Definition BandNR__bwp_SameNumerology__F1 t :=
  match t with
  | BandNR__bwp_SameNumerology__upto2 => 0
  | BandNR__bwp_SameNumerology__upto4 => 1
  end.
Definition BandNR__bwp_SameNumerology__F2 n :=
  match n with
  | 0 => BandNR__bwp_SameNumerology__upto2
  | 1 => BandNR__bwp_SameNumerology__upto4
  | _ => BandNR__bwp_SameNumerology__upto2
  end.
Lemma BandNR__bwp_SameNumerology__F1F2 : forall x : BandNR__bwp_SameNumerology__Type, (BandNR__bwp_SameNumerology__F1 x <= 1) /\ BandNR__bwp_SameNumerology__F2 (BandNR__bwp_SameNumerology__F1 x) = x. imp_solve. Qed.
Lemma BandNR__bwp_SameNumerology__F2F1 : forall (y : nat) (H : y <= 1), BandNR__bwp_SameNumerology__F1 (BandNR__bwp_SameNumerology__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__bwp_DiffNumerology__Type : Set :=
 | BandNR__bwp_DiffNumerology__upto4
.
Definition BandNR__bwp_DiffNumerology__cond := (fun (_ : BandNR__bwp_DiffNumerology__Type) => True).
Lemma BandNR__bwp_DiffNumerology__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__bwp_DiffNumerology__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__bwp_DiffNumerology__nat__helper.

Definition BandNR__bwp_DiffNumerology__F1 t :=
  match t with
  | BandNR__bwp_DiffNumerology__upto4 => 0
  end.
Definition BandNR__bwp_DiffNumerology__F2 n :=
  match n with
  | 0 => BandNR__bwp_DiffNumerology__upto4
  | _ => BandNR__bwp_DiffNumerology__upto4
  end.
Lemma BandNR__bwp_DiffNumerology__F1F2 : forall x : BandNR__bwp_DiffNumerology__Type, (BandNR__bwp_DiffNumerology__F1 x <= 0) /\ BandNR__bwp_DiffNumerology__F2 (BandNR__bwp_DiffNumerology__F1 x) = x. imp_solve. Qed.
Lemma BandNR__bwp_DiffNumerology__F2F1 : forall (y : nat) (H : y <= 0), BandNR__bwp_DiffNumerology__F1 (BandNR__bwp_DiffNumerology__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__crossCarrierScheduling_SameSCS__Type : Set :=
 | BandNR__crossCarrierScheduling_SameSCS__supported
.
Definition BandNR__crossCarrierScheduling_SameSCS__cond := (fun (_ : BandNR__crossCarrierScheduling_SameSCS__Type) => True).
Lemma BandNR__crossCarrierScheduling_SameSCS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__crossCarrierScheduling_SameSCS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__crossCarrierScheduling_SameSCS__nat__helper.

Definition BandNR__crossCarrierScheduling_SameSCS__F1 t :=
  match t with
  | BandNR__crossCarrierScheduling_SameSCS__supported => 0
  end.
Definition BandNR__crossCarrierScheduling_SameSCS__F2 n :=
  match n with
  | 0 => BandNR__crossCarrierScheduling_SameSCS__supported
  | _ => BandNR__crossCarrierScheduling_SameSCS__supported
  end.
Lemma BandNR__crossCarrierScheduling_SameSCS__F1F2 : forall x : BandNR__crossCarrierScheduling_SameSCS__Type, (BandNR__crossCarrierScheduling_SameSCS__F1 x <= 0) /\ BandNR__crossCarrierScheduling_SameSCS__F2 (BandNR__crossCarrierScheduling_SameSCS__F1 x) = x. imp_solve. Qed.
Lemma BandNR__crossCarrierScheduling_SameSCS__F2F1 : forall (y : nat) (H : y <= 0), BandNR__crossCarrierScheduling_SameSCS__F1 (BandNR__crossCarrierScheduling_SameSCS__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__pdsch_256QAM_FR2__Type : Set :=
 | BandNR__pdsch_256QAM_FR2__supported
.
Definition BandNR__pdsch_256QAM_FR2__cond := (fun (_ : BandNR__pdsch_256QAM_FR2__Type) => True).
Lemma BandNR__pdsch_256QAM_FR2__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__pdsch_256QAM_FR2__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__pdsch_256QAM_FR2__nat__helper.

Definition BandNR__pdsch_256QAM_FR2__F1 t :=
  match t with
  | BandNR__pdsch_256QAM_FR2__supported => 0
  end.
Definition BandNR__pdsch_256QAM_FR2__F2 n :=
  match n with
  | 0 => BandNR__pdsch_256QAM_FR2__supported
  | _ => BandNR__pdsch_256QAM_FR2__supported
  end.
Lemma BandNR__pdsch_256QAM_FR2__F1F2 : forall x : BandNR__pdsch_256QAM_FR2__Type, (BandNR__pdsch_256QAM_FR2__F1 x <= 0) /\ BandNR__pdsch_256QAM_FR2__F2 (BandNR__pdsch_256QAM_FR2__F1 x) = x. imp_solve. Qed.
Lemma BandNR__pdsch_256QAM_FR2__F2F1 : forall (y : nat) (H : y <= 0), BandNR__pdsch_256QAM_FR2__F1 (BandNR__pdsch_256QAM_FR2__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__pusch_256QAM__Type : Set :=
 | BandNR__pusch_256QAM__supported
.
Definition BandNR__pusch_256QAM__cond := (fun (_ : BandNR__pusch_256QAM__Type) => True).
Lemma BandNR__pusch_256QAM__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__pusch_256QAM__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__pusch_256QAM__nat__helper.

Definition BandNR__pusch_256QAM__F1 t :=
  match t with
  | BandNR__pusch_256QAM__supported => 0
  end.
Definition BandNR__pusch_256QAM__F2 n :=
  match n with
  | 0 => BandNR__pusch_256QAM__supported
  | _ => BandNR__pusch_256QAM__supported
  end.
Lemma BandNR__pusch_256QAM__F1F2 : forall x : BandNR__pusch_256QAM__Type, (BandNR__pusch_256QAM__F1 x <= 0) /\ BandNR__pusch_256QAM__F2 (BandNR__pusch_256QAM__F1 x) = x. imp_solve. Qed.
Lemma BandNR__pusch_256QAM__F2F1 : forall (y : nat) (H : y <= 0), BandNR__pusch_256QAM__F1 (BandNR__pusch_256QAM__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ue_PowerClass__Type : Set :=
 | BandNR__ue_PowerClass__pc1
 | BandNR__ue_PowerClass__pc2
 | BandNR__ue_PowerClass__pc3
 | BandNR__ue_PowerClass__pc4
.
Definition BandNR__ue_PowerClass__cond := (fun (_ : BandNR__ue_PowerClass__Type) => True).
Lemma BandNR__ue_PowerClass__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ue_PowerClass__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BandNR__ue_PowerClass__nat__helper.

Definition BandNR__ue_PowerClass__F1 t :=
  match t with
  | BandNR__ue_PowerClass__pc1 => 0
  | BandNR__ue_PowerClass__pc2 => 1
  | BandNR__ue_PowerClass__pc3 => 2
  | BandNR__ue_PowerClass__pc4 => 3
  end.
Definition BandNR__ue_PowerClass__F2 n :=
  match n with
  | 0 => BandNR__ue_PowerClass__pc1
  | 1 => BandNR__ue_PowerClass__pc2
  | 2 => BandNR__ue_PowerClass__pc3
  | 3 => BandNR__ue_PowerClass__pc4
  | _ => BandNR__ue_PowerClass__pc1
  end.
Lemma BandNR__ue_PowerClass__F1F2 : forall x : BandNR__ue_PowerClass__Type, (BandNR__ue_PowerClass__F1 x <= 3) /\ BandNR__ue_PowerClass__F2 (BandNR__ue_PowerClass__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ue_PowerClass__F2F1 : forall (y : nat) (H : y <= 3), BandNR__ue_PowerClass__F1 (BandNR__ue_PowerClass__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__rateMatchingLTE_CRS__Type : Set :=
 | BandNR__rateMatchingLTE_CRS__supported
.
Definition BandNR__rateMatchingLTE_CRS__cond := (fun (_ : BandNR__rateMatchingLTE_CRS__Type) => True).
Lemma BandNR__rateMatchingLTE_CRS__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__rateMatchingLTE_CRS__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__rateMatchingLTE_CRS__nat__helper.

Definition BandNR__rateMatchingLTE_CRS__F1 t :=
  match t with
  | BandNR__rateMatchingLTE_CRS__supported => 0
  end.
Definition BandNR__rateMatchingLTE_CRS__F2 n :=
  match n with
  | 0 => BandNR__rateMatchingLTE_CRS__supported
  | _ => BandNR__rateMatchingLTE_CRS__supported
  end.
Lemma BandNR__rateMatchingLTE_CRS__F1F2 : forall x : BandNR__rateMatchingLTE_CRS__Type, (BandNR__rateMatchingLTE_CRS__F1 x <= 0) /\ BandNR__rateMatchingLTE_CRS__F2 (BandNR__rateMatchingLTE_CRS__F1 x) = x. imp_solve. Qed.
Lemma BandNR__rateMatchingLTE_CRS__F2F1 : forall (y : nat) (H : y <= 0), BandNR__rateMatchingLTE_CRS__F1 (BandNR__rateMatchingLTE_CRS__F2 y) = y. enum_solve H y. Qed.

Definition BandNR__channelBWs_DL__fr1__scs_15kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_DL__fr1__scs_15kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__channelBWs_DL__fr1__scs_30kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_DL__fr1__scs_30kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__channelBWs_DL__fr1__scs_60kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_DL__fr1__scs_60kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__channelBWs_DL__fr1__Type : Set :=
  make__BandNR__channelBWs_DL__fr1__Type {
    BandNR__channelBWs_DL__fr1__scs_15kHz : option BandNR__channelBWs_DL__fr1__scs_15kHz__Type ;
    BandNR__channelBWs_DL__fr1__scs_30kHz : option BandNR__channelBWs_DL__fr1__scs_30kHz__Type ;
    BandNR__channelBWs_DL__fr1__scs_60kHz : option BandNR__channelBWs_DL__fr1__scs_60kHz__Type ;
}.
Definition BandNR__channelBWs_DL__fr1__list := (
 Opt BandNR__channelBWs_DL__fr1__scs_15kHz__Type BandNR__channelBWs_DL__fr1__scs_15kHz__cond ::
 Opt BandNR__channelBWs_DL__fr1__scs_30kHz__Type BandNR__channelBWs_DL__fr1__scs_30kHz__cond ::
 Opt BandNR__channelBWs_DL__fr1__scs_60kHz__Type BandNR__channelBWs_DL__fr1__scs_60kHz__cond ::
 nil).
Definition BandNR__channelBWs_DL__fr1__cond z := 
  opt_cond BandNR__channelBWs_DL__fr1__scs_15kHz__cond (BandNR__channelBWs_DL__fr1__scs_15kHz z) /\
  opt_cond BandNR__channelBWs_DL__fr1__scs_30kHz__cond (BandNR__channelBWs_DL__fr1__scs_30kHz z) /\
  opt_cond BandNR__channelBWs_DL__fr1__scs_60kHz__cond (BandNR__channelBWs_DL__fr1__scs_60kHz z) /\
  True.

Definition BandNR__channelBWs_DL__fr2__scs_60kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_DL__fr2__scs_60kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 3 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__channelBWs_DL__fr2__scs_120kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_DL__fr2__scs_120kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 3 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__channelBWs_DL__fr2__Type : Set :=
  make__BandNR__channelBWs_DL__fr2__Type {
    BandNR__channelBWs_DL__fr2__scs_60kHz : option BandNR__channelBWs_DL__fr2__scs_60kHz__Type ;
    BandNR__channelBWs_DL__fr2__scs_120kHz : option BandNR__channelBWs_DL__fr2__scs_120kHz__Type ;
}.
Definition BandNR__channelBWs_DL__fr2__list := (
 Opt BandNR__channelBWs_DL__fr2__scs_60kHz__Type BandNR__channelBWs_DL__fr2__scs_60kHz__cond ::
 Opt BandNR__channelBWs_DL__fr2__scs_120kHz__Type BandNR__channelBWs_DL__fr2__scs_120kHz__cond ::
 nil).
Definition BandNR__channelBWs_DL__fr2__cond z := 
  opt_cond BandNR__channelBWs_DL__fr2__scs_60kHz__cond (BandNR__channelBWs_DL__fr2__scs_60kHz z) /\
  opt_cond BandNR__channelBWs_DL__fr2__scs_120kHz__cond (BandNR__channelBWs_DL__fr2__scs_120kHz z) /\
  True.


Inductive BandNR__channelBWs_DL__Type : Set :=
  | BandNR__channelBWs_DL__fr1 : BandNR__channelBWs_DL__fr1__Type -> BandNR__channelBWs_DL__Type
  | BandNR__channelBWs_DL__fr2 : BandNR__channelBWs_DL__fr2__Type -> BandNR__channelBWs_DL__Type
.
Definition BandNR__channelBWs_DL__list : list typ := (
typ_cons BandNR__channelBWs_DL__fr1__Type BandNR__channelBWs_DL__fr1__cond ::
typ_cons BandNR__channelBWs_DL__fr2__Type BandNR__channelBWs_DL__fr2__cond ::
 nil).
Definition BandNR__channelBWs_DL__cond (c : BandNR__channelBWs_DL__Type) := 
  match c with
  | BandNR__channelBWs_DL__fr1 t => BandNR__channelBWs_DL__fr1__cond t 
  | BandNR__channelBWs_DL__fr2 t => BandNR__channelBWs_DL__fr2__cond t 
  end.

Lemma BandNR__channelBWs_DL__len_helper1 : to_bit_sz (length BandNR__channelBWs_DL__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandNR__channelBWs_DL__len_helper2 : 2 <= length2 BandNR__channelBWs_DL__list.
 simpl. lia. Qed.
Definition BandNR__channelBWs_UL__fr1__scs_15kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_UL__fr1__scs_15kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__channelBWs_UL__fr1__scs_30kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_UL__fr1__scs_30kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__channelBWs_UL__fr1__scs_60kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_UL__fr1__scs_60kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 10 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__channelBWs_UL__fr1__Type : Set :=
  make__BandNR__channelBWs_UL__fr1__Type {
    BandNR__channelBWs_UL__fr1__scs_15kHz : option BandNR__channelBWs_UL__fr1__scs_15kHz__Type ;
    BandNR__channelBWs_UL__fr1__scs_30kHz : option BandNR__channelBWs_UL__fr1__scs_30kHz__Type ;
    BandNR__channelBWs_UL__fr1__scs_60kHz : option BandNR__channelBWs_UL__fr1__scs_60kHz__Type ;
}.
Definition BandNR__channelBWs_UL__fr1__list := (
 Opt BandNR__channelBWs_UL__fr1__scs_15kHz__Type BandNR__channelBWs_UL__fr1__scs_15kHz__cond ::
 Opt BandNR__channelBWs_UL__fr1__scs_30kHz__Type BandNR__channelBWs_UL__fr1__scs_30kHz__cond ::
 Opt BandNR__channelBWs_UL__fr1__scs_60kHz__Type BandNR__channelBWs_UL__fr1__scs_60kHz__cond ::
 nil).
Definition BandNR__channelBWs_UL__fr1__cond z := 
  opt_cond BandNR__channelBWs_UL__fr1__scs_15kHz__cond (BandNR__channelBWs_UL__fr1__scs_15kHz z) /\
  opt_cond BandNR__channelBWs_UL__fr1__scs_30kHz__cond (BandNR__channelBWs_UL__fr1__scs_30kHz z) /\
  opt_cond BandNR__channelBWs_UL__fr1__scs_60kHz__cond (BandNR__channelBWs_UL__fr1__scs_60kHz z) /\
  True.

Definition BandNR__channelBWs_UL__fr2__scs_60kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_UL__fr2__scs_60kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 3 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__channelBWs_UL__fr2__scs_120kHz__Type := bit_string_fixed.
Definition BandNR__channelBWs_UL__fr2__scs_120kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 3 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__channelBWs_UL__fr2__Type : Set :=
  make__BandNR__channelBWs_UL__fr2__Type {
    BandNR__channelBWs_UL__fr2__scs_60kHz : option BandNR__channelBWs_UL__fr2__scs_60kHz__Type ;
    BandNR__channelBWs_UL__fr2__scs_120kHz : option BandNR__channelBWs_UL__fr2__scs_120kHz__Type ;
}.
Definition BandNR__channelBWs_UL__fr2__list := (
 Opt BandNR__channelBWs_UL__fr2__scs_60kHz__Type BandNR__channelBWs_UL__fr2__scs_60kHz__cond ::
 Opt BandNR__channelBWs_UL__fr2__scs_120kHz__Type BandNR__channelBWs_UL__fr2__scs_120kHz__cond ::
 nil).
Definition BandNR__channelBWs_UL__fr2__cond z := 
  opt_cond BandNR__channelBWs_UL__fr2__scs_60kHz__cond (BandNR__channelBWs_UL__fr2__scs_60kHz z) /\
  opt_cond BandNR__channelBWs_UL__fr2__scs_120kHz__cond (BandNR__channelBWs_UL__fr2__scs_120kHz z) /\
  True.


Inductive BandNR__channelBWs_UL__Type : Set :=
  | BandNR__channelBWs_UL__fr1 : BandNR__channelBWs_UL__fr1__Type -> BandNR__channelBWs_UL__Type
  | BandNR__channelBWs_UL__fr2 : BandNR__channelBWs_UL__fr2__Type -> BandNR__channelBWs_UL__Type
.
Definition BandNR__channelBWs_UL__list : list typ := (
typ_cons BandNR__channelBWs_UL__fr1__Type BandNR__channelBWs_UL__fr1__cond ::
typ_cons BandNR__channelBWs_UL__fr2__Type BandNR__channelBWs_UL__fr2__cond ::
 nil).
Definition BandNR__channelBWs_UL__cond (c : BandNR__channelBWs_UL__Type) := 
  match c with
  | BandNR__channelBWs_UL__fr1 t => BandNR__channelBWs_UL__fr1__cond t 
  | BandNR__channelBWs_UL__fr2 t => BandNR__channelBWs_UL__fr2__cond t 
  end.

Lemma BandNR__channelBWs_UL__len_helper1 : to_bit_sz (length BandNR__channelBWs_UL__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandNR__channelBWs_UL__len_helper2 : 2 <= length2 BandNR__channelBWs_UL__list.
 simpl. lia. Qed.
Inductive BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Type : Set :=
 | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n60
 | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n70
 | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n80
 | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n90
 | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n100
.
Definition BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__cond := (fun (_ : BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Type) => True).
Lemma BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__nat__helper.

Definition BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F1 t :=
  match t with
  | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n60 => 0
  | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n70 => 1
  | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n80 => 2
  | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n90 => 3
  | BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n100 => 4
  end.
Definition BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F2 n :=
  match n with
  | 0 => BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n60
  | 1 => BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n70
  | 2 => BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n80
  | 3 => BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n90
  | 4 => BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n100
  | _ => BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__n60
  end.
Lemma BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F1F2 : forall x : BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Type, (BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F1 x <= 4) /\ BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F2 (BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F2F1 : forall (y : nat) (H : y <= 4), BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F1 (BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext0O__Type : Set :=
  make__BandNR__ext0O__Type {
    BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1 : option BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Type ;
}.
Definition BandNR__ext0O__list := (
 Opt BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Type BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__cond ::
 nil).
Definition BandNR__ext0O__cond z := 
  opt_cond BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__cond (BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1 z) /\
  True.

Definition BandNR__ext0__Type := BandNR__ext0O__Type.
Definition BandNR__ext0__cond := BandNR__ext0O__cond.

Inductive BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Type : Set :=
 | BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__supported
.
Definition BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__cond := (fun (_ : BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Type) => True).
Lemma BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__nat__helper.

Definition BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F1 t :=
  match t with
  | BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__supported => 0
  end.
Definition BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F2 n :=
  match n with
  | 0 => BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__supported
  | _ => BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__supported
  end.
Lemma BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F1F2 : forall x : BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Type, (BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F1 x <= 0) /\ BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F2 (BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F1 (BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext1O__powerBoosting_pi2BPSK__Type : Set :=
 | BandNR__ext1O__powerBoosting_pi2BPSK__supported
.
Definition BandNR__ext1O__powerBoosting_pi2BPSK__cond := (fun (_ : BandNR__ext1O__powerBoosting_pi2BPSK__Type) => True).
Lemma BandNR__ext1O__powerBoosting_pi2BPSK__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext1O__powerBoosting_pi2BPSK__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext1O__powerBoosting_pi2BPSK__nat__helper.

Definition BandNR__ext1O__powerBoosting_pi2BPSK__F1 t :=
  match t with
  | BandNR__ext1O__powerBoosting_pi2BPSK__supported => 0
  end.
Definition BandNR__ext1O__powerBoosting_pi2BPSK__F2 n :=
  match n with
  | 0 => BandNR__ext1O__powerBoosting_pi2BPSK__supported
  | _ => BandNR__ext1O__powerBoosting_pi2BPSK__supported
  end.
Lemma BandNR__ext1O__powerBoosting_pi2BPSK__F1F2 : forall x : BandNR__ext1O__powerBoosting_pi2BPSK__Type, (BandNR__ext1O__powerBoosting_pi2BPSK__F1 x <= 0) /\ BandNR__ext1O__powerBoosting_pi2BPSK__F2 (BandNR__ext1O__powerBoosting_pi2BPSK__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext1O__powerBoosting_pi2BPSK__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext1O__powerBoosting_pi2BPSK__F1 (BandNR__ext1O__powerBoosting_pi2BPSK__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext1O__Type : Set :=
  make__BandNR__ext1O__Type {
    BandNR__ext1O__pucch_SpatialRelInfoMAC_CE : option BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Type ;
    BandNR__ext1O__powerBoosting_pi2BPSK : option BandNR__ext1O__powerBoosting_pi2BPSK__Type ;
}.
Definition BandNR__ext1O__list := (
 Opt BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Type BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__cond ::
 Opt BandNR__ext1O__powerBoosting_pi2BPSK__Type BandNR__ext1O__powerBoosting_pi2BPSK__cond ::
 nil).
Definition BandNR__ext1O__cond z := 
  opt_cond BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__cond (BandNR__ext1O__pucch_SpatialRelInfoMAC_CE z) /\
  opt_cond BandNR__ext1O__powerBoosting_pi2BPSK__cond (BandNR__ext1O__powerBoosting_pi2BPSK z) /\
  True.

Definition BandNR__ext1__Type := BandNR__ext1O__Type.
Definition BandNR__ext1__cond := BandNR__ext1O__cond.

Inductive BandNR__ext2O__maxUplinkDutyCycle_FR2__Type : Set :=
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n15
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n20
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n25
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n30
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n40
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n50
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n60
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n70
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n80
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n90
 | BandNR__ext2O__maxUplinkDutyCycle_FR2__n100
.
Definition BandNR__ext2O__maxUplinkDutyCycle_FR2__cond := (fun (_ : BandNR__ext2O__maxUplinkDutyCycle_FR2__Type) => True).
Lemma BandNR__ext2O__maxUplinkDutyCycle_FR2__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext2O__maxUplinkDutyCycle_FR2__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 BandNR__ext2O__maxUplinkDutyCycle_FR2__nat__helper.

Definition BandNR__ext2O__maxUplinkDutyCycle_FR2__F1 t :=
  match t with
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n15 => 0
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n20 => 1
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n25 => 2
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n30 => 3
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n40 => 4
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n50 => 5
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n60 => 6
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n70 => 7
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n80 => 8
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n90 => 9
  | BandNR__ext2O__maxUplinkDutyCycle_FR2__n100 => 10
  end.
Definition BandNR__ext2O__maxUplinkDutyCycle_FR2__F2 n :=
  match n with
  | 0 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n15
  | 1 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n20
  | 2 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n25
  | 3 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n30
  | 4 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n40
  | 5 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n50
  | 6 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n60
  | 7 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n70
  | 8 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n80
  | 9 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n90
  | 10 => BandNR__ext2O__maxUplinkDutyCycle_FR2__n100
  | _ => BandNR__ext2O__maxUplinkDutyCycle_FR2__n15
  end.
Lemma BandNR__ext2O__maxUplinkDutyCycle_FR2__F1F2 : forall x : BandNR__ext2O__maxUplinkDutyCycle_FR2__Type, (BandNR__ext2O__maxUplinkDutyCycle_FR2__F1 x <= 10) /\ BandNR__ext2O__maxUplinkDutyCycle_FR2__F2 (BandNR__ext2O__maxUplinkDutyCycle_FR2__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext2O__maxUplinkDutyCycle_FR2__F2F1 : forall (y : nat) (H : y <= 10), BandNR__ext2O__maxUplinkDutyCycle_FR2__F1 (BandNR__ext2O__maxUplinkDutyCycle_FR2__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext2O__Type : Set :=
  make__BandNR__ext2O__Type {
    BandNR__ext2O__maxUplinkDutyCycle_FR2 : option BandNR__ext2O__maxUplinkDutyCycle_FR2__Type ;
}.
Definition BandNR__ext2O__list := (
 Opt BandNR__ext2O__maxUplinkDutyCycle_FR2__Type BandNR__ext2O__maxUplinkDutyCycle_FR2__cond ::
 nil).
Definition BandNR__ext2O__cond z := 
  opt_cond BandNR__ext2O__maxUplinkDutyCycle_FR2__cond (BandNR__ext2O__maxUplinkDutyCycle_FR2 z) /\
  True.

Definition BandNR__ext2__Type := BandNR__ext2O__Type.
Definition BandNR__ext2__cond := BandNR__ext2O__cond.

Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__ext3O__channelBWs_DL_v1590__fr1__Type : Set :=
  make__BandNR__ext3O__channelBWs_DL_v1590__fr1__Type {
    BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz : option BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__Type ;
    BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz : option BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__Type ;
    BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz : option BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__Type ;
}.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__list := (
 Opt BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__cond ::
 Opt BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__cond ::
 Opt BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__cond ::
 nil).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__cond z := 
  opt_cond BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__cond (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz z) /\
  opt_cond BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__cond (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz z) /\
  opt_cond BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__cond (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz z) /\
  True.

Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__ext3O__channelBWs_DL_v1590__fr2__Type : Set :=
  make__BandNR__ext3O__channelBWs_DL_v1590__fr2__Type {
    BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz : option BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__Type ;
    BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz : option BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__Type ;
}.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__list := (
 Opt BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__cond ::
 Opt BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__cond ::
 nil).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__cond z := 
  opt_cond BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__cond (BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz z) /\
  opt_cond BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__cond (BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz z) /\
  True.


Inductive BandNR__ext3O__channelBWs_DL_v1590__Type : Set :=
  | BandNR__ext3O__channelBWs_DL_v1590__fr1 : BandNR__ext3O__channelBWs_DL_v1590__fr1__Type -> BandNR__ext3O__channelBWs_DL_v1590__Type
  | BandNR__ext3O__channelBWs_DL_v1590__fr2 : BandNR__ext3O__channelBWs_DL_v1590__fr2__Type -> BandNR__ext3O__channelBWs_DL_v1590__Type
.
Definition BandNR__ext3O__channelBWs_DL_v1590__list : list typ := (
typ_cons BandNR__ext3O__channelBWs_DL_v1590__fr1__Type BandNR__ext3O__channelBWs_DL_v1590__fr1__cond ::
typ_cons BandNR__ext3O__channelBWs_DL_v1590__fr2__Type BandNR__ext3O__channelBWs_DL_v1590__fr2__cond ::
 nil).
Definition BandNR__ext3O__channelBWs_DL_v1590__cond (c : BandNR__ext3O__channelBWs_DL_v1590__Type) := 
  match c with
  | BandNR__ext3O__channelBWs_DL_v1590__fr1 t => BandNR__ext3O__channelBWs_DL_v1590__fr1__cond t 
  | BandNR__ext3O__channelBWs_DL_v1590__fr2 t => BandNR__ext3O__channelBWs_DL_v1590__fr2__cond t 
  end.

Lemma BandNR__ext3O__channelBWs_DL_v1590__len_helper1 : to_bit_sz (length BandNR__ext3O__channelBWs_DL_v1590__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandNR__ext3O__channelBWs_DL_v1590__len_helper2 : 2 <= length2 BandNR__ext3O__channelBWs_DL_v1590__list.
 simpl. lia. Qed.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__ext3O__channelBWs_UL_v1590__fr1__Type : Set :=
  make__BandNR__ext3O__channelBWs_UL_v1590__fr1__Type {
    BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz : option BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__Type ;
    BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz : option BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__Type ;
    BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz : option BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__Type ;
}.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__list := (
 Opt BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__cond ::
 Opt BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__cond ::
 Opt BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__cond ::
 nil).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__cond z := 
  opt_cond BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__cond (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz z) /\
  opt_cond BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__cond (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz z) /\
  opt_cond BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__cond (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz z) /\
  True.

Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__Type := bit_string_fixed.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__ext3O__channelBWs_UL_v1590__fr2__Type : Set :=
  make__BandNR__ext3O__channelBWs_UL_v1590__fr2__Type {
    BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz : option BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__Type ;
    BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz : option BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__Type ;
}.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__list := (
 Opt BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__cond ::
 Opt BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__cond ::
 nil).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__cond z := 
  opt_cond BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__cond (BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz z) /\
  opt_cond BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__cond (BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz z) /\
  True.


Inductive BandNR__ext3O__channelBWs_UL_v1590__Type : Set :=
  | BandNR__ext3O__channelBWs_UL_v1590__fr1 : BandNR__ext3O__channelBWs_UL_v1590__fr1__Type -> BandNR__ext3O__channelBWs_UL_v1590__Type
  | BandNR__ext3O__channelBWs_UL_v1590__fr2 : BandNR__ext3O__channelBWs_UL_v1590__fr2__Type -> BandNR__ext3O__channelBWs_UL_v1590__Type
.
Definition BandNR__ext3O__channelBWs_UL_v1590__list : list typ := (
typ_cons BandNR__ext3O__channelBWs_UL_v1590__fr1__Type BandNR__ext3O__channelBWs_UL_v1590__fr1__cond ::
typ_cons BandNR__ext3O__channelBWs_UL_v1590__fr2__Type BandNR__ext3O__channelBWs_UL_v1590__fr2__cond ::
 nil).
Definition BandNR__ext3O__channelBWs_UL_v1590__cond (c : BandNR__ext3O__channelBWs_UL_v1590__Type) := 
  match c with
  | BandNR__ext3O__channelBWs_UL_v1590__fr1 t => BandNR__ext3O__channelBWs_UL_v1590__fr1__cond t 
  | BandNR__ext3O__channelBWs_UL_v1590__fr2 t => BandNR__ext3O__channelBWs_UL_v1590__fr2__cond t 
  end.

Lemma BandNR__ext3O__channelBWs_UL_v1590__len_helper1 : to_bit_sz (length BandNR__ext3O__channelBWs_UL_v1590__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandNR__ext3O__channelBWs_UL_v1590__len_helper2 : 2 <= length2 BandNR__ext3O__channelBWs_UL_v1590__list.
 simpl. lia. Qed.
Record BandNR__ext3O__Type : Set :=
  make__BandNR__ext3O__Type {
    BandNR__ext3O__channelBWs_DL_v1590 : option BandNR__ext3O__channelBWs_DL_v1590__Type ;
    BandNR__ext3O__channelBWs_UL_v1590 : option BandNR__ext3O__channelBWs_UL_v1590__Type ;
}.
Definition BandNR__ext3O__list := (
 Opt BandNR__ext3O__channelBWs_DL_v1590__Type BandNR__ext3O__channelBWs_DL_v1590__cond ::
 Opt BandNR__ext3O__channelBWs_UL_v1590__Type BandNR__ext3O__channelBWs_UL_v1590__cond ::
 nil).
Definition BandNR__ext3O__cond z := 
  opt_cond BandNR__ext3O__channelBWs_DL_v1590__cond (BandNR__ext3O__channelBWs_DL_v1590 z) /\
  opt_cond BandNR__ext3O__channelBWs_UL_v1590__cond (BandNR__ext3O__channelBWs_UL_v1590 z) /\
  True.

Definition BandNR__ext3__Type := BandNR__ext3O__Type.
Definition BandNR__ext3__cond := BandNR__ext3O__cond.

Lemma BandNR__ext4O__asymmetricBandwidthCombinationSet__helper1 : (0 <= 1 <= 32)%Z.  lia. Qed.
Lemma BandNR__ext4O__asymmetricBandwidthCombinationSet__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext4O__asymmetricBandwidthCombinationSet__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext4O__asymmetricBandwidthCombinationSet__Type := bit_string.
Definition BandNR__ext4O__asymmetricBandwidthCombinationSet__cond := (fun z : bit_string => (1 <= Z.of_nat (fst z) <= 32)%Z /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__ext4O__Type : Set :=
  make__BandNR__ext4O__Type {
    BandNR__ext4O__asymmetricBandwidthCombinationSet : option BandNR__ext4O__asymmetricBandwidthCombinationSet__Type ;
}.
Definition BandNR__ext4O__list := (
 Opt BandNR__ext4O__asymmetricBandwidthCombinationSet__Type BandNR__ext4O__asymmetricBandwidthCombinationSet__cond ::
 nil).
Definition BandNR__ext4O__cond z := 
  opt_cond BandNR__ext4O__asymmetricBandwidthCombinationSet__cond (BandNR__ext4O__asymmetricBandwidthCombinationSet z) /\
  True.

Definition BandNR__ext4__Type := BandNR__ext4O__Type.
Definition BandNR__ext4__cond := BandNR__ext4O__cond.

Require Import NR.SharedSpectrumChAccessParamsPerBand_r16.

Opaque SharedSpectrumChAccessParamsPerBand_r16__cond SharedSpectrumChAccessParamsPerBand_r16__Format.

Inductive BandNR__ext5O__cancelOverlappingPUSCH_r16__Type : Set :=
 | BandNR__ext5O__cancelOverlappingPUSCH_r16__supported
.
Definition BandNR__ext5O__cancelOverlappingPUSCH_r16__cond := (fun (_ : BandNR__ext5O__cancelOverlappingPUSCH_r16__Type) => True).
Lemma BandNR__ext5O__cancelOverlappingPUSCH_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__cancelOverlappingPUSCH_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__cancelOverlappingPUSCH_r16__nat__helper.

Definition BandNR__ext5O__cancelOverlappingPUSCH_r16__F1 t :=
  match t with
  | BandNR__ext5O__cancelOverlappingPUSCH_r16__supported => 0
  end.
Definition BandNR__ext5O__cancelOverlappingPUSCH_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__cancelOverlappingPUSCH_r16__supported
  | _ => BandNR__ext5O__cancelOverlappingPUSCH_r16__supported
  end.
Lemma BandNR__ext5O__cancelOverlappingPUSCH_r16__F1F2 : forall x : BandNR__ext5O__cancelOverlappingPUSCH_r16__Type, (BandNR__ext5O__cancelOverlappingPUSCH_r16__F1 x <= 0) /\ BandNR__ext5O__cancelOverlappingPUSCH_r16__F2 (BandNR__ext5O__cancelOverlappingPUSCH_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__cancelOverlappingPUSCH_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__cancelOverlappingPUSCH_r16__F1 (BandNR__ext5O__cancelOverlappingPUSCH_r16__F2 y) = y. enum_solve H y. Qed.

Lemma BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__helper1 : (2 <= 6)%Z.  lia. Qed.
Lemma BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__helper2 : to_bit_sz (Z.to_nat (6 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (6 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__Type := Z.
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__cond := (fun z => (2 <= z <= 6)%Z).
Lemma BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__helper1 : (1 <= 3)%Z.  lia. Qed.
Lemma BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__Type := Z.
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__cond := (fun z => (1 <= z <= 3)%Z).
Record BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Type : Set :=
  make__BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Type {
    BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16 : Z ;
    BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16 : Z ;
}.
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list := (
 Nor Z BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__cond ::
 Nor Z BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__cond ::
 nil).
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond z := 
  BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__cond (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16 z) /\
  BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__cond (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16 z) /\
  True.

Inductive BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Type : Set :=
 | BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__supported
.
Definition BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__cond := (fun (_ : BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Type) => True).
Lemma BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__nat__helper.

Definition BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F1 t :=
  match t with
  | BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__supported => 0
  end.
Definition BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__supported
  | _ => BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__supported
  end.
Lemma BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F1F2 : forall x : BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Type, (BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F1 x <= 0) /\ BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F2 (BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F1 (BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Type : Set :=
 | BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__supported
.
Definition BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__cond := (fun (_ : BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Type) => True).
Lemma BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__nat__helper.

Definition BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F1 t :=
  match t with
  | BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__supported => 0
  end.
Definition BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__supported
  | _ => BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__supported
  end.
Lemma BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F1F2 : forall x : BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Type, (BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F1 x <= 0) /\ BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F2 (BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F1 (BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__oneSlotPeriodicTRS_r16__Type : Set :=
 | BandNR__ext5O__oneSlotPeriodicTRS_r16__supported
.
Definition BandNR__ext5O__oneSlotPeriodicTRS_r16__cond := (fun (_ : BandNR__ext5O__oneSlotPeriodicTRS_r16__Type) => True).
Lemma BandNR__ext5O__oneSlotPeriodicTRS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__oneSlotPeriodicTRS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__oneSlotPeriodicTRS_r16__nat__helper.

Definition BandNR__ext5O__oneSlotPeriodicTRS_r16__F1 t :=
  match t with
  | BandNR__ext5O__oneSlotPeriodicTRS_r16__supported => 0
  end.
Definition BandNR__ext5O__oneSlotPeriodicTRS_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__oneSlotPeriodicTRS_r16__supported
  | _ => BandNR__ext5O__oneSlotPeriodicTRS_r16__supported
  end.
Lemma BandNR__ext5O__oneSlotPeriodicTRS_r16__F1F2 : forall x : BandNR__ext5O__oneSlotPeriodicTRS_r16__Type, (BandNR__ext5O__oneSlotPeriodicTRS_r16__F1 x <= 0) /\ BandNR__ext5O__oneSlotPeriodicTRS_r16__F2 (BandNR__ext5O__oneSlotPeriodicTRS_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__oneSlotPeriodicTRS_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__oneSlotPeriodicTRS_r16__F1 (BandNR__ext5O__oneSlotPeriodicTRS_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.OLPC_SRS_Pos_r16.

Opaque OLPC_SRS_Pos_r16__cond OLPC_SRS_Pos_r16__Format.

Require Import NR.SpatialRelationsSRS_Pos_r16.

Opaque SpatialRelationsSRS_Pos_r16__cond SpatialRelationsSRS_Pos_r16__Format.

Inductive BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Type : Set :=
 | BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__n2
.
Definition BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__cond := (fun (_ : BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Type) => True).
Lemma BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__nat__helper.

Definition BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F1 t :=
  match t with
  | BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__n2 => 0
  end.
Definition BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__n2
  | _ => BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__n2
  end.
Lemma BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F1F2 : forall x : BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Type, (BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F1 x <= 0) /\ BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F2 (BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F1 (BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Type : Set :=
 | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__supported
.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__cond := (fun (_ : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__nat__helper.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__supported
  | _ => BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F1F2 : forall x : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Type, (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F2 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F1 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Type : Set :=
 | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__supported
.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__cond := (fun (_ : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__nat__helper.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__supported
  | _ => BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F1F2 : forall x : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Type, (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F2 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F1 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Type : Set :=
 | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__supported
.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__cond := (fun (_ : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__nat__helper.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__supported
  | _ => BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F1F2 : forall x : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Type, (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F2 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F1 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type : Set :=
  make__BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type {
    BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz : option BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Type ;
    BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz : option BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Type ;
    BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz : option BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Type ;
}.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list := (
 Opt BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__cond ::
 Opt BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__cond ::
 Opt BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__cond ::
 nil).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond z := 
  opt_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__cond (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz z) /\
  opt_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__cond (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz z) /\
  opt_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__cond (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz z) /\
  True.

Inductive BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Type : Set :=
 | BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__supported
.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__cond := (fun (_ : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__nat__helper.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__supported
  | _ => BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F1F2 : forall x : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Type, (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F2 (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F1 (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Type : Set :=
 | BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__supported
.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__cond := (fun (_ : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__nat__helper.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__supported
  | _ => BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F1F2 : forall x : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Type, (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F2 (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F1 (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type : Set :=
  make__BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type {
    BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz : option BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Type ;
    BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz : option BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Type ;
}.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list := (
 Opt BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__cond ::
 Opt BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__cond ::
 nil).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond z := 
  opt_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__cond (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz z) /\
  opt_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__cond (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz z) /\
  True.


Inductive BandNR__ext5O__channelBW_DL_IAB_r16__Type : Set :=
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type -> BandNR__ext5O__channelBW_DL_IAB_r16__Type
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type -> BandNR__ext5O__channelBW_DL_IAB_r16__Type
.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__list : list typ := (
typ_cons BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond ::
typ_cons BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond ::
 nil).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__cond (c : BandNR__ext5O__channelBW_DL_IAB_r16__Type) := 
  match c with
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz t => BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond t 
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz t => BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond t 
  end.

Lemma BandNR__ext5O__channelBW_DL_IAB_r16__len_helper1 : to_bit_sz (length BandNR__ext5O__channelBW_DL_IAB_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__len_helper2 : 2 <= length2 BandNR__ext5O__channelBW_DL_IAB_r16__list.
 simpl. lia. Qed.
Inductive BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Type : Set :=
 | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__supported
.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__cond := (fun (_ : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__nat__helper.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__supported
  | _ => BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F1F2 : forall x : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Type, (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F2 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F1 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Type : Set :=
 | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__supported
.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__cond := (fun (_ : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__nat__helper.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__supported
  | _ => BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F1F2 : forall x : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Type, (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F2 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F1 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Type : Set :=
 | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__supported
.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__cond := (fun (_ : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__nat__helper.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__supported
  | _ => BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F1F2 : forall x : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Type, (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F2 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F1 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type : Set :=
  make__BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type {
    BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz : option BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Type ;
    BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz : option BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Type ;
    BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz : option BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Type ;
}.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list := (
 Opt BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__cond ::
 Opt BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__cond ::
 Opt BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__cond ::
 nil).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond z := 
  opt_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__cond (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz z) /\
  opt_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__cond (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz z) /\
  opt_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__cond (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz z) /\
  True.

Inductive BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Type : Set :=
 | BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__supported
.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__cond := (fun (_ : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__nat__helper.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__supported
  | _ => BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F1F2 : forall x : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Type, (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F2 (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F1 (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Type : Set :=
 | BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__supported
.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__cond := (fun (_ : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Type) => True).
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__nat__helper.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F1 t :=
  match t with
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__supported => 0
  end.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F2 n :=
  match n with
  | 0 => BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__supported
  | _ => BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__supported
  end.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F1F2 : forall x : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Type, (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F1 x <= 0) /\ BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F2 (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F1 (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type : Set :=
  make__BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type {
    BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz : option BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Type ;
    BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz : option BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Type ;
}.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list := (
 Opt BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__cond ::
 Opt BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__cond ::
 nil).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond z := 
  opt_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__cond (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz z) /\
  opt_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__cond (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz z) /\
  True.


Inductive BandNR__ext5O__channelBW_UL_IAB_r16__Type : Set :=
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type -> BandNR__ext5O__channelBW_UL_IAB_r16__Type
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type -> BandNR__ext5O__channelBW_UL_IAB_r16__Type
.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__list : list typ := (
typ_cons BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond ::
typ_cons BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond ::
 nil).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__cond (c : BandNR__ext5O__channelBW_UL_IAB_r16__Type) := 
  match c with
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz t => BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond t 
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz t => BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond t 
  end.

Lemma BandNR__ext5O__channelBW_UL_IAB_r16__len_helper1 : to_bit_sz (length BandNR__ext5O__channelBW_UL_IAB_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__len_helper2 : 2 <= length2 BandNR__ext5O__channelBW_UL_IAB_r16__list.
 simpl. lia. Qed.
Inductive BandNR__ext5O__rasterShift7dot5_IAB_r16__Type : Set :=
 | BandNR__ext5O__rasterShift7dot5_IAB_r16__supported
.
Definition BandNR__ext5O__rasterShift7dot5_IAB_r16__cond := (fun (_ : BandNR__ext5O__rasterShift7dot5_IAB_r16__Type) => True).
Lemma BandNR__ext5O__rasterShift7dot5_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__rasterShift7dot5_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__rasterShift7dot5_IAB_r16__nat__helper.

Definition BandNR__ext5O__rasterShift7dot5_IAB_r16__F1 t :=
  match t with
  | BandNR__ext5O__rasterShift7dot5_IAB_r16__supported => 0
  end.
Definition BandNR__ext5O__rasterShift7dot5_IAB_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__rasterShift7dot5_IAB_r16__supported
  | _ => BandNR__ext5O__rasterShift7dot5_IAB_r16__supported
  end.
Lemma BandNR__ext5O__rasterShift7dot5_IAB_r16__F1F2 : forall x : BandNR__ext5O__rasterShift7dot5_IAB_r16__Type, (BandNR__ext5O__rasterShift7dot5_IAB_r16__F1 x <= 0) /\ BandNR__ext5O__rasterShift7dot5_IAB_r16__F2 (BandNR__ext5O__rasterShift7dot5_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__rasterShift7dot5_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__rasterShift7dot5_IAB_r16__F1 (BandNR__ext5O__rasterShift7dot5_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__ue_PowerClass_v1610__Type : Set :=
 | BandNR__ext5O__ue_PowerClass_v1610__pc1dot5
.
Definition BandNR__ext5O__ue_PowerClass_v1610__cond := (fun (_ : BandNR__ext5O__ue_PowerClass_v1610__Type) => True).
Lemma BandNR__ext5O__ue_PowerClass_v1610__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__ue_PowerClass_v1610__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__ue_PowerClass_v1610__nat__helper.

Definition BandNR__ext5O__ue_PowerClass_v1610__F1 t :=
  match t with
  | BandNR__ext5O__ue_PowerClass_v1610__pc1dot5 => 0
  end.
Definition BandNR__ext5O__ue_PowerClass_v1610__F2 n :=
  match n with
  | 0 => BandNR__ext5O__ue_PowerClass_v1610__pc1dot5
  | _ => BandNR__ext5O__ue_PowerClass_v1610__pc1dot5
  end.
Lemma BandNR__ext5O__ue_PowerClass_v1610__F1F2 : forall x : BandNR__ext5O__ue_PowerClass_v1610__Type, (BandNR__ext5O__ue_PowerClass_v1610__F1 x <= 0) /\ BandNR__ext5O__ue_PowerClass_v1610__F2 (BandNR__ext5O__ue_PowerClass_v1610__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__ue_PowerClass_v1610__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__ue_PowerClass_v1610__F1 (BandNR__ext5O__ue_PowerClass_v1610__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__condHandover_r16__Type : Set :=
 | BandNR__ext5O__condHandover_r16__supported
.
Definition BandNR__ext5O__condHandover_r16__cond := (fun (_ : BandNR__ext5O__condHandover_r16__Type) => True).
Lemma BandNR__ext5O__condHandover_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__condHandover_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__condHandover_r16__nat__helper.

Definition BandNR__ext5O__condHandover_r16__F1 t :=
  match t with
  | BandNR__ext5O__condHandover_r16__supported => 0
  end.
Definition BandNR__ext5O__condHandover_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__condHandover_r16__supported
  | _ => BandNR__ext5O__condHandover_r16__supported
  end.
Lemma BandNR__ext5O__condHandover_r16__F1F2 : forall x : BandNR__ext5O__condHandover_r16__Type, (BandNR__ext5O__condHandover_r16__F1 x <= 0) /\ BandNR__ext5O__condHandover_r16__F2 (BandNR__ext5O__condHandover_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__condHandover_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__condHandover_r16__F1 (BandNR__ext5O__condHandover_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__condHandoverFailure_r16__Type : Set :=
 | BandNR__ext5O__condHandoverFailure_r16__supported
.
Definition BandNR__ext5O__condHandoverFailure_r16__cond := (fun (_ : BandNR__ext5O__condHandoverFailure_r16__Type) => True).
Lemma BandNR__ext5O__condHandoverFailure_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__condHandoverFailure_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__condHandoverFailure_r16__nat__helper.

Definition BandNR__ext5O__condHandoverFailure_r16__F1 t :=
  match t with
  | BandNR__ext5O__condHandoverFailure_r16__supported => 0
  end.
Definition BandNR__ext5O__condHandoverFailure_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__condHandoverFailure_r16__supported
  | _ => BandNR__ext5O__condHandoverFailure_r16__supported
  end.
Lemma BandNR__ext5O__condHandoverFailure_r16__F1F2 : forall x : BandNR__ext5O__condHandoverFailure_r16__Type, (BandNR__ext5O__condHandoverFailure_r16__F1 x <= 0) /\ BandNR__ext5O__condHandoverFailure_r16__F2 (BandNR__ext5O__condHandoverFailure_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__condHandoverFailure_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__condHandoverFailure_r16__F1 (BandNR__ext5O__condHandoverFailure_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Type : Set :=
 | BandNR__ext5O__condHandoverTwoTriggerEvents_r16__supported
.
Definition BandNR__ext5O__condHandoverTwoTriggerEvents_r16__cond := (fun (_ : BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Type) => True).
Lemma BandNR__ext5O__condHandoverTwoTriggerEvents_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__condHandoverTwoTriggerEvents_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__condHandoverTwoTriggerEvents_r16__nat__helper.

Definition BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F1 t :=
  match t with
  | BandNR__ext5O__condHandoverTwoTriggerEvents_r16__supported => 0
  end.
Definition BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__condHandoverTwoTriggerEvents_r16__supported
  | _ => BandNR__ext5O__condHandoverTwoTriggerEvents_r16__supported
  end.
Lemma BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F1F2 : forall x : BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Type, (BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F1 x <= 0) /\ BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F2 (BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F1 (BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__condPSCellChange_r16__Type : Set :=
 | BandNR__ext5O__condPSCellChange_r16__supported
.
Definition BandNR__ext5O__condPSCellChange_r16__cond := (fun (_ : BandNR__ext5O__condPSCellChange_r16__Type) => True).
Lemma BandNR__ext5O__condPSCellChange_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__condPSCellChange_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__condPSCellChange_r16__nat__helper.

Definition BandNR__ext5O__condPSCellChange_r16__F1 t :=
  match t with
  | BandNR__ext5O__condPSCellChange_r16__supported => 0
  end.
Definition BandNR__ext5O__condPSCellChange_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__condPSCellChange_r16__supported
  | _ => BandNR__ext5O__condPSCellChange_r16__supported
  end.
Lemma BandNR__ext5O__condPSCellChange_r16__F1F2 : forall x : BandNR__ext5O__condPSCellChange_r16__Type, (BandNR__ext5O__condPSCellChange_r16__F1 x <= 0) /\ BandNR__ext5O__condPSCellChange_r16__F2 (BandNR__ext5O__condPSCellChange_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__condPSCellChange_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__condPSCellChange_r16__F1 (BandNR__ext5O__condPSCellChange_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Type : Set :=
 | BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__supported
.
Definition BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__cond := (fun (_ : BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Type) => True).
Lemma BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__nat__helper.

Definition BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F1 t :=
  match t with
  | BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__supported => 0
  end.
Definition BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__supported
  | _ => BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__supported
  end.
Lemma BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F1F2 : forall x : BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Type, (BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F1 x <= 0) /\ BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F2 (BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F1 (BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__mpr_PowerBoost_FR2_r16__Type : Set :=
 | BandNR__ext5O__mpr_PowerBoost_FR2_r16__supported
.
Definition BandNR__ext5O__mpr_PowerBoost_FR2_r16__cond := (fun (_ : BandNR__ext5O__mpr_PowerBoost_FR2_r16__Type) => True).
Lemma BandNR__ext5O__mpr_PowerBoost_FR2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__mpr_PowerBoost_FR2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__mpr_PowerBoost_FR2_r16__nat__helper.

Definition BandNR__ext5O__mpr_PowerBoost_FR2_r16__F1 t :=
  match t with
  | BandNR__ext5O__mpr_PowerBoost_FR2_r16__supported => 0
  end.
Definition BandNR__ext5O__mpr_PowerBoost_FR2_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__mpr_PowerBoost_FR2_r16__supported
  | _ => BandNR__ext5O__mpr_PowerBoost_FR2_r16__supported
  end.
Lemma BandNR__ext5O__mpr_PowerBoost_FR2_r16__F1F2 : forall x : BandNR__ext5O__mpr_PowerBoost_FR2_r16__Type, (BandNR__ext5O__mpr_PowerBoost_FR2_r16__F1 x <= 0) /\ BandNR__ext5O__mpr_PowerBoost_FR2_r16__F2 (BandNR__ext5O__mpr_PowerBoost_FR2_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__mpr_PowerBoost_FR2_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__mpr_PowerBoost_FR2_r16__F1 (BandNR__ext5O__mpr_PowerBoost_FR2_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Type : Set :=
 | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n1
 | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n2
 | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n4
 | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n8
 | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n12
.
Definition BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__cond := (fun (_ : BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Type) => True).
Lemma BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__nat__helper.

Definition BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F1 t :=
  match t with
  | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n1 => 0
  | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n2 => 1
  | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n4 => 2
  | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n8 => 3
  | BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n12 => 4
  end.
Definition BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n1
  | 1 => BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n2
  | 2 => BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n4
  | 3 => BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n8
  | 4 => BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n12
  | _ => BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__n1
  end.
Lemma BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F1F2 : forall x : BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Type, (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F1 x <= 4) /\ BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F2 (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F2F1 : forall (y : nat) (H : y <= 4), BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F1 (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F2 y) = y. enum_solve H y. Qed.

Lemma BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__helper1 : (2 <= 32)%Z.  lia. Qed.
Lemma BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__helper2 : to_bit_sz (Z.to_nat (32 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__Type := Z.
Definition BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__cond := (fun z => (2 <= z <= 32)%Z).
Record BandNR__ext5O__activeConfiguredGrant_r16__Type : Set :=
  make__BandNR__ext5O__activeConfiguredGrant_r16__Type {
    BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16 : BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Type ;
    BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16 : Z ;
}.
Definition BandNR__ext5O__activeConfiguredGrant_r16__list := (
 Nor BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Type BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__cond ::
 Nor Z BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__cond ::
 nil).
Definition BandNR__ext5O__activeConfiguredGrant_r16__cond z := 
  BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__cond (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16 z) /\
  BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__cond (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16 z) /\
  True.

Inductive BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Type : Set :=
 | BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__supported
.
Definition BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__cond := (fun (_ : BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Type) => True).
Lemma BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__nat__helper.

Definition BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F1 t :=
  match t with
  | BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__supported => 0
  end.
Definition BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__supported
  | _ => BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__supported
  end.
Lemma BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F1F2 : forall x : BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Type, (BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F1 x <= 0) /\ BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F2 (BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F1 (BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F2 y) = y. enum_solve H y. Qed.

Lemma BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__Type := Z.
Definition BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__cond := (fun z => (1 <= z <= 8)%Z).
Lemma BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__helper1 : (2 <= 32)%Z.  lia. Qed.
Lemma BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__helper2 : to_bit_sz (Z.to_nat (32 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__Type := Z.
Definition BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__cond := (fun z => (2 <= z <= 32)%Z).
Record BandNR__ext5O__sps_r16__Type : Set :=
  make__BandNR__ext5O__sps_r16__Type {
    BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16 : Z ;
    BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16 : Z ;
}.
Definition BandNR__ext5O__sps_r16__list := (
 Nor Z BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__cond ::
 Nor Z BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__cond ::
 nil).
Definition BandNR__ext5O__sps_r16__cond z := 
  BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__cond (BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16 z) /\
  BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__cond (BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16 z) /\
  True.

Inductive BandNR__ext5O__jointReleaseSPS_r16__Type : Set :=
 | BandNR__ext5O__jointReleaseSPS_r16__supported
.
Definition BandNR__ext5O__jointReleaseSPS_r16__cond := (fun (_ : BandNR__ext5O__jointReleaseSPS_r16__Type) => True).
Lemma BandNR__ext5O__jointReleaseSPS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__jointReleaseSPS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__jointReleaseSPS_r16__nat__helper.

Definition BandNR__ext5O__jointReleaseSPS_r16__F1 t :=
  match t with
  | BandNR__ext5O__jointReleaseSPS_r16__supported => 0
  end.
Definition BandNR__ext5O__jointReleaseSPS_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__jointReleaseSPS_r16__supported
  | _ => BandNR__ext5O__jointReleaseSPS_r16__supported
  end.
Lemma BandNR__ext5O__jointReleaseSPS_r16__F1F2 : forall x : BandNR__ext5O__jointReleaseSPS_r16__Type, (BandNR__ext5O__jointReleaseSPS_r16__F1 x <= 0) /\ BandNR__ext5O__jointReleaseSPS_r16__F2 (BandNR__ext5O__jointReleaseSPS_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__jointReleaseSPS_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__jointReleaseSPS_r16__F1 (BandNR__ext5O__jointReleaseSPS_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__simulSRS_TransWithinBand_r16__Type : Set :=
 | BandNR__ext5O__simulSRS_TransWithinBand_r16__n2
.
Definition BandNR__ext5O__simulSRS_TransWithinBand_r16__cond := (fun (_ : BandNR__ext5O__simulSRS_TransWithinBand_r16__Type) => True).
Lemma BandNR__ext5O__simulSRS_TransWithinBand_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__simulSRS_TransWithinBand_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__simulSRS_TransWithinBand_r16__nat__helper.

Definition BandNR__ext5O__simulSRS_TransWithinBand_r16__F1 t :=
  match t with
  | BandNR__ext5O__simulSRS_TransWithinBand_r16__n2 => 0
  end.
Definition BandNR__ext5O__simulSRS_TransWithinBand_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__simulSRS_TransWithinBand_r16__n2
  | _ => BandNR__ext5O__simulSRS_TransWithinBand_r16__n2
  end.
Lemma BandNR__ext5O__simulSRS_TransWithinBand_r16__F1F2 : forall x : BandNR__ext5O__simulSRS_TransWithinBand_r16__Type, (BandNR__ext5O__simulSRS_TransWithinBand_r16__F1 x <= 0) /\ BandNR__ext5O__simulSRS_TransWithinBand_r16__F2 (BandNR__ext5O__simulSRS_TransWithinBand_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__simulSRS_TransWithinBand_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__simulSRS_TransWithinBand_r16__F1 (BandNR__ext5O__simulSRS_TransWithinBand_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__trs_AdditionalBandwidth_r16__Type : Set :=
 | BandNR__ext5O__trs_AdditionalBandwidth_r16__trs_AddBW_Set1
 | BandNR__ext5O__trs_AdditionalBandwidth_r16__trs_AddBW_Set2
.
Definition BandNR__ext5O__trs_AdditionalBandwidth_r16__cond := (fun (_ : BandNR__ext5O__trs_AdditionalBandwidth_r16__Type) => True).
Lemma BandNR__ext5O__trs_AdditionalBandwidth_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__trs_AdditionalBandwidth_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandNR__ext5O__trs_AdditionalBandwidth_r16__nat__helper.

Definition BandNR__ext5O__trs_AdditionalBandwidth_r16__F1 t :=
  match t with
  | BandNR__ext5O__trs_AdditionalBandwidth_r16__trs_AddBW_Set1 => 0
  | BandNR__ext5O__trs_AdditionalBandwidth_r16__trs_AddBW_Set2 => 1
  end.
Definition BandNR__ext5O__trs_AdditionalBandwidth_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__trs_AdditionalBandwidth_r16__trs_AddBW_Set1
  | 1 => BandNR__ext5O__trs_AdditionalBandwidth_r16__trs_AddBW_Set2
  | _ => BandNR__ext5O__trs_AdditionalBandwidth_r16__trs_AddBW_Set1
  end.
Lemma BandNR__ext5O__trs_AdditionalBandwidth_r16__F1F2 : forall x : BandNR__ext5O__trs_AdditionalBandwidth_r16__Type, (BandNR__ext5O__trs_AdditionalBandwidth_r16__F1 x <= 1) /\ BandNR__ext5O__trs_AdditionalBandwidth_r16__F2 (BandNR__ext5O__trs_AdditionalBandwidth_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__trs_AdditionalBandwidth_r16__F2F1 : forall (y : nat) (H : y <= 1), BandNR__ext5O__trs_AdditionalBandwidth_r16__F1 (BandNR__ext5O__trs_AdditionalBandwidth_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext5O__handoverIntraF_IAB_r16__Type : Set :=
 | BandNR__ext5O__handoverIntraF_IAB_r16__supported
.
Definition BandNR__ext5O__handoverIntraF_IAB_r16__cond := (fun (_ : BandNR__ext5O__handoverIntraF_IAB_r16__Type) => True).
Lemma BandNR__ext5O__handoverIntraF_IAB_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext5O__handoverIntraF_IAB_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext5O__handoverIntraF_IAB_r16__nat__helper.

Definition BandNR__ext5O__handoverIntraF_IAB_r16__F1 t :=
  match t with
  | BandNR__ext5O__handoverIntraF_IAB_r16__supported => 0
  end.
Definition BandNR__ext5O__handoverIntraF_IAB_r16__F2 n :=
  match n with
  | 0 => BandNR__ext5O__handoverIntraF_IAB_r16__supported
  | _ => BandNR__ext5O__handoverIntraF_IAB_r16__supported
  end.
Lemma BandNR__ext5O__handoverIntraF_IAB_r16__F1F2 : forall x : BandNR__ext5O__handoverIntraF_IAB_r16__Type, (BandNR__ext5O__handoverIntraF_IAB_r16__F1 x <= 0) /\ BandNR__ext5O__handoverIntraF_IAB_r16__F2 (BandNR__ext5O__handoverIntraF_IAB_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext5O__handoverIntraF_IAB_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext5O__handoverIntraF_IAB_r16__F1 (BandNR__ext5O__handoverIntraF_IAB_r16__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext5O__Type : Set :=
  make__BandNR__ext5O__Type {
    BandNR__ext5O__sharedSpectrumChAccessParamsPerBand_r16 : option SharedSpectrumChAccessParamsPerBand_r16__Type ;
    BandNR__ext5O__cancelOverlappingPUSCH_r16 : option BandNR__ext5O__cancelOverlappingPUSCH_r16__Type ;
    BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16 : option BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Type ;
    BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16 : option BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Type ;
    BandNR__ext5O__pdsch_MappingTypeB_Alt_r16 : option BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Type ;
    BandNR__ext5O__oneSlotPeriodicTRS_r16 : option BandNR__ext5O__oneSlotPeriodicTRS_r16__Type ;
    BandNR__ext5O__olpc_SRS_Pos_r16 : option OLPC_SRS_Pos_r16__Type ;
    BandNR__ext5O__spatialRelationsSRS_Pos_r16 : option SpatialRelationsSRS_Pos_r16__Type ;
    BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16 : option BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Type ;
    BandNR__ext5O__channelBW_DL_IAB_r16 : option BandNR__ext5O__channelBW_DL_IAB_r16__Type ;
    BandNR__ext5O__channelBW_UL_IAB_r16 : option BandNR__ext5O__channelBW_UL_IAB_r16__Type ;
    BandNR__ext5O__rasterShift7dot5_IAB_r16 : option BandNR__ext5O__rasterShift7dot5_IAB_r16__Type ;
    BandNR__ext5O__ue_PowerClass_v1610 : option BandNR__ext5O__ue_PowerClass_v1610__Type ;
    BandNR__ext5O__condHandover_r16 : option BandNR__ext5O__condHandover_r16__Type ;
    BandNR__ext5O__condHandoverFailure_r16 : option BandNR__ext5O__condHandoverFailure_r16__Type ;
    BandNR__ext5O__condHandoverTwoTriggerEvents_r16 : option BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Type ;
    BandNR__ext5O__condPSCellChange_r16 : option BandNR__ext5O__condPSCellChange_r16__Type ;
    BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16 : option BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Type ;
    BandNR__ext5O__mpr_PowerBoost_FR2_r16 : option BandNR__ext5O__mpr_PowerBoost_FR2_r16__Type ;
    BandNR__ext5O__activeConfiguredGrant_r16 : option BandNR__ext5O__activeConfiguredGrant_r16__Type ;
    BandNR__ext5O__jointReleaseConfiguredGrantType2_r16 : option BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Type ;
    BandNR__ext5O__sps_r16 : option BandNR__ext5O__sps_r16__Type ;
    BandNR__ext5O__jointReleaseSPS_r16 : option BandNR__ext5O__jointReleaseSPS_r16__Type ;
    BandNR__ext5O__simulSRS_TransWithinBand_r16 : option BandNR__ext5O__simulSRS_TransWithinBand_r16__Type ;
    BandNR__ext5O__trs_AdditionalBandwidth_r16 : option BandNR__ext5O__trs_AdditionalBandwidth_r16__Type ;
    BandNR__ext5O__handoverIntraF_IAB_r16 : option BandNR__ext5O__handoverIntraF_IAB_r16__Type ;
}.
Definition BandNR__ext5O__list := (
 Opt SharedSpectrumChAccessParamsPerBand_r16__Type SharedSpectrumChAccessParamsPerBand_r16__cond ::
 Opt BandNR__ext5O__cancelOverlappingPUSCH_r16__Type BandNR__ext5O__cancelOverlappingPUSCH_r16__cond ::
 Opt BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Type BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond ::
 Opt BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Type BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__cond ::
 Opt BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Type BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__cond ::
 Opt BandNR__ext5O__oneSlotPeriodicTRS_r16__Type BandNR__ext5O__oneSlotPeriodicTRS_r16__cond ::
 Opt OLPC_SRS_Pos_r16__Type OLPC_SRS_Pos_r16__cond ::
 Opt SpatialRelationsSRS_Pos_r16__Type SpatialRelationsSRS_Pos_r16__cond ::
 Opt BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Type BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__cond ::
 Opt BandNR__ext5O__channelBW_DL_IAB_r16__Type BandNR__ext5O__channelBW_DL_IAB_r16__cond ::
 Opt BandNR__ext5O__channelBW_UL_IAB_r16__Type BandNR__ext5O__channelBW_UL_IAB_r16__cond ::
 Opt BandNR__ext5O__rasterShift7dot5_IAB_r16__Type BandNR__ext5O__rasterShift7dot5_IAB_r16__cond ::
 Opt BandNR__ext5O__ue_PowerClass_v1610__Type BandNR__ext5O__ue_PowerClass_v1610__cond ::
 Opt BandNR__ext5O__condHandover_r16__Type BandNR__ext5O__condHandover_r16__cond ::
 Opt BandNR__ext5O__condHandoverFailure_r16__Type BandNR__ext5O__condHandoverFailure_r16__cond ::
 Opt BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Type BandNR__ext5O__condHandoverTwoTriggerEvents_r16__cond ::
 Opt BandNR__ext5O__condPSCellChange_r16__Type BandNR__ext5O__condPSCellChange_r16__cond ::
 Opt BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Type BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__cond ::
 Opt BandNR__ext5O__mpr_PowerBoost_FR2_r16__Type BandNR__ext5O__mpr_PowerBoost_FR2_r16__cond ::
 Opt BandNR__ext5O__activeConfiguredGrant_r16__Type BandNR__ext5O__activeConfiguredGrant_r16__cond ::
 Opt BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Type BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__cond ::
 Opt BandNR__ext5O__sps_r16__Type BandNR__ext5O__sps_r16__cond ::
 Opt BandNR__ext5O__jointReleaseSPS_r16__Type BandNR__ext5O__jointReleaseSPS_r16__cond ::
 Opt BandNR__ext5O__simulSRS_TransWithinBand_r16__Type BandNR__ext5O__simulSRS_TransWithinBand_r16__cond ::
 Opt BandNR__ext5O__trs_AdditionalBandwidth_r16__Type BandNR__ext5O__trs_AdditionalBandwidth_r16__cond ::
 Opt BandNR__ext5O__handoverIntraF_IAB_r16__Type BandNR__ext5O__handoverIntraF_IAB_r16__cond ::
 nil).
Definition BandNR__ext5O__cond z := 
  opt_cond SharedSpectrumChAccessParamsPerBand_r16__cond (BandNR__ext5O__sharedSpectrumChAccessParamsPerBand_r16 z) /\
  opt_cond BandNR__ext5O__cancelOverlappingPUSCH_r16__cond (BandNR__ext5O__cancelOverlappingPUSCH_r16 z) /\
  opt_cond BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16 z) /\
  opt_cond BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__cond (BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16 z) /\
  opt_cond BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__cond (BandNR__ext5O__pdsch_MappingTypeB_Alt_r16 z) /\
  opt_cond BandNR__ext5O__oneSlotPeriodicTRS_r16__cond (BandNR__ext5O__oneSlotPeriodicTRS_r16 z) /\
  opt_cond OLPC_SRS_Pos_r16__cond (BandNR__ext5O__olpc_SRS_Pos_r16 z) /\
  opt_cond SpatialRelationsSRS_Pos_r16__cond (BandNR__ext5O__spatialRelationsSRS_Pos_r16 z) /\
  opt_cond BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__cond (BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16 z) /\
  opt_cond BandNR__ext5O__channelBW_DL_IAB_r16__cond (BandNR__ext5O__channelBW_DL_IAB_r16 z) /\
  opt_cond BandNR__ext5O__channelBW_UL_IAB_r16__cond (BandNR__ext5O__channelBW_UL_IAB_r16 z) /\
  opt_cond BandNR__ext5O__rasterShift7dot5_IAB_r16__cond (BandNR__ext5O__rasterShift7dot5_IAB_r16 z) /\
  opt_cond BandNR__ext5O__ue_PowerClass_v1610__cond (BandNR__ext5O__ue_PowerClass_v1610 z) /\
  opt_cond BandNR__ext5O__condHandover_r16__cond (BandNR__ext5O__condHandover_r16 z) /\
  opt_cond BandNR__ext5O__condHandoverFailure_r16__cond (BandNR__ext5O__condHandoverFailure_r16 z) /\
  opt_cond BandNR__ext5O__condHandoverTwoTriggerEvents_r16__cond (BandNR__ext5O__condHandoverTwoTriggerEvents_r16 z) /\
  opt_cond BandNR__ext5O__condPSCellChange_r16__cond (BandNR__ext5O__condPSCellChange_r16 z) /\
  opt_cond BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__cond (BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16 z) /\
  opt_cond BandNR__ext5O__mpr_PowerBoost_FR2_r16__cond (BandNR__ext5O__mpr_PowerBoost_FR2_r16 z) /\
  opt_cond BandNR__ext5O__activeConfiguredGrant_r16__cond (BandNR__ext5O__activeConfiguredGrant_r16 z) /\
  opt_cond BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__cond (BandNR__ext5O__jointReleaseConfiguredGrantType2_r16 z) /\
  opt_cond BandNR__ext5O__sps_r16__cond (BandNR__ext5O__sps_r16 z) /\
  opt_cond BandNR__ext5O__jointReleaseSPS_r16__cond (BandNR__ext5O__jointReleaseSPS_r16 z) /\
  opt_cond BandNR__ext5O__simulSRS_TransWithinBand_r16__cond (BandNR__ext5O__simulSRS_TransWithinBand_r16 z) /\
  opt_cond BandNR__ext5O__trs_AdditionalBandwidth_r16__cond (BandNR__ext5O__trs_AdditionalBandwidth_r16 z) /\
  opt_cond BandNR__ext5O__handoverIntraF_IAB_r16__cond (BandNR__ext5O__handoverIntraF_IAB_r16 z) /\
  True.

Definition BandNR__ext5__Type := BandNR__ext5O__Type.
Definition BandNR__ext5__cond := BandNR__ext5O__cond.

Require Import NR.SimulSRS_ForAntennaSwitching_r16.

Opaque SimulSRS_ForAntennaSwitching_r16__cond SimulSRS_ForAntennaSwitching_r16__Format.

Require Import NR.SharedSpectrumChAccessParamsPerBand_v1630.

Opaque SharedSpectrumChAccessParamsPerBand_v1630__cond SharedSpectrumChAccessParamsPerBand_v1630__Format.

Record BandNR__ext6O__Type : Set :=
  make__BandNR__ext6O__Type {
    BandNR__ext6O__simulTX_SRS_AntSwitchingIntraBandUL_CA_r16 : option SimulSRS_ForAntennaSwitching_r16__Type ;
    BandNR__ext6O__sharedSpectrumChAccessParamsPerBand_v1630 : option SharedSpectrumChAccessParamsPerBand_v1630__Type ;
}.
Definition BandNR__ext6O__list := (
 Opt SimulSRS_ForAntennaSwitching_r16__Type SimulSRS_ForAntennaSwitching_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_v1630__Type SharedSpectrumChAccessParamsPerBand_v1630__cond ::
 nil).
Definition BandNR__ext6O__cond z := 
  opt_cond SimulSRS_ForAntennaSwitching_r16__cond (BandNR__ext6O__simulTX_SRS_AntSwitchingIntraBandUL_CA_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_v1630__cond (BandNR__ext6O__sharedSpectrumChAccessParamsPerBand_v1630 z) /\
  True.

Definition BandNR__ext6__Type := BandNR__ext6O__Type.
Definition BandNR__ext6__cond := BandNR__ext6O__cond.

Inductive BandNR__ext7O__handoverUTRA_FDD_r16__Type : Set :=
 | BandNR__ext7O__handoverUTRA_FDD_r16__supported
.
Definition BandNR__ext7O__handoverUTRA_FDD_r16__cond := (fun (_ : BandNR__ext7O__handoverUTRA_FDD_r16__Type) => True).
Lemma BandNR__ext7O__handoverUTRA_FDD_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext7O__handoverUTRA_FDD_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext7O__handoverUTRA_FDD_r16__nat__helper.

Definition BandNR__ext7O__handoverUTRA_FDD_r16__F1 t :=
  match t with
  | BandNR__ext7O__handoverUTRA_FDD_r16__supported => 0
  end.
Definition BandNR__ext7O__handoverUTRA_FDD_r16__F2 n :=
  match n with
  | 0 => BandNR__ext7O__handoverUTRA_FDD_r16__supported
  | _ => BandNR__ext7O__handoverUTRA_FDD_r16__supported
  end.
Lemma BandNR__ext7O__handoverUTRA_FDD_r16__F1F2 : forall x : BandNR__ext7O__handoverUTRA_FDD_r16__Type, (BandNR__ext7O__handoverUTRA_FDD_r16__F1 x <= 0) /\ BandNR__ext7O__handoverUTRA_FDD_r16__F2 (BandNR__ext7O__handoverUTRA_FDD_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext7O__handoverUTRA_FDD_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext7O__handoverUTRA_FDD_r16__F1 (BandNR__ext7O__handoverUTRA_FDD_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext7O__enhancedUL_TransientPeriod_r16__Type : Set :=
 | BandNR__ext7O__enhancedUL_TransientPeriod_r16__us2
 | BandNR__ext7O__enhancedUL_TransientPeriod_r16__us4
 | BandNR__ext7O__enhancedUL_TransientPeriod_r16__us7
.
Definition BandNR__ext7O__enhancedUL_TransientPeriod_r16__cond := (fun (_ : BandNR__ext7O__enhancedUL_TransientPeriod_r16__Type) => True).
Lemma BandNR__ext7O__enhancedUL_TransientPeriod_r16__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext7O__enhancedUL_TransientPeriod_r16__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BandNR__ext7O__enhancedUL_TransientPeriod_r16__nat__helper.

Definition BandNR__ext7O__enhancedUL_TransientPeriod_r16__F1 t :=
  match t with
  | BandNR__ext7O__enhancedUL_TransientPeriod_r16__us2 => 0
  | BandNR__ext7O__enhancedUL_TransientPeriod_r16__us4 => 1
  | BandNR__ext7O__enhancedUL_TransientPeriod_r16__us7 => 2
  end.
Definition BandNR__ext7O__enhancedUL_TransientPeriod_r16__F2 n :=
  match n with
  | 0 => BandNR__ext7O__enhancedUL_TransientPeriod_r16__us2
  | 1 => BandNR__ext7O__enhancedUL_TransientPeriod_r16__us4
  | 2 => BandNR__ext7O__enhancedUL_TransientPeriod_r16__us7
  | _ => BandNR__ext7O__enhancedUL_TransientPeriod_r16__us2
  end.
Lemma BandNR__ext7O__enhancedUL_TransientPeriod_r16__F1F2 : forall x : BandNR__ext7O__enhancedUL_TransientPeriod_r16__Type, (BandNR__ext7O__enhancedUL_TransientPeriod_r16__F1 x <= 2) /\ BandNR__ext7O__enhancedUL_TransientPeriod_r16__F2 (BandNR__ext7O__enhancedUL_TransientPeriod_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext7O__enhancedUL_TransientPeriod_r16__F2F1 : forall (y : nat) (H : y <= 2), BandNR__ext7O__enhancedUL_TransientPeriod_r16__F1 (BandNR__ext7O__enhancedUL_TransientPeriod_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SharedSpectrumChAccessParamsPerBand_v1640.

Opaque SharedSpectrumChAccessParamsPerBand_v1640__cond SharedSpectrumChAccessParamsPerBand_v1640__Format.

Record BandNR__ext7O__Type : Set :=
  make__BandNR__ext7O__Type {
    BandNR__ext7O__handoverUTRA_FDD_r16 : option BandNR__ext7O__handoverUTRA_FDD_r16__Type ;
    BandNR__ext7O__enhancedUL_TransientPeriod_r16 : option BandNR__ext7O__enhancedUL_TransientPeriod_r16__Type ;
    BandNR__ext7O__sharedSpectrumChAccessParamsPerBand_v1640 : option SharedSpectrumChAccessParamsPerBand_v1640__Type ;
}.
Definition BandNR__ext7O__list := (
 Opt BandNR__ext7O__handoverUTRA_FDD_r16__Type BandNR__ext7O__handoverUTRA_FDD_r16__cond ::
 Opt BandNR__ext7O__enhancedUL_TransientPeriod_r16__Type BandNR__ext7O__enhancedUL_TransientPeriod_r16__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_v1640__Type SharedSpectrumChAccessParamsPerBand_v1640__cond ::
 nil).
Definition BandNR__ext7O__cond z := 
  opt_cond BandNR__ext7O__handoverUTRA_FDD_r16__cond (BandNR__ext7O__handoverUTRA_FDD_r16 z) /\
  opt_cond BandNR__ext7O__enhancedUL_TransientPeriod_r16__cond (BandNR__ext7O__enhancedUL_TransientPeriod_r16 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_v1640__cond (BandNR__ext7O__sharedSpectrumChAccessParamsPerBand_v1640 z) /\
  True.

Definition BandNR__ext7__Type := BandNR__ext7O__Type.
Definition BandNR__ext7__cond := BandNR__ext7O__cond.

Inductive BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Type : Set :=
 | BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__supported
.
Definition BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__cond := (fun (_ : BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Type) => True).
Lemma BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__nat__helper.

Definition BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F1 t :=
  match t with
  | BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__supported => 0
  end.
Definition BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F2 n :=
  match n with
  | 0 => BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__supported
  | _ => BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__supported
  end.
Lemma BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F1F2 : forall x : BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Type, (BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F1 x <= 0) /\ BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F2 (BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F1 (BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Type : Set :=
 | BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__supported
.
Definition BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__cond := (fun (_ : BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Type) => True).
Lemma BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__nat__helper.

Definition BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F1 t :=
  match t with
  | BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__supported => 0
  end.
Definition BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F2 n :=
  match n with
  | 0 => BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__supported
  | _ => BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__supported
  end.
Lemma BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F1F2 : forall x : BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Type, (BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F1 x <= 0) /\ BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F2 (BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F1 (BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Type : Set :=
 | BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__supported
.
Definition BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__cond := (fun (_ : BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Type) => True).
Lemma BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__nat__helper.

Definition BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F1 t :=
  match t with
  | BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__supported => 0
  end.
Definition BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F2 n :=
  match n with
  | 0 => BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__supported
  | _ => BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__supported
  end.
Lemma BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F1F2 : forall x : BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Type, (BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F1 x <= 0) /\ BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F2 (BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F1 (BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext8O__configuredUL_GrantType1_v1650__Type : Set :=
 | BandNR__ext8O__configuredUL_GrantType1_v1650__supported
.
Definition BandNR__ext8O__configuredUL_GrantType1_v1650__cond := (fun (_ : BandNR__ext8O__configuredUL_GrantType1_v1650__Type) => True).
Lemma BandNR__ext8O__configuredUL_GrantType1_v1650__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext8O__configuredUL_GrantType1_v1650__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext8O__configuredUL_GrantType1_v1650__nat__helper.

Definition BandNR__ext8O__configuredUL_GrantType1_v1650__F1 t :=
  match t with
  | BandNR__ext8O__configuredUL_GrantType1_v1650__supported => 0
  end.
Definition BandNR__ext8O__configuredUL_GrantType1_v1650__F2 n :=
  match n with
  | 0 => BandNR__ext8O__configuredUL_GrantType1_v1650__supported
  | _ => BandNR__ext8O__configuredUL_GrantType1_v1650__supported
  end.
Lemma BandNR__ext8O__configuredUL_GrantType1_v1650__F1F2 : forall x : BandNR__ext8O__configuredUL_GrantType1_v1650__Type, (BandNR__ext8O__configuredUL_GrantType1_v1650__F1 x <= 0) /\ BandNR__ext8O__configuredUL_GrantType1_v1650__F2 (BandNR__ext8O__configuredUL_GrantType1_v1650__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext8O__configuredUL_GrantType1_v1650__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext8O__configuredUL_GrantType1_v1650__F1 (BandNR__ext8O__configuredUL_GrantType1_v1650__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext8O__configuredUL_GrantType2_v1650__Type : Set :=
 | BandNR__ext8O__configuredUL_GrantType2_v1650__supported
.
Definition BandNR__ext8O__configuredUL_GrantType2_v1650__cond := (fun (_ : BandNR__ext8O__configuredUL_GrantType2_v1650__Type) => True).
Lemma BandNR__ext8O__configuredUL_GrantType2_v1650__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext8O__configuredUL_GrantType2_v1650__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext8O__configuredUL_GrantType2_v1650__nat__helper.

Definition BandNR__ext8O__configuredUL_GrantType2_v1650__F1 t :=
  match t with
  | BandNR__ext8O__configuredUL_GrantType2_v1650__supported => 0
  end.
Definition BandNR__ext8O__configuredUL_GrantType2_v1650__F2 n :=
  match n with
  | 0 => BandNR__ext8O__configuredUL_GrantType2_v1650__supported
  | _ => BandNR__ext8O__configuredUL_GrantType2_v1650__supported
  end.
Lemma BandNR__ext8O__configuredUL_GrantType2_v1650__F1F2 : forall x : BandNR__ext8O__configuredUL_GrantType2_v1650__Type, (BandNR__ext8O__configuredUL_GrantType2_v1650__F1 x <= 0) /\ BandNR__ext8O__configuredUL_GrantType2_v1650__F2 (BandNR__ext8O__configuredUL_GrantType2_v1650__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext8O__configuredUL_GrantType2_v1650__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext8O__configuredUL_GrantType2_v1650__F1 (BandNR__ext8O__configuredUL_GrantType2_v1650__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SharedSpectrumChAccessParamsPerBand_v1650.

Opaque SharedSpectrumChAccessParamsPerBand_v1650__cond SharedSpectrumChAccessParamsPerBand_v1650__Format.

Record BandNR__ext8O__Type : Set :=
  make__BandNR__ext8O__Type {
    BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650 : option BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Type ;
    BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650 : option BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Type ;
    BandNR__ext8O__pusch_RepetitionMultiSlots_v1650 : option BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Type ;
    BandNR__ext8O__configuredUL_GrantType1_v1650 : option BandNR__ext8O__configuredUL_GrantType1_v1650__Type ;
    BandNR__ext8O__configuredUL_GrantType2_v1650 : option BandNR__ext8O__configuredUL_GrantType2_v1650__Type ;
    BandNR__ext8O__sharedSpectrumChAccessParamsPerBand_v1650 : option SharedSpectrumChAccessParamsPerBand_v1650__Type ;
}.
Definition BandNR__ext8O__list := (
 Opt BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Type BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__cond ::
 Opt BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Type BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__cond ::
 Opt BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Type BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__cond ::
 Opt BandNR__ext8O__configuredUL_GrantType1_v1650__Type BandNR__ext8O__configuredUL_GrantType1_v1650__cond ::
 Opt BandNR__ext8O__configuredUL_GrantType2_v1650__Type BandNR__ext8O__configuredUL_GrantType2_v1650__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_v1650__Type SharedSpectrumChAccessParamsPerBand_v1650__cond ::
 nil).
Definition BandNR__ext8O__cond z := 
  opt_cond BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__cond (BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650 z) /\
  opt_cond BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__cond (BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650 z) /\
  opt_cond BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__cond (BandNR__ext8O__pusch_RepetitionMultiSlots_v1650 z) /\
  opt_cond BandNR__ext8O__configuredUL_GrantType1_v1650__cond (BandNR__ext8O__configuredUL_GrantType1_v1650 z) /\
  opt_cond BandNR__ext8O__configuredUL_GrantType2_v1650__cond (BandNR__ext8O__configuredUL_GrantType2_v1650 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_v1650__cond (BandNR__ext8O__sharedSpectrumChAccessParamsPerBand_v1650 z) /\
  True.

Definition BandNR__ext8__Type := BandNR__ext8O__Type.
Definition BandNR__ext8__cond := BandNR__ext8O__cond.

Inductive BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Type : Set :=
 | BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__supported
.
Definition BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__cond := (fun (_ : BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Type) => True).
Lemma BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__nat__helper.

Definition BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F1 t :=
  match t with
  | BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__supported => 0
  end.
Definition BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F2 n :=
  match n with
  | 0 => BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__supported
  | _ => BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__supported
  end.
Lemma BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F1F2 : forall x : BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Type, (BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F1 x <= 0) /\ BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F2 (BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F1 (BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Type : Set :=
 | BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__supported
.
Definition BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__cond := (fun (_ : BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Type) => True).
Lemma BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__nat__helper.

Definition BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F1 t :=
  match t with
  | BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__supported => 0
  end.
Definition BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F2 n :=
  match n with
  | 0 => BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__supported
  | _ => BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__supported
  end.
Lemma BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F1F2 : forall x : BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Type, (BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F1 x <= 0) /\ BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F2 (BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F1 (BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext9O__Type : Set :=
  make__BandNR__ext9O__Type {
    BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660 : option BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Type ;
    BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660 : option BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Type ;
}.
Definition BandNR__ext9O__list := (
 Opt BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Type BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__cond ::
 Opt BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Type BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__cond ::
 nil).
Definition BandNR__ext9O__cond z := 
  opt_cond BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__cond (BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660 z) /\
  opt_cond BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__cond (BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660 z) /\
  True.

Definition BandNR__ext9__Type := BandNR__ext9O__Type.
Definition BandNR__ext9__cond := BandNR__ext9O__cond.

Inductive BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Type : Set :=
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n10
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n15
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n20
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n25
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n30
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n40
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n50
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n60
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n70
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n80
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n90
 | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n100
.
Definition BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__cond := (fun (_ : BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Type) => True).
Lemma BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__nat__helper : to_bit_sz 11 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__nat__Format : T_Format nat (fun z => (z <= 11)) :=
  nat_enum_format 11 BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__nat__helper.

Definition BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F1 t :=
  match t with
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n10 => 0
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n15 => 1
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n20 => 2
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n25 => 3
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n30 => 4
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n40 => 5
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n50 => 6
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n60 => 7
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n70 => 8
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n80 => 9
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n90 => 10
  | BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n100 => 11
  end.
Definition BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F2 n :=
  match n with
  | 0 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n10
  | 1 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n15
  | 2 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n20
  | 3 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n25
  | 4 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n30
  | 5 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n40
  | 6 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n50
  | 7 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n60
  | 8 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n70
  | 9 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n80
  | 10 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n90
  | 11 => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n100
  | _ => BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__n10
  end.
Lemma BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F1F2 : forall x : BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Type, (BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F1 x <= 11) /\ BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F2 (BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F2F1 : forall (y : nat) (H : y <= 11), BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F1 (BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext10O__txDiversity_r16__Type : Set :=
 | BandNR__ext10O__txDiversity_r16__supported
.
Definition BandNR__ext10O__txDiversity_r16__cond := (fun (_ : BandNR__ext10O__txDiversity_r16__Type) => True).
Lemma BandNR__ext10O__txDiversity_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext10O__txDiversity_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext10O__txDiversity_r16__nat__helper.

Definition BandNR__ext10O__txDiversity_r16__F1 t :=
  match t with
  | BandNR__ext10O__txDiversity_r16__supported => 0
  end.
Definition BandNR__ext10O__txDiversity_r16__F2 n :=
  match n with
  | 0 => BandNR__ext10O__txDiversity_r16__supported
  | _ => BandNR__ext10O__txDiversity_r16__supported
  end.
Lemma BandNR__ext10O__txDiversity_r16__F1F2 : forall x : BandNR__ext10O__txDiversity_r16__Type, (BandNR__ext10O__txDiversity_r16__F1 x <= 0) /\ BandNR__ext10O__txDiversity_r16__F2 (BandNR__ext10O__txDiversity_r16__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext10O__txDiversity_r16__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext10O__txDiversity_r16__F1 (BandNR__ext10O__txDiversity_r16__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext10O__Type : Set :=
  make__BandNR__ext10O__Type {
    BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16 : option BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Type ;
    BandNR__ext10O__txDiversity_r16 : option BandNR__ext10O__txDiversity_r16__Type ;
}.
Definition BandNR__ext10O__list := (
 Opt BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Type BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__cond ::
 Opt BandNR__ext10O__txDiversity_r16__Type BandNR__ext10O__txDiversity_r16__cond ::
 nil).
Definition BandNR__ext10O__cond z := 
  opt_cond BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__cond (BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16 z) /\
  opt_cond BandNR__ext10O__txDiversity_r16__cond (BandNR__ext10O__txDiversity_r16 z) /\
  True.

Definition BandNR__ext10__Type := BandNR__ext10O__Type.
Definition BandNR__ext10__cond := BandNR__ext10O__cond.

Inductive BandNR__ext11O__pdsch_1024QAM_FR1_r17__Type : Set :=
 | BandNR__ext11O__pdsch_1024QAM_FR1_r17__supported
.
Definition BandNR__ext11O__pdsch_1024QAM_FR1_r17__cond := (fun (_ : BandNR__ext11O__pdsch_1024QAM_FR1_r17__Type) => True).
Lemma BandNR__ext11O__pdsch_1024QAM_FR1_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__pdsch_1024QAM_FR1_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__pdsch_1024QAM_FR1_r17__nat__helper.

Definition BandNR__ext11O__pdsch_1024QAM_FR1_r17__F1 t :=
  match t with
  | BandNR__ext11O__pdsch_1024QAM_FR1_r17__supported => 0
  end.
Definition BandNR__ext11O__pdsch_1024QAM_FR1_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__pdsch_1024QAM_FR1_r17__supported
  | _ => BandNR__ext11O__pdsch_1024QAM_FR1_r17__supported
  end.
Lemma BandNR__ext11O__pdsch_1024QAM_FR1_r17__F1F2 : forall x : BandNR__ext11O__pdsch_1024QAM_FR1_r17__Type, (BandNR__ext11O__pdsch_1024QAM_FR1_r17__F1 x <= 0) /\ BandNR__ext11O__pdsch_1024QAM_FR1_r17__F2 (BandNR__ext11O__pdsch_1024QAM_FR1_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__pdsch_1024QAM_FR1_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__pdsch_1024QAM_FR1_r17__F1 (BandNR__ext11O__pdsch_1024QAM_FR1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__ue_PowerClass_v1700__Type : Set :=
 | BandNR__ext11O__ue_PowerClass_v1700__pc5
 | BandNR__ext11O__ue_PowerClass_v1700__pc6
 | BandNR__ext11O__ue_PowerClass_v1700__pc7
.
Definition BandNR__ext11O__ue_PowerClass_v1700__cond := (fun (_ : BandNR__ext11O__ue_PowerClass_v1700__Type) => True).
Lemma BandNR__ext11O__ue_PowerClass_v1700__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__ue_PowerClass_v1700__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BandNR__ext11O__ue_PowerClass_v1700__nat__helper.

Definition BandNR__ext11O__ue_PowerClass_v1700__F1 t :=
  match t with
  | BandNR__ext11O__ue_PowerClass_v1700__pc5 => 0
  | BandNR__ext11O__ue_PowerClass_v1700__pc6 => 1
  | BandNR__ext11O__ue_PowerClass_v1700__pc7 => 2
  end.
Definition BandNR__ext11O__ue_PowerClass_v1700__F2 n :=
  match n with
  | 0 => BandNR__ext11O__ue_PowerClass_v1700__pc5
  | 1 => BandNR__ext11O__ue_PowerClass_v1700__pc6
  | 2 => BandNR__ext11O__ue_PowerClass_v1700__pc7
  | _ => BandNR__ext11O__ue_PowerClass_v1700__pc5
  end.
Lemma BandNR__ext11O__ue_PowerClass_v1700__F1F2 : forall x : BandNR__ext11O__ue_PowerClass_v1700__Type, (BandNR__ext11O__ue_PowerClass_v1700__F1 x <= 2) /\ BandNR__ext11O__ue_PowerClass_v1700__F2 (BandNR__ext11O__ue_PowerClass_v1700__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__ue_PowerClass_v1700__F2F1 : forall (y : nat) (H : y <= 2), BandNR__ext11O__ue_PowerClass_v1700__F1 (BandNR__ext11O__ue_PowerClass_v1700__F2 y) = y. enum_solve H y. Qed.

Require Import NR.FR2_2_AccessParamsPerBand_r17.

Opaque FR2_2_AccessParamsPerBand_r17__cond FR2_2_AccessParamsPerBand_r17__Format.

Inductive BandNR__ext11O__rlm_Relaxation_r17__Type : Set :=
 | BandNR__ext11O__rlm_Relaxation_r17__supported
.
Definition BandNR__ext11O__rlm_Relaxation_r17__cond := (fun (_ : BandNR__ext11O__rlm_Relaxation_r17__Type) => True).
Lemma BandNR__ext11O__rlm_Relaxation_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__rlm_Relaxation_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__rlm_Relaxation_r17__nat__helper.

Definition BandNR__ext11O__rlm_Relaxation_r17__F1 t :=
  match t with
  | BandNR__ext11O__rlm_Relaxation_r17__supported => 0
  end.
Definition BandNR__ext11O__rlm_Relaxation_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__rlm_Relaxation_r17__supported
  | _ => BandNR__ext11O__rlm_Relaxation_r17__supported
  end.
Lemma BandNR__ext11O__rlm_Relaxation_r17__F1F2 : forall x : BandNR__ext11O__rlm_Relaxation_r17__Type, (BandNR__ext11O__rlm_Relaxation_r17__F1 x <= 0) /\ BandNR__ext11O__rlm_Relaxation_r17__F2 (BandNR__ext11O__rlm_Relaxation_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__rlm_Relaxation_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__rlm_Relaxation_r17__F1 (BandNR__ext11O__rlm_Relaxation_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__bfd_Relaxation_r17__Type : Set :=
 | BandNR__ext11O__bfd_Relaxation_r17__supported
.
Definition BandNR__ext11O__bfd_Relaxation_r17__cond := (fun (_ : BandNR__ext11O__bfd_Relaxation_r17__Type) => True).
Lemma BandNR__ext11O__bfd_Relaxation_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__bfd_Relaxation_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__bfd_Relaxation_r17__nat__helper.

Definition BandNR__ext11O__bfd_Relaxation_r17__F1 t :=
  match t with
  | BandNR__ext11O__bfd_Relaxation_r17__supported => 0
  end.
Definition BandNR__ext11O__bfd_Relaxation_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__bfd_Relaxation_r17__supported
  | _ => BandNR__ext11O__bfd_Relaxation_r17__supported
  end.
Lemma BandNR__ext11O__bfd_Relaxation_r17__F1F2 : forall x : BandNR__ext11O__bfd_Relaxation_r17__Type, (BandNR__ext11O__bfd_Relaxation_r17__F1 x <= 0) /\ BandNR__ext11O__bfd_Relaxation_r17__F2 (BandNR__ext11O__bfd_Relaxation_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__bfd_Relaxation_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__bfd_Relaxation_r17__F1 (BandNR__ext11O__bfd_Relaxation_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__cg_SDT_r17__Type : Set :=
 | BandNR__ext11O__cg_SDT_r17__supported
.
Definition BandNR__ext11O__cg_SDT_r17__cond := (fun (_ : BandNR__ext11O__cg_SDT_r17__Type) => True).
Lemma BandNR__ext11O__cg_SDT_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__cg_SDT_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__cg_SDT_r17__nat__helper.

Definition BandNR__ext11O__cg_SDT_r17__F1 t :=
  match t with
  | BandNR__ext11O__cg_SDT_r17__supported => 0
  end.
Definition BandNR__ext11O__cg_SDT_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__cg_SDT_r17__supported
  | _ => BandNR__ext11O__cg_SDT_r17__supported
  end.
Lemma BandNR__ext11O__cg_SDT_r17__F1F2 : forall x : BandNR__ext11O__cg_SDT_r17__Type, (BandNR__ext11O__cg_SDT_r17__F1 x <= 0) /\ BandNR__ext11O__cg_SDT_r17__F2 (BandNR__ext11O__cg_SDT_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__cg_SDT_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__cg_SDT_r17__F1 (BandNR__ext11O__cg_SDT_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__locationBasedCondHandover_r17__Type : Set :=
 | BandNR__ext11O__locationBasedCondHandover_r17__supported
.
Definition BandNR__ext11O__locationBasedCondHandover_r17__cond := (fun (_ : BandNR__ext11O__locationBasedCondHandover_r17__Type) => True).
Lemma BandNR__ext11O__locationBasedCondHandover_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__locationBasedCondHandover_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__locationBasedCondHandover_r17__nat__helper.

Definition BandNR__ext11O__locationBasedCondHandover_r17__F1 t :=
  match t with
  | BandNR__ext11O__locationBasedCondHandover_r17__supported => 0
  end.
Definition BandNR__ext11O__locationBasedCondHandover_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__locationBasedCondHandover_r17__supported
  | _ => BandNR__ext11O__locationBasedCondHandover_r17__supported
  end.
Lemma BandNR__ext11O__locationBasedCondHandover_r17__F1F2 : forall x : BandNR__ext11O__locationBasedCondHandover_r17__Type, (BandNR__ext11O__locationBasedCondHandover_r17__F1 x <= 0) /\ BandNR__ext11O__locationBasedCondHandover_r17__F2 (BandNR__ext11O__locationBasedCondHandover_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__locationBasedCondHandover_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__locationBasedCondHandover_r17__F1 (BandNR__ext11O__locationBasedCondHandover_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__timeBasedCondHandover_r17__Type : Set :=
 | BandNR__ext11O__timeBasedCondHandover_r17__supported
.
Definition BandNR__ext11O__timeBasedCondHandover_r17__cond := (fun (_ : BandNR__ext11O__timeBasedCondHandover_r17__Type) => True).
Lemma BandNR__ext11O__timeBasedCondHandover_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__timeBasedCondHandover_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__timeBasedCondHandover_r17__nat__helper.

Definition BandNR__ext11O__timeBasedCondHandover_r17__F1 t :=
  match t with
  | BandNR__ext11O__timeBasedCondHandover_r17__supported => 0
  end.
Definition BandNR__ext11O__timeBasedCondHandover_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__timeBasedCondHandover_r17__supported
  | _ => BandNR__ext11O__timeBasedCondHandover_r17__supported
  end.
Lemma BandNR__ext11O__timeBasedCondHandover_r17__F1F2 : forall x : BandNR__ext11O__timeBasedCondHandover_r17__Type, (BandNR__ext11O__timeBasedCondHandover_r17__F1 x <= 0) /\ BandNR__ext11O__timeBasedCondHandover_r17__F2 (BandNR__ext11O__timeBasedCondHandover_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__timeBasedCondHandover_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__timeBasedCondHandover_r17__F1 (BandNR__ext11O__timeBasedCondHandover_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__eventA4BasedCondHandover_r17__Type : Set :=
 | BandNR__ext11O__eventA4BasedCondHandover_r17__supported
.
Definition BandNR__ext11O__eventA4BasedCondHandover_r17__cond := (fun (_ : BandNR__ext11O__eventA4BasedCondHandover_r17__Type) => True).
Lemma BandNR__ext11O__eventA4BasedCondHandover_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__eventA4BasedCondHandover_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__eventA4BasedCondHandover_r17__nat__helper.

Definition BandNR__ext11O__eventA4BasedCondHandover_r17__F1 t :=
  match t with
  | BandNR__ext11O__eventA4BasedCondHandover_r17__supported => 0
  end.
Definition BandNR__ext11O__eventA4BasedCondHandover_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__eventA4BasedCondHandover_r17__supported
  | _ => BandNR__ext11O__eventA4BasedCondHandover_r17__supported
  end.
Lemma BandNR__ext11O__eventA4BasedCondHandover_r17__F1F2 : forall x : BandNR__ext11O__eventA4BasedCondHandover_r17__Type, (BandNR__ext11O__eventA4BasedCondHandover_r17__F1 x <= 0) /\ BandNR__ext11O__eventA4BasedCondHandover_r17__F2 (BandNR__ext11O__eventA4BasedCondHandover_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__eventA4BasedCondHandover_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__eventA4BasedCondHandover_r17__F1 (BandNR__ext11O__eventA4BasedCondHandover_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Type : Set :=
 | BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__supported
.
Definition BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__cond := (fun (_ : BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Type) => True).
Lemma BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__nat__helper.

Definition BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F1 t :=
  match t with
  | BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__supported => 0
  end.
Definition BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__supported
  | _ => BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__supported
  end.
Lemma BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F1F2 : forall x : BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Type, (BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F1 x <= 0) /\ BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F2 (BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F1 (BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Type : Set :=
 | BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__supported
.
Definition BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__cond := (fun (_ : BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Type) => True).
Lemma BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__nat__helper.

Definition BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F1 t :=
  match t with
  | BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__supported => 0
  end.
Definition BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__supported
  | _ => BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__supported
  end.
Lemma BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F1F2 : forall x : BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Type, (BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F1 x <= 0) /\ BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F2 (BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F1 (BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Type : Set :=
 | BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__supported
.
Definition BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__cond := (fun (_ : BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Type) => True).
Lemma BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__nat__helper.

Definition BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F1 t :=
  match t with
  | BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__supported => 0
  end.
Definition BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__supported
  | _ => BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__supported
  end.
Lemma BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F1F2 : forall x : BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Type, (BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F1 x <= 0) /\ BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F2 (BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F1 (BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__sssg_Switching_1BitInd_r17__Type : Set :=
 | BandNR__ext11O__sssg_Switching_1BitInd_r17__supported
.
Definition BandNR__ext11O__sssg_Switching_1BitInd_r17__cond := (fun (_ : BandNR__ext11O__sssg_Switching_1BitInd_r17__Type) => True).
Lemma BandNR__ext11O__sssg_Switching_1BitInd_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__sssg_Switching_1BitInd_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__sssg_Switching_1BitInd_r17__nat__helper.

Definition BandNR__ext11O__sssg_Switching_1BitInd_r17__F1 t :=
  match t with
  | BandNR__ext11O__sssg_Switching_1BitInd_r17__supported => 0
  end.
Definition BandNR__ext11O__sssg_Switching_1BitInd_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__sssg_Switching_1BitInd_r17__supported
  | _ => BandNR__ext11O__sssg_Switching_1BitInd_r17__supported
  end.
Lemma BandNR__ext11O__sssg_Switching_1BitInd_r17__F1F2 : forall x : BandNR__ext11O__sssg_Switching_1BitInd_r17__Type, (BandNR__ext11O__sssg_Switching_1BitInd_r17__F1 x <= 0) /\ BandNR__ext11O__sssg_Switching_1BitInd_r17__F2 (BandNR__ext11O__sssg_Switching_1BitInd_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__sssg_Switching_1BitInd_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__sssg_Switching_1BitInd_r17__F1 (BandNR__ext11O__sssg_Switching_1BitInd_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__sssg_Switching_2BitInd_r17__Type : Set :=
 | BandNR__ext11O__sssg_Switching_2BitInd_r17__supported
.
Definition BandNR__ext11O__sssg_Switching_2BitInd_r17__cond := (fun (_ : BandNR__ext11O__sssg_Switching_2BitInd_r17__Type) => True).
Lemma BandNR__ext11O__sssg_Switching_2BitInd_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__sssg_Switching_2BitInd_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__sssg_Switching_2BitInd_r17__nat__helper.

Definition BandNR__ext11O__sssg_Switching_2BitInd_r17__F1 t :=
  match t with
  | BandNR__ext11O__sssg_Switching_2BitInd_r17__supported => 0
  end.
Definition BandNR__ext11O__sssg_Switching_2BitInd_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__sssg_Switching_2BitInd_r17__supported
  | _ => BandNR__ext11O__sssg_Switching_2BitInd_r17__supported
  end.
Lemma BandNR__ext11O__sssg_Switching_2BitInd_r17__F1F2 : forall x : BandNR__ext11O__sssg_Switching_2BitInd_r17__Type, (BandNR__ext11O__sssg_Switching_2BitInd_r17__F1 x <= 0) /\ BandNR__ext11O__sssg_Switching_2BitInd_r17__F2 (BandNR__ext11O__sssg_Switching_2BitInd_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__sssg_Switching_2BitInd_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__sssg_Switching_2BitInd_r17__F1 (BandNR__ext11O__sssg_Switching_2BitInd_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Type : Set :=
 | BandNR__ext11O__pdcch_SkippingWithSSSG_r17__supported
.
Definition BandNR__ext11O__pdcch_SkippingWithSSSG_r17__cond := (fun (_ : BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Type) => True).
Lemma BandNR__ext11O__pdcch_SkippingWithSSSG_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__pdcch_SkippingWithSSSG_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__pdcch_SkippingWithSSSG_r17__nat__helper.

Definition BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F1 t :=
  match t with
  | BandNR__ext11O__pdcch_SkippingWithSSSG_r17__supported => 0
  end.
Definition BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__pdcch_SkippingWithSSSG_r17__supported
  | _ => BandNR__ext11O__pdcch_SkippingWithSSSG_r17__supported
  end.
Lemma BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F1F2 : forall x : BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Type, (BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F1 x <= 0) /\ BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F2 (BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F1 (BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Type : Set :=
 | BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__supported
.
Definition BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__cond := (fun (_ : BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Type) => True).
Lemma BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__nat__helper.

Definition BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F1 t :=
  match t with
  | BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__supported => 0
  end.
Definition BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__supported
  | _ => BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__supported
  end.
Lemma BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F1F2 : forall x : BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Type, (BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F1 x <= 0) /\ BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F2 (BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F1 (BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__uplinkPreCompensation_r17__Type : Set :=
 | BandNR__ext11O__uplinkPreCompensation_r17__supported
.
Definition BandNR__ext11O__uplinkPreCompensation_r17__cond := (fun (_ : BandNR__ext11O__uplinkPreCompensation_r17__Type) => True).
Lemma BandNR__ext11O__uplinkPreCompensation_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__uplinkPreCompensation_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__uplinkPreCompensation_r17__nat__helper.

Definition BandNR__ext11O__uplinkPreCompensation_r17__F1 t :=
  match t with
  | BandNR__ext11O__uplinkPreCompensation_r17__supported => 0
  end.
Definition BandNR__ext11O__uplinkPreCompensation_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__uplinkPreCompensation_r17__supported
  | _ => BandNR__ext11O__uplinkPreCompensation_r17__supported
  end.
Lemma BandNR__ext11O__uplinkPreCompensation_r17__F1F2 : forall x : BandNR__ext11O__uplinkPreCompensation_r17__Type, (BandNR__ext11O__uplinkPreCompensation_r17__F1 x <= 0) /\ BandNR__ext11O__uplinkPreCompensation_r17__F2 (BandNR__ext11O__uplinkPreCompensation_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__uplinkPreCompensation_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__uplinkPreCompensation_r17__F1 (BandNR__ext11O__uplinkPreCompensation_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__uplink_TA_Reporting_r17__Type : Set :=
 | BandNR__ext11O__uplink_TA_Reporting_r17__supported
.
Definition BandNR__ext11O__uplink_TA_Reporting_r17__cond := (fun (_ : BandNR__ext11O__uplink_TA_Reporting_r17__Type) => True).
Lemma BandNR__ext11O__uplink_TA_Reporting_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__uplink_TA_Reporting_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__uplink_TA_Reporting_r17__nat__helper.

Definition BandNR__ext11O__uplink_TA_Reporting_r17__F1 t :=
  match t with
  | BandNR__ext11O__uplink_TA_Reporting_r17__supported => 0
  end.
Definition BandNR__ext11O__uplink_TA_Reporting_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__uplink_TA_Reporting_r17__supported
  | _ => BandNR__ext11O__uplink_TA_Reporting_r17__supported
  end.
Lemma BandNR__ext11O__uplink_TA_Reporting_r17__F1F2 : forall x : BandNR__ext11O__uplink_TA_Reporting_r17__Type, (BandNR__ext11O__uplink_TA_Reporting_r17__F1 x <= 0) /\ BandNR__ext11O__uplink_TA_Reporting_r17__F2 (BandNR__ext11O__uplink_TA_Reporting_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__uplink_TA_Reporting_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__uplink_TA_Reporting_r17__F1 (BandNR__ext11O__uplink_TA_Reporting_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__max_HARQ_ProcessNumber_r17__Type : Set :=
 | BandNR__ext11O__max_HARQ_ProcessNumber_r17__u16d32
 | BandNR__ext11O__max_HARQ_ProcessNumber_r17__u32d16
 | BandNR__ext11O__max_HARQ_ProcessNumber_r17__u32d32
.
Definition BandNR__ext11O__max_HARQ_ProcessNumber_r17__cond := (fun (_ : BandNR__ext11O__max_HARQ_ProcessNumber_r17__Type) => True).
Lemma BandNR__ext11O__max_HARQ_ProcessNumber_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__max_HARQ_ProcessNumber_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BandNR__ext11O__max_HARQ_ProcessNumber_r17__nat__helper.

Definition BandNR__ext11O__max_HARQ_ProcessNumber_r17__F1 t :=
  match t with
  | BandNR__ext11O__max_HARQ_ProcessNumber_r17__u16d32 => 0
  | BandNR__ext11O__max_HARQ_ProcessNumber_r17__u32d16 => 1
  | BandNR__ext11O__max_HARQ_ProcessNumber_r17__u32d32 => 2
  end.
Definition BandNR__ext11O__max_HARQ_ProcessNumber_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__max_HARQ_ProcessNumber_r17__u16d32
  | 1 => BandNR__ext11O__max_HARQ_ProcessNumber_r17__u32d16
  | 2 => BandNR__ext11O__max_HARQ_ProcessNumber_r17__u32d32
  | _ => BandNR__ext11O__max_HARQ_ProcessNumber_r17__u16d32
  end.
Lemma BandNR__ext11O__max_HARQ_ProcessNumber_r17__F1F2 : forall x : BandNR__ext11O__max_HARQ_ProcessNumber_r17__Type, (BandNR__ext11O__max_HARQ_ProcessNumber_r17__F1 x <= 2) /\ BandNR__ext11O__max_HARQ_ProcessNumber_r17__F2 (BandNR__ext11O__max_HARQ_ProcessNumber_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__max_HARQ_ProcessNumber_r17__F2F1 : forall (y : nat) (H : y <= 2), BandNR__ext11O__max_HARQ_ProcessNumber_r17__F1 (BandNR__ext11O__max_HARQ_ProcessNumber_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__type2_HARQ_Codebook_r17__Type : Set :=
 | BandNR__ext11O__type2_HARQ_Codebook_r17__supported
.
Definition BandNR__ext11O__type2_HARQ_Codebook_r17__cond := (fun (_ : BandNR__ext11O__type2_HARQ_Codebook_r17__Type) => True).
Lemma BandNR__ext11O__type2_HARQ_Codebook_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__type2_HARQ_Codebook_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__type2_HARQ_Codebook_r17__nat__helper.

Definition BandNR__ext11O__type2_HARQ_Codebook_r17__F1 t :=
  match t with
  | BandNR__ext11O__type2_HARQ_Codebook_r17__supported => 0
  end.
Definition BandNR__ext11O__type2_HARQ_Codebook_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__type2_HARQ_Codebook_r17__supported
  | _ => BandNR__ext11O__type2_HARQ_Codebook_r17__supported
  end.
Lemma BandNR__ext11O__type2_HARQ_Codebook_r17__F1F2 : forall x : BandNR__ext11O__type2_HARQ_Codebook_r17__Type, (BandNR__ext11O__type2_HARQ_Codebook_r17__F1 x <= 0) /\ BandNR__ext11O__type2_HARQ_Codebook_r17__F2 (BandNR__ext11O__type2_HARQ_Codebook_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__type2_HARQ_Codebook_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__type2_HARQ_Codebook_r17__F1 (BandNR__ext11O__type2_HARQ_Codebook_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__type1_HARQ_Codebook_r17__Type : Set :=
 | BandNR__ext11O__type1_HARQ_Codebook_r17__supported
.
Definition BandNR__ext11O__type1_HARQ_Codebook_r17__cond := (fun (_ : BandNR__ext11O__type1_HARQ_Codebook_r17__Type) => True).
Lemma BandNR__ext11O__type1_HARQ_Codebook_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__type1_HARQ_Codebook_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__type1_HARQ_Codebook_r17__nat__helper.

Definition BandNR__ext11O__type1_HARQ_Codebook_r17__F1 t :=
  match t with
  | BandNR__ext11O__type1_HARQ_Codebook_r17__supported => 0
  end.
Definition BandNR__ext11O__type1_HARQ_Codebook_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__type1_HARQ_Codebook_r17__supported
  | _ => BandNR__ext11O__type1_HARQ_Codebook_r17__supported
  end.
Lemma BandNR__ext11O__type1_HARQ_Codebook_r17__F1F2 : forall x : BandNR__ext11O__type1_HARQ_Codebook_r17__Type, (BandNR__ext11O__type1_HARQ_Codebook_r17__F1 x <= 0) /\ BandNR__ext11O__type1_HARQ_Codebook_r17__F2 (BandNR__ext11O__type1_HARQ_Codebook_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__type1_HARQ_Codebook_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__type1_HARQ_Codebook_r17__F1 (BandNR__ext11O__type1_HARQ_Codebook_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__type3_HARQ_Codebook_r17__Type : Set :=
 | BandNR__ext11O__type3_HARQ_Codebook_r17__supported
.
Definition BandNR__ext11O__type3_HARQ_Codebook_r17__cond := (fun (_ : BandNR__ext11O__type3_HARQ_Codebook_r17__Type) => True).
Lemma BandNR__ext11O__type3_HARQ_Codebook_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__type3_HARQ_Codebook_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__type3_HARQ_Codebook_r17__nat__helper.

Definition BandNR__ext11O__type3_HARQ_Codebook_r17__F1 t :=
  match t with
  | BandNR__ext11O__type3_HARQ_Codebook_r17__supported => 0
  end.
Definition BandNR__ext11O__type3_HARQ_Codebook_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__type3_HARQ_Codebook_r17__supported
  | _ => BandNR__ext11O__type3_HARQ_Codebook_r17__supported
  end.
Lemma BandNR__ext11O__type3_HARQ_Codebook_r17__F1F2 : forall x : BandNR__ext11O__type3_HARQ_Codebook_r17__Type, (BandNR__ext11O__type3_HARQ_Codebook_r17__F1 x <= 0) /\ BandNR__ext11O__type3_HARQ_Codebook_r17__F2 (BandNR__ext11O__type3_HARQ_Codebook_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__type3_HARQ_Codebook_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__type3_HARQ_Codebook_r17__F1 (BandNR__ext11O__type3_HARQ_Codebook_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__ue_specific_K_Offset_r17__Type : Set :=
 | BandNR__ext11O__ue_specific_K_Offset_r17__supported
.
Definition BandNR__ext11O__ue_specific_K_Offset_r17__cond := (fun (_ : BandNR__ext11O__ue_specific_K_Offset_r17__Type) => True).
Lemma BandNR__ext11O__ue_specific_K_Offset_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__ue_specific_K_Offset_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__ue_specific_K_Offset_r17__nat__helper.

Definition BandNR__ext11O__ue_specific_K_Offset_r17__F1 t :=
  match t with
  | BandNR__ext11O__ue_specific_K_Offset_r17__supported => 0
  end.
Definition BandNR__ext11O__ue_specific_K_Offset_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__ue_specific_K_Offset_r17__supported
  | _ => BandNR__ext11O__ue_specific_K_Offset_r17__supported
  end.
Lemma BandNR__ext11O__ue_specific_K_Offset_r17__F1F2 : forall x : BandNR__ext11O__ue_specific_K_Offset_r17__Type, (BandNR__ext11O__ue_specific_K_Offset_r17__F1 x <= 0) /\ BandNR__ext11O__ue_specific_K_Offset_r17__F2 (BandNR__ext11O__ue_specific_K_Offset_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__ue_specific_K_Offset_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__ue_specific_K_Offset_r17__F1 (BandNR__ext11O__ue_specific_K_Offset_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type : Set :=
 | BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__supported
.
Definition BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__cond := (fun (_ : BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type) => True).
Lemma BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__nat__helper.

Definition BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 t :=
  match t with
  | BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__supported => 0
  end.
Definition BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__supported
  | _ => BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__supported
  end.
Lemma BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1F2 : forall x : BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type, (BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 x <= 0) /\ BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2 (BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 (BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type : Set :=
 | BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__supported
.
Definition BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__cond := (fun (_ : BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type) => True).
Lemma BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__nat__helper.

Definition BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 t :=
  match t with
  | BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__supported => 0
  end.
Definition BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__supported
  | _ => BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__supported
  end.
Lemma BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1F2 : forall x : BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type, (BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 x <= 0) /\ BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2 (BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 (BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Type : Set :=
 | BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__supported
.
Definition BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__cond := (fun (_ : BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Type) => True).
Lemma BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__nat__helper.

Definition BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F1 t :=
  match t with
  | BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__supported => 0
  end.
Definition BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__supported
  | _ => BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__supported
  end.
Lemma BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F1F2 : forall x : BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Type, (BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F1 x <= 0) /\ BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F2 (BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F1 (BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Type : Set :=
 | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n1
 | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n2
 | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n3
 | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n4
 | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n6
 | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n8
.
Definition BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__cond := (fun (_ : BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Type) => True).
Lemma BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__nat__helper.

Definition BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F1 t :=
  match t with
  | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n1 => 0
  | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n2 => 1
  | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n3 => 2
  | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n4 => 3
  | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n6 => 4
  | BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n8 => 5
  end.
Definition BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n1
  | 1 => BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n2
  | 2 => BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n3
  | 3 => BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n4
  | 4 => BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n6
  | 5 => BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n8
  | _ => BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__n1
  end.
Lemma BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F1F2 : forall x : BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Type, (BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F1 x <= 5) /\ BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F2 (BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F2F1 : forall (y : nat) (H : y <= 5), BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F1 (BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Type : Set :=
 | BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__supported
.
Definition BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__cond := (fun (_ : BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Type) => True).
Lemma BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__nat__helper.

Definition BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F1 t :=
  match t with
  | BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__supported => 0
  end.
Definition BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__supported
  | _ => BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__supported
  end.
Lemma BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F1F2 : forall x : BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Type, (BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F1 x <= 0) /\ BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F2 (BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F1 (BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__prs_ProcessingWindowType1A_r17__Type : Set :=
 | BandNR__ext11O__prs_ProcessingWindowType1A_r17__option1
 | BandNR__ext11O__prs_ProcessingWindowType1A_r17__option2
 | BandNR__ext11O__prs_ProcessingWindowType1A_r17__option3
.
Definition BandNR__ext11O__prs_ProcessingWindowType1A_r17__cond := (fun (_ : BandNR__ext11O__prs_ProcessingWindowType1A_r17__Type) => True).
Lemma BandNR__ext11O__prs_ProcessingWindowType1A_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__prs_ProcessingWindowType1A_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BandNR__ext11O__prs_ProcessingWindowType1A_r17__nat__helper.

Definition BandNR__ext11O__prs_ProcessingWindowType1A_r17__F1 t :=
  match t with
  | BandNR__ext11O__prs_ProcessingWindowType1A_r17__option1 => 0
  | BandNR__ext11O__prs_ProcessingWindowType1A_r17__option2 => 1
  | BandNR__ext11O__prs_ProcessingWindowType1A_r17__option3 => 2
  end.
Definition BandNR__ext11O__prs_ProcessingWindowType1A_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__prs_ProcessingWindowType1A_r17__option1
  | 1 => BandNR__ext11O__prs_ProcessingWindowType1A_r17__option2
  | 2 => BandNR__ext11O__prs_ProcessingWindowType1A_r17__option3
  | _ => BandNR__ext11O__prs_ProcessingWindowType1A_r17__option1
  end.
Lemma BandNR__ext11O__prs_ProcessingWindowType1A_r17__F1F2 : forall x : BandNR__ext11O__prs_ProcessingWindowType1A_r17__Type, (BandNR__ext11O__prs_ProcessingWindowType1A_r17__F1 x <= 2) /\ BandNR__ext11O__prs_ProcessingWindowType1A_r17__F2 (BandNR__ext11O__prs_ProcessingWindowType1A_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__prs_ProcessingWindowType1A_r17__F2F1 : forall (y : nat) (H : y <= 2), BandNR__ext11O__prs_ProcessingWindowType1A_r17__F1 (BandNR__ext11O__prs_ProcessingWindowType1A_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__prs_ProcessingWindowType1B_r17__Type : Set :=
 | BandNR__ext11O__prs_ProcessingWindowType1B_r17__option1
 | BandNR__ext11O__prs_ProcessingWindowType1B_r17__option2
 | BandNR__ext11O__prs_ProcessingWindowType1B_r17__option3
.
Definition BandNR__ext11O__prs_ProcessingWindowType1B_r17__cond := (fun (_ : BandNR__ext11O__prs_ProcessingWindowType1B_r17__Type) => True).
Lemma BandNR__ext11O__prs_ProcessingWindowType1B_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__prs_ProcessingWindowType1B_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BandNR__ext11O__prs_ProcessingWindowType1B_r17__nat__helper.

Definition BandNR__ext11O__prs_ProcessingWindowType1B_r17__F1 t :=
  match t with
  | BandNR__ext11O__prs_ProcessingWindowType1B_r17__option1 => 0
  | BandNR__ext11O__prs_ProcessingWindowType1B_r17__option2 => 1
  | BandNR__ext11O__prs_ProcessingWindowType1B_r17__option3 => 2
  end.
Definition BandNR__ext11O__prs_ProcessingWindowType1B_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__prs_ProcessingWindowType1B_r17__option1
  | 1 => BandNR__ext11O__prs_ProcessingWindowType1B_r17__option2
  | 2 => BandNR__ext11O__prs_ProcessingWindowType1B_r17__option3
  | _ => BandNR__ext11O__prs_ProcessingWindowType1B_r17__option1
  end.
Lemma BandNR__ext11O__prs_ProcessingWindowType1B_r17__F1F2 : forall x : BandNR__ext11O__prs_ProcessingWindowType1B_r17__Type, (BandNR__ext11O__prs_ProcessingWindowType1B_r17__F1 x <= 2) /\ BandNR__ext11O__prs_ProcessingWindowType1B_r17__F2 (BandNR__ext11O__prs_ProcessingWindowType1B_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__prs_ProcessingWindowType1B_r17__F2F1 : forall (y : nat) (H : y <= 2), BandNR__ext11O__prs_ProcessingWindowType1B_r17__F1 (BandNR__ext11O__prs_ProcessingWindowType1B_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__prs_ProcessingWindowType2_r17__Type : Set :=
 | BandNR__ext11O__prs_ProcessingWindowType2_r17__option1
 | BandNR__ext11O__prs_ProcessingWindowType2_r17__option2
 | BandNR__ext11O__prs_ProcessingWindowType2_r17__option3
.
Definition BandNR__ext11O__prs_ProcessingWindowType2_r17__cond := (fun (_ : BandNR__ext11O__prs_ProcessingWindowType2_r17__Type) => True).
Lemma BandNR__ext11O__prs_ProcessingWindowType2_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__prs_ProcessingWindowType2_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BandNR__ext11O__prs_ProcessingWindowType2_r17__nat__helper.

Definition BandNR__ext11O__prs_ProcessingWindowType2_r17__F1 t :=
  match t with
  | BandNR__ext11O__prs_ProcessingWindowType2_r17__option1 => 0
  | BandNR__ext11O__prs_ProcessingWindowType2_r17__option2 => 1
  | BandNR__ext11O__prs_ProcessingWindowType2_r17__option3 => 2
  end.
Definition BandNR__ext11O__prs_ProcessingWindowType2_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__prs_ProcessingWindowType2_r17__option1
  | 1 => BandNR__ext11O__prs_ProcessingWindowType2_r17__option2
  | 2 => BandNR__ext11O__prs_ProcessingWindowType2_r17__option3
  | _ => BandNR__ext11O__prs_ProcessingWindowType2_r17__option1
  end.
Lemma BandNR__ext11O__prs_ProcessingWindowType2_r17__F1F2 : forall x : BandNR__ext11O__prs_ProcessingWindowType2_r17__Type, (BandNR__ext11O__prs_ProcessingWindowType2_r17__F1 x <= 2) /\ BandNR__ext11O__prs_ProcessingWindowType2_r17__F2 (BandNR__ext11O__prs_ProcessingWindowType2_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__prs_ProcessingWindowType2_r17__F2F1 : forall (y : nat) (H : y <= 2), BandNR__ext11O__prs_ProcessingWindowType2_r17__F1 (BandNR__ext11O__prs_ProcessingWindowType2_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SRS_AllPosResourcesRRC_Inactive_r17.

Opaque SRS_AllPosResourcesRRC_Inactive_r17__cond SRS_AllPosResourcesRRC_Inactive_r17__Format.

Require Import NR.OLPC_SRS_Pos_r16.

Opaque OLPC_SRS_Pos_r16__cond OLPC_SRS_Pos_r16__Format.

Require Import NR.SpatialRelationsSRS_Pos_r16.

Opaque SpatialRelationsSRS_Pos_r16__cond SpatialRelationsSRS_Pos_r16__Format.

Inductive BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Type : Set :=
 | BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__supported
.
Definition BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__cond := (fun (_ : BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Type) => True).
Lemma BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__nat__helper.

Definition BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F1 t :=
  match t with
  | BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__supported => 0
  end.
Definition BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__supported
  | _ => BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__supported
  end.
Lemma BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F1F2 : forall x : BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Type, (BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F1 x <= 0) /\ BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F2 (BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F1 (BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Type : Set :=
 | BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__supported
.
Definition BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__cond := (fun (_ : BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Type) => True).
Lemma BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__nat__helper.

Definition BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F1 t :=
  match t with
  | BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__supported => 0
  end.
Definition BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__supported
  | _ => BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__supported
  end.
Lemma BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F1F2 : forall x : BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Type, (BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F1 x <= 0) /\ BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F2 (BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F1 (BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Type : Set :=
 | BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__supported
.
Definition BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__cond := (fun (_ : BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Type) => True).
Lemma BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__nat__helper.

Definition BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F1 t :=
  match t with
  | BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__supported => 0
  end.
Definition BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__supported
  | _ => BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__supported
  end.
Lemma BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F1F2 : forall x : BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Type, (BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F1 x <= 0) /\ BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F2 (BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F1 (BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Type : Set :=
 | BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__supported
.
Definition BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__cond := (fun (_ : BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Type) => True).
Lemma BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__nat__helper.

Definition BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F1 t :=
  match t with
  | BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__supported => 0
  end.
Definition BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__supported
  | _ => BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__supported
  end.
Lemma BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F1F2 : forall x : BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Type, (BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F1 x <= 0) /\ BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F2 (BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F1 (BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Type : Set :=
 | BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n4
 | BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n8
 | BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n16
 | BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n32
.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__cond := (fun (_ : BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Type) => True).
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__nat__helper.

Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F1 t :=
  match t with
  | BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n4 => 0
  | BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n8 => 1
  | BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n16 => 2
  | BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n32 => 3
  end.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n4
  | 1 => BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n8
  | 2 => BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n16
  | 3 => BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n32
  | _ => BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__n4
  end.
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F1F2 : forall x : BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Type, (BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F1 x <= 3) /\ BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F2 (BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F2F1 : forall (y : nat) (H : y <= 3), BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F1 (BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Type : Set :=
 | BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n2
 | BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n4
 | BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n8
 | BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n16
.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__cond := (fun (_ : BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Type) => True).
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__nat__helper.

Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F1 t :=
  match t with
  | BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n2 => 0
  | BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n4 => 1
  | BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n8 => 2
  | BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n16 => 3
  end.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n2
  | 1 => BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n4
  | 2 => BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n8
  | 3 => BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n16
  | _ => BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__n2
  end.
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F1F2 : forall x : BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Type, (BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F1 x <= 3) /\ BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F2 (BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F2F1 : forall (y : nat) (H : y <= 3), BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F1 (BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext11O__maxDurationDMRS_Bundling_r17__Type : Set :=
  make__BandNR__ext11O__maxDurationDMRS_Bundling_r17__Type {
    BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17 : option BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Type ;
    BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17 : option BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Type ;
}.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__list := (
 Opt BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Type BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__cond ::
 Opt BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Type BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__cond ::
 nil).
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond z := 
  opt_cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__cond (BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17 z) /\
  opt_cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__cond (BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17 z) /\
  True.

Inductive BandNR__ext11O__pusch_RepetitionMsg3_r17__Type : Set :=
 | BandNR__ext11O__pusch_RepetitionMsg3_r17__supported
.
Definition BandNR__ext11O__pusch_RepetitionMsg3_r17__cond := (fun (_ : BandNR__ext11O__pusch_RepetitionMsg3_r17__Type) => True).
Lemma BandNR__ext11O__pusch_RepetitionMsg3_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__pusch_RepetitionMsg3_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__pusch_RepetitionMsg3_r17__nat__helper.

Definition BandNR__ext11O__pusch_RepetitionMsg3_r17__F1 t :=
  match t with
  | BandNR__ext11O__pusch_RepetitionMsg3_r17__supported => 0
  end.
Definition BandNR__ext11O__pusch_RepetitionMsg3_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__pusch_RepetitionMsg3_r17__supported
  | _ => BandNR__ext11O__pusch_RepetitionMsg3_r17__supported
  end.
Lemma BandNR__ext11O__pusch_RepetitionMsg3_r17__F1F2 : forall x : BandNR__ext11O__pusch_RepetitionMsg3_r17__Type, (BandNR__ext11O__pusch_RepetitionMsg3_r17__F1 x <= 0) /\ BandNR__ext11O__pusch_RepetitionMsg3_r17__F2 (BandNR__ext11O__pusch_RepetitionMsg3_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__pusch_RepetitionMsg3_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__pusch_RepetitionMsg3_r17__F1 (BandNR__ext11O__pusch_RepetitionMsg3_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SharedSpectrumChAccessParamsPerBand_v1710.

Opaque SharedSpectrumChAccessParamsPerBand_v1710__cond SharedSpectrumChAccessParamsPerBand_v1710__Format.

Inductive BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Type : Set :=
 | BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__supported
.
Definition BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__cond := (fun (_ : BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Type) => True).
Lemma BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__nat__helper.

Definition BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F1 t :=
  match t with
  | BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__supported => 0
  end.
Definition BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__supported
  | _ => BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__supported
  end.
Lemma BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F1F2 : forall x : BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Type, (BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F1 x <= 0) /\ BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F2 (BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F1 (BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Type : Set :=
 | BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n1
 | BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n2
 | BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n3
 | BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n4
.
Definition BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__cond := (fun (_ : BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Type) => True).
Lemma BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__nat__helper.

Definition BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F1 t :=
  match t with
  | BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n1 => 0
  | BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n2 => 1
  | BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n3 => 2
  | BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n4 => 3
  end.
Definition BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n1
  | 1 => BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n2
  | 2 => BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n3
  | 3 => BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n4
  | _ => BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__n1
  end.
Lemma BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F1F2 : forall x : BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Type, (BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F1 x <= 3) /\ BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F2 (BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F2F1 : forall (y : nat) (H : y <= 3), BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F1 (BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__k1_RangeExtension_r17__Type : Set :=
 | BandNR__ext11O__k1_RangeExtension_r17__supported
.
Definition BandNR__ext11O__k1_RangeExtension_r17__cond := (fun (_ : BandNR__ext11O__k1_RangeExtension_r17__Type) => True).
Lemma BandNR__ext11O__k1_RangeExtension_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__k1_RangeExtension_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__k1_RangeExtension_r17__nat__helper.

Definition BandNR__ext11O__k1_RangeExtension_r17__F1 t :=
  match t with
  | BandNR__ext11O__k1_RangeExtension_r17__supported => 0
  end.
Definition BandNR__ext11O__k1_RangeExtension_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__k1_RangeExtension_r17__supported
  | _ => BandNR__ext11O__k1_RangeExtension_r17__supported
  end.
Lemma BandNR__ext11O__k1_RangeExtension_r17__F1F2 : forall x : BandNR__ext11O__k1_RangeExtension_r17__Type, (BandNR__ext11O__k1_RangeExtension_r17__F1 x <= 0) /\ BandNR__ext11O__k1_RangeExtension_r17__F2 (BandNR__ext11O__k1_RangeExtension_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__k1_RangeExtension_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__k1_RangeExtension_r17__F1 (BandNR__ext11O__k1_RangeExtension_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Type : Set :=
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n8
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n16
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n32
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n48
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n64
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n128
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n255
.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__cond := (fun (_ : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Type) => True).
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__nat__helper.

Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F1 t :=
  match t with
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n8 => 0
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n16 => 1
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n32 => 2
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n48 => 3
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n64 => 4
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n128 => 5
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n255 => 6
  end.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n8
  | 1 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n16
  | 2 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n32
  | 3 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n48
  | 4 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n64
  | 5 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n128
  | 6 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n255
  | _ => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__n8
  end.
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F1F2 : forall x : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Type, (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F1 x <= 6) /\ BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F2 (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F2F1 : forall (y : nat) (H : y <= 6), BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F1 (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Type : Set :=
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n8
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n16
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n32
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n64
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n128
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n256
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n512
 | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n1024
.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__cond := (fun (_ : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Type) => True).
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__nat__helper.

Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F1 t :=
  match t with
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n8 => 0
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n16 => 1
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n32 => 2
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n64 => 3
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n128 => 4
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n256 => 5
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n512 => 6
  | BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n1024 => 7
  end.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n8
  | 1 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n16
  | 2 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n32
  | 3 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n64
  | 4 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n128
  | 5 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n256
  | 6 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n512
  | 7 => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n1024
  | _ => BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__n8
  end.
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F1F2 : forall x : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Type, (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F1 x <= 7) /\ BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F2 (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F2F1 : forall (y : nat) (H : y <= 7), BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F1 (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Type : Set :=
  make__BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Type {
    BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17 : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Type ;
    BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17 : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Type ;
}.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list := (
 Nor BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Type BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__cond ::
 Nor BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Type BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__cond ::
 nil).
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond z := 
  BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__cond (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17 z) /\
  BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__cond (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17 z) /\
  True.

Inductive BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Type : Set :=
 | BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__addBW_Set1
 | BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__addBW_Set2
.
Definition BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__cond := (fun (_ : BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Type) => True).
Lemma BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__nat__helper.

Definition BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F1 t :=
  match t with
  | BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__addBW_Set1 => 0
  | BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__addBW_Set2 => 1
  end.
Definition BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__addBW_Set1
  | 1 => BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__addBW_Set2
  | _ => BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__addBW_Set1
  end.
Lemma BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F1F2 : forall x : BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Type, (BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F1 x <= 1) /\ BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F2 (BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F2F1 : forall (y : nat) (H : y <= 1), BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F1 (BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Type : Set :=
 | BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__supported
.
Definition BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__cond := (fun (_ : BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Type) => True).
Lemma BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__nat__helper.

Definition BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F1 t :=
  match t with
  | BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__supported => 0
  end.
Definition BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__supported
  | _ => BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__supported
  end.
Lemma BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F1F2 : forall x : BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Type, (BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F1 x <= 0) /\ BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F2 (BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F1 (BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Type : Set :=
 | BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__supported
.
Definition BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__cond := (fun (_ : BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Type) => True).
Lemma BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__nat__helper.

Definition BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F1 t :=
  match t with
  | BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__supported => 0
  end.
Definition BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__supported
  | _ => BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__supported
  end.
Lemma BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F1F2 : forall x : BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Type, (BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F1 x <= 0) /\ BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F2 (BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F1 (BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PosSRS_RRC_Inactive_OutsideInitialUL_BWP_r17.

Opaque PosSRS_RRC_Inactive_OutsideInitialUL_BWP_r17__cond PosSRS_RRC_Inactive_OutsideInitialUL_BWP_r17__Format.

Definition BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__Type := bit_string_fixed.
Definition BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__Type := bit_string_fixed.
Definition BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__Type := bit_string_fixed.
Definition BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__Type := bit_string_fixed.
Definition BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Inductive BandNR__ext11O__ul_GapFR2_r17__Type : Set :=
 | BandNR__ext11O__ul_GapFR2_r17__supported
.
Definition BandNR__ext11O__ul_GapFR2_r17__cond := (fun (_ : BandNR__ext11O__ul_GapFR2_r17__Type) => True).
Lemma BandNR__ext11O__ul_GapFR2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__ul_GapFR2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__ul_GapFR2_r17__nat__helper.

Definition BandNR__ext11O__ul_GapFR2_r17__F1 t :=
  match t with
  | BandNR__ext11O__ul_GapFR2_r17__supported => 0
  end.
Definition BandNR__ext11O__ul_GapFR2_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__ul_GapFR2_r17__supported
  | _ => BandNR__ext11O__ul_GapFR2_r17__supported
  end.
Lemma BandNR__ext11O__ul_GapFR2_r17__F1F2 : forall x : BandNR__ext11O__ul_GapFR2_r17__Type, (BandNR__ext11O__ul_GapFR2_r17__F1 x <= 0) /\ BandNR__ext11O__ul_GapFR2_r17__F2 (BandNR__ext11O__ul_GapFR2_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__ul_GapFR2_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__ul_GapFR2_r17__F1 (BandNR__ext11O__ul_GapFR2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Type : Set :=
 | BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__supported
.
Definition BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__cond := (fun (_ : BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Type) => True).
Lemma BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__nat__helper.

Definition BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F1 t :=
  match t with
  | BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__supported => 0
  end.
Definition BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__supported
  | _ => BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__supported
  end.
Lemma BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F1F2 : forall x : BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Type, (BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F1 x <= 0) /\ BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F2 (BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F1 (BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Type : Set :=
 | BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__supported
.
Definition BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__cond := (fun (_ : BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Type) => True).
Lemma BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__nat__helper.

Definition BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F1 t :=
  match t with
  | BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__supported => 0
  end.
Definition BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__supported
  | _ => BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__supported
  end.
Lemma BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F1F2 : forall x : BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Type, (BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F1 x <= 0) /\ BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F2 (BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F1 (BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Type : Set :=
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n1
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n2
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n4
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n8
.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__cond := (fun (_ : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Type) => True).
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__nat__helper.

Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F1 t :=
  match t with
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n1 => 0
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n2 => 1
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n4 => 2
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n8 => 3
  end.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n1
  | 1 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n2
  | 2 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n4
  | 3 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n8
  | _ => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__n1
  end.
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F1F2 : forall x : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Type, (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F1 x <= 3) /\ BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F2 (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F2F1 : forall (y : nat) (H : y <= 3), BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F1 (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Type : Set :=
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n1
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n2
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n3
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n4
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n5
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n6
 | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n7
.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__cond := (fun (_ : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Type) => True).
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__nat__helper.

Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F1 t :=
  match t with
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n1 => 0
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n2 => 1
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n3 => 2
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n4 => 3
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n5 => 4
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n6 => 5
  | BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n7 => 6
  end.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n1
  | 1 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n2
  | 2 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n3
  | 3 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n4
  | 4 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n5
  | 5 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n6
  | 6 => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n7
  | _ => BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__n1
  end.
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F1F2 : forall x : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Type, (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F1 x <= 6) /\ BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F2 (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F2F1 : forall (y : nat) (H : y <= 6), BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F1 (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Type : Set :=
  make__BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Type {
    BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17 : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Type ;
    BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17 : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Type ;
}.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list := (
 Nor BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Type BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__cond ::
 Nor BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Type BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__cond ::
 nil).
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond z := 
  BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__cond (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17 z) /\
  BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__cond (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17 z) /\
  True.

Inductive BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Type : Set :=
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_7
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_5
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_3
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_1
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n1
.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__cond := (fun (_ : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Type) => True).
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__nat__helper.

Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F1 t :=
  match t with
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_7 => 0
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_5 => 1
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_3 => 2
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_1 => 3
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n1 => 4
  end.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_7
  | 1 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_5
  | 2 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_3
  | 3 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_1
  | 4 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n1
  | _ => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__n_7
  end.
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F1F2 : forall x : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Type, (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F1 x <= 4) /\ BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F2 (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F2F1 : forall (y : nat) (H : y <= 4), BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F1 (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Type : Set :=
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n4
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n6
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n8
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n10
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n12
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n14
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n16
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n18
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n20
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n22
 | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n24
.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__cond := (fun (_ : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Type) => True).
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__nat__helper.

Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F1 t :=
  match t with
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n4 => 0
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n6 => 1
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n8 => 2
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n10 => 3
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n12 => 4
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n14 => 5
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n16 => 6
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n18 => 7
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n20 => 8
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n22 => 9
  | BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n24 => 10
  end.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F2 n :=
  match n with
  | 0 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n4
  | 1 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n6
  | 2 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n8
  | 3 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n10
  | 4 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n12
  | 5 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n14
  | 6 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n16
  | 7 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n18
  | 8 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n20
  | 9 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n22
  | 10 => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n24
  | _ => BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__n4
  end.
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F1F2 : forall x : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Type, (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F1 x <= 10) /\ BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F2 (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F2F1 : forall (y : nat) (H : y <= 10), BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F1 (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Type : Set :=
  make__BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Type {
    BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17 : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Type ;
    BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17 : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Type ;
}.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list := (
 Nor BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Type BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__cond ::
 Nor BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Type BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__cond ::
 nil).
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond z := 
  BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__cond (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17 z) /\
  BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__cond (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17 z) /\
  True.

Record BandNR__ext11O__Type : Set :=
  make__BandNR__ext11O__Type {
    BandNR__ext11O__pdsch_1024QAM_FR1_r17 : option BandNR__ext11O__pdsch_1024QAM_FR1_r17__Type ;
    BandNR__ext11O__ue_PowerClass_v1700 : option BandNR__ext11O__ue_PowerClass_v1700__Type ;
    BandNR__ext11O__fr2_2_AccessParamsPerBand_r17 : option FR2_2_AccessParamsPerBand_r17__Type ;
    BandNR__ext11O__rlm_Relaxation_r17 : option BandNR__ext11O__rlm_Relaxation_r17__Type ;
    BandNR__ext11O__bfd_Relaxation_r17 : option BandNR__ext11O__bfd_Relaxation_r17__Type ;
    BandNR__ext11O__cg_SDT_r17 : option BandNR__ext11O__cg_SDT_r17__Type ;
    BandNR__ext11O__locationBasedCondHandover_r17 : option BandNR__ext11O__locationBasedCondHandover_r17__Type ;
    BandNR__ext11O__timeBasedCondHandover_r17 : option BandNR__ext11O__timeBasedCondHandover_r17__Type ;
    BandNR__ext11O__eventA4BasedCondHandover_r17 : option BandNR__ext11O__eventA4BasedCondHandover_r17__Type ;
    BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17 : option BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Type ;
    BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17 : option BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Type ;
    BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17 : option BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Type ;
    BandNR__ext11O__sssg_Switching_1BitInd_r17 : option BandNR__ext11O__sssg_Switching_1BitInd_r17__Type ;
    BandNR__ext11O__sssg_Switching_2BitInd_r17 : option BandNR__ext11O__sssg_Switching_2BitInd_r17__Type ;
    BandNR__ext11O__pdcch_SkippingWithSSSG_r17 : option BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Type ;
    BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17 : option BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Type ;
    BandNR__ext11O__uplinkPreCompensation_r17 : option BandNR__ext11O__uplinkPreCompensation_r17__Type ;
    BandNR__ext11O__uplink_TA_Reporting_r17 : option BandNR__ext11O__uplink_TA_Reporting_r17__Type ;
    BandNR__ext11O__max_HARQ_ProcessNumber_r17 : option BandNR__ext11O__max_HARQ_ProcessNumber_r17__Type ;
    BandNR__ext11O__type2_HARQ_Codebook_r17 : option BandNR__ext11O__type2_HARQ_Codebook_r17__Type ;
    BandNR__ext11O__type1_HARQ_Codebook_r17 : option BandNR__ext11O__type1_HARQ_Codebook_r17__Type ;
    BandNR__ext11O__type3_HARQ_Codebook_r17 : option BandNR__ext11O__type3_HARQ_Codebook_r17__Type ;
    BandNR__ext11O__ue_specific_K_Offset_r17 : option BandNR__ext11O__ue_specific_K_Offset_r17__Type ;
    BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17 : option BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type ;
    BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17 : option BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type ;
    BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17 : option BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Type ;
    BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17 : option BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Type ;
    BandNR__ext11O__prs_ProcessingRRC_Inactive_r17 : option BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Type ;
    BandNR__ext11O__prs_ProcessingWindowType1A_r17 : option BandNR__ext11O__prs_ProcessingWindowType1A_r17__Type ;
    BandNR__ext11O__prs_ProcessingWindowType1B_r17 : option BandNR__ext11O__prs_ProcessingWindowType1B_r17__Type ;
    BandNR__ext11O__prs_ProcessingWindowType2_r17 : option BandNR__ext11O__prs_ProcessingWindowType2_r17__Type ;
    BandNR__ext11O__srs_AllPosResourcesRRC_Inactive_r17 : option SRS_AllPosResourcesRRC_Inactive_r17__Type ;
    BandNR__ext11O__olpc_SRS_PosRRC_Inactive_r17 : option OLPC_SRS_Pos_r16__Type ;
    BandNR__ext11O__spatialRelationsSRS_PosRRC_Inactive_r17 : option SpatialRelationsSRS_Pos_r16__Type ;
    BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17 : option BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Type ;
    BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17 : option BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Type ;
    BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17 : option BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Type ;
    BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17 : option BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Type ;
    BandNR__ext11O__maxDurationDMRS_Bundling_r17 : option BandNR__ext11O__maxDurationDMRS_Bundling_r17__Type ;
    BandNR__ext11O__pusch_RepetitionMsg3_r17 : option BandNR__ext11O__pusch_RepetitionMsg3_r17__Type ;
    BandNR__ext11O__sharedSpectrumChAccessParamsPerBand_v1710 : option SharedSpectrumChAccessParamsPerBand_v1710__Type ;
    BandNR__ext11O__parallelMeasurementWithoutRestriction_r17 : option BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Type ;
    BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17 : option BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Type ;
    BandNR__ext11O__k1_RangeExtension_r17 : option BandNR__ext11O__k1_RangeExtension_r17__Type ;
    BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17 : option BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Type ;
    BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17 : option BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Type ;
    BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17 : option BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Type ;
    BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17 : option BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Type ;
    BandNR__ext11O__posSRS_RRC_Inactive_OutsideInitialUL_BWP_r17 : option PosSRS_RRC_Inactive_OutsideInitialUL_BWP_r17__Type ;
    BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17 : option BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__Type ;
    BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17 : option BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__Type ;
    BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17 : option BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__Type ;
    BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17 : option BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__Type ;
    BandNR__ext11O__ul_GapFR2_r17 : option BandNR__ext11O__ul_GapFR2_r17__Type ;
    BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17 : option BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Type ;
    BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17 : option BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Type ;
    BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17 : option BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Type ;
    BandNR__ext11O__triggeredHARQ_CodebookRetx_r17 : option BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Type ;
}.
Definition BandNR__ext11O__list := (
 Opt BandNR__ext11O__pdsch_1024QAM_FR1_r17__Type BandNR__ext11O__pdsch_1024QAM_FR1_r17__cond ::
 Opt BandNR__ext11O__ue_PowerClass_v1700__Type BandNR__ext11O__ue_PowerClass_v1700__cond ::
 Opt FR2_2_AccessParamsPerBand_r17__Type FR2_2_AccessParamsPerBand_r17__cond ::
 Opt BandNR__ext11O__rlm_Relaxation_r17__Type BandNR__ext11O__rlm_Relaxation_r17__cond ::
 Opt BandNR__ext11O__bfd_Relaxation_r17__Type BandNR__ext11O__bfd_Relaxation_r17__cond ::
 Opt BandNR__ext11O__cg_SDT_r17__Type BandNR__ext11O__cg_SDT_r17__cond ::
 Opt BandNR__ext11O__locationBasedCondHandover_r17__Type BandNR__ext11O__locationBasedCondHandover_r17__cond ::
 Opt BandNR__ext11O__timeBasedCondHandover_r17__Type BandNR__ext11O__timeBasedCondHandover_r17__cond ::
 Opt BandNR__ext11O__eventA4BasedCondHandover_r17__Type BandNR__ext11O__eventA4BasedCondHandover_r17__cond ::
 Opt BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Type BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__cond ::
 Opt BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Type BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__cond ::
 Opt BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Type BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__cond ::
 Opt BandNR__ext11O__sssg_Switching_1BitInd_r17__Type BandNR__ext11O__sssg_Switching_1BitInd_r17__cond ::
 Opt BandNR__ext11O__sssg_Switching_2BitInd_r17__Type BandNR__ext11O__sssg_Switching_2BitInd_r17__cond ::
 Opt BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Type BandNR__ext11O__pdcch_SkippingWithSSSG_r17__cond ::
 Opt BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Type BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__cond ::
 Opt BandNR__ext11O__uplinkPreCompensation_r17__Type BandNR__ext11O__uplinkPreCompensation_r17__cond ::
 Opt BandNR__ext11O__uplink_TA_Reporting_r17__Type BandNR__ext11O__uplink_TA_Reporting_r17__cond ::
 Opt BandNR__ext11O__max_HARQ_ProcessNumber_r17__Type BandNR__ext11O__max_HARQ_ProcessNumber_r17__cond ::
 Opt BandNR__ext11O__type2_HARQ_Codebook_r17__Type BandNR__ext11O__type2_HARQ_Codebook_r17__cond ::
 Opt BandNR__ext11O__type1_HARQ_Codebook_r17__Type BandNR__ext11O__type1_HARQ_Codebook_r17__cond ::
 Opt BandNR__ext11O__type3_HARQ_Codebook_r17__Type BandNR__ext11O__type3_HARQ_Codebook_r17__cond ::
 Opt BandNR__ext11O__ue_specific_K_Offset_r17__Type BandNR__ext11O__ue_specific_K_Offset_r17__cond ::
 Opt BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__cond ::
 Opt BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__cond ::
 Opt BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Type BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__cond ::
 Opt BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Type BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__cond ::
 Opt BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Type BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__cond ::
 Opt BandNR__ext11O__prs_ProcessingWindowType1A_r17__Type BandNR__ext11O__prs_ProcessingWindowType1A_r17__cond ::
 Opt BandNR__ext11O__prs_ProcessingWindowType1B_r17__Type BandNR__ext11O__prs_ProcessingWindowType1B_r17__cond ::
 Opt BandNR__ext11O__prs_ProcessingWindowType2_r17__Type BandNR__ext11O__prs_ProcessingWindowType2_r17__cond ::
 Opt SRS_AllPosResourcesRRC_Inactive_r17__Type SRS_AllPosResourcesRRC_Inactive_r17__cond ::
 Opt OLPC_SRS_Pos_r16__Type OLPC_SRS_Pos_r16__cond ::
 Opt SpatialRelationsSRS_Pos_r16__Type SpatialRelationsSRS_Pos_r16__cond ::
 Opt BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Type BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__cond ::
 Opt BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Type BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__cond ::
 Opt BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Type BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__cond ::
 Opt BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Type BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__cond ::
 Opt BandNR__ext11O__maxDurationDMRS_Bundling_r17__Type BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond ::
 Opt BandNR__ext11O__pusch_RepetitionMsg3_r17__Type BandNR__ext11O__pusch_RepetitionMsg3_r17__cond ::
 Opt SharedSpectrumChAccessParamsPerBand_v1710__Type SharedSpectrumChAccessParamsPerBand_v1710__cond ::
 Opt BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Type BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__cond ::
 Opt BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Type BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__cond ::
 Opt BandNR__ext11O__k1_RangeExtension_r17__Type BandNR__ext11O__k1_RangeExtension_r17__cond ::
 Opt BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Type BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond ::
 Opt BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Type BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__cond ::
 Opt BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Type BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__cond ::
 Opt BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Type BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__cond ::
 Opt PosSRS_RRC_Inactive_OutsideInitialUL_BWP_r17__Type PosSRS_RRC_Inactive_OutsideInitialUL_BWP_r17__cond ::
 Opt BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__Type BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__cond ::
 Opt BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__Type BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__cond ::
 Opt BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__Type BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__cond ::
 Opt BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__Type BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__cond ::
 Opt BandNR__ext11O__ul_GapFR2_r17__Type BandNR__ext11O__ul_GapFR2_r17__cond ::
 Opt BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Type BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__cond ::
 Opt BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Type BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__cond ::
 Opt BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Type BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond ::
 Opt BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Type BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond ::
 nil).
Definition BandNR__ext11O__cond z := 
  opt_cond BandNR__ext11O__pdsch_1024QAM_FR1_r17__cond (BandNR__ext11O__pdsch_1024QAM_FR1_r17 z) /\
  opt_cond BandNR__ext11O__ue_PowerClass_v1700__cond (BandNR__ext11O__ue_PowerClass_v1700 z) /\
  opt_cond FR2_2_AccessParamsPerBand_r17__cond (BandNR__ext11O__fr2_2_AccessParamsPerBand_r17 z) /\
  opt_cond BandNR__ext11O__rlm_Relaxation_r17__cond (BandNR__ext11O__rlm_Relaxation_r17 z) /\
  opt_cond BandNR__ext11O__bfd_Relaxation_r17__cond (BandNR__ext11O__bfd_Relaxation_r17 z) /\
  opt_cond BandNR__ext11O__cg_SDT_r17__cond (BandNR__ext11O__cg_SDT_r17 z) /\
  opt_cond BandNR__ext11O__locationBasedCondHandover_r17__cond (BandNR__ext11O__locationBasedCondHandover_r17 z) /\
  opt_cond BandNR__ext11O__timeBasedCondHandover_r17__cond (BandNR__ext11O__timeBasedCondHandover_r17 z) /\
  opt_cond BandNR__ext11O__eventA4BasedCondHandover_r17__cond (BandNR__ext11O__eventA4BasedCondHandover_r17 z) /\
  opt_cond BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__cond (BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17 z) /\
  opt_cond BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__cond (BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17 z) /\
  opt_cond BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__cond (BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17 z) /\
  opt_cond BandNR__ext11O__sssg_Switching_1BitInd_r17__cond (BandNR__ext11O__sssg_Switching_1BitInd_r17 z) /\
  opt_cond BandNR__ext11O__sssg_Switching_2BitInd_r17__cond (BandNR__ext11O__sssg_Switching_2BitInd_r17 z) /\
  opt_cond BandNR__ext11O__pdcch_SkippingWithSSSG_r17__cond (BandNR__ext11O__pdcch_SkippingWithSSSG_r17 z) /\
  opt_cond BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__cond (BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17 z) /\
  opt_cond BandNR__ext11O__uplinkPreCompensation_r17__cond (BandNR__ext11O__uplinkPreCompensation_r17 z) /\
  opt_cond BandNR__ext11O__uplink_TA_Reporting_r17__cond (BandNR__ext11O__uplink_TA_Reporting_r17 z) /\
  opt_cond BandNR__ext11O__max_HARQ_ProcessNumber_r17__cond (BandNR__ext11O__max_HARQ_ProcessNumber_r17 z) /\
  opt_cond BandNR__ext11O__type2_HARQ_Codebook_r17__cond (BandNR__ext11O__type2_HARQ_Codebook_r17 z) /\
  opt_cond BandNR__ext11O__type1_HARQ_Codebook_r17__cond (BandNR__ext11O__type1_HARQ_Codebook_r17 z) /\
  opt_cond BandNR__ext11O__type3_HARQ_Codebook_r17__cond (BandNR__ext11O__type3_HARQ_Codebook_r17 z) /\
  opt_cond BandNR__ext11O__ue_specific_K_Offset_r17__cond (BandNR__ext11O__ue_specific_K_Offset_r17 z) /\
  opt_cond BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__cond (BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17 z) /\
  opt_cond BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__cond (BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17 z) /\
  opt_cond BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__cond (BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17 z) /\
  opt_cond BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__cond (BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17 z) /\
  opt_cond BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__cond (BandNR__ext11O__prs_ProcessingRRC_Inactive_r17 z) /\
  opt_cond BandNR__ext11O__prs_ProcessingWindowType1A_r17__cond (BandNR__ext11O__prs_ProcessingWindowType1A_r17 z) /\
  opt_cond BandNR__ext11O__prs_ProcessingWindowType1B_r17__cond (BandNR__ext11O__prs_ProcessingWindowType1B_r17 z) /\
  opt_cond BandNR__ext11O__prs_ProcessingWindowType2_r17__cond (BandNR__ext11O__prs_ProcessingWindowType2_r17 z) /\
  opt_cond SRS_AllPosResourcesRRC_Inactive_r17__cond (BandNR__ext11O__srs_AllPosResourcesRRC_Inactive_r17 z) /\
  opt_cond OLPC_SRS_Pos_r16__cond (BandNR__ext11O__olpc_SRS_PosRRC_Inactive_r17 z) /\
  opt_cond SpatialRelationsSRS_Pos_r16__cond (BandNR__ext11O__spatialRelationsSRS_PosRRC_Inactive_r17 z) /\
  opt_cond BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__cond (BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17 z) /\
  opt_cond BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__cond (BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17 z) /\
  opt_cond BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__cond (BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17 z) /\
  opt_cond BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__cond (BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17 z) /\
  opt_cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond (BandNR__ext11O__maxDurationDMRS_Bundling_r17 z) /\
  opt_cond BandNR__ext11O__pusch_RepetitionMsg3_r17__cond (BandNR__ext11O__pusch_RepetitionMsg3_r17 z) /\
  opt_cond SharedSpectrumChAccessParamsPerBand_v1710__cond (BandNR__ext11O__sharedSpectrumChAccessParamsPerBand_v1710 z) /\
  opt_cond BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__cond (BandNR__ext11O__parallelMeasurementWithoutRestriction_r17 z) /\
  opt_cond BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__cond (BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17 z) /\
  opt_cond BandNR__ext11O__k1_RangeExtension_r17__cond (BandNR__ext11O__k1_RangeExtension_r17 z) /\
  opt_cond BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17 z) /\
  opt_cond BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__cond (BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17 z) /\
  opt_cond BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__cond (BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17 z) /\
  opt_cond BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__cond (BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17 z) /\
  opt_cond PosSRS_RRC_Inactive_OutsideInitialUL_BWP_r17__cond (BandNR__ext11O__posSRS_RRC_Inactive_OutsideInitialUL_BWP_r17 z) /\
  opt_cond BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__cond (BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17 z) /\
  opt_cond BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__cond (BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17 z) /\
  opt_cond BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__cond (BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17 z) /\
  opt_cond BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__cond (BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17 z) /\
  opt_cond BandNR__ext11O__ul_GapFR2_r17__cond (BandNR__ext11O__ul_GapFR2_r17 z) /\
  opt_cond BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__cond (BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17 z) /\
  opt_cond BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__cond (BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17 z) /\
  opt_cond BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17 z) /\
  opt_cond BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17 z) /\
  True.

Definition BandNR__ext11__Type := BandNR__ext11O__Type.
Definition BandNR__ext11__cond := BandNR__ext11O__cond.

Inductive BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Type : Set :=
 | BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__supported
.
Definition BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__cond := (fun (_ : BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Type) => True).
Lemma BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__nat__helper.

Definition BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F1 t :=
  match t with
  | BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__supported => 0
  end.
Definition BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__supported
  | _ => BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__supported
  end.
Lemma BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F1F2 : forall x : BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Type, (BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F1 x <= 0) /\ BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F2 (BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F1 (BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__pucch_Repetition_F0_2_r17__Type : Set :=
 | BandNR__ext12O__pucch_Repetition_F0_2_r17__supported
.
Definition BandNR__ext12O__pucch_Repetition_F0_2_r17__cond := (fun (_ : BandNR__ext12O__pucch_Repetition_F0_2_r17__Type) => True).
Lemma BandNR__ext12O__pucch_Repetition_F0_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__pucch_Repetition_F0_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__pucch_Repetition_F0_2_r17__nat__helper.

Definition BandNR__ext12O__pucch_Repetition_F0_2_r17__F1 t :=
  match t with
  | BandNR__ext12O__pucch_Repetition_F0_2_r17__supported => 0
  end.
Definition BandNR__ext12O__pucch_Repetition_F0_2_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__pucch_Repetition_F0_2_r17__supported
  | _ => BandNR__ext12O__pucch_Repetition_F0_2_r17__supported
  end.
Lemma BandNR__ext12O__pucch_Repetition_F0_2_r17__F1F2 : forall x : BandNR__ext12O__pucch_Repetition_F0_2_r17__Type, (BandNR__ext12O__pucch_Repetition_F0_2_r17__F1 x <= 0) /\ BandNR__ext12O__pucch_Repetition_F0_2_r17__F2 (BandNR__ext12O__pucch_Repetition_F0_2_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__pucch_Repetition_F0_2_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__pucch_Repetition_F0_2_r17__F1 (BandNR__ext12O__pucch_Repetition_F0_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Type : Set :=
 | BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__supported
.
Definition BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__cond := (fun (_ : BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Type) => True).
Lemma BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__nat__helper.

Definition BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F1 t :=
  match t with
  | BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__supported => 0
  end.
Definition BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__supported
  | _ => BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__supported
  end.
Lemma BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F1F2 : forall x : BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Type, (BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F1 x <= 0) /\ BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F2 (BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F1 (BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Type : Set :=
 | BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__supported
.
Definition BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__cond := (fun (_ : BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Type) => True).
Lemma BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__nat__helper.

Definition BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F1 t :=
  match t with
  | BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__supported => 0
  end.
Definition BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__supported
  | _ => BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__supported
  end.
Lemma BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F1F2 : forall x : BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Type, (BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F1 x <= 0) /\ BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F2 (BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F1 (BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Type : Set :=
 | BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__supported
.
Definition BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__cond := (fun (_ : BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Type) => True).
Lemma BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__nat__helper.

Definition BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F1 t :=
  match t with
  | BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__supported => 0
  end.
Definition BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__supported
  | _ => BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__supported
  end.
Lemma BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F1F2 : forall x : BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Type, (BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F1 x <= 0) /\ BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F2 (BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F1 (BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Type : Set :=
 | BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__supported
.
Definition BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__cond := (fun (_ : BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Type) => True).
Lemma BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__nat__helper.

Definition BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F1 t :=
  match t with
  | BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__supported => 0
  end.
Definition BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__supported
  | _ => BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__supported
  end.
Lemma BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F1F2 : forall x : BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Type, (BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F1 x <= 0) /\ BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F2 (BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F1 (BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F2 y) = y. enum_solve H y. Qed.

Lemma BandNR__ext12O__maxNumberG_RNTI_r17__helper1 : (2 <= 8)%Z.  lia. Qed.
Lemma BandNR__ext12O__maxNumberG_RNTI_r17__helper2 : to_bit_sz (Z.to_nat (8 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext12O__maxNumberG_RNTI_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext12O__maxNumberG_RNTI_r17__Type := Z.
Definition BandNR__ext12O__maxNumberG_RNTI_r17__cond := (fun z => (2 <= z <= 8)%Z).
Inductive BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Type : Set :=
 | BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__supported
.
Definition BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__cond := (fun (_ : BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Type) => True).
Lemma BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__nat__helper.

Definition BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F1 t :=
  match t with
  | BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__supported => 0
  end.
Definition BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__supported
  | _ => BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__supported
  end.
Lemma BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F1F2 : forall x : BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Type, (BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F1 x <= 0) /\ BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F2 (BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F1 (BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Type : Set :=
 | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__qam256
 | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__qam1024
.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__cond := (fun (_ : BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Type) => True).
Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__nat__helper.

Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F1 t :=
  match t with
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__qam256 => 0
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__qam1024 => 1
  end.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__qam256
  | 1 => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__qam1024
  | _ => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__qam256
  end.
Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F1F2 : forall x : BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Type, (BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F1 x <= 1) /\ BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F2 (BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F2F1 : forall (y : nat) (H : y <= 1), BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F1 (BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Type : Set :=
 | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__qam64
 | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__qam256
.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__cond := (fun (_ : BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Type) => True).
Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__nat__helper.

Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F1 t :=
  match t with
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__qam64 => 0
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__qam256 => 1
  end.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__qam64
  | 1 => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__qam256
  | _ => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__qam64
  end.
Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F1F2 : forall x : BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Type, (BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F1 x <= 1) /\ BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F2 (BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F2F1 : forall (y : nat) (H : y <= 1), BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F1 (BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F2 y) = y. enum_solve H y. Qed.


Inductive BandNR__ext12O__maxModulationOrderForMulticast_r17__Type : Set :=
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17 : BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Type -> BandNR__ext12O__maxModulationOrderForMulticast_r17__Type
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17 : BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Type -> BandNR__ext12O__maxModulationOrderForMulticast_r17__Type
.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__list : list typ := (
typ_cons BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Type BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__cond ::
typ_cons BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Type BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__cond ::
 nil).
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__cond (c : BandNR__ext12O__maxModulationOrderForMulticast_r17__Type) := 
  match c with
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17 t => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__cond t 
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17 t => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__cond t 
  end.

Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__len_helper1 : to_bit_sz (length BandNR__ext12O__maxModulationOrderForMulticast_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__len_helper2 : 2 <= length2 BandNR__ext12O__maxModulationOrderForMulticast_r17__list.
 simpl. lia. Qed.
Inductive BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Type : Set :=
 | BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__n8
 | BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__n16
.
Definition BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__cond := (fun (_ : BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Type) => True).
Lemma BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__nat__helper.

Definition BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F1 t :=
  match t with
  | BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__n8 => 0
  | BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__n16 => 1
  end.
Definition BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__n8
  | 1 => BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__n16
  | _ => BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__n8
  end.
Lemma BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F1F2 : forall x : BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Type, (BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F1 x <= 1) /\ BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F2 (BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F2F1 : forall (y : nat) (H : y <= 1), BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F1 (BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Type : Set :=
 | BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__n8
 | BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__n16
.
Definition BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__cond := (fun (_ : BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Type) => True).
Lemma BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__nat__helper.

Definition BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F1 t :=
  match t with
  | BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__n8 => 0
  | BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__n16 => 1
  end.
Definition BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__n8
  | 1 => BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__n16
  | _ => BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__n8
  end.
Lemma BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F1F2 : forall x : BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Type, (BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F1 x <= 1) /\ BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F2 (BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F2F1 : forall (y : nat) (H : y <= 1), BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F1 (BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Type : Set :=
 | BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__supported
.
Definition BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__cond := (fun (_ : BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Type) => True).
Lemma BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__nat__helper.

Definition BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F1 t :=
  match t with
  | BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__supported => 0
  end.
Definition BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__supported
  | _ => BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__supported
  end.
Lemma BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F1F2 : forall x : BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Type, (BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F1 x <= 0) /\ BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F2 (BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F1 (BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Type : Set :=
 | BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__supported
.
Definition BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__cond := (fun (_ : BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Type) => True).
Lemma BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__nat__helper.

Definition BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F1 t :=
  match t with
  | BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__supported => 0
  end.
Definition BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__supported
  | _ => BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__supported
  end.
Lemma BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F1F2 : forall x : BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Type, (BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F1 x <= 0) /\ BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F2 (BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F1 (BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F2 y) = y. enum_solve H y. Qed.

Lemma BandNR__ext12O__maxNumberG_CS_RNTI_r17__helper1 : (2 <= 8)%Z.  lia. Qed.
Lemma BandNR__ext12O__maxNumberG_CS_RNTI_r17__helper2 : to_bit_sz (Z.to_nat (8 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext12O__maxNumberG_CS_RNTI_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext12O__maxNumberG_CS_RNTI_r17__Type := Z.
Definition BandNR__ext12O__maxNumberG_CS_RNTI_r17__cond := (fun z => (2 <= z <= 8)%Z).
Inductive BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Type : Set :=
 | BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__supported
.
Definition BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__cond := (fun (_ : BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Type) => True).
Lemma BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__nat__helper.

Definition BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F1 t :=
  match t with
  | BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__supported => 0
  end.
Definition BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__supported
  | _ => BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__supported
  end.
Lemma BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F1F2 : forall x : BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Type, (BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F1 x <= 0) /\ BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F2 (BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F1 (BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Type : Set :=
 | BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__supported
.
Definition BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__cond := (fun (_ : BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Type) => True).
Lemma BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__nat__helper.

Definition BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F1 t :=
  match t with
  | BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__supported => 0
  end.
Definition BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__supported
  | _ => BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__supported
  end.
Lemma BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F1F2 : forall x : BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Type, (BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F1 x <= 0) /\ BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F2 (BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F1 (BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__prs_MeasurementWithoutMG_r17__Type : Set :=
 | BandNR__ext12O__prs_MeasurementWithoutMG_r17__cpLength
 | BandNR__ext12O__prs_MeasurementWithoutMG_r17__quarterSymbol
 | BandNR__ext12O__prs_MeasurementWithoutMG_r17__halfSymbol
 | BandNR__ext12O__prs_MeasurementWithoutMG_r17__halfSlot
.
Definition BandNR__ext12O__prs_MeasurementWithoutMG_r17__cond := (fun (_ : BandNR__ext12O__prs_MeasurementWithoutMG_r17__Type) => True).
Lemma BandNR__ext12O__prs_MeasurementWithoutMG_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__prs_MeasurementWithoutMG_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BandNR__ext12O__prs_MeasurementWithoutMG_r17__nat__helper.

Definition BandNR__ext12O__prs_MeasurementWithoutMG_r17__F1 t :=
  match t with
  | BandNR__ext12O__prs_MeasurementWithoutMG_r17__cpLength => 0
  | BandNR__ext12O__prs_MeasurementWithoutMG_r17__quarterSymbol => 1
  | BandNR__ext12O__prs_MeasurementWithoutMG_r17__halfSymbol => 2
  | BandNR__ext12O__prs_MeasurementWithoutMG_r17__halfSlot => 3
  end.
Definition BandNR__ext12O__prs_MeasurementWithoutMG_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__prs_MeasurementWithoutMG_r17__cpLength
  | 1 => BandNR__ext12O__prs_MeasurementWithoutMG_r17__quarterSymbol
  | 2 => BandNR__ext12O__prs_MeasurementWithoutMG_r17__halfSymbol
  | 3 => BandNR__ext12O__prs_MeasurementWithoutMG_r17__halfSlot
  | _ => BandNR__ext12O__prs_MeasurementWithoutMG_r17__cpLength
  end.
Lemma BandNR__ext12O__prs_MeasurementWithoutMG_r17__F1F2 : forall x : BandNR__ext12O__prs_MeasurementWithoutMG_r17__Type, (BandNR__ext12O__prs_MeasurementWithoutMG_r17__F1 x <= 3) /\ BandNR__ext12O__prs_MeasurementWithoutMG_r17__F2 (BandNR__ext12O__prs_MeasurementWithoutMG_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__prs_MeasurementWithoutMG_r17__F2F1 : forall (y : nat) (H : y <= 3), BandNR__ext12O__prs_MeasurementWithoutMG_r17__F1 (BandNR__ext12O__prs_MeasurementWithoutMG_r17__F2 y) = y. enum_solve H y. Qed.

Lemma BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__helper1 : (3 <= 4)%Z.  lia. Qed.
Lemma BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__helper2 : to_bit_sz (Z.to_nat (4 - 3)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 3))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__Type := Z.
Definition BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__cond := (fun z => (3 <= z <= 4)%Z).
Require Import NR.PRS_ProcessingCapabilityOutsideMGinPPWperType_r17.

Opaque PRS_ProcessingCapabilityOutsideMGinPPWperType_r17__cond PRS_ProcessingCapabilityOutsideMGinPPWperType_r17__Format.

Definition BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__Type := list PRS_ProcessingCapabilityOutsideMGinPPWperType_r17__Type.

Lemma BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__helper1 : (0 <= 1 <= 3)%Z.  lia. Qed.
Lemma BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__helper2 : to_bit_sz (Z.to_nat (3 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__cond (z : BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__Type) :=  (1 <= Z.of_nat (length z) <= 3)%Z /\ (list_and PRS_ProcessingCapabilityOutsideMGinPPWperType_r17__cond z) .

Inductive BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Type : Set :=
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n1
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n2
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n4
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n8
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n16
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n32
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n64
.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__cond := (fun (_ : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Type) => True).
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__nat__helper.

Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F1 t :=
  match t with
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n1 => 0
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n2 => 1
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n4 => 2
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n8 => 3
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n16 => 4
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n32 => 5
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n64 => 6
  end.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n1
  | 1 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n2
  | 2 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n4
  | 3 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n8
  | 4 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n16
  | 5 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n32
  | 6 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n64
  | _ => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__n1
  end.
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F1F2 : forall x : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Type, (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F1 x <= 6) /\ BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F2 (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F2F1 : forall (y : nat) (H : y <= 6), BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F1 (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Type : Set :=
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n1
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n2
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n3
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n4
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n5
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n6
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n8
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n10
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n12
 | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n14
.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__cond := (fun (_ : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Type) => True).
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__nat__helper.

Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F1 t :=
  match t with
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n1 => 0
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n2 => 1
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n3 => 2
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n4 => 3
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n5 => 4
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n6 => 5
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n8 => 6
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n10 => 7
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n12 => 8
  | BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n14 => 9
  end.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F2 n :=
  match n with
  | 0 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n1
  | 1 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n2
  | 2 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n3
  | 3 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n4
  | 4 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n5
  | 5 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n6
  | 6 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n8
  | 7 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n10
  | 8 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n12
  | 9 => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n14
  | _ => BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__n1
  end.
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F1F2 : forall x : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Type, (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F1 x <= 9) /\ BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F2 (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F2F1 : forall (y : nat) (H : y <= 9), BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F1 (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Type : Set :=
  make__BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Type {
    BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17 : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Type ;
    BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17 : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Type ;
}.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list := (
 Nor BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Type BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__cond ::
 Nor BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Type BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__cond ::
 nil).
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond z := 
  BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__cond (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17 z) /\
  BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__cond (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17 z) /\
  True.

Definition BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__Type := bit_string_fixed.
Definition BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__Type := bit_string_fixed.
Definition BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 8 /\ bit_string_len_prop (fst z) (snd z)).
Record BandNR__ext12O__Type : Set :=
  make__BandNR__ext12O__Type {
    BandNR__ext12O__ue_OneShotUL_TimingAdj_r17 : option BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Type ;
    BandNR__ext12O__pucch_Repetition_F0_2_r17 : option BandNR__ext12O__pucch_Repetition_F0_2_r17__Type ;
    BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17 : option BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Type ;
    BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17 : option BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Type ;
    BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17 : option BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Type ;
    BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17 : option BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Type ;
    BandNR__ext12O__maxNumberG_RNTI_r17 : option Z ;
    BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17 : option BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Type ;
    BandNR__ext12O__maxModulationOrderForMulticast_r17 : option BandNR__ext12O__maxModulationOrderForMulticast_r17__Type ;
    BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17 : option BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Type ;
    BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17 : option BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Type ;
    BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17 : option BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Type ;
    BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17 : option BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Type ;
    BandNR__ext12O__maxNumberG_CS_RNTI_r17 : option Z ;
    BandNR__ext12O__re_LevelRateMatchingForMulticast_r17 : option BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Type ;
    BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17 : option BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Type ;
    BandNR__ext12O__prs_MeasurementWithoutMG_r17 : option BandNR__ext12O__prs_MeasurementWithoutMG_r17__Type ;
    BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17 : option Z ;
    BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17 : option BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__Type ;
    BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17 : option BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Type ;
    BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17 : option BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__Type ;
    BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17 : option BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__Type ;
}.
Definition BandNR__ext12O__list := (
 Opt BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Type BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__cond ::
 Opt BandNR__ext12O__pucch_Repetition_F0_2_r17__Type BandNR__ext12O__pucch_Repetition_F0_2_r17__cond ::
 Opt BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Type BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__cond ::
 Opt BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Type BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__cond ::
 Opt BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Type BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__cond ::
 Opt BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Type BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__cond ::
 Opt Z BandNR__ext12O__maxNumberG_RNTI_r17__cond ::
 Opt BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Type BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__cond ::
 Opt BandNR__ext12O__maxModulationOrderForMulticast_r17__Type BandNR__ext12O__maxModulationOrderForMulticast_r17__cond ::
 Opt BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Type BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__cond ::
 Opt BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Type BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__cond ::
 Opt BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Type BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__cond ::
 Opt BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Type BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__cond ::
 Opt Z BandNR__ext12O__maxNumberG_CS_RNTI_r17__cond ::
 Opt BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Type BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__cond ::
 Opt BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Type BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__cond ::
 Opt BandNR__ext12O__prs_MeasurementWithoutMG_r17__Type BandNR__ext12O__prs_MeasurementWithoutMG_r17__cond ::
 Opt Z BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__cond ::
 Opt BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__Type BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__cond ::
 Opt BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Type BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond ::
 Opt BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__Type BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__cond ::
 Opt BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__Type BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__cond ::
 nil).
Definition BandNR__ext12O__cond z := 
  opt_cond BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__cond (BandNR__ext12O__ue_OneShotUL_TimingAdj_r17 z) /\
  opt_cond BandNR__ext12O__pucch_Repetition_F0_2_r17__cond (BandNR__ext12O__pucch_Repetition_F0_2_r17 z) /\
  opt_cond BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__cond (BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17 z) /\
  opt_cond BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__cond (BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17 z) /\
  opt_cond BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__cond (BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17 z) /\
  opt_cond BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__cond (BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17 z) /\
  opt_cond BandNR__ext12O__maxNumberG_RNTI_r17__cond (BandNR__ext12O__maxNumberG_RNTI_r17 z) /\
  opt_cond BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__cond (BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17 z) /\
  opt_cond BandNR__ext12O__maxModulationOrderForMulticast_r17__cond (BandNR__ext12O__maxModulationOrderForMulticast_r17 z) /\
  opt_cond BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__cond (BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17 z) /\
  opt_cond BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__cond (BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17 z) /\
  opt_cond BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__cond (BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17 z) /\
  opt_cond BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__cond (BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17 z) /\
  opt_cond BandNR__ext12O__maxNumberG_CS_RNTI_r17__cond (BandNR__ext12O__maxNumberG_CS_RNTI_r17 z) /\
  opt_cond BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__cond (BandNR__ext12O__re_LevelRateMatchingForMulticast_r17 z) /\
  opt_cond BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__cond (BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17 z) /\
  opt_cond BandNR__ext12O__prs_MeasurementWithoutMG_r17__cond (BandNR__ext12O__prs_MeasurementWithoutMG_r17 z) /\
  opt_cond BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__cond (BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17 z) /\
  opt_cond BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__cond (BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17 z) /\
  opt_cond BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17 z) /\
  opt_cond BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__cond (BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17 z) /\
  opt_cond BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__cond (BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17 z) /\
  True.

Definition BandNR__ext12__Type := BandNR__ext12O__Type.
Definition BandNR__ext12__cond := BandNR__ext12O__cond.

Inductive BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Type : Set :=
 | BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__supported
.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__cond := (fun (_ : BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Type) => True).
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__nat__helper.

Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F1 t :=
  match t with
  | BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__supported => 0
  end.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F2 n :=
  match n with
  | 0 => BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__supported
  | _ => BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__supported
  end.
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F1F2 : forall x : BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Type, (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F1 x <= 0) /\ BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F2 (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F1 (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Type : Set :=
 | BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__supported
.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__cond := (fun (_ : BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Type) => True).
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__nat__helper.

Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F1 t :=
  match t with
  | BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__supported => 0
  end.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F2 n :=
  match n with
  | 0 => BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__supported
  | _ => BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__supported
  end.
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F1F2 : forall x : BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Type, (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F1 x <= 0) /\ BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F2 (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F1 (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Type : Set :=
 | BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__supported
.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__cond := (fun (_ : BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Type) => True).
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__nat__helper.

Definition BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F1 t :=
  match t with
  | BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__supported => 0
  end.
Definition BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F2 n :=
  match n with
  | 0 => BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__supported
  | _ => BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__supported
  end.
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F1F2 : forall x : BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Type, (BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F1 x <= 0) /\ BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F2 (BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F1 (BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Type : Set :=
 | BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__supported
.
Definition BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__cond := (fun (_ : BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Type) => True).
Lemma BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__nat__helper.

Definition BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F1 t :=
  match t with
  | BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__supported => 0
  end.
Definition BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F2 n :=
  match n with
  | 0 => BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__supported
  | _ => BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__supported
  end.
Lemma BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F1F2 : forall x : BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Type, (BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F1 x <= 0) /\ BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F2 (BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F1 (BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Type : Set :=
 | BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__supported
.
Definition BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__cond := (fun (_ : BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Type) => True).
Lemma BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__nat__helper.

Definition BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F1 t :=
  match t with
  | BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__supported => 0
  end.
Definition BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F2 n :=
  match n with
  | 0 => BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__supported
  | _ => BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__supported
  end.
Lemma BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F1F2 : forall x : BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Type, (BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F1 x <= 0) /\ BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F2 (BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F1 (BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext13O__interSlotFreqHopPUCCH_r17__Type : Set :=
 | BandNR__ext13O__interSlotFreqHopPUCCH_r17__supported
.
Definition BandNR__ext13O__interSlotFreqHopPUCCH_r17__cond := (fun (_ : BandNR__ext13O__interSlotFreqHopPUCCH_r17__Type) => True).
Lemma BandNR__ext13O__interSlotFreqHopPUCCH_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext13O__interSlotFreqHopPUCCH_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext13O__interSlotFreqHopPUCCH_r17__nat__helper.

Definition BandNR__ext13O__interSlotFreqHopPUCCH_r17__F1 t :=
  match t with
  | BandNR__ext13O__interSlotFreqHopPUCCH_r17__supported => 0
  end.
Definition BandNR__ext13O__interSlotFreqHopPUCCH_r17__F2 n :=
  match n with
  | 0 => BandNR__ext13O__interSlotFreqHopPUCCH_r17__supported
  | _ => BandNR__ext13O__interSlotFreqHopPUCCH_r17__supported
  end.
Lemma BandNR__ext13O__interSlotFreqHopPUCCH_r17__F1F2 : forall x : BandNR__ext13O__interSlotFreqHopPUCCH_r17__Type, (BandNR__ext13O__interSlotFreqHopPUCCH_r17__F1 x <= 0) /\ BandNR__ext13O__interSlotFreqHopPUCCH_r17__F2 (BandNR__ext13O__interSlotFreqHopPUCCH_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext13O__interSlotFreqHopPUCCH_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext13O__interSlotFreqHopPUCCH_r17__F1 (BandNR__ext13O__interSlotFreqHopPUCCH_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext13O__dmrs_BundlingRestart_r17__Type : Set :=
 | BandNR__ext13O__dmrs_BundlingRestart_r17__supported
.
Definition BandNR__ext13O__dmrs_BundlingRestart_r17__cond := (fun (_ : BandNR__ext13O__dmrs_BundlingRestart_r17__Type) => True).
Lemma BandNR__ext13O__dmrs_BundlingRestart_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext13O__dmrs_BundlingRestart_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext13O__dmrs_BundlingRestart_r17__nat__helper.

Definition BandNR__ext13O__dmrs_BundlingRestart_r17__F1 t :=
  match t with
  | BandNR__ext13O__dmrs_BundlingRestart_r17__supported => 0
  end.
Definition BandNR__ext13O__dmrs_BundlingRestart_r17__F2 n :=
  match n with
  | 0 => BandNR__ext13O__dmrs_BundlingRestart_r17__supported
  | _ => BandNR__ext13O__dmrs_BundlingRestart_r17__supported
  end.
Lemma BandNR__ext13O__dmrs_BundlingRestart_r17__F1F2 : forall x : BandNR__ext13O__dmrs_BundlingRestart_r17__Type, (BandNR__ext13O__dmrs_BundlingRestart_r17__F1 x <= 0) /\ BandNR__ext13O__dmrs_BundlingRestart_r17__F2 (BandNR__ext13O__dmrs_BundlingRestart_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext13O__dmrs_BundlingRestart_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext13O__dmrs_BundlingRestart_r17__F1 (BandNR__ext13O__dmrs_BundlingRestart_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Type : Set :=
 | BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__supported
.
Definition BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__cond := (fun (_ : BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Type) => True).
Lemma BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__nat__helper.

Definition BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F1 t :=
  match t with
  | BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__supported => 0
  end.
Definition BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F2 n :=
  match n with
  | 0 => BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__supported
  | _ => BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__supported
  end.
Lemma BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F1F2 : forall x : BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Type, (BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F1 x <= 0) /\ BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F2 (BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F1 x) = x. imp_solve. Qed.
Lemma BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F2F1 : forall (y : nat) (H : y <= 0), BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F1 (BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F2 y) = y. enum_solve H y. Qed.

Record BandNR__ext13O__Type : Set :=
  make__BandNR__ext13O__Type {
    BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17 : option BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Type ;
    BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17 : option BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Type ;
    BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17 : option BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Type ;
    BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17 : option BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Type ;
    BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17 : option BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Type ;
    BandNR__ext13O__interSlotFreqHopPUCCH_r17 : option BandNR__ext13O__interSlotFreqHopPUCCH_r17__Type ;
    BandNR__ext13O__dmrs_BundlingRestart_r17 : option BandNR__ext13O__dmrs_BundlingRestart_r17__Type ;
    BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17 : option BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Type ;
}.
Definition BandNR__ext13O__list := (
 Opt BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Type BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__cond ::
 Opt BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Type BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__cond ::
 Opt BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Type BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__cond ::
 Opt BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Type BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__cond ::
 Opt BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Type BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__cond ::
 Opt BandNR__ext13O__interSlotFreqHopPUCCH_r17__Type BandNR__ext13O__interSlotFreqHopPUCCH_r17__cond ::
 Opt BandNR__ext13O__dmrs_BundlingRestart_r17__Type BandNR__ext13O__dmrs_BundlingRestart_r17__cond ::
 Opt BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Type BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__cond ::
 nil).
Definition BandNR__ext13O__cond z := 
  opt_cond BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__cond (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17 z) /\
  opt_cond BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__cond (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17 z) /\
  opt_cond BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__cond (BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17 z) /\
  opt_cond BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__cond (BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17 z) /\
  opt_cond BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__cond (BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17 z) /\
  opt_cond BandNR__ext13O__interSlotFreqHopPUCCH_r17__cond (BandNR__ext13O__interSlotFreqHopPUCCH_r17 z) /\
  opt_cond BandNR__ext13O__dmrs_BundlingRestart_r17__cond (BandNR__ext13O__dmrs_BundlingRestart_r17 z) /\
  opt_cond BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__cond (BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17 z) /\
  True.

Definition BandNR__ext13__Type := BandNR__ext13O__Type.
Definition BandNR__ext13__cond := BandNR__ext13O__cond.

Record BandNR__Type : Set :=
  make__BandNR__Type {
    BandNR__bandNR : FreqBandIndicatorNR__Type ;
    BandNR__modifiedMPR_Behaviour : option BandNR__modifiedMPR_Behaviour__Type ;
    BandNR__mimo_ParametersPerBand : option MIMO_ParametersPerBand__Type ;
    BandNR__extendedCP : option BandNR__extendedCP__Type ;
    BandNR__multipleTCI : option BandNR__multipleTCI__Type ;
    BandNR__bwp_WithoutRestriction : option BandNR__bwp_WithoutRestriction__Type ;
    BandNR__bwp_SameNumerology : option BandNR__bwp_SameNumerology__Type ;
    BandNR__bwp_DiffNumerology : option BandNR__bwp_DiffNumerology__Type ;
    BandNR__crossCarrierScheduling_SameSCS : option BandNR__crossCarrierScheduling_SameSCS__Type ;
    BandNR__pdsch_256QAM_FR2 : option BandNR__pdsch_256QAM_FR2__Type ;
    BandNR__pusch_256QAM : option BandNR__pusch_256QAM__Type ;
    BandNR__ue_PowerClass : option BandNR__ue_PowerClass__Type ;
    BandNR__rateMatchingLTE_CRS : option BandNR__rateMatchingLTE_CRS__Type ;
    BandNR__channelBWs_DL : option BandNR__channelBWs_DL__Type ;
    BandNR__channelBWs_UL : option BandNR__channelBWs_UL__Type ;
    BandNR__ext0 : option BandNR__ext0__Type ;
    BandNR__ext1 : option BandNR__ext1__Type ;
    BandNR__ext2 : option BandNR__ext2__Type ;
    BandNR__ext3 : option BandNR__ext3__Type ;
    BandNR__ext4 : option BandNR__ext4__Type ;
    BandNR__ext5 : option BandNR__ext5__Type ;
    BandNR__ext6 : option BandNR__ext6__Type ;
    BandNR__ext7 : option BandNR__ext7__Type ;
    BandNR__ext8 : option BandNR__ext8__Type ;
    BandNR__ext9 : option BandNR__ext9__Type ;
    BandNR__ext10 : option BandNR__ext10__Type ;
    BandNR__ext11 : option BandNR__ext11__Type ;
    BandNR__ext12 : option BandNR__ext12__Type ;
    BandNR__ext13 : option BandNR__ext13__Type ;
}.
Definition BandNR__root_list : list seq_elem := (
 Nor FreqBandIndicatorNR__Type FreqBandIndicatorNR__cond ::
 Opt BandNR__modifiedMPR_Behaviour__Type BandNR__modifiedMPR_Behaviour__cond ::
 Opt MIMO_ParametersPerBand__Type MIMO_ParametersPerBand__cond ::
 Opt BandNR__extendedCP__Type BandNR__extendedCP__cond ::
 Opt BandNR__multipleTCI__Type BandNR__multipleTCI__cond ::
 Opt BandNR__bwp_WithoutRestriction__Type BandNR__bwp_WithoutRestriction__cond ::
 Opt BandNR__bwp_SameNumerology__Type BandNR__bwp_SameNumerology__cond ::
 Opt BandNR__bwp_DiffNumerology__Type BandNR__bwp_DiffNumerology__cond ::
 Opt BandNR__crossCarrierScheduling_SameSCS__Type BandNR__crossCarrierScheduling_SameSCS__cond ::
 Opt BandNR__pdsch_256QAM_FR2__Type BandNR__pdsch_256QAM_FR2__cond ::
 Opt BandNR__pusch_256QAM__Type BandNR__pusch_256QAM__cond ::
 Opt BandNR__ue_PowerClass__Type BandNR__ue_PowerClass__cond ::
 Opt BandNR__rateMatchingLTE_CRS__Type BandNR__rateMatchingLTE_CRS__cond ::
 Opt BandNR__channelBWs_DL__Type BandNR__channelBWs_DL__cond ::
 Opt BandNR__channelBWs_UL__Type BandNR__channelBWs_UL__cond ::
 nil).
Definition BandNR__ext_list : list typ := (
  typ_cons BandNR__ext0__Type BandNR__ext0__cond ::
  typ_cons BandNR__ext1__Type BandNR__ext1__cond ::
  typ_cons BandNR__ext2__Type BandNR__ext2__cond ::
  typ_cons BandNR__ext3__Type BandNR__ext3__cond ::
  typ_cons BandNR__ext4__Type BandNR__ext4__cond ::
  typ_cons BandNR__ext5__Type BandNR__ext5__cond ::
  typ_cons BandNR__ext6__Type BandNR__ext6__cond ::
  typ_cons BandNR__ext7__Type BandNR__ext7__cond ::
  typ_cons BandNR__ext8__Type BandNR__ext8__cond ::
  typ_cons BandNR__ext9__Type BandNR__ext9__cond ::
  typ_cons BandNR__ext10__Type BandNR__ext10__cond ::
  typ_cons BandNR__ext11__Type BandNR__ext11__cond ::
  typ_cons BandNR__ext12__Type BandNR__ext12__cond ::
  typ_cons BandNR__ext13__Type BandNR__ext13__cond ::
  nil).
Definition BandNR__cond (z : BandNR__Type) := 
(  FreqBandIndicatorNR__cond (BandNR__bandNR z) /\
  opt_cond BandNR__modifiedMPR_Behaviour__cond (BandNR__modifiedMPR_Behaviour z) /\
  opt_cond MIMO_ParametersPerBand__cond (BandNR__mimo_ParametersPerBand z) /\
  opt_cond BandNR__extendedCP__cond (BandNR__extendedCP z) /\
  opt_cond BandNR__multipleTCI__cond (BandNR__multipleTCI z) /\
  opt_cond BandNR__bwp_WithoutRestriction__cond (BandNR__bwp_WithoutRestriction z) /\
  opt_cond BandNR__bwp_SameNumerology__cond (BandNR__bwp_SameNumerology z) /\
  opt_cond BandNR__bwp_DiffNumerology__cond (BandNR__bwp_DiffNumerology z) /\
  opt_cond BandNR__crossCarrierScheduling_SameSCS__cond (BandNR__crossCarrierScheduling_SameSCS z) /\
  opt_cond BandNR__pdsch_256QAM_FR2__cond (BandNR__pdsch_256QAM_FR2 z) /\
  opt_cond BandNR__pusch_256QAM__cond (BandNR__pusch_256QAM z) /\
  opt_cond BandNR__ue_PowerClass__cond (BandNR__ue_PowerClass z) /\
  opt_cond BandNR__rateMatchingLTE_CRS__cond (BandNR__rateMatchingLTE_CRS z) /\
  opt_cond BandNR__channelBWs_DL__cond (BandNR__channelBWs_DL z) /\
  opt_cond BandNR__channelBWs_UL__cond (BandNR__channelBWs_UL z) /\
  True) /\ 
(  opt_cond BandNR__ext0__cond (BandNR__ext0 z) /\
  opt_cond BandNR__ext1__cond (BandNR__ext1 z) /\
  opt_cond BandNR__ext2__cond (BandNR__ext2 z) /\
  opt_cond BandNR__ext3__cond (BandNR__ext3 z) /\
  opt_cond BandNR__ext4__cond (BandNR__ext4 z) /\
  opt_cond BandNR__ext5__cond (BandNR__ext5 z) /\
  opt_cond BandNR__ext6__cond (BandNR__ext6 z) /\
  opt_cond BandNR__ext7__cond (BandNR__ext7 z) /\
  opt_cond BandNR__ext8__cond (BandNR__ext8 z) /\
  opt_cond BandNR__ext9__cond (BandNR__ext9 z) /\
  opt_cond BandNR__ext10__cond (BandNR__ext10 z) /\
  opt_cond BandNR__ext11__cond (BandNR__ext11 z) /\
  opt_cond BandNR__ext12__cond (BandNR__ext12 z) /\
  opt_cond BandNR__ext13__cond (BandNR__ext13 z) /\
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
Definition BandNR__modifiedMPR_Behaviour__Format : T_Format BandNR__modifiedMPR_Behaviour__Type BandNR__modifiedMPR_Behaviour__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__modifiedMPR_Behaviour__cond BandNR__modifiedMPR_Behaviour__Format.

Definition BandNR__extendedCP__Format : T_Format BandNR__extendedCP__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__extendedCP__nat__Format BandNR__extendedCP__F1 BandNR__extendedCP__F2 BandNR__extendedCP__F1F2 BandNR__extendedCP__F2F1.

Opaque BandNR__extendedCP__cond BandNR__extendedCP__Format.

Definition BandNR__multipleTCI__Format : T_Format BandNR__multipleTCI__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__multipleTCI__nat__Format BandNR__multipleTCI__F1 BandNR__multipleTCI__F2 BandNR__multipleTCI__F1F2 BandNR__multipleTCI__F2F1.

Opaque BandNR__multipleTCI__cond BandNR__multipleTCI__Format.

Definition BandNR__bwp_WithoutRestriction__Format : T_Format BandNR__bwp_WithoutRestriction__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__bwp_WithoutRestriction__nat__Format BandNR__bwp_WithoutRestriction__F1 BandNR__bwp_WithoutRestriction__F2 BandNR__bwp_WithoutRestriction__F1F2 BandNR__bwp_WithoutRestriction__F2F1.

Opaque BandNR__bwp_WithoutRestriction__cond BandNR__bwp_WithoutRestriction__Format.

Definition BandNR__bwp_SameNumerology__Format : T_Format BandNR__bwp_SameNumerology__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__bwp_SameNumerology__nat__Format BandNR__bwp_SameNumerology__F1 BandNR__bwp_SameNumerology__F2 BandNR__bwp_SameNumerology__F1F2 BandNR__bwp_SameNumerology__F2F1.

Opaque BandNR__bwp_SameNumerology__cond BandNR__bwp_SameNumerology__Format.

Definition BandNR__bwp_DiffNumerology__Format : T_Format BandNR__bwp_DiffNumerology__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__bwp_DiffNumerology__nat__Format BandNR__bwp_DiffNumerology__F1 BandNR__bwp_DiffNumerology__F2 BandNR__bwp_DiffNumerology__F1F2 BandNR__bwp_DiffNumerology__F2F1.

Opaque BandNR__bwp_DiffNumerology__cond BandNR__bwp_DiffNumerology__Format.

Definition BandNR__crossCarrierScheduling_SameSCS__Format : T_Format BandNR__crossCarrierScheduling_SameSCS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__crossCarrierScheduling_SameSCS__nat__Format BandNR__crossCarrierScheduling_SameSCS__F1 BandNR__crossCarrierScheduling_SameSCS__F2 BandNR__crossCarrierScheduling_SameSCS__F1F2 BandNR__crossCarrierScheduling_SameSCS__F2F1.

Opaque BandNR__crossCarrierScheduling_SameSCS__cond BandNR__crossCarrierScheduling_SameSCS__Format.

Definition BandNR__pdsch_256QAM_FR2__Format : T_Format BandNR__pdsch_256QAM_FR2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__pdsch_256QAM_FR2__nat__Format BandNR__pdsch_256QAM_FR2__F1 BandNR__pdsch_256QAM_FR2__F2 BandNR__pdsch_256QAM_FR2__F1F2 BandNR__pdsch_256QAM_FR2__F2F1.

Opaque BandNR__pdsch_256QAM_FR2__cond BandNR__pdsch_256QAM_FR2__Format.

Definition BandNR__pusch_256QAM__Format : T_Format BandNR__pusch_256QAM__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__pusch_256QAM__nat__Format BandNR__pusch_256QAM__F1 BandNR__pusch_256QAM__F2 BandNR__pusch_256QAM__F1F2 BandNR__pusch_256QAM__F2F1.

Opaque BandNR__pusch_256QAM__cond BandNR__pusch_256QAM__Format.

Definition BandNR__ue_PowerClass__Format : T_Format BandNR__ue_PowerClass__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ue_PowerClass__nat__Format BandNR__ue_PowerClass__F1 BandNR__ue_PowerClass__F2 BandNR__ue_PowerClass__F1F2 BandNR__ue_PowerClass__F2F1.

Opaque BandNR__ue_PowerClass__cond BandNR__ue_PowerClass__Format.

Definition BandNR__rateMatchingLTE_CRS__Format : T_Format BandNR__rateMatchingLTE_CRS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__rateMatchingLTE_CRS__nat__Format BandNR__rateMatchingLTE_CRS__F1 BandNR__rateMatchingLTE_CRS__F2 BandNR__rateMatchingLTE_CRS__F1F2 BandNR__rateMatchingLTE_CRS__F2F1.

Opaque BandNR__rateMatchingLTE_CRS__cond BandNR__rateMatchingLTE_CRS__Format.

Definition BandNR__channelBWs_DL__fr1__scs_15kHz__Format : T_Format BandNR__channelBWs_DL__fr1__scs_15kHz__Type BandNR__channelBWs_DL__fr1__scs_15kHz__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque BandNR__channelBWs_DL__fr1__scs_15kHz__cond BandNR__channelBWs_DL__fr1__scs_15kHz__Format.

Definition BandNR__channelBWs_DL__fr1__scs_30kHz__Format : T_Format BandNR__channelBWs_DL__fr1__scs_30kHz__Type BandNR__channelBWs_DL__fr1__scs_30kHz__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque BandNR__channelBWs_DL__fr1__scs_30kHz__cond BandNR__channelBWs_DL__fr1__scs_30kHz__Format.

Definition BandNR__channelBWs_DL__fr1__scs_60kHz__Format : T_Format BandNR__channelBWs_DL__fr1__scs_60kHz__Type BandNR__channelBWs_DL__fr1__scs_60kHz__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque BandNR__channelBWs_DL__fr1__scs_60kHz__cond BandNR__channelBWs_DL__fr1__scs_60kHz__Format.


Definition BandNR__channelBWs_DL__fr1__Format_Type := Eval cbn in seq_format_prod BandNR__channelBWs_DL__fr1__list.
Definition BandNR__channelBWs_DL__fr1__Format_list : BandNR__channelBWs_DL__fr1__Format_Type :=
  (BandNR__channelBWs_DL__fr1__scs_15kHz__Format, (BandNR__channelBWs_DL__fr1__scs_30kHz__Format, (BandNR__channelBWs_DL__fr1__scs_60kHz__Format, unit_format))).
Definition BandNR__channelBWs_DL__fr1__list__Format := (*Eval compute in *) seq_format BandNR__channelBWs_DL__fr1__list BandNR__channelBWs_DL__fr1__Format_list.
Definition BandNR__channelBWs_DL__fr1__F1 z :=
  (BandNR__channelBWs_DL__fr1__scs_15kHz z, (BandNR__channelBWs_DL__fr1__scs_30kHz z, (BandNR__channelBWs_DL__fr1__scs_60kHz z, tt))).
Definition BandNR__channelBWs_DL__fr1__F2 (y : seq_type BandNR__channelBWs_DL__fr1__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandNR__channelBWs_DL__fr1__Type i0 i1 i2
  end.
Lemma BandNR__channelBWs_DL__fr1__F1F2_cond (z : BandNR__channelBWs_DL__fr1__Type)
  : BandNR__channelBWs_DL__fr1__cond z ->
  (seq_cond BandNR__channelBWs_DL__fr1__list (BandNR__channelBWs_DL__fr1__F1 z)).
intro H. unfold BandNR__channelBWs_DL__fr1__cond in H. simpl. auto. Qed.
Lemma BandNR__channelBWs_DL__fr1__F1F2_cond2 (z : BandNR__channelBWs_DL__fr1__Type)
 : BandNR__channelBWs_DL__fr1__F2 (BandNR__channelBWs_DL__fr1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__channelBWs_DL__fr1__F2F1_cond (y : seq_type BandNR__channelBWs_DL__fr1__list)
  : seq_cond BandNR__channelBWs_DL__fr1__list y ->
 (BandNR__channelBWs_DL__fr1__cond (BandNR__channelBWs_DL__fr1__F2 y)) /\  BandNR__channelBWs_DL__fr1__F1 (BandNR__channelBWs_DL__fr1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__channelBWs_DL__fr1__cond. simpl in *. auto.
 - simpl. unfold BandNR__channelBWs_DL__fr1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__channelBWs_DL__fr1__Format : T_Format BandNR__channelBWs_DL__fr1__Type BandNR__channelBWs_DL__fr1__cond :=
        proj2_format  BandNR__channelBWs_DL__fr1__cond BandNR__channelBWs_DL__fr1__list__Format
    BandNR__channelBWs_DL__fr1__F1 BandNR__channelBWs_DL__fr1__F2 BandNR__channelBWs_DL__fr1__F1F2_cond  BandNR__channelBWs_DL__fr1__F1F2_cond2 BandNR__channelBWs_DL__fr1__F2F1_cond.
Opaque BandNR__channelBWs_DL__fr1__cond BandNR__channelBWs_DL__fr1__Format.

Definition BandNR__channelBWs_DL__fr2__scs_60kHz__Format : T_Format BandNR__channelBWs_DL__fr2__scs_60kHz__Type BandNR__channelBWs_DL__fr2__scs_60kHz__cond := (* Eval compute in *) bit_string_fixed_format 3.
Opaque BandNR__channelBWs_DL__fr2__scs_60kHz__cond BandNR__channelBWs_DL__fr2__scs_60kHz__Format.

Definition BandNR__channelBWs_DL__fr2__scs_120kHz__Format : T_Format BandNR__channelBWs_DL__fr2__scs_120kHz__Type BandNR__channelBWs_DL__fr2__scs_120kHz__cond := (* Eval compute in *) bit_string_fixed_format 3.
Opaque BandNR__channelBWs_DL__fr2__scs_120kHz__cond BandNR__channelBWs_DL__fr2__scs_120kHz__Format.


Definition BandNR__channelBWs_DL__fr2__Format_Type := Eval cbn in seq_format_prod BandNR__channelBWs_DL__fr2__list.
Definition BandNR__channelBWs_DL__fr2__Format_list : BandNR__channelBWs_DL__fr2__Format_Type :=
  (BandNR__channelBWs_DL__fr2__scs_60kHz__Format, (BandNR__channelBWs_DL__fr2__scs_120kHz__Format, unit_format)).
Definition BandNR__channelBWs_DL__fr2__list__Format := (*Eval compute in *) seq_format BandNR__channelBWs_DL__fr2__list BandNR__channelBWs_DL__fr2__Format_list.
Definition BandNR__channelBWs_DL__fr2__F1 z :=
  (BandNR__channelBWs_DL__fr2__scs_60kHz z, (BandNR__channelBWs_DL__fr2__scs_120kHz z, tt)).
Definition BandNR__channelBWs_DL__fr2__F2 (y : seq_type BandNR__channelBWs_DL__fr2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__channelBWs_DL__fr2__Type i0 i1
  end.
Lemma BandNR__channelBWs_DL__fr2__F1F2_cond (z : BandNR__channelBWs_DL__fr2__Type)
  : BandNR__channelBWs_DL__fr2__cond z ->
  (seq_cond BandNR__channelBWs_DL__fr2__list (BandNR__channelBWs_DL__fr2__F1 z)).
intro H. unfold BandNR__channelBWs_DL__fr2__cond in H. simpl. auto. Qed.
Lemma BandNR__channelBWs_DL__fr2__F1F2_cond2 (z : BandNR__channelBWs_DL__fr2__Type)
 : BandNR__channelBWs_DL__fr2__F2 (BandNR__channelBWs_DL__fr2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__channelBWs_DL__fr2__F2F1_cond (y : seq_type BandNR__channelBWs_DL__fr2__list)
  : seq_cond BandNR__channelBWs_DL__fr2__list y ->
 (BandNR__channelBWs_DL__fr2__cond (BandNR__channelBWs_DL__fr2__F2 y)) /\  BandNR__channelBWs_DL__fr2__F1 (BandNR__channelBWs_DL__fr2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__channelBWs_DL__fr2__cond. simpl in *. auto.
 - simpl. unfold BandNR__channelBWs_DL__fr2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__channelBWs_DL__fr2__Format : T_Format BandNR__channelBWs_DL__fr2__Type BandNR__channelBWs_DL__fr2__cond :=
        proj2_format  BandNR__channelBWs_DL__fr2__cond BandNR__channelBWs_DL__fr2__list__Format
    BandNR__channelBWs_DL__fr2__F1 BandNR__channelBWs_DL__fr2__F2 BandNR__channelBWs_DL__fr2__F1F2_cond  BandNR__channelBWs_DL__fr2__F1F2_cond2 BandNR__channelBWs_DL__fr2__F2F1_cond.
Opaque BandNR__channelBWs_DL__fr2__cond BandNR__channelBWs_DL__fr2__Format.


Definition BandNR__channelBWs_DL__Format_Type := Eval cbn in get_formats BandNR__channelBWs_DL__list.
Definition BandNR__channelBWs_DL__Format_list : BandNR__channelBWs_DL__Format_Type :=
  (BandNR__channelBWs_DL__fr1__Format, (BandNR__channelBWs_DL__fr2__Format, unit__Format)).
Definition BandNR__channelBWs_DL__list__Format := Eval compute in choice_format BandNR__channelBWs_DL__list BandNR__channelBWs_DL__len_helper1 BandNR__channelBWs_DL__len_helper2  BandNR__channelBWs_DL__Format_list.
Definition BandNR__channelBWs_DL__F1 (z : BandNR__channelBWs_DL__Type) : (choice BandNR__channelBWs_DL__list) :=
  match z with
   | BandNR__channelBWs_DL__fr1 t => existT _ 0 t
  | BandNR__channelBWs_DL__fr2 t => existT _ 1 t
  end.
Definition BandNR__channelBWs_DL__g := (fun n => typ_set (get_nth_typ BandNR__channelBWs_DL__list n)).
Definition BandNR__channelBWs_DL__F2 (y : choice BandNR__channelBWs_DL__list) : BandNR__channelBWs_DL__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandNR__channelBWs_DL__g n -> BandNR__channelBWs_DL__Type) with
    | 0 => fun (t : BandNR__channelBWs_DL__fr1__Type) => BandNR__channelBWs_DL__fr1 t 
    | 1 => fun (t : BandNR__channelBWs_DL__fr2__Type) => BandNR__channelBWs_DL__fr2 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandNR__channelBWs_DL__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandNR__channelBWs_DL__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandNR__channelBWs_DL__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandNR__channelBWs_DL__Type with end) n0
           end t0).

Lemma BandNR__channelBWs_DL__helper2 :  forall (y : BandNR__channelBWs_DL__Type), BandNR__channelBWs_DL__cond y -> choice_cond BandNR__channelBWs_DL__list (BandNR__channelBWs_DL__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandNR__channelBWs_DL__helper3 :  forall (y : BandNR__channelBWs_DL__Type), BandNR__channelBWs_DL__F2 (BandNR__channelBWs_DL__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandNR__channelBWs_DL__helper4 : (forall b : choice BandNR__channelBWs_DL__list, choice_cond BandNR__channelBWs_DL__list b -> BandNR__channelBWs_DL__cond (BandNR__channelBWs_DL__F2 b) /\ BandNR__channelBWs_DL__F1 (BandNR__channelBWs_DL__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandNR__channelBWs_DL__F1 BandNR__channelBWs_DL__F2.
Definition BandNR__channelBWs_DL__Format : T_Format BandNR__channelBWs_DL__Type BandNR__channelBWs_DL__cond :=
  (* Eval compute in *) proj2_format BandNR__channelBWs_DL__cond BandNR__channelBWs_DL__list__Format BandNR__channelBWs_DL__F1 BandNR__channelBWs_DL__F2 BandNR__channelBWs_DL__helper2 BandNR__channelBWs_DL__helper3 BandNR__channelBWs_DL__helper4.
Opaque BandNR__channelBWs_DL__cond BandNR__channelBWs_DL__Format.

Definition BandNR__channelBWs_UL__fr1__scs_15kHz__Format : T_Format BandNR__channelBWs_UL__fr1__scs_15kHz__Type BandNR__channelBWs_UL__fr1__scs_15kHz__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque BandNR__channelBWs_UL__fr1__scs_15kHz__cond BandNR__channelBWs_UL__fr1__scs_15kHz__Format.

Definition BandNR__channelBWs_UL__fr1__scs_30kHz__Format : T_Format BandNR__channelBWs_UL__fr1__scs_30kHz__Type BandNR__channelBWs_UL__fr1__scs_30kHz__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque BandNR__channelBWs_UL__fr1__scs_30kHz__cond BandNR__channelBWs_UL__fr1__scs_30kHz__Format.

Definition BandNR__channelBWs_UL__fr1__scs_60kHz__Format : T_Format BandNR__channelBWs_UL__fr1__scs_60kHz__Type BandNR__channelBWs_UL__fr1__scs_60kHz__cond := (* Eval compute in *) bit_string_fixed_format 10.
Opaque BandNR__channelBWs_UL__fr1__scs_60kHz__cond BandNR__channelBWs_UL__fr1__scs_60kHz__Format.


Definition BandNR__channelBWs_UL__fr1__Format_Type := Eval cbn in seq_format_prod BandNR__channelBWs_UL__fr1__list.
Definition BandNR__channelBWs_UL__fr1__Format_list : BandNR__channelBWs_UL__fr1__Format_Type :=
  (BandNR__channelBWs_UL__fr1__scs_15kHz__Format, (BandNR__channelBWs_UL__fr1__scs_30kHz__Format, (BandNR__channelBWs_UL__fr1__scs_60kHz__Format, unit_format))).
Definition BandNR__channelBWs_UL__fr1__list__Format := (*Eval compute in *) seq_format BandNR__channelBWs_UL__fr1__list BandNR__channelBWs_UL__fr1__Format_list.
Definition BandNR__channelBWs_UL__fr1__F1 z :=
  (BandNR__channelBWs_UL__fr1__scs_15kHz z, (BandNR__channelBWs_UL__fr1__scs_30kHz z, (BandNR__channelBWs_UL__fr1__scs_60kHz z, tt))).
Definition BandNR__channelBWs_UL__fr1__F2 (y : seq_type BandNR__channelBWs_UL__fr1__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandNR__channelBWs_UL__fr1__Type i0 i1 i2
  end.
Lemma BandNR__channelBWs_UL__fr1__F1F2_cond (z : BandNR__channelBWs_UL__fr1__Type)
  : BandNR__channelBWs_UL__fr1__cond z ->
  (seq_cond BandNR__channelBWs_UL__fr1__list (BandNR__channelBWs_UL__fr1__F1 z)).
intro H. unfold BandNR__channelBWs_UL__fr1__cond in H. simpl. auto. Qed.
Lemma BandNR__channelBWs_UL__fr1__F1F2_cond2 (z : BandNR__channelBWs_UL__fr1__Type)
 : BandNR__channelBWs_UL__fr1__F2 (BandNR__channelBWs_UL__fr1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__channelBWs_UL__fr1__F2F1_cond (y : seq_type BandNR__channelBWs_UL__fr1__list)
  : seq_cond BandNR__channelBWs_UL__fr1__list y ->
 (BandNR__channelBWs_UL__fr1__cond (BandNR__channelBWs_UL__fr1__F2 y)) /\  BandNR__channelBWs_UL__fr1__F1 (BandNR__channelBWs_UL__fr1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__channelBWs_UL__fr1__cond. simpl in *. auto.
 - simpl. unfold BandNR__channelBWs_UL__fr1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__channelBWs_UL__fr1__Format : T_Format BandNR__channelBWs_UL__fr1__Type BandNR__channelBWs_UL__fr1__cond :=
        proj2_format  BandNR__channelBWs_UL__fr1__cond BandNR__channelBWs_UL__fr1__list__Format
    BandNR__channelBWs_UL__fr1__F1 BandNR__channelBWs_UL__fr1__F2 BandNR__channelBWs_UL__fr1__F1F2_cond  BandNR__channelBWs_UL__fr1__F1F2_cond2 BandNR__channelBWs_UL__fr1__F2F1_cond.
Opaque BandNR__channelBWs_UL__fr1__cond BandNR__channelBWs_UL__fr1__Format.

Definition BandNR__channelBWs_UL__fr2__scs_60kHz__Format : T_Format BandNR__channelBWs_UL__fr2__scs_60kHz__Type BandNR__channelBWs_UL__fr2__scs_60kHz__cond := (* Eval compute in *) bit_string_fixed_format 3.
Opaque BandNR__channelBWs_UL__fr2__scs_60kHz__cond BandNR__channelBWs_UL__fr2__scs_60kHz__Format.

Definition BandNR__channelBWs_UL__fr2__scs_120kHz__Format : T_Format BandNR__channelBWs_UL__fr2__scs_120kHz__Type BandNR__channelBWs_UL__fr2__scs_120kHz__cond := (* Eval compute in *) bit_string_fixed_format 3.
Opaque BandNR__channelBWs_UL__fr2__scs_120kHz__cond BandNR__channelBWs_UL__fr2__scs_120kHz__Format.


Definition BandNR__channelBWs_UL__fr2__Format_Type := Eval cbn in seq_format_prod BandNR__channelBWs_UL__fr2__list.
Definition BandNR__channelBWs_UL__fr2__Format_list : BandNR__channelBWs_UL__fr2__Format_Type :=
  (BandNR__channelBWs_UL__fr2__scs_60kHz__Format, (BandNR__channelBWs_UL__fr2__scs_120kHz__Format, unit_format)).
Definition BandNR__channelBWs_UL__fr2__list__Format := (*Eval compute in *) seq_format BandNR__channelBWs_UL__fr2__list BandNR__channelBWs_UL__fr2__Format_list.
Definition BandNR__channelBWs_UL__fr2__F1 z :=
  (BandNR__channelBWs_UL__fr2__scs_60kHz z, (BandNR__channelBWs_UL__fr2__scs_120kHz z, tt)).
Definition BandNR__channelBWs_UL__fr2__F2 (y : seq_type BandNR__channelBWs_UL__fr2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__channelBWs_UL__fr2__Type i0 i1
  end.
Lemma BandNR__channelBWs_UL__fr2__F1F2_cond (z : BandNR__channelBWs_UL__fr2__Type)
  : BandNR__channelBWs_UL__fr2__cond z ->
  (seq_cond BandNR__channelBWs_UL__fr2__list (BandNR__channelBWs_UL__fr2__F1 z)).
intro H. unfold BandNR__channelBWs_UL__fr2__cond in H. simpl. auto. Qed.
Lemma BandNR__channelBWs_UL__fr2__F1F2_cond2 (z : BandNR__channelBWs_UL__fr2__Type)
 : BandNR__channelBWs_UL__fr2__F2 (BandNR__channelBWs_UL__fr2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__channelBWs_UL__fr2__F2F1_cond (y : seq_type BandNR__channelBWs_UL__fr2__list)
  : seq_cond BandNR__channelBWs_UL__fr2__list y ->
 (BandNR__channelBWs_UL__fr2__cond (BandNR__channelBWs_UL__fr2__F2 y)) /\  BandNR__channelBWs_UL__fr2__F1 (BandNR__channelBWs_UL__fr2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__channelBWs_UL__fr2__cond. simpl in *. auto.
 - simpl. unfold BandNR__channelBWs_UL__fr2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__channelBWs_UL__fr2__Format : T_Format BandNR__channelBWs_UL__fr2__Type BandNR__channelBWs_UL__fr2__cond :=
        proj2_format  BandNR__channelBWs_UL__fr2__cond BandNR__channelBWs_UL__fr2__list__Format
    BandNR__channelBWs_UL__fr2__F1 BandNR__channelBWs_UL__fr2__F2 BandNR__channelBWs_UL__fr2__F1F2_cond  BandNR__channelBWs_UL__fr2__F1F2_cond2 BandNR__channelBWs_UL__fr2__F2F1_cond.
Opaque BandNR__channelBWs_UL__fr2__cond BandNR__channelBWs_UL__fr2__Format.


Definition BandNR__channelBWs_UL__Format_Type := Eval cbn in get_formats BandNR__channelBWs_UL__list.
Definition BandNR__channelBWs_UL__Format_list : BandNR__channelBWs_UL__Format_Type :=
  (BandNR__channelBWs_UL__fr1__Format, (BandNR__channelBWs_UL__fr2__Format, unit__Format)).
Definition BandNR__channelBWs_UL__list__Format := Eval compute in choice_format BandNR__channelBWs_UL__list BandNR__channelBWs_UL__len_helper1 BandNR__channelBWs_UL__len_helper2  BandNR__channelBWs_UL__Format_list.
Definition BandNR__channelBWs_UL__F1 (z : BandNR__channelBWs_UL__Type) : (choice BandNR__channelBWs_UL__list) :=
  match z with
   | BandNR__channelBWs_UL__fr1 t => existT _ 0 t
  | BandNR__channelBWs_UL__fr2 t => existT _ 1 t
  end.
Definition BandNR__channelBWs_UL__g := (fun n => typ_set (get_nth_typ BandNR__channelBWs_UL__list n)).
Definition BandNR__channelBWs_UL__F2 (y : choice BandNR__channelBWs_UL__list) : BandNR__channelBWs_UL__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandNR__channelBWs_UL__g n -> BandNR__channelBWs_UL__Type) with
    | 0 => fun (t : BandNR__channelBWs_UL__fr1__Type) => BandNR__channelBWs_UL__fr1 t 
    | 1 => fun (t : BandNR__channelBWs_UL__fr2__Type) => BandNR__channelBWs_UL__fr2 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandNR__channelBWs_UL__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandNR__channelBWs_UL__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandNR__channelBWs_UL__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandNR__channelBWs_UL__Type with end) n0
           end t0).

Lemma BandNR__channelBWs_UL__helper2 :  forall (y : BandNR__channelBWs_UL__Type), BandNR__channelBWs_UL__cond y -> choice_cond BandNR__channelBWs_UL__list (BandNR__channelBWs_UL__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandNR__channelBWs_UL__helper3 :  forall (y : BandNR__channelBWs_UL__Type), BandNR__channelBWs_UL__F2 (BandNR__channelBWs_UL__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandNR__channelBWs_UL__helper4 : (forall b : choice BandNR__channelBWs_UL__list, choice_cond BandNR__channelBWs_UL__list b -> BandNR__channelBWs_UL__cond (BandNR__channelBWs_UL__F2 b) /\ BandNR__channelBWs_UL__F1 (BandNR__channelBWs_UL__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandNR__channelBWs_UL__F1 BandNR__channelBWs_UL__F2.
Definition BandNR__channelBWs_UL__Format : T_Format BandNR__channelBWs_UL__Type BandNR__channelBWs_UL__cond :=
  (* Eval compute in *) proj2_format BandNR__channelBWs_UL__cond BandNR__channelBWs_UL__list__Format BandNR__channelBWs_UL__F1 BandNR__channelBWs_UL__F2 BandNR__channelBWs_UL__helper2 BandNR__channelBWs_UL__helper3 BandNR__channelBWs_UL__helper4.
Opaque BandNR__channelBWs_UL__cond BandNR__channelBWs_UL__Format.

Definition BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Format : T_Format BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__nat__Format BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F1 BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F2 BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F1F2 BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__F2F1.

Opaque BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__cond BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Format.


Definition BandNR__ext0O__Format_Type := Eval cbn in seq_format_prod BandNR__ext0O__list.
Definition BandNR__ext0O__Format_list : BandNR__ext0O__Format_Type :=
  (BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1__Format, unit_format).
Definition BandNR__ext0O__list__Format := (*Eval compute in *) seq_format BandNR__ext0O__list BandNR__ext0O__Format_list.
Definition BandNR__ext0O__F1 z :=
  (BandNR__ext0O__maxUplinkDutyCycle_PC2_FR1 z, tt).
Definition BandNR__ext0O__F2 (y : seq_type BandNR__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__BandNR__ext0O__Type i0
  end.
Lemma BandNR__ext0O__F1F2_cond (z : BandNR__ext0O__Type)
  : BandNR__ext0O__cond z ->
  (seq_cond BandNR__ext0O__list (BandNR__ext0O__F1 z)).
intro H. unfold BandNR__ext0O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext0O__F1F2_cond2 (z : BandNR__ext0O__Type)
 : BandNR__ext0O__F2 (BandNR__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext0O__F2F1_cond (y : seq_type BandNR__ext0O__list)
  : seq_cond BandNR__ext0O__list y ->
 (BandNR__ext0O__cond (BandNR__ext0O__F2 y)) /\  BandNR__ext0O__F1 (BandNR__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext0O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext0O__Format : T_Format BandNR__ext0O__Type BandNR__ext0O__cond :=
        proj2_format  BandNR__ext0O__cond BandNR__ext0O__list__Format
    BandNR__ext0O__F1 BandNR__ext0O__F2 BandNR__ext0O__F1F2_cond  BandNR__ext0O__F1F2_cond2 BandNR__ext0O__F2F1_cond.
Opaque BandNR__ext0O__cond BandNR__ext0O__Format.

Definition BandNR__ext0__check_all_none (b : BandNR__ext0O__Type) : bool :=
match b with 
  | make__BandNR__ext0O__Type None  => false 
  | _ => true 
 end.
Definition BandNR__ext0__Format : T_Format BandNR__ext0__Type BandNR__ext0__cond :=
  restrict_add_format BandNR__ext0__check_all_none BandNR__ext0O__Format.

Opaque BandNR__ext0__cond BandNR__ext0__Format.

Definition BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Format : T_Format BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__nat__Format BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F1 BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F2 BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F1F2 BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__F2F1.

Opaque BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__cond BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Format.

Definition BandNR__ext1O__powerBoosting_pi2BPSK__Format : T_Format BandNR__ext1O__powerBoosting_pi2BPSK__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext1O__powerBoosting_pi2BPSK__nat__Format BandNR__ext1O__powerBoosting_pi2BPSK__F1 BandNR__ext1O__powerBoosting_pi2BPSK__F2 BandNR__ext1O__powerBoosting_pi2BPSK__F1F2 BandNR__ext1O__powerBoosting_pi2BPSK__F2F1.

Opaque BandNR__ext1O__powerBoosting_pi2BPSK__cond BandNR__ext1O__powerBoosting_pi2BPSK__Format.


Definition BandNR__ext1O__Format_Type := Eval cbn in seq_format_prod BandNR__ext1O__list.
Definition BandNR__ext1O__Format_list : BandNR__ext1O__Format_Type :=
  (BandNR__ext1O__pucch_SpatialRelInfoMAC_CE__Format, (BandNR__ext1O__powerBoosting_pi2BPSK__Format, unit_format)).
Definition BandNR__ext1O__list__Format := (*Eval compute in *) seq_format BandNR__ext1O__list BandNR__ext1O__Format_list.
Definition BandNR__ext1O__F1 z :=
  (BandNR__ext1O__pucch_SpatialRelInfoMAC_CE z, (BandNR__ext1O__powerBoosting_pi2BPSK z, tt)).
Definition BandNR__ext1O__F2 (y : seq_type BandNR__ext1O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext1O__Type i0 i1
  end.
Lemma BandNR__ext1O__F1F2_cond (z : BandNR__ext1O__Type)
  : BandNR__ext1O__cond z ->
  (seq_cond BandNR__ext1O__list (BandNR__ext1O__F1 z)).
intro H. unfold BandNR__ext1O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext1O__F1F2_cond2 (z : BandNR__ext1O__Type)
 : BandNR__ext1O__F2 (BandNR__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext1O__F2F1_cond (y : seq_type BandNR__ext1O__list)
  : seq_cond BandNR__ext1O__list y ->
 (BandNR__ext1O__cond (BandNR__ext1O__F2 y)) /\  BandNR__ext1O__F1 (BandNR__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext1O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext1O__Format : T_Format BandNR__ext1O__Type BandNR__ext1O__cond :=
        proj2_format  BandNR__ext1O__cond BandNR__ext1O__list__Format
    BandNR__ext1O__F1 BandNR__ext1O__F2 BandNR__ext1O__F1F2_cond  BandNR__ext1O__F1F2_cond2 BandNR__ext1O__F2F1_cond.
Opaque BandNR__ext1O__cond BandNR__ext1O__Format.

Definition BandNR__ext1__check_all_none (b : BandNR__ext1O__Type) : bool :=
match b with 
  | make__BandNR__ext1O__Type None None  => false 
  | _ => true 
 end.
Definition BandNR__ext1__Format : T_Format BandNR__ext1__Type BandNR__ext1__cond :=
  restrict_add_format BandNR__ext1__check_all_none BandNR__ext1O__Format.

Opaque BandNR__ext1__cond BandNR__ext1__Format.

Definition BandNR__ext2O__maxUplinkDutyCycle_FR2__Format : T_Format BandNR__ext2O__maxUplinkDutyCycle_FR2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext2O__maxUplinkDutyCycle_FR2__nat__Format BandNR__ext2O__maxUplinkDutyCycle_FR2__F1 BandNR__ext2O__maxUplinkDutyCycle_FR2__F2 BandNR__ext2O__maxUplinkDutyCycle_FR2__F1F2 BandNR__ext2O__maxUplinkDutyCycle_FR2__F2F1.

Opaque BandNR__ext2O__maxUplinkDutyCycle_FR2__cond BandNR__ext2O__maxUplinkDutyCycle_FR2__Format.


Definition BandNR__ext2O__Format_Type := Eval cbn in seq_format_prod BandNR__ext2O__list.
Definition BandNR__ext2O__Format_list : BandNR__ext2O__Format_Type :=
  (BandNR__ext2O__maxUplinkDutyCycle_FR2__Format, unit_format).
Definition BandNR__ext2O__list__Format := (*Eval compute in *) seq_format BandNR__ext2O__list BandNR__ext2O__Format_list.
Definition BandNR__ext2O__F1 z :=
  (BandNR__ext2O__maxUplinkDutyCycle_FR2 z, tt).
Definition BandNR__ext2O__F2 (y : seq_type BandNR__ext2O__list) :=
  match y with
  | (i0, _)=>
    make__BandNR__ext2O__Type i0
  end.
Lemma BandNR__ext2O__F1F2_cond (z : BandNR__ext2O__Type)
  : BandNR__ext2O__cond z ->
  (seq_cond BandNR__ext2O__list (BandNR__ext2O__F1 z)).
intro H. unfold BandNR__ext2O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext2O__F1F2_cond2 (z : BandNR__ext2O__Type)
 : BandNR__ext2O__F2 (BandNR__ext2O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext2O__F2F1_cond (y : seq_type BandNR__ext2O__list)
  : seq_cond BandNR__ext2O__list y ->
 (BandNR__ext2O__cond (BandNR__ext2O__F2 y)) /\  BandNR__ext2O__F1 (BandNR__ext2O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext2O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext2O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext2O__Format : T_Format BandNR__ext2O__Type BandNR__ext2O__cond :=
        proj2_format  BandNR__ext2O__cond BandNR__ext2O__list__Format
    BandNR__ext2O__F1 BandNR__ext2O__F2 BandNR__ext2O__F1F2_cond  BandNR__ext2O__F1F2_cond2 BandNR__ext2O__F2F1_cond.
Opaque BandNR__ext2O__cond BandNR__ext2O__Format.

Definition BandNR__ext2__check_all_none (b : BandNR__ext2O__Type) : bool :=
match b with 
  | make__BandNR__ext2O__Type None  => false 
  | _ => true 
 end.
Definition BandNR__ext2__Format : T_Format BandNR__ext2__Type BandNR__ext2__cond :=
  restrict_add_format BandNR__ext2__check_all_none BandNR__ext2O__Format.

Opaque BandNR__ext2__cond BandNR__ext2__Format.

Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__Format : T_Format BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__cond BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__Format.

Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__Format : T_Format BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__cond BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__Format.

Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__Format : T_Format BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__cond BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__Format.


Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__Format_Type := Eval cbn in seq_format_prod BandNR__ext3O__channelBWs_DL_v1590__fr1__list.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__Format_list : BandNR__ext3O__channelBWs_DL_v1590__fr1__Format_Type :=
  (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz__Format, (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz__Format, (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz__Format, unit_format))).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__list__Format := (*Eval compute in *) seq_format BandNR__ext3O__channelBWs_DL_v1590__fr1__list BandNR__ext3O__channelBWs_DL_v1590__fr1__Format_list.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__F1 z :=
  (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_15kHz z, (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_30kHz z, (BandNR__ext3O__channelBWs_DL_v1590__fr1__scs_60kHz z, tt))).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__F2 (y : seq_type BandNR__ext3O__channelBWs_DL_v1590__fr1__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandNR__ext3O__channelBWs_DL_v1590__fr1__Type i0 i1 i2
  end.
Lemma BandNR__ext3O__channelBWs_DL_v1590__fr1__F1F2_cond (z : BandNR__ext3O__channelBWs_DL_v1590__fr1__Type)
  : BandNR__ext3O__channelBWs_DL_v1590__fr1__cond z ->
  (seq_cond BandNR__ext3O__channelBWs_DL_v1590__fr1__list (BandNR__ext3O__channelBWs_DL_v1590__fr1__F1 z)).
intro H. unfold BandNR__ext3O__channelBWs_DL_v1590__fr1__cond in H. simpl. auto. Qed.
Lemma BandNR__ext3O__channelBWs_DL_v1590__fr1__F1F2_cond2 (z : BandNR__ext3O__channelBWs_DL_v1590__fr1__Type)
 : BandNR__ext3O__channelBWs_DL_v1590__fr1__F2 (BandNR__ext3O__channelBWs_DL_v1590__fr1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext3O__channelBWs_DL_v1590__fr1__F2F1_cond (y : seq_type BandNR__ext3O__channelBWs_DL_v1590__fr1__list)
  : seq_cond BandNR__ext3O__channelBWs_DL_v1590__fr1__list y ->
 (BandNR__ext3O__channelBWs_DL_v1590__fr1__cond (BandNR__ext3O__channelBWs_DL_v1590__fr1__F2 y)) /\  BandNR__ext3O__channelBWs_DL_v1590__fr1__F1 (BandNR__ext3O__channelBWs_DL_v1590__fr1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext3O__channelBWs_DL_v1590__fr1__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext3O__channelBWs_DL_v1590__fr1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr1__Format : T_Format BandNR__ext3O__channelBWs_DL_v1590__fr1__Type BandNR__ext3O__channelBWs_DL_v1590__fr1__cond :=
        proj2_format  BandNR__ext3O__channelBWs_DL_v1590__fr1__cond BandNR__ext3O__channelBWs_DL_v1590__fr1__list__Format
    BandNR__ext3O__channelBWs_DL_v1590__fr1__F1 BandNR__ext3O__channelBWs_DL_v1590__fr1__F2 BandNR__ext3O__channelBWs_DL_v1590__fr1__F1F2_cond  BandNR__ext3O__channelBWs_DL_v1590__fr1__F1F2_cond2 BandNR__ext3O__channelBWs_DL_v1590__fr1__F2F1_cond.
Opaque BandNR__ext3O__channelBWs_DL_v1590__fr1__cond BandNR__ext3O__channelBWs_DL_v1590__fr1__Format.

Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__Format : T_Format BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__cond BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__Format.

Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__Format : T_Format BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__Type BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__cond BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__Format.


Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__Format_Type := Eval cbn in seq_format_prod BandNR__ext3O__channelBWs_DL_v1590__fr2__list.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__Format_list : BandNR__ext3O__channelBWs_DL_v1590__fr2__Format_Type :=
  (BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz__Format, (BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz__Format, unit_format)).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__list__Format := (*Eval compute in *) seq_format BandNR__ext3O__channelBWs_DL_v1590__fr2__list BandNR__ext3O__channelBWs_DL_v1590__fr2__Format_list.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__F1 z :=
  (BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_60kHz z, (BandNR__ext3O__channelBWs_DL_v1590__fr2__scs_120kHz z, tt)).
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__F2 (y : seq_type BandNR__ext3O__channelBWs_DL_v1590__fr2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext3O__channelBWs_DL_v1590__fr2__Type i0 i1
  end.
Lemma BandNR__ext3O__channelBWs_DL_v1590__fr2__F1F2_cond (z : BandNR__ext3O__channelBWs_DL_v1590__fr2__Type)
  : BandNR__ext3O__channelBWs_DL_v1590__fr2__cond z ->
  (seq_cond BandNR__ext3O__channelBWs_DL_v1590__fr2__list (BandNR__ext3O__channelBWs_DL_v1590__fr2__F1 z)).
intro H. unfold BandNR__ext3O__channelBWs_DL_v1590__fr2__cond in H. simpl. auto. Qed.
Lemma BandNR__ext3O__channelBWs_DL_v1590__fr2__F1F2_cond2 (z : BandNR__ext3O__channelBWs_DL_v1590__fr2__Type)
 : BandNR__ext3O__channelBWs_DL_v1590__fr2__F2 (BandNR__ext3O__channelBWs_DL_v1590__fr2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext3O__channelBWs_DL_v1590__fr2__F2F1_cond (y : seq_type BandNR__ext3O__channelBWs_DL_v1590__fr2__list)
  : seq_cond BandNR__ext3O__channelBWs_DL_v1590__fr2__list y ->
 (BandNR__ext3O__channelBWs_DL_v1590__fr2__cond (BandNR__ext3O__channelBWs_DL_v1590__fr2__F2 y)) /\  BandNR__ext3O__channelBWs_DL_v1590__fr2__F1 (BandNR__ext3O__channelBWs_DL_v1590__fr2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext3O__channelBWs_DL_v1590__fr2__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext3O__channelBWs_DL_v1590__fr2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext3O__channelBWs_DL_v1590__fr2__Format : T_Format BandNR__ext3O__channelBWs_DL_v1590__fr2__Type BandNR__ext3O__channelBWs_DL_v1590__fr2__cond :=
        proj2_format  BandNR__ext3O__channelBWs_DL_v1590__fr2__cond BandNR__ext3O__channelBWs_DL_v1590__fr2__list__Format
    BandNR__ext3O__channelBWs_DL_v1590__fr2__F1 BandNR__ext3O__channelBWs_DL_v1590__fr2__F2 BandNR__ext3O__channelBWs_DL_v1590__fr2__F1F2_cond  BandNR__ext3O__channelBWs_DL_v1590__fr2__F1F2_cond2 BandNR__ext3O__channelBWs_DL_v1590__fr2__F2F1_cond.
Opaque BandNR__ext3O__channelBWs_DL_v1590__fr2__cond BandNR__ext3O__channelBWs_DL_v1590__fr2__Format.


Definition BandNR__ext3O__channelBWs_DL_v1590__Format_Type := Eval cbn in get_formats BandNR__ext3O__channelBWs_DL_v1590__list.
Definition BandNR__ext3O__channelBWs_DL_v1590__Format_list : BandNR__ext3O__channelBWs_DL_v1590__Format_Type :=
  (BandNR__ext3O__channelBWs_DL_v1590__fr1__Format, (BandNR__ext3O__channelBWs_DL_v1590__fr2__Format, unit__Format)).
Definition BandNR__ext3O__channelBWs_DL_v1590__list__Format := Eval compute in choice_format BandNR__ext3O__channelBWs_DL_v1590__list BandNR__ext3O__channelBWs_DL_v1590__len_helper1 BandNR__ext3O__channelBWs_DL_v1590__len_helper2  BandNR__ext3O__channelBWs_DL_v1590__Format_list.
Definition BandNR__ext3O__channelBWs_DL_v1590__F1 (z : BandNR__ext3O__channelBWs_DL_v1590__Type) : (choice BandNR__ext3O__channelBWs_DL_v1590__list) :=
  match z with
   | BandNR__ext3O__channelBWs_DL_v1590__fr1 t => existT _ 0 t
  | BandNR__ext3O__channelBWs_DL_v1590__fr2 t => existT _ 1 t
  end.
Definition BandNR__ext3O__channelBWs_DL_v1590__g := (fun n => typ_set (get_nth_typ BandNR__ext3O__channelBWs_DL_v1590__list n)).
Definition BandNR__ext3O__channelBWs_DL_v1590__F2 (y : choice BandNR__ext3O__channelBWs_DL_v1590__list) : BandNR__ext3O__channelBWs_DL_v1590__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandNR__ext3O__channelBWs_DL_v1590__g n -> BandNR__ext3O__channelBWs_DL_v1590__Type) with
    | 0 => fun (t : BandNR__ext3O__channelBWs_DL_v1590__fr1__Type) => BandNR__ext3O__channelBWs_DL_v1590__fr1 t 
    | 1 => fun (t : BandNR__ext3O__channelBWs_DL_v1590__fr2__Type) => BandNR__ext3O__channelBWs_DL_v1590__fr2 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandNR__ext3O__channelBWs_DL_v1590__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandNR__ext3O__channelBWs_DL_v1590__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandNR__ext3O__channelBWs_DL_v1590__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandNR__ext3O__channelBWs_DL_v1590__Type with end) n0
           end t0).

Lemma BandNR__ext3O__channelBWs_DL_v1590__helper2 :  forall (y : BandNR__ext3O__channelBWs_DL_v1590__Type), BandNR__ext3O__channelBWs_DL_v1590__cond y -> choice_cond BandNR__ext3O__channelBWs_DL_v1590__list (BandNR__ext3O__channelBWs_DL_v1590__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandNR__ext3O__channelBWs_DL_v1590__helper3 :  forall (y : BandNR__ext3O__channelBWs_DL_v1590__Type), BandNR__ext3O__channelBWs_DL_v1590__F2 (BandNR__ext3O__channelBWs_DL_v1590__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandNR__ext3O__channelBWs_DL_v1590__helper4 : (forall b : choice BandNR__ext3O__channelBWs_DL_v1590__list, choice_cond BandNR__ext3O__channelBWs_DL_v1590__list b -> BandNR__ext3O__channelBWs_DL_v1590__cond (BandNR__ext3O__channelBWs_DL_v1590__F2 b) /\ BandNR__ext3O__channelBWs_DL_v1590__F1 (BandNR__ext3O__channelBWs_DL_v1590__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandNR__ext3O__channelBWs_DL_v1590__F1 BandNR__ext3O__channelBWs_DL_v1590__F2.
Definition BandNR__ext3O__channelBWs_DL_v1590__Format : T_Format BandNR__ext3O__channelBWs_DL_v1590__Type BandNR__ext3O__channelBWs_DL_v1590__cond :=
  (* Eval compute in *) proj2_format BandNR__ext3O__channelBWs_DL_v1590__cond BandNR__ext3O__channelBWs_DL_v1590__list__Format BandNR__ext3O__channelBWs_DL_v1590__F1 BandNR__ext3O__channelBWs_DL_v1590__F2 BandNR__ext3O__channelBWs_DL_v1590__helper2 BandNR__ext3O__channelBWs_DL_v1590__helper3 BandNR__ext3O__channelBWs_DL_v1590__helper4.
Opaque BandNR__ext3O__channelBWs_DL_v1590__cond BandNR__ext3O__channelBWs_DL_v1590__Format.

Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__Format : T_Format BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__cond BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__Format.

Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__Format : T_Format BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__cond BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__Format.

Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__Format : T_Format BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__cond BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__Format.


Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__Format_Type := Eval cbn in seq_format_prod BandNR__ext3O__channelBWs_UL_v1590__fr1__list.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__Format_list : BandNR__ext3O__channelBWs_UL_v1590__fr1__Format_Type :=
  (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz__Format, (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz__Format, (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz__Format, unit_format))).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__list__Format := (*Eval compute in *) seq_format BandNR__ext3O__channelBWs_UL_v1590__fr1__list BandNR__ext3O__channelBWs_UL_v1590__fr1__Format_list.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__F1 z :=
  (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_15kHz z, (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_30kHz z, (BandNR__ext3O__channelBWs_UL_v1590__fr1__scs_60kHz z, tt))).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__F2 (y : seq_type BandNR__ext3O__channelBWs_UL_v1590__fr1__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandNR__ext3O__channelBWs_UL_v1590__fr1__Type i0 i1 i2
  end.
Lemma BandNR__ext3O__channelBWs_UL_v1590__fr1__F1F2_cond (z : BandNR__ext3O__channelBWs_UL_v1590__fr1__Type)
  : BandNR__ext3O__channelBWs_UL_v1590__fr1__cond z ->
  (seq_cond BandNR__ext3O__channelBWs_UL_v1590__fr1__list (BandNR__ext3O__channelBWs_UL_v1590__fr1__F1 z)).
intro H. unfold BandNR__ext3O__channelBWs_UL_v1590__fr1__cond in H. simpl. auto. Qed.
Lemma BandNR__ext3O__channelBWs_UL_v1590__fr1__F1F2_cond2 (z : BandNR__ext3O__channelBWs_UL_v1590__fr1__Type)
 : BandNR__ext3O__channelBWs_UL_v1590__fr1__F2 (BandNR__ext3O__channelBWs_UL_v1590__fr1__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext3O__channelBWs_UL_v1590__fr1__F2F1_cond (y : seq_type BandNR__ext3O__channelBWs_UL_v1590__fr1__list)
  : seq_cond BandNR__ext3O__channelBWs_UL_v1590__fr1__list y ->
 (BandNR__ext3O__channelBWs_UL_v1590__fr1__cond (BandNR__ext3O__channelBWs_UL_v1590__fr1__F2 y)) /\  BandNR__ext3O__channelBWs_UL_v1590__fr1__F1 (BandNR__ext3O__channelBWs_UL_v1590__fr1__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext3O__channelBWs_UL_v1590__fr1__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext3O__channelBWs_UL_v1590__fr1__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr1__Format : T_Format BandNR__ext3O__channelBWs_UL_v1590__fr1__Type BandNR__ext3O__channelBWs_UL_v1590__fr1__cond :=
        proj2_format  BandNR__ext3O__channelBWs_UL_v1590__fr1__cond BandNR__ext3O__channelBWs_UL_v1590__fr1__list__Format
    BandNR__ext3O__channelBWs_UL_v1590__fr1__F1 BandNR__ext3O__channelBWs_UL_v1590__fr1__F2 BandNR__ext3O__channelBWs_UL_v1590__fr1__F1F2_cond  BandNR__ext3O__channelBWs_UL_v1590__fr1__F1F2_cond2 BandNR__ext3O__channelBWs_UL_v1590__fr1__F2F1_cond.
Opaque BandNR__ext3O__channelBWs_UL_v1590__fr1__cond BandNR__ext3O__channelBWs_UL_v1590__fr1__Format.

Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__Format : T_Format BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__cond BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__Format.

Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__Format : T_Format BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__Type BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__cond BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__Format.


Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__Format_Type := Eval cbn in seq_format_prod BandNR__ext3O__channelBWs_UL_v1590__fr2__list.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__Format_list : BandNR__ext3O__channelBWs_UL_v1590__fr2__Format_Type :=
  (BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz__Format, (BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz__Format, unit_format)).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__list__Format := (*Eval compute in *) seq_format BandNR__ext3O__channelBWs_UL_v1590__fr2__list BandNR__ext3O__channelBWs_UL_v1590__fr2__Format_list.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__F1 z :=
  (BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_60kHz z, (BandNR__ext3O__channelBWs_UL_v1590__fr2__scs_120kHz z, tt)).
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__F2 (y : seq_type BandNR__ext3O__channelBWs_UL_v1590__fr2__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext3O__channelBWs_UL_v1590__fr2__Type i0 i1
  end.
Lemma BandNR__ext3O__channelBWs_UL_v1590__fr2__F1F2_cond (z : BandNR__ext3O__channelBWs_UL_v1590__fr2__Type)
  : BandNR__ext3O__channelBWs_UL_v1590__fr2__cond z ->
  (seq_cond BandNR__ext3O__channelBWs_UL_v1590__fr2__list (BandNR__ext3O__channelBWs_UL_v1590__fr2__F1 z)).
intro H. unfold BandNR__ext3O__channelBWs_UL_v1590__fr2__cond in H. simpl. auto. Qed.
Lemma BandNR__ext3O__channelBWs_UL_v1590__fr2__F1F2_cond2 (z : BandNR__ext3O__channelBWs_UL_v1590__fr2__Type)
 : BandNR__ext3O__channelBWs_UL_v1590__fr2__F2 (BandNR__ext3O__channelBWs_UL_v1590__fr2__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext3O__channelBWs_UL_v1590__fr2__F2F1_cond (y : seq_type BandNR__ext3O__channelBWs_UL_v1590__fr2__list)
  : seq_cond BandNR__ext3O__channelBWs_UL_v1590__fr2__list y ->
 (BandNR__ext3O__channelBWs_UL_v1590__fr2__cond (BandNR__ext3O__channelBWs_UL_v1590__fr2__F2 y)) /\  BandNR__ext3O__channelBWs_UL_v1590__fr2__F1 (BandNR__ext3O__channelBWs_UL_v1590__fr2__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext3O__channelBWs_UL_v1590__fr2__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext3O__channelBWs_UL_v1590__fr2__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext3O__channelBWs_UL_v1590__fr2__Format : T_Format BandNR__ext3O__channelBWs_UL_v1590__fr2__Type BandNR__ext3O__channelBWs_UL_v1590__fr2__cond :=
        proj2_format  BandNR__ext3O__channelBWs_UL_v1590__fr2__cond BandNR__ext3O__channelBWs_UL_v1590__fr2__list__Format
    BandNR__ext3O__channelBWs_UL_v1590__fr2__F1 BandNR__ext3O__channelBWs_UL_v1590__fr2__F2 BandNR__ext3O__channelBWs_UL_v1590__fr2__F1F2_cond  BandNR__ext3O__channelBWs_UL_v1590__fr2__F1F2_cond2 BandNR__ext3O__channelBWs_UL_v1590__fr2__F2F1_cond.
Opaque BandNR__ext3O__channelBWs_UL_v1590__fr2__cond BandNR__ext3O__channelBWs_UL_v1590__fr2__Format.


Definition BandNR__ext3O__channelBWs_UL_v1590__Format_Type := Eval cbn in get_formats BandNR__ext3O__channelBWs_UL_v1590__list.
Definition BandNR__ext3O__channelBWs_UL_v1590__Format_list : BandNR__ext3O__channelBWs_UL_v1590__Format_Type :=
  (BandNR__ext3O__channelBWs_UL_v1590__fr1__Format, (BandNR__ext3O__channelBWs_UL_v1590__fr2__Format, unit__Format)).
Definition BandNR__ext3O__channelBWs_UL_v1590__list__Format := Eval compute in choice_format BandNR__ext3O__channelBWs_UL_v1590__list BandNR__ext3O__channelBWs_UL_v1590__len_helper1 BandNR__ext3O__channelBWs_UL_v1590__len_helper2  BandNR__ext3O__channelBWs_UL_v1590__Format_list.
Definition BandNR__ext3O__channelBWs_UL_v1590__F1 (z : BandNR__ext3O__channelBWs_UL_v1590__Type) : (choice BandNR__ext3O__channelBWs_UL_v1590__list) :=
  match z with
   | BandNR__ext3O__channelBWs_UL_v1590__fr1 t => existT _ 0 t
  | BandNR__ext3O__channelBWs_UL_v1590__fr2 t => existT _ 1 t
  end.
Definition BandNR__ext3O__channelBWs_UL_v1590__g := (fun n => typ_set (get_nth_typ BandNR__ext3O__channelBWs_UL_v1590__list n)).
Definition BandNR__ext3O__channelBWs_UL_v1590__F2 (y : choice BandNR__ext3O__channelBWs_UL_v1590__list) : BandNR__ext3O__channelBWs_UL_v1590__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandNR__ext3O__channelBWs_UL_v1590__g n -> BandNR__ext3O__channelBWs_UL_v1590__Type) with
    | 0 => fun (t : BandNR__ext3O__channelBWs_UL_v1590__fr1__Type) => BandNR__ext3O__channelBWs_UL_v1590__fr1 t 
    | 1 => fun (t : BandNR__ext3O__channelBWs_UL_v1590__fr2__Type) => BandNR__ext3O__channelBWs_UL_v1590__fr2 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandNR__ext3O__channelBWs_UL_v1590__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandNR__ext3O__channelBWs_UL_v1590__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandNR__ext3O__channelBWs_UL_v1590__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandNR__ext3O__channelBWs_UL_v1590__Type with end) n0
           end t0).

Lemma BandNR__ext3O__channelBWs_UL_v1590__helper2 :  forall (y : BandNR__ext3O__channelBWs_UL_v1590__Type), BandNR__ext3O__channelBWs_UL_v1590__cond y -> choice_cond BandNR__ext3O__channelBWs_UL_v1590__list (BandNR__ext3O__channelBWs_UL_v1590__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandNR__ext3O__channelBWs_UL_v1590__helper3 :  forall (y : BandNR__ext3O__channelBWs_UL_v1590__Type), BandNR__ext3O__channelBWs_UL_v1590__F2 (BandNR__ext3O__channelBWs_UL_v1590__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandNR__ext3O__channelBWs_UL_v1590__helper4 : (forall b : choice BandNR__ext3O__channelBWs_UL_v1590__list, choice_cond BandNR__ext3O__channelBWs_UL_v1590__list b -> BandNR__ext3O__channelBWs_UL_v1590__cond (BandNR__ext3O__channelBWs_UL_v1590__F2 b) /\ BandNR__ext3O__channelBWs_UL_v1590__F1 (BandNR__ext3O__channelBWs_UL_v1590__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandNR__ext3O__channelBWs_UL_v1590__F1 BandNR__ext3O__channelBWs_UL_v1590__F2.
Definition BandNR__ext3O__channelBWs_UL_v1590__Format : T_Format BandNR__ext3O__channelBWs_UL_v1590__Type BandNR__ext3O__channelBWs_UL_v1590__cond :=
  (* Eval compute in *) proj2_format BandNR__ext3O__channelBWs_UL_v1590__cond BandNR__ext3O__channelBWs_UL_v1590__list__Format BandNR__ext3O__channelBWs_UL_v1590__F1 BandNR__ext3O__channelBWs_UL_v1590__F2 BandNR__ext3O__channelBWs_UL_v1590__helper2 BandNR__ext3O__channelBWs_UL_v1590__helper3 BandNR__ext3O__channelBWs_UL_v1590__helper4.
Opaque BandNR__ext3O__channelBWs_UL_v1590__cond BandNR__ext3O__channelBWs_UL_v1590__Format.


Definition BandNR__ext3O__Format_Type := Eval cbn in seq_format_prod BandNR__ext3O__list.
Definition BandNR__ext3O__Format_list : BandNR__ext3O__Format_Type :=
  (BandNR__ext3O__channelBWs_DL_v1590__Format, (BandNR__ext3O__channelBWs_UL_v1590__Format, unit_format)).
Definition BandNR__ext3O__list__Format := (*Eval compute in *) seq_format BandNR__ext3O__list BandNR__ext3O__Format_list.
Definition BandNR__ext3O__F1 z :=
  (BandNR__ext3O__channelBWs_DL_v1590 z, (BandNR__ext3O__channelBWs_UL_v1590 z, tt)).
Definition BandNR__ext3O__F2 (y : seq_type BandNR__ext3O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext3O__Type i0 i1
  end.
Lemma BandNR__ext3O__F1F2_cond (z : BandNR__ext3O__Type)
  : BandNR__ext3O__cond z ->
  (seq_cond BandNR__ext3O__list (BandNR__ext3O__F1 z)).
intro H. unfold BandNR__ext3O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext3O__F1F2_cond2 (z : BandNR__ext3O__Type)
 : BandNR__ext3O__F2 (BandNR__ext3O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext3O__F2F1_cond (y : seq_type BandNR__ext3O__list)
  : seq_cond BandNR__ext3O__list y ->
 (BandNR__ext3O__cond (BandNR__ext3O__F2 y)) /\  BandNR__ext3O__F1 (BandNR__ext3O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext3O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext3O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext3O__Format : T_Format BandNR__ext3O__Type BandNR__ext3O__cond :=
        proj2_format  BandNR__ext3O__cond BandNR__ext3O__list__Format
    BandNR__ext3O__F1 BandNR__ext3O__F2 BandNR__ext3O__F1F2_cond  BandNR__ext3O__F1F2_cond2 BandNR__ext3O__F2F1_cond.
Opaque BandNR__ext3O__cond BandNR__ext3O__Format.

Definition BandNR__ext3__check_all_none (b : BandNR__ext3O__Type) : bool :=
match b with 
  | make__BandNR__ext3O__Type None None  => false 
  | _ => true 
 end.
Definition BandNR__ext3__Format : T_Format BandNR__ext3__Type BandNR__ext3__cond :=
  restrict_add_format BandNR__ext3__check_all_none BandNR__ext3O__Format.

Opaque BandNR__ext3__cond BandNR__ext3__Format.

Definition BandNR__ext4O__asymmetricBandwidthCombinationSet__Format : T_Format BandNR__ext4O__asymmetricBandwidthCombinationSet__Type BandNR__ext4O__asymmetricBandwidthCombinationSet__cond := (* Eval compute in *) bit_string_ranged_format 1 32 BandNR__ext4O__asymmetricBandwidthCombinationSet__helper1 BandNR__ext4O__asymmetricBandwidthCombinationSet__helper2.
Opaque BandNR__ext4O__asymmetricBandwidthCombinationSet__cond BandNR__ext4O__asymmetricBandwidthCombinationSet__Format.


Definition BandNR__ext4O__Format_Type := Eval cbn in seq_format_prod BandNR__ext4O__list.
Definition BandNR__ext4O__Format_list : BandNR__ext4O__Format_Type :=
  (BandNR__ext4O__asymmetricBandwidthCombinationSet__Format, unit_format).
Definition BandNR__ext4O__list__Format := (*Eval compute in *) seq_format BandNR__ext4O__list BandNR__ext4O__Format_list.
Definition BandNR__ext4O__F1 z :=
  (BandNR__ext4O__asymmetricBandwidthCombinationSet z, tt).
Definition BandNR__ext4O__F2 (y : seq_type BandNR__ext4O__list) :=
  match y with
  | (i0, _)=>
    make__BandNR__ext4O__Type i0
  end.
Lemma BandNR__ext4O__F1F2_cond (z : BandNR__ext4O__Type)
  : BandNR__ext4O__cond z ->
  (seq_cond BandNR__ext4O__list (BandNR__ext4O__F1 z)).
intro H. unfold BandNR__ext4O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext4O__F1F2_cond2 (z : BandNR__ext4O__Type)
 : BandNR__ext4O__F2 (BandNR__ext4O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext4O__F2F1_cond (y : seq_type BandNR__ext4O__list)
  : seq_cond BandNR__ext4O__list y ->
 (BandNR__ext4O__cond (BandNR__ext4O__F2 y)) /\  BandNR__ext4O__F1 (BandNR__ext4O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext4O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext4O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext4O__Format : T_Format BandNR__ext4O__Type BandNR__ext4O__cond :=
        proj2_format  BandNR__ext4O__cond BandNR__ext4O__list__Format
    BandNR__ext4O__F1 BandNR__ext4O__F2 BandNR__ext4O__F1F2_cond  BandNR__ext4O__F1F2_cond2 BandNR__ext4O__F2F1_cond.
Opaque BandNR__ext4O__cond BandNR__ext4O__Format.

Definition BandNR__ext4__check_all_none (b : BandNR__ext4O__Type) : bool :=
match b with 
  | make__BandNR__ext4O__Type None  => false 
  | _ => true 
 end.
Definition BandNR__ext4__Format : T_Format BandNR__ext4__Type BandNR__ext4__cond :=
  restrict_add_format BandNR__ext4__check_all_none BandNR__ext4O__Format.

Opaque BandNR__ext4__cond BandNR__ext4__Format.

Definition BandNR__ext5O__cancelOverlappingPUSCH_r16__Format : T_Format BandNR__ext5O__cancelOverlappingPUSCH_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__cancelOverlappingPUSCH_r16__nat__Format BandNR__ext5O__cancelOverlappingPUSCH_r16__F1 BandNR__ext5O__cancelOverlappingPUSCH_r16__F2 BandNR__ext5O__cancelOverlappingPUSCH_r16__F1F2 BandNR__ext5O__cancelOverlappingPUSCH_r16__F2F1.

Opaque BandNR__ext5O__cancelOverlappingPUSCH_r16__cond BandNR__ext5O__cancelOverlappingPUSCH_r16__Format.

Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__Format : T_Format Z BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__cond :=
 ranged_int_format (2) (6) BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__helper1 BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__helper2.

Opaque BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__cond BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__Format.

Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__Format : T_Format Z BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__cond :=
 ranged_int_format (1) (3) BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__helper1 BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__helper2.

Opaque BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__cond BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__Format.


Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Format_Type := Eval cbn in seq_format_prod BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list.
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Format_list : BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Format_Type :=
  (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16__Format, (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16__Format, unit_format)).
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list__Format := (*Eval compute in *) seq_format BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Format_list.
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1 z :=
  (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberPatterns_r16 z, (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__maxNumberNon_OverlapPatterns_r16 z, tt)).
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F2 (y : seq_type BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Type i0 i1
  end.
Lemma BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1F2_cond (z : BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Type)
  : BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond z ->
  (seq_cond BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1 z)).
intro H. unfold BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond in H. simpl. auto. Qed.
Lemma BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1F2_cond2 (z : BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Type)
 : BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F2 (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F2F1_cond (y : seq_type BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list)
  : seq_cond BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list y ->
 (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F2 y)) /\  BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1 (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Format : T_Format BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Type BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond :=
        proj2_format  BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__list__Format
    BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1 BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F2 BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1F2_cond  BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F1F2_cond2 BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__F2F1_cond.
Opaque BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__cond BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Format.

Definition BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Format : T_Format BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__nat__Format BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F1 BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F2 BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F1F2 BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__F2F1.

Opaque BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__cond BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Format.

Definition BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Format : T_Format BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__nat__Format BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F1 BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F2 BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F1F2 BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__F2F1.

Opaque BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__cond BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Format.

Definition BandNR__ext5O__oneSlotPeriodicTRS_r16__Format : T_Format BandNR__ext5O__oneSlotPeriodicTRS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__oneSlotPeriodicTRS_r16__nat__Format BandNR__ext5O__oneSlotPeriodicTRS_r16__F1 BandNR__ext5O__oneSlotPeriodicTRS_r16__F2 BandNR__ext5O__oneSlotPeriodicTRS_r16__F1F2 BandNR__ext5O__oneSlotPeriodicTRS_r16__F2F1.

Opaque BandNR__ext5O__oneSlotPeriodicTRS_r16__cond BandNR__ext5O__oneSlotPeriodicTRS_r16__Format.

Definition BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Format : T_Format BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__nat__Format BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F1 BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F2 BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F1F2 BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__F2F1.

Opaque BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__cond BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Format.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Format : T_Format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__nat__Format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F1 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F1F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__F2F1.

Opaque BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Format.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Format : T_Format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__nat__Format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F1 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F1F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__F2F1.

Opaque BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Format.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Format : T_Format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__nat__Format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F1 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F1F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__F2F1.

Opaque BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Format.


Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Format_Type := Eval cbn in seq_format_prod BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Format_list : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Format_Type :=
  (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz__Format, (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz__Format, (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz__Format, unit_format))).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list__Format := (*Eval compute in *) seq_format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Format_list.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1 z :=
  (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_15kHz z, (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_30kHz z, (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__scs_60kHz z, tt))).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F2 (y : seq_type BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type i0 i1 i2
  end.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1F2_cond (z : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type)
  : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond z ->
  (seq_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1 z)).
intro H. unfold BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond in H. simpl. auto. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1F2_cond2 (z : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type)
 : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F2 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F2F1_cond (y : seq_type BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list)
  : seq_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list y ->
 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F2 y)) /\  BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1 (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Format : T_Format BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond :=
        proj2_format  BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__list__Format
    BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1F2_cond  BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F1F2_cond2 BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__F2F1_cond.
Opaque BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Format.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Format : T_Format BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__nat__Format BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F1 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F1F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__F2F1.

Opaque BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Format.

Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Format : T_Format BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__nat__Format BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F1 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F1F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__F2F1.

Opaque BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Format.


Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Format_Type := Eval cbn in seq_format_prod BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Format_list : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Format_Type :=
  (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz__Format, (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz__Format, unit_format)).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list__Format := (*Eval compute in *) seq_format BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Format_list.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1 z :=
  (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_60kHz z, (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__scs_120kHz z, tt)).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F2 (y : seq_type BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type i0 i1
  end.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1F2_cond (z : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type)
  : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond z ->
  (seq_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1 z)).
intro H. unfold BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond in H. simpl. auto. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1F2_cond2 (z : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type)
 : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F2 (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F2F1_cond (y : seq_type BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list)
  : seq_cond BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list y ->
 (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F2 y)) /\  BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1 (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Format : T_Format BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond :=
        proj2_format  BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__list__Format
    BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F2 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1F2_cond  BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F1F2_cond2 BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__F2F1_cond.
Opaque BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__cond BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Format.


Definition BandNR__ext5O__channelBW_DL_IAB_r16__Format_Type := Eval cbn in get_formats BandNR__ext5O__channelBW_DL_IAB_r16__list.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__Format_list : BandNR__ext5O__channelBW_DL_IAB_r16__Format_Type :=
  (BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Format, (BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Format, unit__Format)).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__list__Format := Eval compute in choice_format BandNR__ext5O__channelBW_DL_IAB_r16__list BandNR__ext5O__channelBW_DL_IAB_r16__len_helper1 BandNR__ext5O__channelBW_DL_IAB_r16__len_helper2  BandNR__ext5O__channelBW_DL_IAB_r16__Format_list.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__F1 (z : BandNR__ext5O__channelBW_DL_IAB_r16__Type) : (choice BandNR__ext5O__channelBW_DL_IAB_r16__list) :=
  match z with
   | BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz t => existT _ 0 t
  | BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz t => existT _ 1 t
  end.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__g := (fun n => typ_set (get_nth_typ BandNR__ext5O__channelBW_DL_IAB_r16__list n)).
Definition BandNR__ext5O__channelBW_DL_IAB_r16__F2 (y : choice BandNR__ext5O__channelBW_DL_IAB_r16__list) : BandNR__ext5O__channelBW_DL_IAB_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandNR__ext5O__channelBW_DL_IAB_r16__g n -> BandNR__ext5O__channelBW_DL_IAB_r16__Type) with
    | 0 => fun (t : BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz__Type) => BandNR__ext5O__channelBW_DL_IAB_r16__fr1_100mhz t 
    | 1 => fun (t : BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz__Type) => BandNR__ext5O__channelBW_DL_IAB_r16__fr2_200mhz t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandNR__ext5O__channelBW_DL_IAB_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandNR__ext5O__channelBW_DL_IAB_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandNR__ext5O__channelBW_DL_IAB_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandNR__ext5O__channelBW_DL_IAB_r16__Type with end) n0
           end t0).

Lemma BandNR__ext5O__channelBW_DL_IAB_r16__helper2 :  forall (y : BandNR__ext5O__channelBW_DL_IAB_r16__Type), BandNR__ext5O__channelBW_DL_IAB_r16__cond y -> choice_cond BandNR__ext5O__channelBW_DL_IAB_r16__list (BandNR__ext5O__channelBW_DL_IAB_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandNR__ext5O__channelBW_DL_IAB_r16__helper3 :  forall (y : BandNR__ext5O__channelBW_DL_IAB_r16__Type), BandNR__ext5O__channelBW_DL_IAB_r16__F2 (BandNR__ext5O__channelBW_DL_IAB_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandNR__ext5O__channelBW_DL_IAB_r16__helper4 : (forall b : choice BandNR__ext5O__channelBW_DL_IAB_r16__list, choice_cond BandNR__ext5O__channelBW_DL_IAB_r16__list b -> BandNR__ext5O__channelBW_DL_IAB_r16__cond (BandNR__ext5O__channelBW_DL_IAB_r16__F2 b) /\ BandNR__ext5O__channelBW_DL_IAB_r16__F1 (BandNR__ext5O__channelBW_DL_IAB_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandNR__ext5O__channelBW_DL_IAB_r16__F1 BandNR__ext5O__channelBW_DL_IAB_r16__F2.
Definition BandNR__ext5O__channelBW_DL_IAB_r16__Format : T_Format BandNR__ext5O__channelBW_DL_IAB_r16__Type BandNR__ext5O__channelBW_DL_IAB_r16__cond :=
  (* Eval compute in *) proj2_format BandNR__ext5O__channelBW_DL_IAB_r16__cond BandNR__ext5O__channelBW_DL_IAB_r16__list__Format BandNR__ext5O__channelBW_DL_IAB_r16__F1 BandNR__ext5O__channelBW_DL_IAB_r16__F2 BandNR__ext5O__channelBW_DL_IAB_r16__helper2 BandNR__ext5O__channelBW_DL_IAB_r16__helper3 BandNR__ext5O__channelBW_DL_IAB_r16__helper4.
Opaque BandNR__ext5O__channelBW_DL_IAB_r16__cond BandNR__ext5O__channelBW_DL_IAB_r16__Format.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Format : T_Format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__nat__Format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F1 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F1F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__F2F1.

Opaque BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Format.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Format : T_Format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__nat__Format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F1 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F1F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__F2F1.

Opaque BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Format.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Format : T_Format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__nat__Format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F1 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F1F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__F2F1.

Opaque BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Format.


Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Format_Type := Eval cbn in seq_format_prod BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Format_list : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Format_Type :=
  (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz__Format, (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz__Format, (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz__Format, unit_format))).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list__Format := (*Eval compute in *) seq_format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Format_list.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1 z :=
  (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_15kHz z, (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_30kHz z, (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__scs_60kHz z, tt))).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F2 (y : seq_type BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type i0 i1 i2
  end.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1F2_cond (z : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type)
  : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond z ->
  (seq_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1 z)).
intro H. unfold BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond in H. simpl. auto. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1F2_cond2 (z : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type)
 : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F2 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F2F1_cond (y : seq_type BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list)
  : seq_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list y ->
 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F2 y)) /\  BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1 (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Format : T_Format BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond :=
        proj2_format  BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__list__Format
    BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1F2_cond  BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F1F2_cond2 BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__F2F1_cond.
Opaque BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Format.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Format : T_Format BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__nat__Format BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F1 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F1F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__F2F1.

Opaque BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Format.

Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Format : T_Format BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__nat__Format BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F1 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F1F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__F2F1.

Opaque BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Format.


Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Format_Type := Eval cbn in seq_format_prod BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Format_list : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Format_Type :=
  (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz__Format, (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz__Format, unit_format)).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list__Format := (*Eval compute in *) seq_format BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Format_list.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1 z :=
  (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_60kHz z, (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__scs_120kHz z, tt)).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F2 (y : seq_type BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type i0 i1
  end.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1F2_cond (z : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type)
  : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond z ->
  (seq_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1 z)).
intro H. unfold BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond in H. simpl. auto. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1F2_cond2 (z : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type)
 : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F2 (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F2F1_cond (y : seq_type BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list)
  : seq_cond BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list y ->
 (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F2 y)) /\  BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1 (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Format : T_Format BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond :=
        proj2_format  BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__list__Format
    BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F2 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1F2_cond  BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F1F2_cond2 BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__F2F1_cond.
Opaque BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__cond BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Format.


Definition BandNR__ext5O__channelBW_UL_IAB_r16__Format_Type := Eval cbn in get_formats BandNR__ext5O__channelBW_UL_IAB_r16__list.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__Format_list : BandNR__ext5O__channelBW_UL_IAB_r16__Format_Type :=
  (BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Format, (BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Format, unit__Format)).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__list__Format := Eval compute in choice_format BandNR__ext5O__channelBW_UL_IAB_r16__list BandNR__ext5O__channelBW_UL_IAB_r16__len_helper1 BandNR__ext5O__channelBW_UL_IAB_r16__len_helper2  BandNR__ext5O__channelBW_UL_IAB_r16__Format_list.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__F1 (z : BandNR__ext5O__channelBW_UL_IAB_r16__Type) : (choice BandNR__ext5O__channelBW_UL_IAB_r16__list) :=
  match z with
   | BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz t => existT _ 0 t
  | BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz t => existT _ 1 t
  end.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__g := (fun n => typ_set (get_nth_typ BandNR__ext5O__channelBW_UL_IAB_r16__list n)).
Definition BandNR__ext5O__channelBW_UL_IAB_r16__F2 (y : choice BandNR__ext5O__channelBW_UL_IAB_r16__list) : BandNR__ext5O__channelBW_UL_IAB_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandNR__ext5O__channelBW_UL_IAB_r16__g n -> BandNR__ext5O__channelBW_UL_IAB_r16__Type) with
    | 0 => fun (t : BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz__Type) => BandNR__ext5O__channelBW_UL_IAB_r16__fr1_100mhz t 
    | 1 => fun (t : BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz__Type) => BandNR__ext5O__channelBW_UL_IAB_r16__fr2_200mhz t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandNR__ext5O__channelBW_UL_IAB_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandNR__ext5O__channelBW_UL_IAB_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandNR__ext5O__channelBW_UL_IAB_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandNR__ext5O__channelBW_UL_IAB_r16__Type with end) n0
           end t0).

Lemma BandNR__ext5O__channelBW_UL_IAB_r16__helper2 :  forall (y : BandNR__ext5O__channelBW_UL_IAB_r16__Type), BandNR__ext5O__channelBW_UL_IAB_r16__cond y -> choice_cond BandNR__ext5O__channelBW_UL_IAB_r16__list (BandNR__ext5O__channelBW_UL_IAB_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandNR__ext5O__channelBW_UL_IAB_r16__helper3 :  forall (y : BandNR__ext5O__channelBW_UL_IAB_r16__Type), BandNR__ext5O__channelBW_UL_IAB_r16__F2 (BandNR__ext5O__channelBW_UL_IAB_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandNR__ext5O__channelBW_UL_IAB_r16__helper4 : (forall b : choice BandNR__ext5O__channelBW_UL_IAB_r16__list, choice_cond BandNR__ext5O__channelBW_UL_IAB_r16__list b -> BandNR__ext5O__channelBW_UL_IAB_r16__cond (BandNR__ext5O__channelBW_UL_IAB_r16__F2 b) /\ BandNR__ext5O__channelBW_UL_IAB_r16__F1 (BandNR__ext5O__channelBW_UL_IAB_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandNR__ext5O__channelBW_UL_IAB_r16__F1 BandNR__ext5O__channelBW_UL_IAB_r16__F2.
Definition BandNR__ext5O__channelBW_UL_IAB_r16__Format : T_Format BandNR__ext5O__channelBW_UL_IAB_r16__Type BandNR__ext5O__channelBW_UL_IAB_r16__cond :=
  (* Eval compute in *) proj2_format BandNR__ext5O__channelBW_UL_IAB_r16__cond BandNR__ext5O__channelBW_UL_IAB_r16__list__Format BandNR__ext5O__channelBW_UL_IAB_r16__F1 BandNR__ext5O__channelBW_UL_IAB_r16__F2 BandNR__ext5O__channelBW_UL_IAB_r16__helper2 BandNR__ext5O__channelBW_UL_IAB_r16__helper3 BandNR__ext5O__channelBW_UL_IAB_r16__helper4.
Opaque BandNR__ext5O__channelBW_UL_IAB_r16__cond BandNR__ext5O__channelBW_UL_IAB_r16__Format.

Definition BandNR__ext5O__rasterShift7dot5_IAB_r16__Format : T_Format BandNR__ext5O__rasterShift7dot5_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__rasterShift7dot5_IAB_r16__nat__Format BandNR__ext5O__rasterShift7dot5_IAB_r16__F1 BandNR__ext5O__rasterShift7dot5_IAB_r16__F2 BandNR__ext5O__rasterShift7dot5_IAB_r16__F1F2 BandNR__ext5O__rasterShift7dot5_IAB_r16__F2F1.

Opaque BandNR__ext5O__rasterShift7dot5_IAB_r16__cond BandNR__ext5O__rasterShift7dot5_IAB_r16__Format.

Definition BandNR__ext5O__ue_PowerClass_v1610__Format : T_Format BandNR__ext5O__ue_PowerClass_v1610__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__ue_PowerClass_v1610__nat__Format BandNR__ext5O__ue_PowerClass_v1610__F1 BandNR__ext5O__ue_PowerClass_v1610__F2 BandNR__ext5O__ue_PowerClass_v1610__F1F2 BandNR__ext5O__ue_PowerClass_v1610__F2F1.

Opaque BandNR__ext5O__ue_PowerClass_v1610__cond BandNR__ext5O__ue_PowerClass_v1610__Format.

Definition BandNR__ext5O__condHandover_r16__Format : T_Format BandNR__ext5O__condHandover_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__condHandover_r16__nat__Format BandNR__ext5O__condHandover_r16__F1 BandNR__ext5O__condHandover_r16__F2 BandNR__ext5O__condHandover_r16__F1F2 BandNR__ext5O__condHandover_r16__F2F1.

Opaque BandNR__ext5O__condHandover_r16__cond BandNR__ext5O__condHandover_r16__Format.

Definition BandNR__ext5O__condHandoverFailure_r16__Format : T_Format BandNR__ext5O__condHandoverFailure_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__condHandoverFailure_r16__nat__Format BandNR__ext5O__condHandoverFailure_r16__F1 BandNR__ext5O__condHandoverFailure_r16__F2 BandNR__ext5O__condHandoverFailure_r16__F1F2 BandNR__ext5O__condHandoverFailure_r16__F2F1.

Opaque BandNR__ext5O__condHandoverFailure_r16__cond BandNR__ext5O__condHandoverFailure_r16__Format.

Definition BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Format : T_Format BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__condHandoverTwoTriggerEvents_r16__nat__Format BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F1 BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F2 BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F1F2 BandNR__ext5O__condHandoverTwoTriggerEvents_r16__F2F1.

Opaque BandNR__ext5O__condHandoverTwoTriggerEvents_r16__cond BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Format.

Definition BandNR__ext5O__condPSCellChange_r16__Format : T_Format BandNR__ext5O__condPSCellChange_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__condPSCellChange_r16__nat__Format BandNR__ext5O__condPSCellChange_r16__F1 BandNR__ext5O__condPSCellChange_r16__F2 BandNR__ext5O__condPSCellChange_r16__F1F2 BandNR__ext5O__condPSCellChange_r16__F2F1.

Opaque BandNR__ext5O__condPSCellChange_r16__cond BandNR__ext5O__condPSCellChange_r16__Format.

Definition BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Format : T_Format BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__nat__Format BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F1 BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F2 BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F1F2 BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__F2F1.

Opaque BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__cond BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Format.

Definition BandNR__ext5O__mpr_PowerBoost_FR2_r16__Format : T_Format BandNR__ext5O__mpr_PowerBoost_FR2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__mpr_PowerBoost_FR2_r16__nat__Format BandNR__ext5O__mpr_PowerBoost_FR2_r16__F1 BandNR__ext5O__mpr_PowerBoost_FR2_r16__F2 BandNR__ext5O__mpr_PowerBoost_FR2_r16__F1F2 BandNR__ext5O__mpr_PowerBoost_FR2_r16__F2F1.

Opaque BandNR__ext5O__mpr_PowerBoost_FR2_r16__cond BandNR__ext5O__mpr_PowerBoost_FR2_r16__Format.

Definition BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Format : T_Format BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__nat__Format BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F1 BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F2 BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F1F2 BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__F2F1.

Opaque BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__cond BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Format.

Definition BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__Format : T_Format Z BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__cond :=
 ranged_int_format (2) (32) BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__helper1 BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__helper2.

Opaque BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__cond BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__Format.


Definition BandNR__ext5O__activeConfiguredGrant_r16__Format_Type := Eval cbn in seq_format_prod BandNR__ext5O__activeConfiguredGrant_r16__list.
Definition BandNR__ext5O__activeConfiguredGrant_r16__Format_list : BandNR__ext5O__activeConfiguredGrant_r16__Format_Type :=
  (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16__Format, (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16__Format, unit_format)).
Definition BandNR__ext5O__activeConfiguredGrant_r16__list__Format := (*Eval compute in *) seq_format BandNR__ext5O__activeConfiguredGrant_r16__list BandNR__ext5O__activeConfiguredGrant_r16__Format_list.
Definition BandNR__ext5O__activeConfiguredGrant_r16__F1 z :=
  (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsPerBWP_r16 z, (BandNR__ext5O__activeConfiguredGrant_r16__maxNumberConfigsAllCC_r16 z, tt)).
Definition BandNR__ext5O__activeConfiguredGrant_r16__F2 (y : seq_type BandNR__ext5O__activeConfiguredGrant_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext5O__activeConfiguredGrant_r16__Type i0 i1
  end.
Lemma BandNR__ext5O__activeConfiguredGrant_r16__F1F2_cond (z : BandNR__ext5O__activeConfiguredGrant_r16__Type)
  : BandNR__ext5O__activeConfiguredGrant_r16__cond z ->
  (seq_cond BandNR__ext5O__activeConfiguredGrant_r16__list (BandNR__ext5O__activeConfiguredGrant_r16__F1 z)).
intro H. unfold BandNR__ext5O__activeConfiguredGrant_r16__cond in H. simpl. auto. Qed.
Lemma BandNR__ext5O__activeConfiguredGrant_r16__F1F2_cond2 (z : BandNR__ext5O__activeConfiguredGrant_r16__Type)
 : BandNR__ext5O__activeConfiguredGrant_r16__F2 (BandNR__ext5O__activeConfiguredGrant_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext5O__activeConfiguredGrant_r16__F2F1_cond (y : seq_type BandNR__ext5O__activeConfiguredGrant_r16__list)
  : seq_cond BandNR__ext5O__activeConfiguredGrant_r16__list y ->
 (BandNR__ext5O__activeConfiguredGrant_r16__cond (BandNR__ext5O__activeConfiguredGrant_r16__F2 y)) /\  BandNR__ext5O__activeConfiguredGrant_r16__F1 (BandNR__ext5O__activeConfiguredGrant_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext5O__activeConfiguredGrant_r16__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext5O__activeConfiguredGrant_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext5O__activeConfiguredGrant_r16__Format : T_Format BandNR__ext5O__activeConfiguredGrant_r16__Type BandNR__ext5O__activeConfiguredGrant_r16__cond :=
        proj2_format  BandNR__ext5O__activeConfiguredGrant_r16__cond BandNR__ext5O__activeConfiguredGrant_r16__list__Format
    BandNR__ext5O__activeConfiguredGrant_r16__F1 BandNR__ext5O__activeConfiguredGrant_r16__F2 BandNR__ext5O__activeConfiguredGrant_r16__F1F2_cond  BandNR__ext5O__activeConfiguredGrant_r16__F1F2_cond2 BandNR__ext5O__activeConfiguredGrant_r16__F2F1_cond.
Opaque BandNR__ext5O__activeConfiguredGrant_r16__cond BandNR__ext5O__activeConfiguredGrant_r16__Format.

Definition BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Format : T_Format BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__nat__Format BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F1 BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F2 BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F1F2 BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__F2F1.

Opaque BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__cond BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Format.

Definition BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__Format : T_Format Z BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__cond :=
 ranged_int_format (1) (8) BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__helper1 BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__helper2.

Opaque BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__cond BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__Format.

Definition BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__Format : T_Format Z BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__cond :=
 ranged_int_format (2) (32) BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__helper1 BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__helper2.

Opaque BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__cond BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__Format.


Definition BandNR__ext5O__sps_r16__Format_Type := Eval cbn in seq_format_prod BandNR__ext5O__sps_r16__list.
Definition BandNR__ext5O__sps_r16__Format_list : BandNR__ext5O__sps_r16__Format_Type :=
  (BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16__Format, (BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16__Format, unit_format)).
Definition BandNR__ext5O__sps_r16__list__Format := (*Eval compute in *) seq_format BandNR__ext5O__sps_r16__list BandNR__ext5O__sps_r16__Format_list.
Definition BandNR__ext5O__sps_r16__F1 z :=
  (BandNR__ext5O__sps_r16__maxNumberConfigsPerBWP_r16 z, (BandNR__ext5O__sps_r16__maxNumberConfigsAllCC_r16 z, tt)).
Definition BandNR__ext5O__sps_r16__F2 (y : seq_type BandNR__ext5O__sps_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext5O__sps_r16__Type i0 i1
  end.
Lemma BandNR__ext5O__sps_r16__F1F2_cond (z : BandNR__ext5O__sps_r16__Type)
  : BandNR__ext5O__sps_r16__cond z ->
  (seq_cond BandNR__ext5O__sps_r16__list (BandNR__ext5O__sps_r16__F1 z)).
intro H. unfold BandNR__ext5O__sps_r16__cond in H. simpl. auto. Qed.
Lemma BandNR__ext5O__sps_r16__F1F2_cond2 (z : BandNR__ext5O__sps_r16__Type)
 : BandNR__ext5O__sps_r16__F2 (BandNR__ext5O__sps_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext5O__sps_r16__F2F1_cond (y : seq_type BandNR__ext5O__sps_r16__list)
  : seq_cond BandNR__ext5O__sps_r16__list y ->
 (BandNR__ext5O__sps_r16__cond (BandNR__ext5O__sps_r16__F2 y)) /\  BandNR__ext5O__sps_r16__F1 (BandNR__ext5O__sps_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext5O__sps_r16__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext5O__sps_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext5O__sps_r16__Format : T_Format BandNR__ext5O__sps_r16__Type BandNR__ext5O__sps_r16__cond :=
        proj2_format  BandNR__ext5O__sps_r16__cond BandNR__ext5O__sps_r16__list__Format
    BandNR__ext5O__sps_r16__F1 BandNR__ext5O__sps_r16__F2 BandNR__ext5O__sps_r16__F1F2_cond  BandNR__ext5O__sps_r16__F1F2_cond2 BandNR__ext5O__sps_r16__F2F1_cond.
Opaque BandNR__ext5O__sps_r16__cond BandNR__ext5O__sps_r16__Format.

Definition BandNR__ext5O__jointReleaseSPS_r16__Format : T_Format BandNR__ext5O__jointReleaseSPS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__jointReleaseSPS_r16__nat__Format BandNR__ext5O__jointReleaseSPS_r16__F1 BandNR__ext5O__jointReleaseSPS_r16__F2 BandNR__ext5O__jointReleaseSPS_r16__F1F2 BandNR__ext5O__jointReleaseSPS_r16__F2F1.

Opaque BandNR__ext5O__jointReleaseSPS_r16__cond BandNR__ext5O__jointReleaseSPS_r16__Format.

Definition BandNR__ext5O__simulSRS_TransWithinBand_r16__Format : T_Format BandNR__ext5O__simulSRS_TransWithinBand_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__simulSRS_TransWithinBand_r16__nat__Format BandNR__ext5O__simulSRS_TransWithinBand_r16__F1 BandNR__ext5O__simulSRS_TransWithinBand_r16__F2 BandNR__ext5O__simulSRS_TransWithinBand_r16__F1F2 BandNR__ext5O__simulSRS_TransWithinBand_r16__F2F1.

Opaque BandNR__ext5O__simulSRS_TransWithinBand_r16__cond BandNR__ext5O__simulSRS_TransWithinBand_r16__Format.

Definition BandNR__ext5O__trs_AdditionalBandwidth_r16__Format : T_Format BandNR__ext5O__trs_AdditionalBandwidth_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__trs_AdditionalBandwidth_r16__nat__Format BandNR__ext5O__trs_AdditionalBandwidth_r16__F1 BandNR__ext5O__trs_AdditionalBandwidth_r16__F2 BandNR__ext5O__trs_AdditionalBandwidth_r16__F1F2 BandNR__ext5O__trs_AdditionalBandwidth_r16__F2F1.

Opaque BandNR__ext5O__trs_AdditionalBandwidth_r16__cond BandNR__ext5O__trs_AdditionalBandwidth_r16__Format.

Definition BandNR__ext5O__handoverIntraF_IAB_r16__Format : T_Format BandNR__ext5O__handoverIntraF_IAB_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext5O__handoverIntraF_IAB_r16__nat__Format BandNR__ext5O__handoverIntraF_IAB_r16__F1 BandNR__ext5O__handoverIntraF_IAB_r16__F2 BandNR__ext5O__handoverIntraF_IAB_r16__F1F2 BandNR__ext5O__handoverIntraF_IAB_r16__F2F1.

Opaque BandNR__ext5O__handoverIntraF_IAB_r16__cond BandNR__ext5O__handoverIntraF_IAB_r16__Format.


Definition BandNR__ext5O__Format_Type := Eval cbn in seq_format_prod BandNR__ext5O__list.
Definition BandNR__ext5O__Format_list : BandNR__ext5O__Format_Type :=
  (SharedSpectrumChAccessParamsPerBand_r16__Format, (BandNR__ext5O__cancelOverlappingPUSCH_r16__Format, (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16__Format, (BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16__Format, (BandNR__ext5O__pdsch_MappingTypeB_Alt_r16__Format, (BandNR__ext5O__oneSlotPeriodicTRS_r16__Format, (OLPC_SRS_Pos_r16__Format, (SpatialRelationsSRS_Pos_r16__Format, (BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16__Format, (BandNR__ext5O__channelBW_DL_IAB_r16__Format, (BandNR__ext5O__channelBW_UL_IAB_r16__Format, (BandNR__ext5O__rasterShift7dot5_IAB_r16__Format, (BandNR__ext5O__ue_PowerClass_v1610__Format, (BandNR__ext5O__condHandover_r16__Format, (BandNR__ext5O__condHandoverFailure_r16__Format, (BandNR__ext5O__condHandoverTwoTriggerEvents_r16__Format, (BandNR__ext5O__condPSCellChange_r16__Format, (BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16__Format, (BandNR__ext5O__mpr_PowerBoost_FR2_r16__Format, (BandNR__ext5O__activeConfiguredGrant_r16__Format, (BandNR__ext5O__jointReleaseConfiguredGrantType2_r16__Format, (BandNR__ext5O__sps_r16__Format, (BandNR__ext5O__jointReleaseSPS_r16__Format, (BandNR__ext5O__simulSRS_TransWithinBand_r16__Format, (BandNR__ext5O__trs_AdditionalBandwidth_r16__Format, (BandNR__ext5O__handoverIntraF_IAB_r16__Format, unit_format)))))))))))))))))))))))))).
Definition BandNR__ext5O__list__Format := (*Eval compute in *) seq_format BandNR__ext5O__list BandNR__ext5O__Format_list.
Definition BandNR__ext5O__F1 z :=
  (BandNR__ext5O__sharedSpectrumChAccessParamsPerBand_r16 z, (BandNR__ext5O__cancelOverlappingPUSCH_r16 z, (BandNR__ext5O__multipleRateMatchingEUTRA_CRS_r16 z, (BandNR__ext5O__overlapRateMatchingEUTRA_CRS_r16 z, (BandNR__ext5O__pdsch_MappingTypeB_Alt_r16 z, (BandNR__ext5O__oneSlotPeriodicTRS_r16 z, (BandNR__ext5O__olpc_SRS_Pos_r16 z, (BandNR__ext5O__spatialRelationsSRS_Pos_r16 z, (BandNR__ext5O__simulSRS_MIMO_TransWithinBand_r16 z, (BandNR__ext5O__channelBW_DL_IAB_r16 z, (BandNR__ext5O__channelBW_UL_IAB_r16 z, (BandNR__ext5O__rasterShift7dot5_IAB_r16 z, (BandNR__ext5O__ue_PowerClass_v1610 z, (BandNR__ext5O__condHandover_r16 z, (BandNR__ext5O__condHandoverFailure_r16 z, (BandNR__ext5O__condHandoverTwoTriggerEvents_r16 z, (BandNR__ext5O__condPSCellChange_r16 z, (BandNR__ext5O__condPSCellChangeTwoTriggerEvents_r16 z, (BandNR__ext5O__mpr_PowerBoost_FR2_r16 z, (BandNR__ext5O__activeConfiguredGrant_r16 z, (BandNR__ext5O__jointReleaseConfiguredGrantType2_r16 z, (BandNR__ext5O__sps_r16 z, (BandNR__ext5O__jointReleaseSPS_r16 z, (BandNR__ext5O__simulSRS_TransWithinBand_r16 z, (BandNR__ext5O__trs_AdditionalBandwidth_r16 z, (BandNR__ext5O__handoverIntraF_IAB_r16 z, tt)))))))))))))))))))))))))).
Definition BandNR__ext5O__F2 (y : seq_type BandNR__ext5O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, (i24, (i25, _))))))))))))))))))))))))))=>
    make__BandNR__ext5O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25
  end.
Lemma BandNR__ext5O__F1F2_cond (z : BandNR__ext5O__Type)
  : BandNR__ext5O__cond z ->
  (seq_cond BandNR__ext5O__list (BandNR__ext5O__F1 z)).
intro H. unfold BandNR__ext5O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext5O__F1F2_cond2 (z : BandNR__ext5O__Type)
 : BandNR__ext5O__F2 (BandNR__ext5O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext5O__F2F1_cond (y : seq_type BandNR__ext5O__list)
  : seq_cond BandNR__ext5O__list y ->
 (BandNR__ext5O__cond (BandNR__ext5O__F2 y)) /\  BandNR__ext5O__F1 (BandNR__ext5O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext5O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext5O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext5O__Format : T_Format BandNR__ext5O__Type BandNR__ext5O__cond :=
        proj2_format  BandNR__ext5O__cond BandNR__ext5O__list__Format
    BandNR__ext5O__F1 BandNR__ext5O__F2 BandNR__ext5O__F1F2_cond  BandNR__ext5O__F1F2_cond2 BandNR__ext5O__F2F1_cond.
Opaque BandNR__ext5O__cond BandNR__ext5O__Format.

Definition BandNR__ext5__check_all_none (b : BandNR__ext5O__Type) : bool :=
match b with 
  | make__BandNR__ext5O__Type None None None None None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition BandNR__ext5__Format : T_Format BandNR__ext5__Type BandNR__ext5__cond :=
  restrict_add_format BandNR__ext5__check_all_none BandNR__ext5O__Format.

Opaque BandNR__ext5__cond BandNR__ext5__Format.


Definition BandNR__ext6O__Format_Type := Eval cbn in seq_format_prod BandNR__ext6O__list.
Definition BandNR__ext6O__Format_list : BandNR__ext6O__Format_Type :=
  (SimulSRS_ForAntennaSwitching_r16__Format, (SharedSpectrumChAccessParamsPerBand_v1630__Format, unit_format)).
Definition BandNR__ext6O__list__Format := (*Eval compute in *) seq_format BandNR__ext6O__list BandNR__ext6O__Format_list.
Definition BandNR__ext6O__F1 z :=
  (BandNR__ext6O__simulTX_SRS_AntSwitchingIntraBandUL_CA_r16 z, (BandNR__ext6O__sharedSpectrumChAccessParamsPerBand_v1630 z, tt)).
Definition BandNR__ext6O__F2 (y : seq_type BandNR__ext6O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext6O__Type i0 i1
  end.
Lemma BandNR__ext6O__F1F2_cond (z : BandNR__ext6O__Type)
  : BandNR__ext6O__cond z ->
  (seq_cond BandNR__ext6O__list (BandNR__ext6O__F1 z)).
intro H. unfold BandNR__ext6O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext6O__F1F2_cond2 (z : BandNR__ext6O__Type)
 : BandNR__ext6O__F2 (BandNR__ext6O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext6O__F2F1_cond (y : seq_type BandNR__ext6O__list)
  : seq_cond BandNR__ext6O__list y ->
 (BandNR__ext6O__cond (BandNR__ext6O__F2 y)) /\  BandNR__ext6O__F1 (BandNR__ext6O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext6O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext6O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext6O__Format : T_Format BandNR__ext6O__Type BandNR__ext6O__cond :=
        proj2_format  BandNR__ext6O__cond BandNR__ext6O__list__Format
    BandNR__ext6O__F1 BandNR__ext6O__F2 BandNR__ext6O__F1F2_cond  BandNR__ext6O__F1F2_cond2 BandNR__ext6O__F2F1_cond.
Opaque BandNR__ext6O__cond BandNR__ext6O__Format.

Definition BandNR__ext6__check_all_none (b : BandNR__ext6O__Type) : bool :=
match b with 
  | make__BandNR__ext6O__Type None None  => false 
  | _ => true 
 end.
Definition BandNR__ext6__Format : T_Format BandNR__ext6__Type BandNR__ext6__cond :=
  restrict_add_format BandNR__ext6__check_all_none BandNR__ext6O__Format.

Opaque BandNR__ext6__cond BandNR__ext6__Format.

Definition BandNR__ext7O__handoverUTRA_FDD_r16__Format : T_Format BandNR__ext7O__handoverUTRA_FDD_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext7O__handoverUTRA_FDD_r16__nat__Format BandNR__ext7O__handoverUTRA_FDD_r16__F1 BandNR__ext7O__handoverUTRA_FDD_r16__F2 BandNR__ext7O__handoverUTRA_FDD_r16__F1F2 BandNR__ext7O__handoverUTRA_FDD_r16__F2F1.

Opaque BandNR__ext7O__handoverUTRA_FDD_r16__cond BandNR__ext7O__handoverUTRA_FDD_r16__Format.

Definition BandNR__ext7O__enhancedUL_TransientPeriod_r16__Format : T_Format BandNR__ext7O__enhancedUL_TransientPeriod_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext7O__enhancedUL_TransientPeriod_r16__nat__Format BandNR__ext7O__enhancedUL_TransientPeriod_r16__F1 BandNR__ext7O__enhancedUL_TransientPeriod_r16__F2 BandNR__ext7O__enhancedUL_TransientPeriod_r16__F1F2 BandNR__ext7O__enhancedUL_TransientPeriod_r16__F2F1.

Opaque BandNR__ext7O__enhancedUL_TransientPeriod_r16__cond BandNR__ext7O__enhancedUL_TransientPeriod_r16__Format.


Definition BandNR__ext7O__Format_Type := Eval cbn in seq_format_prod BandNR__ext7O__list.
Definition BandNR__ext7O__Format_list : BandNR__ext7O__Format_Type :=
  (BandNR__ext7O__handoverUTRA_FDD_r16__Format, (BandNR__ext7O__enhancedUL_TransientPeriod_r16__Format, (SharedSpectrumChAccessParamsPerBand_v1640__Format, unit_format))).
Definition BandNR__ext7O__list__Format := (*Eval compute in *) seq_format BandNR__ext7O__list BandNR__ext7O__Format_list.
Definition BandNR__ext7O__F1 z :=
  (BandNR__ext7O__handoverUTRA_FDD_r16 z, (BandNR__ext7O__enhancedUL_TransientPeriod_r16 z, (BandNR__ext7O__sharedSpectrumChAccessParamsPerBand_v1640 z, tt))).
Definition BandNR__ext7O__F2 (y : seq_type BandNR__ext7O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandNR__ext7O__Type i0 i1 i2
  end.
Lemma BandNR__ext7O__F1F2_cond (z : BandNR__ext7O__Type)
  : BandNR__ext7O__cond z ->
  (seq_cond BandNR__ext7O__list (BandNR__ext7O__F1 z)).
intro H. unfold BandNR__ext7O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext7O__F1F2_cond2 (z : BandNR__ext7O__Type)
 : BandNR__ext7O__F2 (BandNR__ext7O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext7O__F2F1_cond (y : seq_type BandNR__ext7O__list)
  : seq_cond BandNR__ext7O__list y ->
 (BandNR__ext7O__cond (BandNR__ext7O__F2 y)) /\  BandNR__ext7O__F1 (BandNR__ext7O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext7O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext7O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext7O__Format : T_Format BandNR__ext7O__Type BandNR__ext7O__cond :=
        proj2_format  BandNR__ext7O__cond BandNR__ext7O__list__Format
    BandNR__ext7O__F1 BandNR__ext7O__F2 BandNR__ext7O__F1F2_cond  BandNR__ext7O__F1F2_cond2 BandNR__ext7O__F2F1_cond.
Opaque BandNR__ext7O__cond BandNR__ext7O__Format.

Definition BandNR__ext7__check_all_none (b : BandNR__ext7O__Type) : bool :=
match b with 
  | make__BandNR__ext7O__Type None None None  => false 
  | _ => true 
 end.
Definition BandNR__ext7__Format : T_Format BandNR__ext7__Type BandNR__ext7__cond :=
  restrict_add_format BandNR__ext7__check_all_none BandNR__ext7O__Format.

Opaque BandNR__ext7__cond BandNR__ext7__Format.

Definition BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Format : T_Format BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__nat__Format BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F1 BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F2 BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F1F2 BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__F2F1.

Opaque BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__cond BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Format.

Definition BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Format : T_Format BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__nat__Format BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F1 BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F2 BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F1F2 BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__F2F1.

Opaque BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__cond BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Format.

Definition BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Format : T_Format BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__nat__Format BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F1 BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F2 BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F1F2 BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__F2F1.

Opaque BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__cond BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Format.

Definition BandNR__ext8O__configuredUL_GrantType1_v1650__Format : T_Format BandNR__ext8O__configuredUL_GrantType1_v1650__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext8O__configuredUL_GrantType1_v1650__nat__Format BandNR__ext8O__configuredUL_GrantType1_v1650__F1 BandNR__ext8O__configuredUL_GrantType1_v1650__F2 BandNR__ext8O__configuredUL_GrantType1_v1650__F1F2 BandNR__ext8O__configuredUL_GrantType1_v1650__F2F1.

Opaque BandNR__ext8O__configuredUL_GrantType1_v1650__cond BandNR__ext8O__configuredUL_GrantType1_v1650__Format.

Definition BandNR__ext8O__configuredUL_GrantType2_v1650__Format : T_Format BandNR__ext8O__configuredUL_GrantType2_v1650__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext8O__configuredUL_GrantType2_v1650__nat__Format BandNR__ext8O__configuredUL_GrantType2_v1650__F1 BandNR__ext8O__configuredUL_GrantType2_v1650__F2 BandNR__ext8O__configuredUL_GrantType2_v1650__F1F2 BandNR__ext8O__configuredUL_GrantType2_v1650__F2F1.

Opaque BandNR__ext8O__configuredUL_GrantType2_v1650__cond BandNR__ext8O__configuredUL_GrantType2_v1650__Format.


Definition BandNR__ext8O__Format_Type := Eval cbn in seq_format_prod BandNR__ext8O__list.
Definition BandNR__ext8O__Format_list : BandNR__ext8O__Format_Type :=
  (BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650__Format, (BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650__Format, (BandNR__ext8O__pusch_RepetitionMultiSlots_v1650__Format, (BandNR__ext8O__configuredUL_GrantType1_v1650__Format, (BandNR__ext8O__configuredUL_GrantType2_v1650__Format, (SharedSpectrumChAccessParamsPerBand_v1650__Format, unit_format)))))).
Definition BandNR__ext8O__list__Format := (*Eval compute in *) seq_format BandNR__ext8O__list BandNR__ext8O__Format_list.
Definition BandNR__ext8O__F1 z :=
  (BandNR__ext8O__type1_PUSCH_RepetitionMultiSlots_v1650 z, (BandNR__ext8O__type2_PUSCH_RepetitionMultiSlots_v1650 z, (BandNR__ext8O__pusch_RepetitionMultiSlots_v1650 z, (BandNR__ext8O__configuredUL_GrantType1_v1650 z, (BandNR__ext8O__configuredUL_GrantType2_v1650 z, (BandNR__ext8O__sharedSpectrumChAccessParamsPerBand_v1650 z, tt)))))).
Definition BandNR__ext8O__F2 (y : seq_type BandNR__ext8O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__BandNR__ext8O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma BandNR__ext8O__F1F2_cond (z : BandNR__ext8O__Type)
  : BandNR__ext8O__cond z ->
  (seq_cond BandNR__ext8O__list (BandNR__ext8O__F1 z)).
intro H. unfold BandNR__ext8O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext8O__F1F2_cond2 (z : BandNR__ext8O__Type)
 : BandNR__ext8O__F2 (BandNR__ext8O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext8O__F2F1_cond (y : seq_type BandNR__ext8O__list)
  : seq_cond BandNR__ext8O__list y ->
 (BandNR__ext8O__cond (BandNR__ext8O__F2 y)) /\  BandNR__ext8O__F1 (BandNR__ext8O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext8O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext8O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext8O__Format : T_Format BandNR__ext8O__Type BandNR__ext8O__cond :=
        proj2_format  BandNR__ext8O__cond BandNR__ext8O__list__Format
    BandNR__ext8O__F1 BandNR__ext8O__F2 BandNR__ext8O__F1F2_cond  BandNR__ext8O__F1F2_cond2 BandNR__ext8O__F2F1_cond.
Opaque BandNR__ext8O__cond BandNR__ext8O__Format.

Definition BandNR__ext8__check_all_none (b : BandNR__ext8O__Type) : bool :=
match b with 
  | make__BandNR__ext8O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition BandNR__ext8__Format : T_Format BandNR__ext8__Type BandNR__ext8__cond :=
  restrict_add_format BandNR__ext8__check_all_none BandNR__ext8O__Format.

Opaque BandNR__ext8__cond BandNR__ext8__Format.

Definition BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Format : T_Format BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__nat__Format BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F1 BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F2 BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F1F2 BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__F2F1.

Opaque BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__cond BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Format.

Definition BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Format : T_Format BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__nat__Format BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F1 BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F2 BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F1F2 BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__F2F1.

Opaque BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__cond BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Format.


Definition BandNR__ext9O__Format_Type := Eval cbn in seq_format_prod BandNR__ext9O__list.
Definition BandNR__ext9O__Format_list : BandNR__ext9O__Format_Type :=
  (BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660__Format, (BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660__Format, unit_format)).
Definition BandNR__ext9O__list__Format := (*Eval compute in *) seq_format BandNR__ext9O__list BandNR__ext9O__Format_list.
Definition BandNR__ext9O__F1 z :=
  (BandNR__ext9O__enhancedSkipUplinkTxConfigured_v1660 z, (BandNR__ext9O__enhancedSkipUplinkTxDynamic_v1660 z, tt)).
Definition BandNR__ext9O__F2 (y : seq_type BandNR__ext9O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext9O__Type i0 i1
  end.
Lemma BandNR__ext9O__F1F2_cond (z : BandNR__ext9O__Type)
  : BandNR__ext9O__cond z ->
  (seq_cond BandNR__ext9O__list (BandNR__ext9O__F1 z)).
intro H. unfold BandNR__ext9O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext9O__F1F2_cond2 (z : BandNR__ext9O__Type)
 : BandNR__ext9O__F2 (BandNR__ext9O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext9O__F2F1_cond (y : seq_type BandNR__ext9O__list)
  : seq_cond BandNR__ext9O__list y ->
 (BandNR__ext9O__cond (BandNR__ext9O__F2 y)) /\  BandNR__ext9O__F1 (BandNR__ext9O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext9O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext9O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext9O__Format : T_Format BandNR__ext9O__Type BandNR__ext9O__cond :=
        proj2_format  BandNR__ext9O__cond BandNR__ext9O__list__Format
    BandNR__ext9O__F1 BandNR__ext9O__F2 BandNR__ext9O__F1F2_cond  BandNR__ext9O__F1F2_cond2 BandNR__ext9O__F2F1_cond.
Opaque BandNR__ext9O__cond BandNR__ext9O__Format.

Definition BandNR__ext9__check_all_none (b : BandNR__ext9O__Type) : bool :=
match b with 
  | make__BandNR__ext9O__Type None None  => false 
  | _ => true 
 end.
Definition BandNR__ext9__Format : T_Format BandNR__ext9__Type BandNR__ext9__cond :=
  restrict_add_format BandNR__ext9__check_all_none BandNR__ext9O__Format.

Opaque BandNR__ext9__cond BandNR__ext9__Format.

Definition BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Format : T_Format BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__nat__Format BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F1 BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F2 BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F1F2 BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__F2F1.

Opaque BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__cond BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Format.

Definition BandNR__ext10O__txDiversity_r16__Format : T_Format BandNR__ext10O__txDiversity_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext10O__txDiversity_r16__nat__Format BandNR__ext10O__txDiversity_r16__F1 BandNR__ext10O__txDiversity_r16__F2 BandNR__ext10O__txDiversity_r16__F1F2 BandNR__ext10O__txDiversity_r16__F2F1.

Opaque BandNR__ext10O__txDiversity_r16__cond BandNR__ext10O__txDiversity_r16__Format.


Definition BandNR__ext10O__Format_Type := Eval cbn in seq_format_prod BandNR__ext10O__list.
Definition BandNR__ext10O__Format_list : BandNR__ext10O__Format_Type :=
  (BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16__Format, (BandNR__ext10O__txDiversity_r16__Format, unit_format)).
Definition BandNR__ext10O__list__Format := (*Eval compute in *) seq_format BandNR__ext10O__list BandNR__ext10O__Format_list.
Definition BandNR__ext10O__F1 z :=
  (BandNR__ext10O__maxUplinkDutyCycle_PC1dot5_MPE_FR1_r16 z, (BandNR__ext10O__txDiversity_r16 z, tt)).
Definition BandNR__ext10O__F2 (y : seq_type BandNR__ext10O__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext10O__Type i0 i1
  end.
Lemma BandNR__ext10O__F1F2_cond (z : BandNR__ext10O__Type)
  : BandNR__ext10O__cond z ->
  (seq_cond BandNR__ext10O__list (BandNR__ext10O__F1 z)).
intro H. unfold BandNR__ext10O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext10O__F1F2_cond2 (z : BandNR__ext10O__Type)
 : BandNR__ext10O__F2 (BandNR__ext10O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext10O__F2F1_cond (y : seq_type BandNR__ext10O__list)
  : seq_cond BandNR__ext10O__list y ->
 (BandNR__ext10O__cond (BandNR__ext10O__F2 y)) /\  BandNR__ext10O__F1 (BandNR__ext10O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext10O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext10O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext10O__Format : T_Format BandNR__ext10O__Type BandNR__ext10O__cond :=
        proj2_format  BandNR__ext10O__cond BandNR__ext10O__list__Format
    BandNR__ext10O__F1 BandNR__ext10O__F2 BandNR__ext10O__F1F2_cond  BandNR__ext10O__F1F2_cond2 BandNR__ext10O__F2F1_cond.
Opaque BandNR__ext10O__cond BandNR__ext10O__Format.

Definition BandNR__ext10__check_all_none (b : BandNR__ext10O__Type) : bool :=
match b with 
  | make__BandNR__ext10O__Type None None  => false 
  | _ => true 
 end.
Definition BandNR__ext10__Format : T_Format BandNR__ext10__Type BandNR__ext10__cond :=
  restrict_add_format BandNR__ext10__check_all_none BandNR__ext10O__Format.

Opaque BandNR__ext10__cond BandNR__ext10__Format.

Definition BandNR__ext11O__pdsch_1024QAM_FR1_r17__Format : T_Format BandNR__ext11O__pdsch_1024QAM_FR1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__pdsch_1024QAM_FR1_r17__nat__Format BandNR__ext11O__pdsch_1024QAM_FR1_r17__F1 BandNR__ext11O__pdsch_1024QAM_FR1_r17__F2 BandNR__ext11O__pdsch_1024QAM_FR1_r17__F1F2 BandNR__ext11O__pdsch_1024QAM_FR1_r17__F2F1.

Opaque BandNR__ext11O__pdsch_1024QAM_FR1_r17__cond BandNR__ext11O__pdsch_1024QAM_FR1_r17__Format.

Definition BandNR__ext11O__ue_PowerClass_v1700__Format : T_Format BandNR__ext11O__ue_PowerClass_v1700__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__ue_PowerClass_v1700__nat__Format BandNR__ext11O__ue_PowerClass_v1700__F1 BandNR__ext11O__ue_PowerClass_v1700__F2 BandNR__ext11O__ue_PowerClass_v1700__F1F2 BandNR__ext11O__ue_PowerClass_v1700__F2F1.

Opaque BandNR__ext11O__ue_PowerClass_v1700__cond BandNR__ext11O__ue_PowerClass_v1700__Format.

Definition BandNR__ext11O__rlm_Relaxation_r17__Format : T_Format BandNR__ext11O__rlm_Relaxation_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__rlm_Relaxation_r17__nat__Format BandNR__ext11O__rlm_Relaxation_r17__F1 BandNR__ext11O__rlm_Relaxation_r17__F2 BandNR__ext11O__rlm_Relaxation_r17__F1F2 BandNR__ext11O__rlm_Relaxation_r17__F2F1.

Opaque BandNR__ext11O__rlm_Relaxation_r17__cond BandNR__ext11O__rlm_Relaxation_r17__Format.

Definition BandNR__ext11O__bfd_Relaxation_r17__Format : T_Format BandNR__ext11O__bfd_Relaxation_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__bfd_Relaxation_r17__nat__Format BandNR__ext11O__bfd_Relaxation_r17__F1 BandNR__ext11O__bfd_Relaxation_r17__F2 BandNR__ext11O__bfd_Relaxation_r17__F1F2 BandNR__ext11O__bfd_Relaxation_r17__F2F1.

Opaque BandNR__ext11O__bfd_Relaxation_r17__cond BandNR__ext11O__bfd_Relaxation_r17__Format.

Definition BandNR__ext11O__cg_SDT_r17__Format : T_Format BandNR__ext11O__cg_SDT_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__cg_SDT_r17__nat__Format BandNR__ext11O__cg_SDT_r17__F1 BandNR__ext11O__cg_SDT_r17__F2 BandNR__ext11O__cg_SDT_r17__F1F2 BandNR__ext11O__cg_SDT_r17__F2F1.

Opaque BandNR__ext11O__cg_SDT_r17__cond BandNR__ext11O__cg_SDT_r17__Format.

Definition BandNR__ext11O__locationBasedCondHandover_r17__Format : T_Format BandNR__ext11O__locationBasedCondHandover_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__locationBasedCondHandover_r17__nat__Format BandNR__ext11O__locationBasedCondHandover_r17__F1 BandNR__ext11O__locationBasedCondHandover_r17__F2 BandNR__ext11O__locationBasedCondHandover_r17__F1F2 BandNR__ext11O__locationBasedCondHandover_r17__F2F1.

Opaque BandNR__ext11O__locationBasedCondHandover_r17__cond BandNR__ext11O__locationBasedCondHandover_r17__Format.

Definition BandNR__ext11O__timeBasedCondHandover_r17__Format : T_Format BandNR__ext11O__timeBasedCondHandover_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__timeBasedCondHandover_r17__nat__Format BandNR__ext11O__timeBasedCondHandover_r17__F1 BandNR__ext11O__timeBasedCondHandover_r17__F2 BandNR__ext11O__timeBasedCondHandover_r17__F1F2 BandNR__ext11O__timeBasedCondHandover_r17__F2F1.

Opaque BandNR__ext11O__timeBasedCondHandover_r17__cond BandNR__ext11O__timeBasedCondHandover_r17__Format.

Definition BandNR__ext11O__eventA4BasedCondHandover_r17__Format : T_Format BandNR__ext11O__eventA4BasedCondHandover_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__eventA4BasedCondHandover_r17__nat__Format BandNR__ext11O__eventA4BasedCondHandover_r17__F1 BandNR__ext11O__eventA4BasedCondHandover_r17__F2 BandNR__ext11O__eventA4BasedCondHandover_r17__F1F2 BandNR__ext11O__eventA4BasedCondHandover_r17__F2F1.

Opaque BandNR__ext11O__eventA4BasedCondHandover_r17__cond BandNR__ext11O__eventA4BasedCondHandover_r17__Format.

Definition BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Format : T_Format BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__nat__Format BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F1 BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F2 BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F1F2 BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__F2F1.

Opaque BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__cond BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Format.

Definition BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Format : T_Format BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__nat__Format BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F1 BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F2 BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F1F2 BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__F2F1.

Opaque BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__cond BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Format.

Definition BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Format : T_Format BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__nat__Format BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F1 BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F2 BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F1F2 BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__F2F1.

Opaque BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__cond BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Format.

Definition BandNR__ext11O__sssg_Switching_1BitInd_r17__Format : T_Format BandNR__ext11O__sssg_Switching_1BitInd_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__sssg_Switching_1BitInd_r17__nat__Format BandNR__ext11O__sssg_Switching_1BitInd_r17__F1 BandNR__ext11O__sssg_Switching_1BitInd_r17__F2 BandNR__ext11O__sssg_Switching_1BitInd_r17__F1F2 BandNR__ext11O__sssg_Switching_1BitInd_r17__F2F1.

Opaque BandNR__ext11O__sssg_Switching_1BitInd_r17__cond BandNR__ext11O__sssg_Switching_1BitInd_r17__Format.

Definition BandNR__ext11O__sssg_Switching_2BitInd_r17__Format : T_Format BandNR__ext11O__sssg_Switching_2BitInd_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__sssg_Switching_2BitInd_r17__nat__Format BandNR__ext11O__sssg_Switching_2BitInd_r17__F1 BandNR__ext11O__sssg_Switching_2BitInd_r17__F2 BandNR__ext11O__sssg_Switching_2BitInd_r17__F1F2 BandNR__ext11O__sssg_Switching_2BitInd_r17__F2F1.

Opaque BandNR__ext11O__sssg_Switching_2BitInd_r17__cond BandNR__ext11O__sssg_Switching_2BitInd_r17__Format.

Definition BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Format : T_Format BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__pdcch_SkippingWithSSSG_r17__nat__Format BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F1 BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F2 BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F1F2 BandNR__ext11O__pdcch_SkippingWithSSSG_r17__F2F1.

Opaque BandNR__ext11O__pdcch_SkippingWithSSSG_r17__cond BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Format.

Definition BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Format : T_Format BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__nat__Format BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F1 BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F2 BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F1F2 BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__F2F1.

Opaque BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__cond BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Format.

Definition BandNR__ext11O__uplinkPreCompensation_r17__Format : T_Format BandNR__ext11O__uplinkPreCompensation_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__uplinkPreCompensation_r17__nat__Format BandNR__ext11O__uplinkPreCompensation_r17__F1 BandNR__ext11O__uplinkPreCompensation_r17__F2 BandNR__ext11O__uplinkPreCompensation_r17__F1F2 BandNR__ext11O__uplinkPreCompensation_r17__F2F1.

Opaque BandNR__ext11O__uplinkPreCompensation_r17__cond BandNR__ext11O__uplinkPreCompensation_r17__Format.

Definition BandNR__ext11O__uplink_TA_Reporting_r17__Format : T_Format BandNR__ext11O__uplink_TA_Reporting_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__uplink_TA_Reporting_r17__nat__Format BandNR__ext11O__uplink_TA_Reporting_r17__F1 BandNR__ext11O__uplink_TA_Reporting_r17__F2 BandNR__ext11O__uplink_TA_Reporting_r17__F1F2 BandNR__ext11O__uplink_TA_Reporting_r17__F2F1.

Opaque BandNR__ext11O__uplink_TA_Reporting_r17__cond BandNR__ext11O__uplink_TA_Reporting_r17__Format.

Definition BandNR__ext11O__max_HARQ_ProcessNumber_r17__Format : T_Format BandNR__ext11O__max_HARQ_ProcessNumber_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__max_HARQ_ProcessNumber_r17__nat__Format BandNR__ext11O__max_HARQ_ProcessNumber_r17__F1 BandNR__ext11O__max_HARQ_ProcessNumber_r17__F2 BandNR__ext11O__max_HARQ_ProcessNumber_r17__F1F2 BandNR__ext11O__max_HARQ_ProcessNumber_r17__F2F1.

Opaque BandNR__ext11O__max_HARQ_ProcessNumber_r17__cond BandNR__ext11O__max_HARQ_ProcessNumber_r17__Format.

Definition BandNR__ext11O__type2_HARQ_Codebook_r17__Format : T_Format BandNR__ext11O__type2_HARQ_Codebook_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__type2_HARQ_Codebook_r17__nat__Format BandNR__ext11O__type2_HARQ_Codebook_r17__F1 BandNR__ext11O__type2_HARQ_Codebook_r17__F2 BandNR__ext11O__type2_HARQ_Codebook_r17__F1F2 BandNR__ext11O__type2_HARQ_Codebook_r17__F2F1.

Opaque BandNR__ext11O__type2_HARQ_Codebook_r17__cond BandNR__ext11O__type2_HARQ_Codebook_r17__Format.

Definition BandNR__ext11O__type1_HARQ_Codebook_r17__Format : T_Format BandNR__ext11O__type1_HARQ_Codebook_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__type1_HARQ_Codebook_r17__nat__Format BandNR__ext11O__type1_HARQ_Codebook_r17__F1 BandNR__ext11O__type1_HARQ_Codebook_r17__F2 BandNR__ext11O__type1_HARQ_Codebook_r17__F1F2 BandNR__ext11O__type1_HARQ_Codebook_r17__F2F1.

Opaque BandNR__ext11O__type1_HARQ_Codebook_r17__cond BandNR__ext11O__type1_HARQ_Codebook_r17__Format.

Definition BandNR__ext11O__type3_HARQ_Codebook_r17__Format : T_Format BandNR__ext11O__type3_HARQ_Codebook_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__type3_HARQ_Codebook_r17__nat__Format BandNR__ext11O__type3_HARQ_Codebook_r17__F1 BandNR__ext11O__type3_HARQ_Codebook_r17__F2 BandNR__ext11O__type3_HARQ_Codebook_r17__F1F2 BandNR__ext11O__type3_HARQ_Codebook_r17__F2F1.

Opaque BandNR__ext11O__type3_HARQ_Codebook_r17__cond BandNR__ext11O__type3_HARQ_Codebook_r17__Format.

Definition BandNR__ext11O__ue_specific_K_Offset_r17__Format : T_Format BandNR__ext11O__ue_specific_K_Offset_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__ue_specific_K_Offset_r17__nat__Format BandNR__ext11O__ue_specific_K_Offset_r17__F1 BandNR__ext11O__ue_specific_K_Offset_r17__F2 BandNR__ext11O__ue_specific_K_Offset_r17__F1F2 BandNR__ext11O__ue_specific_K_Offset_r17__F2F1.

Opaque BandNR__ext11O__ue_specific_K_Offset_r17__cond BandNR__ext11O__ue_specific_K_Offset_r17__Format.

Definition BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Format : T_Format BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__nat__Format BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2 BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1F2 BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2F1.

Opaque BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__cond BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Format.

Definition BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Format : T_Format BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__nat__Format BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1 BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2 BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F1F2 BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__F2F1.

Opaque BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__cond BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Format.

Definition BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Format : T_Format BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__nat__Format BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F1 BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F2 BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F1F2 BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__F2F1.

Opaque BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__cond BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Format.

Definition BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Format : T_Format BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__nat__Format BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F1 BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F2 BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F1F2 BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__F2F1.

Opaque BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__cond BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Format.

Definition BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Format : T_Format BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__nat__Format BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F1 BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F2 BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F1F2 BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__F2F1.

Opaque BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__cond BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Format.

Definition BandNR__ext11O__prs_ProcessingWindowType1A_r17__Format : T_Format BandNR__ext11O__prs_ProcessingWindowType1A_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__prs_ProcessingWindowType1A_r17__nat__Format BandNR__ext11O__prs_ProcessingWindowType1A_r17__F1 BandNR__ext11O__prs_ProcessingWindowType1A_r17__F2 BandNR__ext11O__prs_ProcessingWindowType1A_r17__F1F2 BandNR__ext11O__prs_ProcessingWindowType1A_r17__F2F1.

Opaque BandNR__ext11O__prs_ProcessingWindowType1A_r17__cond BandNR__ext11O__prs_ProcessingWindowType1A_r17__Format.

Definition BandNR__ext11O__prs_ProcessingWindowType1B_r17__Format : T_Format BandNR__ext11O__prs_ProcessingWindowType1B_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__prs_ProcessingWindowType1B_r17__nat__Format BandNR__ext11O__prs_ProcessingWindowType1B_r17__F1 BandNR__ext11O__prs_ProcessingWindowType1B_r17__F2 BandNR__ext11O__prs_ProcessingWindowType1B_r17__F1F2 BandNR__ext11O__prs_ProcessingWindowType1B_r17__F2F1.

Opaque BandNR__ext11O__prs_ProcessingWindowType1B_r17__cond BandNR__ext11O__prs_ProcessingWindowType1B_r17__Format.

Definition BandNR__ext11O__prs_ProcessingWindowType2_r17__Format : T_Format BandNR__ext11O__prs_ProcessingWindowType2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__prs_ProcessingWindowType2_r17__nat__Format BandNR__ext11O__prs_ProcessingWindowType2_r17__F1 BandNR__ext11O__prs_ProcessingWindowType2_r17__F2 BandNR__ext11O__prs_ProcessingWindowType2_r17__F1F2 BandNR__ext11O__prs_ProcessingWindowType2_r17__F2F1.

Opaque BandNR__ext11O__prs_ProcessingWindowType2_r17__cond BandNR__ext11O__prs_ProcessingWindowType2_r17__Format.

Definition BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Format : T_Format BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__nat__Format BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F1 BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F2 BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F1F2 BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__F2F1.

Opaque BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__cond BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Format.

Definition BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Format : T_Format BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__nat__Format BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F1 BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F2 BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F1F2 BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__F2F1.

Opaque BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__cond BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Format.

Definition BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Format : T_Format BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__nat__Format BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F1 BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F2 BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F1F2 BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__F2F1.

Opaque BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__cond BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Format.

Definition BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Format : T_Format BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__nat__Format BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F1 BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F2 BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F1F2 BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__F2F1.

Opaque BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__cond BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Format.

Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Format : T_Format BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__nat__Format BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F1 BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F2 BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F1F2 BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__F2F1.

Opaque BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Format.

Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Format : T_Format BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__nat__Format BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F1 BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F2 BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F1F2 BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__F2F1.

Opaque BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Format.


Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__Format_Type := Eval cbn in seq_format_prod BandNR__ext11O__maxDurationDMRS_Bundling_r17__list.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__Format_list : BandNR__ext11O__maxDurationDMRS_Bundling_r17__Format_Type :=
  (BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17__Format, (BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17__Format, unit_format)).
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__list__Format := (*Eval compute in *) seq_format BandNR__ext11O__maxDurationDMRS_Bundling_r17__list BandNR__ext11O__maxDurationDMRS_Bundling_r17__Format_list.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1 z :=
  (BandNR__ext11O__maxDurationDMRS_Bundling_r17__fdd_r17 z, (BandNR__ext11O__maxDurationDMRS_Bundling_r17__tdd_r17 z, tt)).
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__F2 (y : seq_type BandNR__ext11O__maxDurationDMRS_Bundling_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext11O__maxDurationDMRS_Bundling_r17__Type i0 i1
  end.
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1F2_cond (z : BandNR__ext11O__maxDurationDMRS_Bundling_r17__Type)
  : BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond z ->
  (seq_cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__list (BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1 z)).
intro H. unfold BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond in H. simpl. auto. Qed.
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1F2_cond2 (z : BandNR__ext11O__maxDurationDMRS_Bundling_r17__Type)
 : BandNR__ext11O__maxDurationDMRS_Bundling_r17__F2 (BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext11O__maxDurationDMRS_Bundling_r17__F2F1_cond (y : seq_type BandNR__ext11O__maxDurationDMRS_Bundling_r17__list)
  : seq_cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__list y ->
 (BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond (BandNR__ext11O__maxDurationDMRS_Bundling_r17__F2 y)) /\  BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1 (BandNR__ext11O__maxDurationDMRS_Bundling_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext11O__maxDurationDMRS_Bundling_r17__Format : T_Format BandNR__ext11O__maxDurationDMRS_Bundling_r17__Type BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond :=
        proj2_format  BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__list__Format
    BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1 BandNR__ext11O__maxDurationDMRS_Bundling_r17__F2 BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1F2_cond  BandNR__ext11O__maxDurationDMRS_Bundling_r17__F1F2_cond2 BandNR__ext11O__maxDurationDMRS_Bundling_r17__F2F1_cond.
Opaque BandNR__ext11O__maxDurationDMRS_Bundling_r17__cond BandNR__ext11O__maxDurationDMRS_Bundling_r17__Format.

Definition BandNR__ext11O__pusch_RepetitionMsg3_r17__Format : T_Format BandNR__ext11O__pusch_RepetitionMsg3_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__pusch_RepetitionMsg3_r17__nat__Format BandNR__ext11O__pusch_RepetitionMsg3_r17__F1 BandNR__ext11O__pusch_RepetitionMsg3_r17__F2 BandNR__ext11O__pusch_RepetitionMsg3_r17__F1F2 BandNR__ext11O__pusch_RepetitionMsg3_r17__F2F1.

Opaque BandNR__ext11O__pusch_RepetitionMsg3_r17__cond BandNR__ext11O__pusch_RepetitionMsg3_r17__Format.

Definition BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Format : T_Format BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__nat__Format BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F1 BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F2 BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F1F2 BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__F2F1.

Opaque BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__cond BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Format.

Definition BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Format : T_Format BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__nat__Format BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F1 BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F2 BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F1F2 BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__F2F1.

Opaque BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__cond BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Format.

Definition BandNR__ext11O__k1_RangeExtension_r17__Format : T_Format BandNR__ext11O__k1_RangeExtension_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__k1_RangeExtension_r17__nat__Format BandNR__ext11O__k1_RangeExtension_r17__F1 BandNR__ext11O__k1_RangeExtension_r17__F2 BandNR__ext11O__k1_RangeExtension_r17__F1F2 BandNR__ext11O__k1_RangeExtension_r17__F2F1.

Opaque BandNR__ext11O__k1_RangeExtension_r17__cond BandNR__ext11O__k1_RangeExtension_r17__Format.

Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Format : T_Format BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__nat__Format BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F1 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F2 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F1F2 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__F2F1.

Opaque BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__cond BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Format.

Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Format : T_Format BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__nat__Format BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F1 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F2 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F1F2 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__F2F1.

Opaque BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__cond BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Format.


Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Format_Type := Eval cbn in seq_format_prod BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Format_list : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Format_Type :=
  (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17__Format, (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17__Format, unit_format)).
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list__Format := (*Eval compute in *) seq_format BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Format_list.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1 z :=
  (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_PerCC_r17 z, (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__maxNumberAperiodicCSI_RS_AcrossCCs_r17 z, tt)).
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F2 (y : seq_type BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Type i0 i1
  end.
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1F2_cond (z : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Type)
  : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond z ->
  (seq_cond BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1 z)).
intro H. unfold BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond in H. simpl. auto. Qed.
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1F2_cond2 (z : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Type)
 : BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F2 (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F2F1_cond (y : seq_type BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list)
  : seq_cond BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list y ->
 (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F2 y)) /\  BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1 (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Format : T_Format BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Type BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond :=
        proj2_format  BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__list__Format
    BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F2 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1F2_cond  BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F1F2_cond2 BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__F2F1_cond.
Opaque BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__cond BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Format.

Definition BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Format : T_Format BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__nat__Format BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F1 BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F2 BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F1F2 BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__F2F1.

Opaque BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__cond BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Format.

Definition BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Format : T_Format BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__nat__Format BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F1 BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F2 BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F1F2 BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__F2F1.

Opaque BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__cond BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Format.

Definition BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Format : T_Format BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__nat__Format BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F1 BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F2 BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F1F2 BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__F2F1.

Opaque BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__cond BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Format.

Definition BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__Format : T_Format BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__Type BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__cond BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__Format.

Definition BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__Format : T_Format BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__Type BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__cond BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__Format.

Definition BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__Format : T_Format BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__Type BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__cond BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__Format.

Definition BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__Format : T_Format BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__Type BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__cond BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__Format.

Definition BandNR__ext11O__ul_GapFR2_r17__Format : T_Format BandNR__ext11O__ul_GapFR2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__ul_GapFR2_r17__nat__Format BandNR__ext11O__ul_GapFR2_r17__F1 BandNR__ext11O__ul_GapFR2_r17__F2 BandNR__ext11O__ul_GapFR2_r17__F1F2 BandNR__ext11O__ul_GapFR2_r17__F2F1.

Opaque BandNR__ext11O__ul_GapFR2_r17__cond BandNR__ext11O__ul_GapFR2_r17__Format.

Definition BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Format : T_Format BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__nat__Format BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F1 BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F2 BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F1F2 BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__F2F1.

Opaque BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__cond BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Format.

Definition BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Format : T_Format BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__nat__Format BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F1 BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F2 BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F1F2 BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__F2F1.

Opaque BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__cond BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Format.

Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Format : T_Format BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__nat__Format BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F1 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F2 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F1F2 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__F2F1.

Opaque BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__cond BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Format.

Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Format : T_Format BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__nat__Format BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F1 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F2 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F1F2 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__F2F1.

Opaque BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__cond BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Format.


Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Format_Type := Eval cbn in seq_format_prod BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Format_list : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Format_Type :=
  (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17__Format, (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17__Format, unit_format)).
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list__Format := (*Eval compute in *) seq_format BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Format_list.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1 z :=
  (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__enhancedType3_HARQ_Codebooks_r17 z, (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__maxNumberPUCCH_Transmissions_r17 z, tt)).
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F2 (y : seq_type BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Type i0 i1
  end.
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1F2_cond (z : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Type)
  : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond z ->
  (seq_cond BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1 z)).
intro H. unfold BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond in H. simpl. auto. Qed.
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1F2_cond2 (z : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Type)
 : BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F2 (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F2F1_cond (y : seq_type BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list)
  : seq_cond BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list y ->
 (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F2 y)) /\  BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1 (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Format : T_Format BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Type BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond :=
        proj2_format  BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__list__Format
    BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F2 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1F2_cond  BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F1F2_cond2 BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__F2F1_cond.
Opaque BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__cond BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Format.

Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Format : T_Format BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__nat__Format BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F1 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F2 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F1F2 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__F2F1.

Opaque BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__cond BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Format.

Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Format : T_Format BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__nat__Format BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F1 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F2 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F1F2 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__F2F1.

Opaque BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__cond BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Format.


Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Format_Type := Eval cbn in seq_format_prod BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Format_list : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Format_Type :=
  (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17__Format, (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17__Format, unit_format)).
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list__Format := (*Eval compute in *) seq_format BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Format_list.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1 z :=
  (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__minHARQ_Retx_Offset_r17 z, (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__maxHARQ_Retx_Offset_r17 z, tt)).
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F2 (y : seq_type BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Type i0 i1
  end.
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1F2_cond (z : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Type)
  : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond z ->
  (seq_cond BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1 z)).
intro H. unfold BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond in H. simpl. auto. Qed.
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1F2_cond2 (z : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Type)
 : BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F2 (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F2F1_cond (y : seq_type BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list)
  : seq_cond BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list y ->
 (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F2 y)) /\  BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1 (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Format : T_Format BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Type BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond :=
        proj2_format  BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__list__Format
    BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F2 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1F2_cond  BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F1F2_cond2 BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__F2F1_cond.
Opaque BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__cond BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Format.


Definition BandNR__ext11O__Format_Type := Eval cbn in seq_format_prod BandNR__ext11O__list.
Definition BandNR__ext11O__Format_list : BandNR__ext11O__Format_Type :=
  (BandNR__ext11O__pdsch_1024QAM_FR1_r17__Format, (BandNR__ext11O__ue_PowerClass_v1700__Format, (FR2_2_AccessParamsPerBand_r17__Format, (BandNR__ext11O__rlm_Relaxation_r17__Format, (BandNR__ext11O__bfd_Relaxation_r17__Format, (BandNR__ext11O__cg_SDT_r17__Format, (BandNR__ext11O__locationBasedCondHandover_r17__Format, (BandNR__ext11O__timeBasedCondHandover_r17__Format, (BandNR__ext11O__eventA4BasedCondHandover_r17__Format, (BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17__Format, (BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17__Format, (BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17__Format, (BandNR__ext11O__sssg_Switching_1BitInd_r17__Format, (BandNR__ext11O__sssg_Switching_2BitInd_r17__Format, (BandNR__ext11O__pdcch_SkippingWithSSSG_r17__Format, (BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17__Format, (BandNR__ext11O__uplinkPreCompensation_r17__Format, (BandNR__ext11O__uplink_TA_Reporting_r17__Format, (BandNR__ext11O__max_HARQ_ProcessNumber_r17__Format, (BandNR__ext11O__type2_HARQ_Codebook_r17__Format, (BandNR__ext11O__type1_HARQ_Codebook_r17__Format, (BandNR__ext11O__type3_HARQ_Codebook_r17__Format, (BandNR__ext11O__ue_specific_K_Offset_r17__Format, (BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Format, (BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17__Format, (BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17__Format, (BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17__Format, (BandNR__ext11O__prs_ProcessingRRC_Inactive_r17__Format, (BandNR__ext11O__prs_ProcessingWindowType1A_r17__Format, (BandNR__ext11O__prs_ProcessingWindowType1B_r17__Format, (BandNR__ext11O__prs_ProcessingWindowType2_r17__Format, (SRS_AllPosResourcesRRC_Inactive_r17__Format, (OLPC_SRS_Pos_r16__Format, (SpatialRelationsSRS_Pos_r16__Format, (BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17__Format, (BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17__Format, (BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17__Format, (BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17__Format, (BandNR__ext11O__maxDurationDMRS_Bundling_r17__Format, (BandNR__ext11O__pusch_RepetitionMsg3_r17__Format, (SharedSpectrumChAccessParamsPerBand_v1710__Format, (BandNR__ext11O__parallelMeasurementWithoutRestriction_r17__Format, (BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17__Format, (BandNR__ext11O__k1_RangeExtension_r17__Format, (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17__Format, (BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17__Format, (BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17__Format, (BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17__Format, (PosSRS_RRC_Inactive_OutsideInitialUL_BWP_r17__Format, (BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17__Format, (BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17__Format, (BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17__Format, (BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17__Format, (BandNR__ext11O__ul_GapFR2_r17__Format, (BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17__Format, (BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17__Format, (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17__Format, (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17__Format, unit_format)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition BandNR__ext11O__list__Format := (*Eval compute in *) seq_format BandNR__ext11O__list BandNR__ext11O__Format_list.
Definition BandNR__ext11O__F1 z :=
  (BandNR__ext11O__pdsch_1024QAM_FR1_r17 z, (BandNR__ext11O__ue_PowerClass_v1700 z, (BandNR__ext11O__fr2_2_AccessParamsPerBand_r17 z, (BandNR__ext11O__rlm_Relaxation_r17 z, (BandNR__ext11O__bfd_Relaxation_r17 z, (BandNR__ext11O__cg_SDT_r17 z, (BandNR__ext11O__locationBasedCondHandover_r17 z, (BandNR__ext11O__timeBasedCondHandover_r17 z, (BandNR__ext11O__eventA4BasedCondHandover_r17 z, (BandNR__ext11O__mn_InitiatedCondPSCellChangeNRDC_r17 z, (BandNR__ext11O__sn_InitiatedCondPSCellChangeNRDC_r17 z, (BandNR__ext11O__pdcch_SkippingWithoutSSSG_r17 z, (BandNR__ext11O__sssg_Switching_1BitInd_r17 z, (BandNR__ext11O__sssg_Switching_2BitInd_r17 z, (BandNR__ext11O__pdcch_SkippingWithSSSG_r17 z, (BandNR__ext11O__searchSpaceSetGrp_switchCap2_r17 z, (BandNR__ext11O__uplinkPreCompensation_r17 z, (BandNR__ext11O__uplink_TA_Reporting_r17 z, (BandNR__ext11O__max_HARQ_ProcessNumber_r17 z, (BandNR__ext11O__type2_HARQ_Codebook_r17 z, (BandNR__ext11O__type1_HARQ_Codebook_r17 z, (BandNR__ext11O__type3_HARQ_Codebook_r17 z, (BandNR__ext11O__ue_specific_K_Offset_r17 z, (BandNR__ext11O__multiPDSCH_SingleDCI_FR2_1_SCS_120kHz_r17 z, (BandNR__ext11O__multiPUSCH_SingleDCI_FR2_1_SCS_120kHz_r17 z, (BandNR__ext11O__parallelPRS_MeasRRC_Inactive_r17 z, (BandNR__ext11O__nr_UE_TxTEG_ID_MaxSupport_r17 z, (BandNR__ext11O__prs_ProcessingRRC_Inactive_r17 z, (BandNR__ext11O__prs_ProcessingWindowType1A_r17 z, (BandNR__ext11O__prs_ProcessingWindowType1B_r17 z, (BandNR__ext11O__prs_ProcessingWindowType2_r17 z, (BandNR__ext11O__srs_AllPosResourcesRRC_Inactive_r17 z, (BandNR__ext11O__olpc_SRS_PosRRC_Inactive_r17 z, (BandNR__ext11O__spatialRelationsSRS_PosRRC_Inactive_r17 z, (BandNR__ext11O__maxNumberPUSCH_TypeA_Repetition_r17 z, (BandNR__ext11O__puschTypeA_RepetitionsAvailSlot_r17 z, (BandNR__ext11O__tb_ProcessingMultiSlotPUSCH_r17 z, (BandNR__ext11O__tb_ProcessingRepMultiSlotPUSCH_r17 z, (BandNR__ext11O__maxDurationDMRS_Bundling_r17 z, (BandNR__ext11O__pusch_RepetitionMsg3_r17 z, (BandNR__ext11O__sharedSpectrumChAccessParamsPerBand_v1710 z, (BandNR__ext11O__parallelMeasurementWithoutRestriction_r17 z, (BandNR__ext11O__maxNumber_NGSO_SatellitesWithinOneSMTC_r17 z, (BandNR__ext11O__k1_RangeExtension_r17 z, (BandNR__ext11O__aperiodicCSI_RS_FastScellActivation_r17 z, (BandNR__ext11O__aperiodicCSI_RS_AdditionalBandwidth_r17 z, (BandNR__ext11O__bwp_WithoutCD_SSB_OrNCD_SSB_RedCap_r17 z, (BandNR__ext11O__halfDuplexFDD_TypeA_RedCap_r17 z, (BandNR__ext11O__posSRS_RRC_Inactive_OutsideInitialUL_BWP_r17 z, (BandNR__ext11O__channelBWs_DL_SCS_480kHz_FR2_2_r17 z, (BandNR__ext11O__channelBWs_UL_SCS_480kHz_FR2_2_r17 z, (BandNR__ext11O__channelBWs_DL_SCS_960kHz_FR2_2_r17 z, (BandNR__ext11O__channelBWs_UL_SCS_960kHz_FR2_2_r17 z, (BandNR__ext11O__ul_GapFR2_r17 z, (BandNR__ext11O__oneShotHARQ_feedbackTriggeredByDCI_1_2_r17 z, (BandNR__ext11O__oneShotHARQ_feedbackPhy_Priority_r17 z, (BandNR__ext11O__enhancedType3_HARQ_CodebookFeedback_r17 z, (BandNR__ext11O__triggeredHARQ_CodebookRetx_r17 z, tt)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition BandNR__ext11O__F2 (y : seq_type BandNR__ext11O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, (i22, (i23, (i24, (i25, (i26, (i27, (i28, (i29, (i30, (i31, (i32, (i33, (i34, (i35, (i36, (i37, (i38, (i39, (i40, (i41, (i42, (i43, (i44, (i45, (i46, (i47, (i48, (i49, (i50, (i51, (i52, (i53, (i54, (i55, (i56, (i57, _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))=>
    make__BandNR__ext11O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 i32 i33 i34 i35 i36 i37 i38 i39 i40 i41 i42 i43 i44 i45 i46 i47 i48 i49 i50 i51 i52 i53 i54 i55 i56 i57
  end.
Lemma BandNR__ext11O__F1F2_cond (z : BandNR__ext11O__Type)
  : BandNR__ext11O__cond z ->
  (seq_cond BandNR__ext11O__list (BandNR__ext11O__F1 z)).
intro H. unfold BandNR__ext11O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext11O__F1F2_cond2 (z : BandNR__ext11O__Type)
 : BandNR__ext11O__F2 (BandNR__ext11O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext11O__F2F1_cond (y : seq_type BandNR__ext11O__list)
  : seq_cond BandNR__ext11O__list y ->
 (BandNR__ext11O__cond (BandNR__ext11O__F2 y)) /\  BandNR__ext11O__F1 (BandNR__ext11O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext11O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext11O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext11O__Format : T_Format BandNR__ext11O__Type BandNR__ext11O__cond :=
        proj2_format  BandNR__ext11O__cond BandNR__ext11O__list__Format
    BandNR__ext11O__F1 BandNR__ext11O__F2 BandNR__ext11O__F1F2_cond  BandNR__ext11O__F1F2_cond2 BandNR__ext11O__F2F1_cond.
Opaque BandNR__ext11O__cond BandNR__ext11O__Format.

Definition BandNR__ext11__check_all_none (b : BandNR__ext11O__Type) : bool :=
match b with 
  | make__BandNR__ext11O__Type None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition BandNR__ext11__Format : T_Format BandNR__ext11__Type BandNR__ext11__cond :=
  restrict_add_format BandNR__ext11__check_all_none BandNR__ext11O__Format.

Opaque BandNR__ext11__cond BandNR__ext11__Format.

Definition BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Format : T_Format BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__nat__Format BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F1 BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F2 BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F1F2 BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__F2F1.

Opaque BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__cond BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Format.

Definition BandNR__ext12O__pucch_Repetition_F0_2_r17__Format : T_Format BandNR__ext12O__pucch_Repetition_F0_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__pucch_Repetition_F0_2_r17__nat__Format BandNR__ext12O__pucch_Repetition_F0_2_r17__F1 BandNR__ext12O__pucch_Repetition_F0_2_r17__F2 BandNR__ext12O__pucch_Repetition_F0_2_r17__F1F2 BandNR__ext12O__pucch_Repetition_F0_2_r17__F2F1.

Opaque BandNR__ext12O__pucch_Repetition_F0_2_r17__cond BandNR__ext12O__pucch_Repetition_F0_2_r17__Format.

Definition BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Format : T_Format BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__nat__Format BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F1 BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F2 BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F1F2 BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__F2F1.

Opaque BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__cond BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Format.

Definition BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Format : T_Format BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__nat__Format BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F1 BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F2 BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F1F2 BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__F2F1.

Opaque BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__cond BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Format.

Definition BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Format : T_Format BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__nat__Format BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F1 BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F2 BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F1F2 BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__F2F1.

Opaque BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__cond BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Format.

Definition BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Format : T_Format BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__nat__Format BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F1 BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F2 BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F1F2 BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__F2F1.

Opaque BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__cond BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Format.

Definition BandNR__ext12O__maxNumberG_RNTI_r17__Format : T_Format Z BandNR__ext12O__maxNumberG_RNTI_r17__cond :=
 ranged_int_format (2) (8) BandNR__ext12O__maxNumberG_RNTI_r17__helper1 BandNR__ext12O__maxNumberG_RNTI_r17__helper2.

Opaque BandNR__ext12O__maxNumberG_RNTI_r17__cond BandNR__ext12O__maxNumberG_RNTI_r17__Format.

Definition BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Format : T_Format BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__nat__Format BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F1 BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F2 BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F1F2 BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__F2F1.

Opaque BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__cond BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Format.

Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Format : T_Format BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__nat__Format BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F1 BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F2 BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F1F2 BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__F2F1.

Opaque BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__cond BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Format.

Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Format : T_Format BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__nat__Format BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F1 BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F2 BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F1F2 BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__F2F1.

Opaque BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__cond BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Format.


Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__Format_Type := Eval cbn in get_formats BandNR__ext12O__maxModulationOrderForMulticast_r17__list.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__Format_list : BandNR__ext12O__maxModulationOrderForMulticast_r17__Format_Type :=
  (BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Format, (BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Format, unit__Format)).
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__list__Format := Eval compute in choice_format BandNR__ext12O__maxModulationOrderForMulticast_r17__list BandNR__ext12O__maxModulationOrderForMulticast_r17__len_helper1 BandNR__ext12O__maxModulationOrderForMulticast_r17__len_helper2  BandNR__ext12O__maxModulationOrderForMulticast_r17__Format_list.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__F1 (z : BandNR__ext12O__maxModulationOrderForMulticast_r17__Type) : (choice BandNR__ext12O__maxModulationOrderForMulticast_r17__list) :=
  match z with
   | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17 t => existT _ 0 t
  | BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17 t => existT _ 1 t
  end.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__g := (fun n => typ_set (get_nth_typ BandNR__ext12O__maxModulationOrderForMulticast_r17__list n)).
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__F2 (y : choice BandNR__ext12O__maxModulationOrderForMulticast_r17__list) : BandNR__ext12O__maxModulationOrderForMulticast_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandNR__ext12O__maxModulationOrderForMulticast_r17__g n -> BandNR__ext12O__maxModulationOrderForMulticast_r17__Type) with
    | 0 => fun (t : BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17__Type) => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr1_r17 t 
    | 1 => fun (t : BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17__Type) => BandNR__ext12O__maxModulationOrderForMulticast_r17__fr2_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandNR__ext12O__maxModulationOrderForMulticast_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandNR__ext12O__maxModulationOrderForMulticast_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandNR__ext12O__maxModulationOrderForMulticast_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandNR__ext12O__maxModulationOrderForMulticast_r17__Type with end) n0
           end t0).

Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__helper2 :  forall (y : BandNR__ext12O__maxModulationOrderForMulticast_r17__Type), BandNR__ext12O__maxModulationOrderForMulticast_r17__cond y -> choice_cond BandNR__ext12O__maxModulationOrderForMulticast_r17__list (BandNR__ext12O__maxModulationOrderForMulticast_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__helper3 :  forall (y : BandNR__ext12O__maxModulationOrderForMulticast_r17__Type), BandNR__ext12O__maxModulationOrderForMulticast_r17__F2 (BandNR__ext12O__maxModulationOrderForMulticast_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandNR__ext12O__maxModulationOrderForMulticast_r17__helper4 : (forall b : choice BandNR__ext12O__maxModulationOrderForMulticast_r17__list, choice_cond BandNR__ext12O__maxModulationOrderForMulticast_r17__list b -> BandNR__ext12O__maxModulationOrderForMulticast_r17__cond (BandNR__ext12O__maxModulationOrderForMulticast_r17__F2 b) /\ BandNR__ext12O__maxModulationOrderForMulticast_r17__F1 (BandNR__ext12O__maxModulationOrderForMulticast_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandNR__ext12O__maxModulationOrderForMulticast_r17__F1 BandNR__ext12O__maxModulationOrderForMulticast_r17__F2.
Definition BandNR__ext12O__maxModulationOrderForMulticast_r17__Format : T_Format BandNR__ext12O__maxModulationOrderForMulticast_r17__Type BandNR__ext12O__maxModulationOrderForMulticast_r17__cond :=
  (* Eval compute in *) proj2_format BandNR__ext12O__maxModulationOrderForMulticast_r17__cond BandNR__ext12O__maxModulationOrderForMulticast_r17__list__Format BandNR__ext12O__maxModulationOrderForMulticast_r17__F1 BandNR__ext12O__maxModulationOrderForMulticast_r17__F2 BandNR__ext12O__maxModulationOrderForMulticast_r17__helper2 BandNR__ext12O__maxModulationOrderForMulticast_r17__helper3 BandNR__ext12O__maxModulationOrderForMulticast_r17__helper4.
Opaque BandNR__ext12O__maxModulationOrderForMulticast_r17__cond BandNR__ext12O__maxModulationOrderForMulticast_r17__Format.

Definition BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Format : T_Format BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__nat__Format BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F1 BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F2 BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F1F2 BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__F2F1.

Opaque BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__cond BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Format.

Definition BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Format : T_Format BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__nat__Format BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F1 BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F2 BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F1F2 BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__F2F1.

Opaque BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__cond BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Format.

Definition BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Format : T_Format BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__nat__Format BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F1 BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F2 BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F1F2 BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__F2F1.

Opaque BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__cond BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Format.

Definition BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Format : T_Format BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__nat__Format BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F1 BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F2 BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F1F2 BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__F2F1.

Opaque BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__cond BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Format.

Definition BandNR__ext12O__maxNumberG_CS_RNTI_r17__Format : T_Format Z BandNR__ext12O__maxNumberG_CS_RNTI_r17__cond :=
 ranged_int_format (2) (8) BandNR__ext12O__maxNumberG_CS_RNTI_r17__helper1 BandNR__ext12O__maxNumberG_CS_RNTI_r17__helper2.

Opaque BandNR__ext12O__maxNumberG_CS_RNTI_r17__cond BandNR__ext12O__maxNumberG_CS_RNTI_r17__Format.

Definition BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Format : T_Format BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__nat__Format BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F1 BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F2 BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F1F2 BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__F2F1.

Opaque BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__cond BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Format.

Definition BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Format : T_Format BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__nat__Format BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F1 BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F2 BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F1F2 BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__F2F1.

Opaque BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__cond BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Format.

Definition BandNR__ext12O__prs_MeasurementWithoutMG_r17__Format : T_Format BandNR__ext12O__prs_MeasurementWithoutMG_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__prs_MeasurementWithoutMG_r17__nat__Format BandNR__ext12O__prs_MeasurementWithoutMG_r17__F1 BandNR__ext12O__prs_MeasurementWithoutMG_r17__F2 BandNR__ext12O__prs_MeasurementWithoutMG_r17__F1F2 BandNR__ext12O__prs_MeasurementWithoutMG_r17__F2F1.

Opaque BandNR__ext12O__prs_MeasurementWithoutMG_r17__cond BandNR__ext12O__prs_MeasurementWithoutMG_r17__Format.

Definition BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__Format : T_Format Z BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__cond :=
 ranged_int_format (3) (4) BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__helper1 BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__helper2.

Opaque BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__cond BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__Format.

Definition BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__Format : T_Format BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__Type BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__cond := seq_of_format PRS_ProcessingCapabilityOutsideMGinPPWperType_r17__Format 1 3 BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__helper1 BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__helper2.

Opaque BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__cond BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__Format.

Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Format : T_Format BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__nat__Format BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F1 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F2 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F1F2 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__F2F1.

Opaque BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__cond BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Format.

Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Format : T_Format BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__nat__Format BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F1 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F2 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F1F2 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__F2F1.

Opaque BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__cond BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Format.


Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Format_Type := Eval cbn in seq_format_prod BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Format_list : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Format_Type :=
  (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17__Format, (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17__Format, unit_format)).
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list__Format := (*Eval compute in *) seq_format BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Format_list.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1 z :=
  (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResources_r17 z, (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__maxNumOfSemiPersistentSRSposResourcesPerSlot_r17 z, tt)).
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F2 (y : seq_type BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Type i0 i1
  end.
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1F2_cond (z : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Type)
  : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond z ->
  (seq_cond BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1 z)).
intro H. unfold BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond in H. simpl. auto. Qed.
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1F2_cond2 (z : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Type)
 : BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F2 (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F2F1_cond (y : seq_type BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list)
  : seq_cond BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list y ->
 (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F2 y)) /\  BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1 (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Format : T_Format BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Type BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond :=
        proj2_format  BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__list__Format
    BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F2 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1F2_cond  BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F1F2_cond2 BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__F2F1_cond.
Opaque BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__cond BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Format.

Definition BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__Format : T_Format BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__Type BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__cond BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__Format.

Definition BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__Format : T_Format BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__Type BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__cond := (* Eval compute in *) bit_string_fixed_format 8.
Opaque BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__cond BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__Format.


Definition BandNR__ext12O__Format_Type := Eval cbn in seq_format_prod BandNR__ext12O__list.
Definition BandNR__ext12O__Format_list : BandNR__ext12O__Format_Type :=
  (BandNR__ext12O__ue_OneShotUL_TimingAdj_r17__Format, (BandNR__ext12O__pucch_Repetition_F0_2_r17__Format, (BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17__Format, (BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17__Format, (BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17__Format, (BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17__Format, (BandNR__ext12O__maxNumberG_RNTI_r17__Format, (BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17__Format, (BandNR__ext12O__maxModulationOrderForMulticast_r17__Format, (BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17__Format, (BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17__Format, (BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17__Format, (BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17__Format, (BandNR__ext12O__maxNumberG_CS_RNTI_r17__Format, (BandNR__ext12O__re_LevelRateMatchingForMulticast_r17__Format, (BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17__Format, (BandNR__ext12O__prs_MeasurementWithoutMG_r17__Format, (BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17__Format, (BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17__Format, (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17__Format, (BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17__Format, (BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17__Format, unit_format)))))))))))))))))))))).
Definition BandNR__ext12O__list__Format := (*Eval compute in *) seq_format BandNR__ext12O__list BandNR__ext12O__Format_list.
Definition BandNR__ext12O__F1 z :=
  (BandNR__ext12O__ue_OneShotUL_TimingAdj_r17 z, (BandNR__ext12O__pucch_Repetition_F0_2_r17 z, (BandNR__ext12O__cqi_4_BitsSubbandNTN_SharedSpectrumChAccess_r17 z, (BandNR__ext12O__mux_HARQ_ACK_DiffPriorities_r17 z, (BandNR__ext12O__ta_BasedPDC_NTN_SharedSpectrumChAccess_r17 z, (BandNR__ext12O__ack_NACK_FeedbackForMulticastWithDCI_Enabler_r17 z, (BandNR__ext12O__maxNumberG_RNTI_r17 z, (BandNR__ext12O__dynamicMulticastDCI_Format4_2_r17 z, (BandNR__ext12O__maxModulationOrderForMulticast_r17 z, (BandNR__ext12O__dynamicSlotRepetitionMulticastTN_NonSharedSpectrumChAccess_r17 z, (BandNR__ext12O__dynamicSlotRepetitionMulticastNTN_SharedSpectrumChAccess_r17 z, (BandNR__ext12O__nack_OnlyFeedbackForMulticastWithDCI_Enabler_r17 z, (BandNR__ext12O__ack_NACK_FeedbackForSPS_MulticastWithDCI_Enabler_r17 z, (BandNR__ext12O__maxNumberG_CS_RNTI_r17 z, (BandNR__ext12O__re_LevelRateMatchingForMulticast_r17 z, (BandNR__ext12O__pdsch_1024QAM_2MIMO_FR1_r17 z, (BandNR__ext12O__prs_MeasurementWithoutMG_r17 z, (BandNR__ext12O__maxNumber_LEO_SatellitesPerCarrier_r17 z, (BandNR__ext12O__prs_ProcessingCapabilityOutsideMGinPPW_r17 z, (BandNR__ext12O__srs_SemiPersistent_PosResourcesRRC_Inactive_r17 z, (BandNR__ext12O__channelBWs_DL_SCS_120kHz_FR2_2_r17 z, (BandNR__ext12O__channelBWs_UL_SCS_120kHz_FR2_2_r17 z, tt)))))))))))))))))))))).
Definition BandNR__ext12O__F2 (y : seq_type BandNR__ext12O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, (i14, (i15, (i16, (i17, (i18, (i19, (i20, (i21, _))))))))))))))))))))))=>
    make__BandNR__ext12O__Type i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21
  end.
Lemma BandNR__ext12O__F1F2_cond (z : BandNR__ext12O__Type)
  : BandNR__ext12O__cond z ->
  (seq_cond BandNR__ext12O__list (BandNR__ext12O__F1 z)).
intro H. unfold BandNR__ext12O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext12O__F1F2_cond2 (z : BandNR__ext12O__Type)
 : BandNR__ext12O__F2 (BandNR__ext12O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext12O__F2F1_cond (y : seq_type BandNR__ext12O__list)
  : seq_cond BandNR__ext12O__list y ->
 (BandNR__ext12O__cond (BandNR__ext12O__F2 y)) /\  BandNR__ext12O__F1 (BandNR__ext12O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext12O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext12O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext12O__Format : T_Format BandNR__ext12O__Type BandNR__ext12O__cond :=
        proj2_format  BandNR__ext12O__cond BandNR__ext12O__list__Format
    BandNR__ext12O__F1 BandNR__ext12O__F2 BandNR__ext12O__F1F2_cond  BandNR__ext12O__F1F2_cond2 BandNR__ext12O__F2F1_cond.
Opaque BandNR__ext12O__cond BandNR__ext12O__Format.

Definition BandNR__ext12__check_all_none (b : BandNR__ext12O__Type) : bool :=
match b with 
  | make__BandNR__ext12O__Type None None None None None None None None None None None None None None None None None None None None None None  => false 
  | _ => true 
 end.
Definition BandNR__ext12__Format : T_Format BandNR__ext12__Type BandNR__ext12__cond :=
  restrict_add_format BandNR__ext12__check_all_none BandNR__ext12O__Format.

Opaque BandNR__ext12__cond BandNR__ext12__Format.

Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Format : T_Format BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__nat__Format BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F1 BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F2 BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F1F2 BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__F2F1.

Opaque BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__cond BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Format.

Definition BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Format : T_Format BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__nat__Format BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F1 BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F2 BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F1F2 BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__F2F1.

Opaque BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__cond BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Format.

Definition BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Format : T_Format BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__nat__Format BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F1 BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F2 BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F1F2 BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__F2F1.

Opaque BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__cond BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Format.

Definition BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Format : T_Format BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__nat__Format BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F1 BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F2 BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F1F2 BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__F2F1.

Opaque BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__cond BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Format.

Definition BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Format : T_Format BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__nat__Format BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F1 BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F2 BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F1F2 BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__F2F1.

Opaque BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__cond BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Format.

Definition BandNR__ext13O__interSlotFreqHopPUCCH_r17__Format : T_Format BandNR__ext13O__interSlotFreqHopPUCCH_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext13O__interSlotFreqHopPUCCH_r17__nat__Format BandNR__ext13O__interSlotFreqHopPUCCH_r17__F1 BandNR__ext13O__interSlotFreqHopPUCCH_r17__F2 BandNR__ext13O__interSlotFreqHopPUCCH_r17__F1F2 BandNR__ext13O__interSlotFreqHopPUCCH_r17__F2F1.

Opaque BandNR__ext13O__interSlotFreqHopPUCCH_r17__cond BandNR__ext13O__interSlotFreqHopPUCCH_r17__Format.

Definition BandNR__ext13O__dmrs_BundlingRestart_r17__Format : T_Format BandNR__ext13O__dmrs_BundlingRestart_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext13O__dmrs_BundlingRestart_r17__nat__Format BandNR__ext13O__dmrs_BundlingRestart_r17__F1 BandNR__ext13O__dmrs_BundlingRestart_r17__F2 BandNR__ext13O__dmrs_BundlingRestart_r17__F1F2 BandNR__ext13O__dmrs_BundlingRestart_r17__F2F1.

Opaque BandNR__ext13O__dmrs_BundlingRestart_r17__cond BandNR__ext13O__dmrs_BundlingRestart_r17__Format.

Definition BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Format : T_Format BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__nat__Format BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F1 BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F2 BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F1F2 BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__F2F1.

Opaque BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__cond BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Format.


Definition BandNR__ext13O__Format_Type := Eval cbn in seq_format_prod BandNR__ext13O__list.
Definition BandNR__ext13O__Format_list : BandNR__ext13O__Format_Type :=
  (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17__Format, (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17__Format, (BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17__Format, (BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17__Format, (BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17__Format, (BandNR__ext13O__interSlotFreqHopPUCCH_r17__Format, (BandNR__ext13O__dmrs_BundlingRestart_r17__Format, (BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17__Format, unit_format)))))))).
Definition BandNR__ext13O__list__Format := (*Eval compute in *) seq_format BandNR__ext13O__list BandNR__ext13O__Format_list.
Definition BandNR__ext13O__F1 z :=
  (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeA_r17 z, (BandNR__ext13O__dmrs_BundlingPUSCH_RepTypeB_r17 z, (BandNR__ext13O__dmrs_BundlingPUSCH_multiSlot_r17 z, (BandNR__ext13O__dmrs_BundlingPUCCH_Rep_r17 z, (BandNR__ext13O__interSlotFreqHopInterSlotBundlingPUSCH_r17 z, (BandNR__ext13O__interSlotFreqHopPUCCH_r17 z, (BandNR__ext13O__dmrs_BundlingRestart_r17 z, (BandNR__ext13O__dmrs_BundlingNonBackToBackTX_r17 z, tt)))))))).
Definition BandNR__ext13O__F2 (y : seq_type BandNR__ext13O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, _))))))))=>
    make__BandNR__ext13O__Type i0 i1 i2 i3 i4 i5 i6 i7
  end.
Lemma BandNR__ext13O__F1F2_cond (z : BandNR__ext13O__Type)
  : BandNR__ext13O__cond z ->
  (seq_cond BandNR__ext13O__list (BandNR__ext13O__F1 z)).
intro H. unfold BandNR__ext13O__cond in H. simpl. auto. Qed.
Lemma BandNR__ext13O__F1F2_cond2 (z : BandNR__ext13O__Type)
 : BandNR__ext13O__F2 (BandNR__ext13O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandNR__ext13O__F2F1_cond (y : seq_type BandNR__ext13O__list)
  : seq_cond BandNR__ext13O__list y ->
 (BandNR__ext13O__cond (BandNR__ext13O__F2 y)) /\  BandNR__ext13O__F1 (BandNR__ext13O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandNR__ext13O__cond. simpl in *. auto.
 - simpl. unfold BandNR__ext13O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandNR__ext13O__Format : T_Format BandNR__ext13O__Type BandNR__ext13O__cond :=
        proj2_format  BandNR__ext13O__cond BandNR__ext13O__list__Format
    BandNR__ext13O__F1 BandNR__ext13O__F2 BandNR__ext13O__F1F2_cond  BandNR__ext13O__F1F2_cond2 BandNR__ext13O__F2F1_cond.
Opaque BandNR__ext13O__cond BandNR__ext13O__Format.

Definition BandNR__ext13__check_all_none (b : BandNR__ext13O__Type) : bool :=
match b with 
  | make__BandNR__ext13O__Type None None None None None None None None  => false 
  | _ => true 
 end.
Definition BandNR__ext13__Format : T_Format BandNR__ext13__Type BandNR__ext13__cond :=
  restrict_add_format BandNR__ext13__check_all_none BandNR__ext13O__Format.

Opaque BandNR__ext13__cond BandNR__ext13__Format.


Definition BandNR__root_Format_Type := Eval cbn in seq_format_prod BandNR__root_list.
Definition BandNR__root_Format_list : BandNR__root_Format_Type :=
  (FreqBandIndicatorNR__Format, (BandNR__modifiedMPR_Behaviour__Format, (MIMO_ParametersPerBand__Format, (BandNR__extendedCP__Format, (BandNR__multipleTCI__Format, (BandNR__bwp_WithoutRestriction__Format, (BandNR__bwp_SameNumerology__Format, (BandNR__bwp_DiffNumerology__Format, (BandNR__crossCarrierScheduling_SameSCS__Format, (BandNR__pdsch_256QAM_FR2__Format, (BandNR__pusch_256QAM__Format, (BandNR__ue_PowerClass__Format, (BandNR__rateMatchingLTE_CRS__Format, (BandNR__channelBWs_DL__Format, (BandNR__channelBWs_UL__Format, unit_format))))))))))))))).

Definition BandNR__ext_Format_Type := Eval cbn in get_formats BandNR__ext_list.
Definition BandNR__ext_Format_list : BandNR__ext_Format_Type :=
  (BandNR__ext0__Format, (BandNR__ext1__Format, (BandNR__ext2__Format, (BandNR__ext3__Format, (BandNR__ext4__Format, (BandNR__ext5__Format, (BandNR__ext6__Format, (BandNR__ext7__Format, (BandNR__ext8__Format, (BandNR__ext9__Format, (BandNR__ext10__Format, (BandNR__ext11__Format, (BandNR__ext12__Format, (BandNR__ext13__Format, unit__Format)))))))))))))).

Definition BandNR__list_type : Set := (seq_type BandNR__root_list) * (seq_ext_type BandNR__ext_list).
Definition BandNR__list_cond (z : BandNR__list_type) : Prop :=
        (seq_cond BandNR__root_list (fst z)) /\ (seq_ext_cond BandNR__ext_list (snd z)).
Definition BandNR__list_format : T_Format BandNR__list_type BandNR__list_cond :=
 (* Eval compute in *) seq_ext_format BandNR__root_list BandNR__root_Format_list BandNR__ext_list BandNR__ext_Format_list.

Opaque BandNR__list_format.
Definition BandNR__F1 (z : BandNR__Type) : BandNR__list_type :=
  (((BandNR__bandNR z, (BandNR__modifiedMPR_Behaviour z, (BandNR__mimo_ParametersPerBand z, (BandNR__extendedCP z, (BandNR__multipleTCI z, (BandNR__bwp_WithoutRestriction z, (BandNR__bwp_SameNumerology z, (BandNR__bwp_DiffNumerology z, (BandNR__crossCarrierScheduling_SameSCS z, (BandNR__pdsch_256QAM_FR2 z, (BandNR__pusch_256QAM z, (BandNR__ue_PowerClass z, (BandNR__rateMatchingLTE_CRS z, (BandNR__channelBWs_DL z, (BandNR__channelBWs_UL z, tt)))))))))))))))), (
(BandNR__ext0 z, (BandNR__ext1 z, (BandNR__ext2 z, (BandNR__ext3 z, (BandNR__ext4 z, (BandNR__ext5 z, (BandNR__ext6 z, (BandNR__ext7 z, (BandNR__ext8 z, (BandNR__ext9 z, (BandNR__ext10 z, (BandNR__ext11 z, (BandNR__ext12 z, (BandNR__ext13 z, tt)))))))))))))))).
Definition BandNR__F2 (y : BandNR__list_type) : BandNR__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, (j7, (j8, (j9, (j10, (j11, (j12, (j13, (j14, _))))))))))))))), (i0, (i1, (i2, (i3, (i4, (i5, (i6, (i7, (i8, (i9, (i10, (i11, (i12, (i13, _)))))))))))))))=>
    make__BandNR__Type j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  end.
Definition BandNR__helper1 : (forall a : BandNR__Type, BandNR__cond a -> BandNR__list_cond (BandNR__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BandNR__helper2 : (forall a : BandNR__Type, BandNR__F2 (BandNR__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BandNR__helper3 : (forall b : BandNR__list_type, BandNR__list_cond b -> BandNR__cond (BandNR__F2 b) /\ BandNR__F1 (BandNR__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BandNR__cond, BandNR__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BandNR__Format : T_Format BandNR__Type BandNR__cond :=
 proj2_format BandNR__cond BandNR__list_format  BandNR__F1 BandNR__F2 BandNR__helper1 BandNR__helper2 BandNR__helper3.

Opaque BandNR__cond BandNR__Format.

