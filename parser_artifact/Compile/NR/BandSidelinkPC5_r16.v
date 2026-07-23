Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Require Import NR.FreqBandIndicatorNR.

Opaque FreqBandIndicatorNR__cond FreqBandIndicatorNR__Format.

Inductive BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Type : Set :=
 | BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n16
 | BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n24
 | BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n32
 | BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n64
.
Definition BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__cond := (fun (_ : BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Type) => True).
Lemma BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__nat__helper.

Definition BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n16 => 0
  | BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n24 => 1
  | BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n32 => 2
  | BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n64 => 3
  end.
Definition BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n16
  | 1 => BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n24
  | 2 => BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n32
  | 3 => BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n64
  | _ => BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__n16
  end.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F1F2 : forall x : BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Type, (BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F1 x <= 3) /\ BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F2 (BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F2F1 : forall (y : nat) (H : y <= 3), BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F1 (BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Type : Set :=
 | BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__value1
 | BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__value2
.
Definition BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__cond := (fun (_ : BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Type) => True).
Lemma BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__nat__helper.

Definition BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__value1 => 0
  | BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__value2 => 1
  end.
Definition BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__value1
  | 1 => BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__value2
  | _ => BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__value1
  end.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F1F2 : forall x : BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Type, (BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F1 x <= 1) /\ BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F2 (BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F2F1 : forall (y : nat) (H : y <= 1), BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F1 (BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F2 y) = y. enum_solve H y. Qed.

Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__Type := bit_string_fixed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__Type := bit_string_fixed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__Type := bit_string_fixed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Record BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type : Set :=
  make__BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type {
    BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16 : option BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__Type ;
    BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16 : option BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__Type ;
    BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16 : option BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__Type ;
}.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list := (
 Opt BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__cond ::
 Opt BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__cond ::
 Opt BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__cond ::
 nil).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond z := 
  opt_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16 z) /\
  opt_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16 z) /\
  opt_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16 z) /\
  True.

Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__Type := bit_string_fixed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__Type := bit_string_fixed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 16 /\ bit_string_len_prop (fst z) (snd z)).
Record BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type : Set :=
  make__BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type {
    BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16 : option BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__Type ;
    BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16 : option BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__Type ;
}.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list := (
 Opt BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__cond ::
 Opt BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__cond ::
 nil).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond z := 
  opt_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16 z) /\
  opt_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16 z) /\
  True.


Inductive BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type : Set :=
  | BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16 : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type -> BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type
  | BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16 : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type -> BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type
.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list : list typ := (
typ_cons BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond ::
typ_cons BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond ::
 nil).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__cond (c : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type) := 
  match c with
  | BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16 t => BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond t 
  | BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16 t => BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond t 
  end.

Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__len_helper1 : to_bit_sz (length BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__len_helper2 : 2 <= length2 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list.
 simpl. lia. Qed.
Inductive BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Type : Set :=
 | BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__supported
.
Definition BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__cond := (fun (_ : BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Type) => True).
Lemma BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__nat__helper.

Definition BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__supported => 0
  end.
Definition BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__supported
  | _ => BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__supported
  end.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F1F2 : forall x : BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Type, (BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F1 x <= 0) /\ BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F2 (BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F1 (BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F2 y) = y. enum_solve H y. Qed.

Record BandSidelinkPC5_r16__sl_Reception_r16__Type : Set :=
  make__BandSidelinkPC5_r16__sl_Reception_r16__Type {
    BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16 : BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Type ;
    BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16 : BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Type ;
    BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16 : option BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type ;
    BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16 : option BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Type ;
}.
Definition BandSidelinkPC5_r16__sl_Reception_r16__list := (
 Nor BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__cond ::
 Nor BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__cond ::
 Opt BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__cond ::
 Opt BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__cond ::
 nil).
Definition BandSidelinkPC5_r16__sl_Reception_r16__cond z := 
  BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16 z) /\
  BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16 z) /\
  opt_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16 z) /\
  opt_cond BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16 z) /\
  True.

Inductive BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Type : Set :=
 | BandSidelinkPC5_r16__sl_Tx_256QAM_r16__supported
.
Definition BandSidelinkPC5_r16__sl_Tx_256QAM_r16__cond := (fun (_ : BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Type) => True).
Lemma BandSidelinkPC5_r16__sl_Tx_256QAM_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__sl_Tx_256QAM_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__sl_Tx_256QAM_r16__nat__helper.

Definition BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__sl_Tx_256QAM_r16__supported => 0
  end.
Definition BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__sl_Tx_256QAM_r16__supported
  | _ => BandSidelinkPC5_r16__sl_Tx_256QAM_r16__supported
  end.
Lemma BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F1F2 : forall x : BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Type, (BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F1 x <= 0) /\ BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F2 (BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F1 (BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Type : Set :=
 | BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__supported
.
Definition BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__cond := (fun (_ : BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Type) => True).
Lemma BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__nat__helper.

Definition BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__supported => 0
  end.
Definition BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__supported
  | _ => BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__supported
  end.
Lemma BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F1F2 : forall x : BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Type, (BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F1 x <= 0) /\ BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F2 (BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F1 (BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Type : Set :=
 | BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__p1
 | BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__p2
.
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__cond := (fun (_ : BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Type) => True).
Lemma BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__nat__helper.

Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__p1 => 0
  | BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__p2 => 1
  end.
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__p1
  | 1 => BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__p2
  | _ => BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__p1
  end.
Lemma BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F1F2 : forall x : BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Type, (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F1 x <= 1) /\ BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F2 (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F2F1 : forall (y : nat) (H : y <= 1), BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F1 (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F2 y) = y. enum_solve H y. Qed.

Record BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Type : Set :=
  make__BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Type {
    BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16 : BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Type ;
}.
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list := (
 Nor BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Type BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__cond ::
 nil).
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond z := 
  BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__cond (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16 z) /\
  True.

Inductive BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Type : Set :=
 | BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__supported
.
Definition BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__cond := (fun (_ : BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Type) => True).
Lemma BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__nat__helper.

Definition BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__supported => 0
  end.
Definition BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__supported
  | _ => BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__supported
  end.
Lemma BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F1F2 : forall x : BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Type, (BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F1 x <= 0) /\ BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F2 (BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F1 (BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Type : Set :=
 | BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__supported
.
Definition BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__cond := (fun (_ : BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Type) => True).
Lemma BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__nat__helper.

Definition BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__supported => 0
  end.
Definition BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__supported
  | _ => BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__supported
  end.
Lemma BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F1F2 : forall x : BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Type, (BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F1 x <= 0) /\ BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F2 (BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F1 (BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Type : Set :=
 | BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__supported
.
Definition BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__cond := (fun (_ : BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Type) => True).
Lemma BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__nat__helper.

Definition BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__supported => 0
  end.
Definition BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__supported
  | _ => BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__supported
  end.
Lemma BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F1F2 : forall x : BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Type, (BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F1 x <= 0) /\ BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F2 (BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F1 (BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F2 y) = y. enum_solve H y. Qed.

Record BandSidelinkPC5_r16__ext0O__Type : Set :=
  make__BandSidelinkPC5_r16__ext0O__Type {
    BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16 : option BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Type ;
    BandSidelinkPC5_r16__ext0O__rankTwoReception_r16 : option BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Type ;
    BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16 : option BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Type ;
    BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16 : option BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Type ;
}.
Definition BandSidelinkPC5_r16__ext0O__list := (
 Opt BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Type BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond ::
 Opt BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Type BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__cond ::
 Opt BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Type BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__cond ::
 Opt BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Type BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__cond ::
 nil).
Definition BandSidelinkPC5_r16__ext0O__cond z := 
  opt_cond BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16 z) /\
  opt_cond BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__cond (BandSidelinkPC5_r16__ext0O__rankTwoReception_r16 z) /\
  opt_cond BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__cond (BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16 z) /\
  opt_cond BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__cond (BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16 z) /\
  True.

Definition BandSidelinkPC5_r16__ext0__Type := BandSidelinkPC5_r16__ext0O__Type.
Definition BandSidelinkPC5_r16__ext0__cond := BandSidelinkPC5_r16__ext0O__cond.

Inductive BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Type : Set :=
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__supported
.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__cond := (fun (_ : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Type) => True).
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__nat__helper.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__supported => 0
  end.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__supported
  | _ => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__supported
  end.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F1F2 : forall x : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Type, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F1 x <= 0) /\ BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F2 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F1 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Type : Set :=
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__supported
.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__cond := (fun (_ : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Type) => True).
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__nat__helper.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__supported => 0
  end.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__supported
  | _ => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__supported
  end.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F1F2 : forall x : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Type, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F1 x <= 0) /\ BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F2 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F1 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Type : Set :=
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n5
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n15
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n25
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n32
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n35
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n45
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n50
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n64
.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__cond := (fun (_ : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Type) => True).
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__nat__helper.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n5 => 0
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n15 => 1
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n25 => 2
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n32 => 3
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n35 => 4
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n45 => 5
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n50 => 6
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n64 => 7
  end.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n5
  | 1 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n15
  | 2 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n25
  | 3 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n32
  | 4 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n35
  | 5 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n45
  | 6 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n50
  | 7 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n64
  | _ => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__n5
  end.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F1F2 : forall x : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Type, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F1 x <= 7) /\ BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F2 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F2F1 : forall (y : nat) (H : y <= 7), BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F1 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Type : Set :=
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__supported
.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__cond := (fun (_ : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Type) => True).
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__nat__helper.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__supported => 0
  end.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__supported
  | _ => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__supported
  end.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F1F2 : forall x : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Type, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F1 x <= 0) /\ BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F2 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F1 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Type : Set :=
 | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__supported
.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__cond := (fun (_ : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Type) => True).
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__nat__helper.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__supported => 0
  end.
Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__supported
  | _ => BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__supported
  end.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F1F2 : forall x : BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Type, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F1 x <= 0) /\ BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F2 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F1 (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F2 y) = y. enum_solve H y. Qed.

Inductive BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Type : Set :=
 | BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__supported
.
Definition BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__cond := (fun (_ : BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Type) => True).
Lemma BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__nat__helper.

Definition BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F1 t :=
  match t with
  | BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__supported => 0
  end.
Definition BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F2 n :=
  match n with
  | 0 => BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__supported
  | _ => BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__supported
  end.
Lemma BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F1F2 : forall x : BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Type, (BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F1 x <= 0) /\ BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F2 (BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F1 x) = x. imp_solve. Qed.
Lemma BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F2F1 : forall (y : nat) (H : y <= 0), BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F1 (BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F2 y) = y. enum_solve H y. Qed.

Record BandSidelinkPC5_r16__ext1O__Type : Set :=
  make__BandSidelinkPC5_r16__ext1O__Type {
    BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17 : option BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Type ;
    BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17 : option BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Type ;
    BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17 : option BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Type ;
    BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17 : option BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Type ;
    BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17 : option BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Type ;
    BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17 : option BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Type ;
}.
Definition BandSidelinkPC5_r16__ext1O__list := (
 Opt BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Type BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__cond ::
 Opt BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Type BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__cond ::
 Opt BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Type BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__cond ::
 Opt BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Type BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__cond ::
 Opt BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Type BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__cond ::
 Opt BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Type BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__cond ::
 nil).
Definition BandSidelinkPC5_r16__ext1O__cond z := 
  opt_cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__cond (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17 z) /\
  opt_cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__cond (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17 z) /\
  opt_cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__cond (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17 z) /\
  opt_cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__cond (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17 z) /\
  opt_cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__cond (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17 z) /\
  opt_cond BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__cond (BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17 z) /\
  True.

Definition BandSidelinkPC5_r16__ext1__Type := BandSidelinkPC5_r16__ext1O__Type.
Definition BandSidelinkPC5_r16__ext1__cond := BandSidelinkPC5_r16__ext1O__cond.

Record BandSidelinkPC5_r16__Type : Set :=
  make__BandSidelinkPC5_r16__Type {
    BandSidelinkPC5_r16__freqBandSidelink_r16 : FreqBandIndicatorNR__Type ;
    BandSidelinkPC5_r16__sl_Reception_r16 : option BandSidelinkPC5_r16__sl_Reception_r16__Type ;
    BandSidelinkPC5_r16__sl_Tx_256QAM_r16 : option BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Type ;
    BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16 : option BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Type ;
    BandSidelinkPC5_r16__ext0 : option BandSidelinkPC5_r16__ext0__Type ;
    BandSidelinkPC5_r16__ext1 : option BandSidelinkPC5_r16__ext1__Type ;
}.
Definition BandSidelinkPC5_r16__root_list : list seq_elem := (
 Nor FreqBandIndicatorNR__Type FreqBandIndicatorNR__cond ::
 Opt BandSidelinkPC5_r16__sl_Reception_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__cond ::
 Opt BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Type BandSidelinkPC5_r16__sl_Tx_256QAM_r16__cond ::
 Opt BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Type BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__cond ::
 nil).
Definition BandSidelinkPC5_r16__ext_list : list typ := (
  typ_cons BandSidelinkPC5_r16__ext0__Type BandSidelinkPC5_r16__ext0__cond ::
  typ_cons BandSidelinkPC5_r16__ext1__Type BandSidelinkPC5_r16__ext1__cond ::
  nil).
Definition BandSidelinkPC5_r16__cond (z : BandSidelinkPC5_r16__Type) := 
(  FreqBandIndicatorNR__cond (BandSidelinkPC5_r16__freqBandSidelink_r16 z) /\
  opt_cond BandSidelinkPC5_r16__sl_Reception_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16 z) /\
  opt_cond BandSidelinkPC5_r16__sl_Tx_256QAM_r16__cond (BandSidelinkPC5_r16__sl_Tx_256QAM_r16 z) /\
  opt_cond BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__cond (BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16 z) /\
  True) /\ 
(  opt_cond BandSidelinkPC5_r16__ext0__cond (BandSidelinkPC5_r16__ext0 z) /\
  opt_cond BandSidelinkPC5_r16__ext1__cond (BandSidelinkPC5_r16__ext1 z) /\
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
Definition BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__nat__Format BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F1 BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F2 BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F1F2 BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__F2F1.

Opaque BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Format.

Definition BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__nat__Format BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F1 BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F2 BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F1F2 BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__F2F1.

Opaque BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Format.

Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__Format.

Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__Format.

Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__Format.


Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Format_Type := Eval cbn in seq_format_prod BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Format_list : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Format_Type :=
  (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16__Format, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16__Format, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16__Format, unit_format))).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list__Format := (*Eval compute in *) seq_format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Format_list.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1 z :=
  (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_15kHz_r16 z, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_30kHz_r16 z, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__scs_60kHz_r16 z, tt))).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F2 (y : seq_type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type i0 i1 i2
  end.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1F2_cond (z : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type)
  : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond z ->
  (seq_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1 z)).
intro H. unfold BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond in H. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1F2_cond2 (z : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type)
 : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F2 (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F2F1_cond (y : seq_type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list)
  : seq_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list y ->
 (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F2 y)) /\  BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1 (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond. simpl in *. auto.
 - simpl. unfold BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond :=
        proj2_format  BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__list__Format
    BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F2 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1F2_cond  BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F1F2_cond2 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__F2F1_cond.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Format.

Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__Format.

Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__cond := (* Eval compute in *) bit_string_fixed_format 16.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__Format.


Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Format_Type := Eval cbn in seq_format_prod BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Format_list : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Format_Type :=
  (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16__Format, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16__Format, unit_format)).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list__Format := (*Eval compute in *) seq_format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Format_list.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1 z :=
  (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_60kHz_r16 z, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__scs_120kHz_r16 z, tt)).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F2 (y : seq_type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type i0 i1
  end.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1F2_cond (z : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type)
  : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond z ->
  (seq_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1 z)).
intro H. unfold BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond in H. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1F2_cond2 (z : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type)
 : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F2 (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F2F1_cond (y : seq_type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list)
  : seq_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list y ->
 (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F2 y)) /\  BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1 (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond. simpl in *. auto.
 - simpl. unfold BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond :=
        proj2_format  BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__list__Format
    BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F2 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1F2_cond  BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F1F2_cond2 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__F2F1_cond.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Format.


Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Format_Type := Eval cbn in get_formats BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Format_list : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Format_Type :=
  (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Format, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Format, unit__Format)).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list__Format := Eval compute in choice_format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__len_helper1 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__len_helper2  BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Format_list.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F1 (z : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type) : (choice BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list) :=
  match z with
   | BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16 t => existT _ 0 t
  | BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16 t => existT _ 1 t
  end.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__g := (fun n => typ_set (get_nth_typ BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list n)).
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F2 (y : choice BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list) : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__g n -> BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type) with
    | 0 => fun (t : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16__Type) => BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr1_r16 t 
    | 1 => fun (t : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16__Type) => BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__fr2_r16 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type with end) n0
           end t0).

Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__helper2 :  forall (y : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type), BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__cond y -> choice_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__helper3 :  forall (y : BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type), BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F2 (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__helper4 : (forall b : choice BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list, choice_cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list b -> BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F2 b) /\ BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F1 (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F1 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F2.
Definition BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__cond :=
  (* Eval compute in *) proj2_format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__list__Format BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F1 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__F2 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__helper2 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__helper3 BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__helper4.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Format.

Definition BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__nat__Format BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F1 BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F2 BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F1F2 BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__F2F1.

Opaque BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Format.


Definition BandSidelinkPC5_r16__sl_Reception_r16__Format_Type := Eval cbn in seq_format_prod BandSidelinkPC5_r16__sl_Reception_r16__list.
Definition BandSidelinkPC5_r16__sl_Reception_r16__Format_list : BandSidelinkPC5_r16__sl_Reception_r16__Format_Type :=
  (BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16__Format, (BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16__Format, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16__Format, (BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16__Format, unit_format)))).
Definition BandSidelinkPC5_r16__sl_Reception_r16__list__Format := (*Eval compute in *) seq_format BandSidelinkPC5_r16__sl_Reception_r16__list BandSidelinkPC5_r16__sl_Reception_r16__Format_list.
Definition BandSidelinkPC5_r16__sl_Reception_r16__F1 z :=
  (BandSidelinkPC5_r16__sl_Reception_r16__harq_RxProcessSidelink_r16 z, (BandSidelinkPC5_r16__sl_Reception_r16__pscch_RxSidelink_r16 z, (BandSidelinkPC5_r16__sl_Reception_r16__scs_CP_PatternRxSidelink_r16 z, (BandSidelinkPC5_r16__sl_Reception_r16__extendedCP_RxSidelink_r16 z, tt)))).
Definition BandSidelinkPC5_r16__sl_Reception_r16__F2 (y : seq_type BandSidelinkPC5_r16__sl_Reception_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__BandSidelinkPC5_r16__sl_Reception_r16__Type i0 i1 i2 i3
  end.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__F1F2_cond (z : BandSidelinkPC5_r16__sl_Reception_r16__Type)
  : BandSidelinkPC5_r16__sl_Reception_r16__cond z ->
  (seq_cond BandSidelinkPC5_r16__sl_Reception_r16__list (BandSidelinkPC5_r16__sl_Reception_r16__F1 z)).
intro H. unfold BandSidelinkPC5_r16__sl_Reception_r16__cond in H. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__F1F2_cond2 (z : BandSidelinkPC5_r16__sl_Reception_r16__Type)
 : BandSidelinkPC5_r16__sl_Reception_r16__F2 (BandSidelinkPC5_r16__sl_Reception_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__sl_Reception_r16__F2F1_cond (y : seq_type BandSidelinkPC5_r16__sl_Reception_r16__list)
  : seq_cond BandSidelinkPC5_r16__sl_Reception_r16__list y ->
 (BandSidelinkPC5_r16__sl_Reception_r16__cond (BandSidelinkPC5_r16__sl_Reception_r16__F2 y)) /\  BandSidelinkPC5_r16__sl_Reception_r16__F1 (BandSidelinkPC5_r16__sl_Reception_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandSidelinkPC5_r16__sl_Reception_r16__cond. simpl in *. auto.
 - simpl. unfold BandSidelinkPC5_r16__sl_Reception_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandSidelinkPC5_r16__sl_Reception_r16__Format : T_Format BandSidelinkPC5_r16__sl_Reception_r16__Type BandSidelinkPC5_r16__sl_Reception_r16__cond :=
        proj2_format  BandSidelinkPC5_r16__sl_Reception_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__list__Format
    BandSidelinkPC5_r16__sl_Reception_r16__F1 BandSidelinkPC5_r16__sl_Reception_r16__F2 BandSidelinkPC5_r16__sl_Reception_r16__F1F2_cond  BandSidelinkPC5_r16__sl_Reception_r16__F1F2_cond2 BandSidelinkPC5_r16__sl_Reception_r16__F2F1_cond.
Opaque BandSidelinkPC5_r16__sl_Reception_r16__cond BandSidelinkPC5_r16__sl_Reception_r16__Format.

Definition BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Format : T_Format BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__sl_Tx_256QAM_r16__nat__Format BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F1 BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F2 BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F1F2 BandSidelinkPC5_r16__sl_Tx_256QAM_r16__F2F1.

Opaque BandSidelinkPC5_r16__sl_Tx_256QAM_r16__cond BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Format.

Definition BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Format : T_Format BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__nat__Format BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F1 BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F2 BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F1F2 BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__F2F1.

Opaque BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__cond BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Format.

Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Format : T_Format BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__nat__Format BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F1 BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F2 BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F1F2 BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__F2F1.

Opaque BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__cond BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Format.


Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Format_Type := Eval cbn in seq_format_prod BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list.
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Format_list : BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Format_Type :=
  (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16__Format, unit_format).
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list__Format := (*Eval compute in *) seq_format BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Format_list.
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1 z :=
  (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__csi_RS_PortsSidelink_r16 z, tt).
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F2 (y : seq_type BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list) :=
  match y with
  | (i0, _)=>
    make__BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Type i0
  end.
Lemma BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1F2_cond (z : BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Type)
  : BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond z ->
  (seq_cond BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1 z)).
intro H. unfold BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond in H. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1F2_cond2 (z : BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Type)
 : BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F2 (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F2F1_cond (y : seq_type BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list)
  : seq_cond BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list y ->
 (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F2 y)) /\  BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1 (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond. simpl in *. auto.
 - simpl. unfold BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Format : T_Format BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Type BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond :=
        proj2_format  BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__list__Format
    BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1 BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F2 BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1F2_cond  BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F1F2_cond2 BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__F2F1_cond.
Opaque BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__cond BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Format.

Definition BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Format : T_Format BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__nat__Format BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F1 BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F2 BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F1F2 BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__F2F1.

Opaque BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__cond BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Format.

Definition BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Format : T_Format BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__nat__Format BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F1 BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F2 BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F1F2 BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__F2F1.

Opaque BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__cond BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Format.

Definition BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Format : T_Format BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__nat__Format BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F1 BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F2 BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F1F2 BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__F2F1.

Opaque BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__cond BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Format.


Definition BandSidelinkPC5_r16__ext0O__Format_Type := Eval cbn in seq_format_prod BandSidelinkPC5_r16__ext0O__list.
Definition BandSidelinkPC5_r16__ext0O__Format_list : BandSidelinkPC5_r16__ext0O__Format_Type :=
  (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16__Format, (BandSidelinkPC5_r16__ext0O__rankTwoReception_r16__Format, (BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16__Format, (BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16__Format, unit_format)))).
Definition BandSidelinkPC5_r16__ext0O__list__Format := (*Eval compute in *) seq_format BandSidelinkPC5_r16__ext0O__list BandSidelinkPC5_r16__ext0O__Format_list.
Definition BandSidelinkPC5_r16__ext0O__F1 z :=
  (BandSidelinkPC5_r16__ext0O__csi_ReportSidelink_r16 z, (BandSidelinkPC5_r16__ext0O__rankTwoReception_r16 z, (BandSidelinkPC5_r16__ext0O__sl_openLoopPC_RSRP_ReportSidelink_r16 z, (BandSidelinkPC5_r16__ext0O__sl_Rx_256QAM_r16 z, tt)))).
Definition BandSidelinkPC5_r16__ext0O__F2 (y : seq_type BandSidelinkPC5_r16__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__BandSidelinkPC5_r16__ext0O__Type i0 i1 i2 i3
  end.
Lemma BandSidelinkPC5_r16__ext0O__F1F2_cond (z : BandSidelinkPC5_r16__ext0O__Type)
  : BandSidelinkPC5_r16__ext0O__cond z ->
  (seq_cond BandSidelinkPC5_r16__ext0O__list (BandSidelinkPC5_r16__ext0O__F1 z)).
intro H. unfold BandSidelinkPC5_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__ext0O__F1F2_cond2 (z : BandSidelinkPC5_r16__ext0O__Type)
 : BandSidelinkPC5_r16__ext0O__F2 (BandSidelinkPC5_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__ext0O__F2F1_cond (y : seq_type BandSidelinkPC5_r16__ext0O__list)
  : seq_cond BandSidelinkPC5_r16__ext0O__list y ->
 (BandSidelinkPC5_r16__ext0O__cond (BandSidelinkPC5_r16__ext0O__F2 y)) /\  BandSidelinkPC5_r16__ext0O__F1 (BandSidelinkPC5_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandSidelinkPC5_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold BandSidelinkPC5_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandSidelinkPC5_r16__ext0O__Format : T_Format BandSidelinkPC5_r16__ext0O__Type BandSidelinkPC5_r16__ext0O__cond :=
        proj2_format  BandSidelinkPC5_r16__ext0O__cond BandSidelinkPC5_r16__ext0O__list__Format
    BandSidelinkPC5_r16__ext0O__F1 BandSidelinkPC5_r16__ext0O__F2 BandSidelinkPC5_r16__ext0O__F1F2_cond  BandSidelinkPC5_r16__ext0O__F1F2_cond2 BandSidelinkPC5_r16__ext0O__F2F1_cond.
Opaque BandSidelinkPC5_r16__ext0O__cond BandSidelinkPC5_r16__ext0O__Format.

Definition BandSidelinkPC5_r16__ext0__check_all_none (b : BandSidelinkPC5_r16__ext0O__Type) : bool :=
match b with 
  | make__BandSidelinkPC5_r16__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition BandSidelinkPC5_r16__ext0__Format : T_Format BandSidelinkPC5_r16__ext0__Type BandSidelinkPC5_r16__ext0__cond :=
  restrict_add_format BandSidelinkPC5_r16__ext0__check_all_none BandSidelinkPC5_r16__ext0O__Format.

Opaque BandSidelinkPC5_r16__ext0__cond BandSidelinkPC5_r16__ext0__Format.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Format : T_Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__nat__Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F1 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F1F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__F2F1.

Opaque BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Format.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Format : T_Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__nat__Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F1 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F1F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__F2F1.

Opaque BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Format.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Format : T_Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__nat__Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F1 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F1F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__F2F1.

Opaque BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Format.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Format : T_Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__nat__Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F1 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F1F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__F2F1.

Opaque BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Format.

Definition BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Format : T_Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__nat__Format BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F1 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F1F2 BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__F2F1.

Opaque BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__cond BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Format.

Definition BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Format : T_Format BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__nat__Format BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F1 BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F2 BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F1F2 BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__F2F1.

Opaque BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__cond BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Format.


Definition BandSidelinkPC5_r16__ext1O__Format_Type := Eval cbn in seq_format_prod BandSidelinkPC5_r16__ext1O__list.
Definition BandSidelinkPC5_r16__ext1O__Format_list : BandSidelinkPC5_r16__ext1O__Format_Type :=
  (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17__Format, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17__Format, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17__Format, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17__Format, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17__Format, (BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17__Format, unit_format)))))).
Definition BandSidelinkPC5_r16__ext1O__list__Format := (*Eval compute in *) seq_format BandSidelinkPC5_r16__ext1O__list BandSidelinkPC5_r16__ext1O__Format_list.
Definition BandSidelinkPC5_r16__ext1O__F1 z :=
  (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_PreferredMode2Sidelink_r17 z, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_NonPreferredMode2Sidelink_r17 z, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme2_Mode2Sidelink_r17 z, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_r17 z, (BandSidelinkPC5_r16__ext1O__rx_IUC_Scheme1_SCI_ExplicitReq_r17 z, (BandSidelinkPC5_r16__ext1O__scheme2_ConflictDeterminationRSRP_r17 z, tt)))))).
Definition BandSidelinkPC5_r16__ext1O__F2 (y : seq_type BandSidelinkPC5_r16__ext1O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__BandSidelinkPC5_r16__ext1O__Type i0 i1 i2 i3 i4 i5
  end.
Lemma BandSidelinkPC5_r16__ext1O__F1F2_cond (z : BandSidelinkPC5_r16__ext1O__Type)
  : BandSidelinkPC5_r16__ext1O__cond z ->
  (seq_cond BandSidelinkPC5_r16__ext1O__list (BandSidelinkPC5_r16__ext1O__F1 z)).
intro H. unfold BandSidelinkPC5_r16__ext1O__cond in H. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__ext1O__F1F2_cond2 (z : BandSidelinkPC5_r16__ext1O__Type)
 : BandSidelinkPC5_r16__ext1O__F2 (BandSidelinkPC5_r16__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandSidelinkPC5_r16__ext1O__F2F1_cond (y : seq_type BandSidelinkPC5_r16__ext1O__list)
  : seq_cond BandSidelinkPC5_r16__ext1O__list y ->
 (BandSidelinkPC5_r16__ext1O__cond (BandSidelinkPC5_r16__ext1O__F2 y)) /\  BandSidelinkPC5_r16__ext1O__F1 (BandSidelinkPC5_r16__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandSidelinkPC5_r16__ext1O__cond. simpl in *. auto.
 - simpl. unfold BandSidelinkPC5_r16__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandSidelinkPC5_r16__ext1O__Format : T_Format BandSidelinkPC5_r16__ext1O__Type BandSidelinkPC5_r16__ext1O__cond :=
        proj2_format  BandSidelinkPC5_r16__ext1O__cond BandSidelinkPC5_r16__ext1O__list__Format
    BandSidelinkPC5_r16__ext1O__F1 BandSidelinkPC5_r16__ext1O__F2 BandSidelinkPC5_r16__ext1O__F1F2_cond  BandSidelinkPC5_r16__ext1O__F1F2_cond2 BandSidelinkPC5_r16__ext1O__F2F1_cond.
Opaque BandSidelinkPC5_r16__ext1O__cond BandSidelinkPC5_r16__ext1O__Format.

Definition BandSidelinkPC5_r16__ext1__check_all_none (b : BandSidelinkPC5_r16__ext1O__Type) : bool :=
match b with 
  | make__BandSidelinkPC5_r16__ext1O__Type None None None None None None  => false 
  | _ => true 
 end.
Definition BandSidelinkPC5_r16__ext1__Format : T_Format BandSidelinkPC5_r16__ext1__Type BandSidelinkPC5_r16__ext1__cond :=
  restrict_add_format BandSidelinkPC5_r16__ext1__check_all_none BandSidelinkPC5_r16__ext1O__Format.

Opaque BandSidelinkPC5_r16__ext1__cond BandSidelinkPC5_r16__ext1__Format.


Definition BandSidelinkPC5_r16__root_Format_Type := Eval cbn in seq_format_prod BandSidelinkPC5_r16__root_list.
Definition BandSidelinkPC5_r16__root_Format_list : BandSidelinkPC5_r16__root_Format_Type :=
  (FreqBandIndicatorNR__Format, (BandSidelinkPC5_r16__sl_Reception_r16__Format, (BandSidelinkPC5_r16__sl_Tx_256QAM_r16__Format, (BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16__Format, unit_format)))).

Definition BandSidelinkPC5_r16__ext_Format_Type := Eval cbn in get_formats BandSidelinkPC5_r16__ext_list.
Definition BandSidelinkPC5_r16__ext_Format_list : BandSidelinkPC5_r16__ext_Format_Type :=
  (BandSidelinkPC5_r16__ext0__Format, (BandSidelinkPC5_r16__ext1__Format, unit__Format)).

Definition BandSidelinkPC5_r16__list_type : Set := (seq_type BandSidelinkPC5_r16__root_list) * (seq_ext_type BandSidelinkPC5_r16__ext_list).
Definition BandSidelinkPC5_r16__list_cond (z : BandSidelinkPC5_r16__list_type) : Prop :=
        (seq_cond BandSidelinkPC5_r16__root_list (fst z)) /\ (seq_ext_cond BandSidelinkPC5_r16__ext_list (snd z)).
Definition BandSidelinkPC5_r16__list_format : T_Format BandSidelinkPC5_r16__list_type BandSidelinkPC5_r16__list_cond :=
 (* Eval compute in *) seq_ext_format BandSidelinkPC5_r16__root_list BandSidelinkPC5_r16__root_Format_list BandSidelinkPC5_r16__ext_list BandSidelinkPC5_r16__ext_Format_list.

Opaque BandSidelinkPC5_r16__list_format.
Definition BandSidelinkPC5_r16__F1 (z : BandSidelinkPC5_r16__Type) : BandSidelinkPC5_r16__list_type :=
  (((BandSidelinkPC5_r16__freqBandSidelink_r16 z, (BandSidelinkPC5_r16__sl_Reception_r16 z, (BandSidelinkPC5_r16__sl_Tx_256QAM_r16 z, (BandSidelinkPC5_r16__lowSE_64QAM_MCS_TableSidelink_r16 z, tt))))), (
(BandSidelinkPC5_r16__ext0 z, (BandSidelinkPC5_r16__ext1 z, tt)))).
Definition BandSidelinkPC5_r16__F2 (y : BandSidelinkPC5_r16__list_type) : BandSidelinkPC5_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__BandSidelinkPC5_r16__Type j0 j1 j2 j3 i0 i1
  end.
Definition BandSidelinkPC5_r16__helper1 : (forall a : BandSidelinkPC5_r16__Type, BandSidelinkPC5_r16__cond a -> BandSidelinkPC5_r16__list_cond (BandSidelinkPC5_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition BandSidelinkPC5_r16__helper2 : (forall a : BandSidelinkPC5_r16__Type, BandSidelinkPC5_r16__F2 (BandSidelinkPC5_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition BandSidelinkPC5_r16__helper3 : (forall b : BandSidelinkPC5_r16__list_type, BandSidelinkPC5_r16__list_cond b -> BandSidelinkPC5_r16__cond (BandSidelinkPC5_r16__F2 b) /\ BandSidelinkPC5_r16__F1 (BandSidelinkPC5_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold BandSidelinkPC5_r16__cond, BandSidelinkPC5_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition BandSidelinkPC5_r16__Format : T_Format BandSidelinkPC5_r16__Type BandSidelinkPC5_r16__cond :=
 proj2_format BandSidelinkPC5_r16__cond BandSidelinkPC5_r16__list_format  BandSidelinkPC5_r16__F1 BandSidelinkPC5_r16__F2 BandSidelinkPC5_r16__helper1 BandSidelinkPC5_r16__helper2 BandSidelinkPC5_r16__helper3.

Opaque BandSidelinkPC5_r16__cond BandSidelinkPC5_r16__Format.

