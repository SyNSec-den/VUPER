Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Type : Set :=
 | Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__supported
.
Definition Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__cond := (fun (_ : Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Type) => True).
Lemma Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__nat__helper.

Definition Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F1 t :=
  match t with
  | Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__supported => 0
  end.
Definition Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F2 n :=
  match n with
  | 0 => Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__supported
  | _ => Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__supported
  end.
Lemma Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F1F2 : forall x : Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Type, (Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F1 x <= 0) /\ Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F2 (Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F1 (Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFR1__scs_60kHz__Type : Set :=
 | Phy_ParametersFR1__scs_60kHz__supported
.
Definition Phy_ParametersFR1__scs_60kHz__cond := (fun (_ : Phy_ParametersFR1__scs_60kHz__Type) => True).
Lemma Phy_ParametersFR1__scs_60kHz__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFR1__scs_60kHz__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFR1__scs_60kHz__nat__helper.

Definition Phy_ParametersFR1__scs_60kHz__F1 t :=
  match t with
  | Phy_ParametersFR1__scs_60kHz__supported => 0
  end.
Definition Phy_ParametersFR1__scs_60kHz__F2 n :=
  match n with
  | 0 => Phy_ParametersFR1__scs_60kHz__supported
  | _ => Phy_ParametersFR1__scs_60kHz__supported
  end.
Lemma Phy_ParametersFR1__scs_60kHz__F1F2 : forall x : Phy_ParametersFR1__scs_60kHz__Type, (Phy_ParametersFR1__scs_60kHz__F1 x <= 0) /\ Phy_ParametersFR1__scs_60kHz__F2 (Phy_ParametersFR1__scs_60kHz__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFR1__scs_60kHz__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFR1__scs_60kHz__F1 (Phy_ParametersFR1__scs_60kHz__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFR1__pdsch_256QAM_FR1__Type : Set :=
 | Phy_ParametersFR1__pdsch_256QAM_FR1__supported
.
Definition Phy_ParametersFR1__pdsch_256QAM_FR1__cond := (fun (_ : Phy_ParametersFR1__pdsch_256QAM_FR1__Type) => True).
Lemma Phy_ParametersFR1__pdsch_256QAM_FR1__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFR1__pdsch_256QAM_FR1__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFR1__pdsch_256QAM_FR1__nat__helper.

Definition Phy_ParametersFR1__pdsch_256QAM_FR1__F1 t :=
  match t with
  | Phy_ParametersFR1__pdsch_256QAM_FR1__supported => 0
  end.
Definition Phy_ParametersFR1__pdsch_256QAM_FR1__F2 n :=
  match n with
  | 0 => Phy_ParametersFR1__pdsch_256QAM_FR1__supported
  | _ => Phy_ParametersFR1__pdsch_256QAM_FR1__supported
  end.
Lemma Phy_ParametersFR1__pdsch_256QAM_FR1__F1F2 : forall x : Phy_ParametersFR1__pdsch_256QAM_FR1__Type, (Phy_ParametersFR1__pdsch_256QAM_FR1__F1 x <= 0) /\ Phy_ParametersFR1__pdsch_256QAM_FR1__F2 (Phy_ParametersFR1__pdsch_256QAM_FR1__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFR1__pdsch_256QAM_FR1__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFR1__pdsch_256QAM_FR1__F1 (Phy_ParametersFR1__pdsch_256QAM_FR1__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Type : Set :=
 | Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__n10
 | Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__n20
.
Definition Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__cond := (fun (_ : Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Type) => True).
Lemma Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__nat__helper.

Definition Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F1 t :=
  match t with
  | Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__n10 => 0
  | Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__n20 => 1
  end.
Definition Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F2 n :=
  match n with
  | 0 => Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__n10
  | 1 => Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__n20
  | _ => Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__n10
  end.
Lemma Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F1F2 : forall x : Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Type, (Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F1 x <= 1) /\ Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F2 (Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F2F1 : forall (y : nat) (H : y <= 1), Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F1 (Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F2 y) = y. enum_solve H y. Qed.

Inductive Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Type : Set :=
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n16
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n32
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n48
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n64
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n80
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n96
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n112
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n128
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n144
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n160
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n176
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n192
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n208
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n224
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n240
 | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n256
.
Definition Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__cond := (fun (_ : Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Type) => True).
Lemma Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__nat__helper.

Definition Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F1 t :=
  match t with
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n16 => 0
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n32 => 1
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n48 => 2
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n64 => 3
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n80 => 4
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n96 => 5
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n112 => 6
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n128 => 7
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n144 => 8
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n160 => 9
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n176 => 10
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n192 => 11
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n208 => 12
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n224 => 13
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n240 => 14
  | Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n256 => 15
  end.
Definition Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F2 n :=
  match n with
  | 0 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n16
  | 1 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n32
  | 2 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n48
  | 3 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n64
  | 4 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n80
  | 5 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n96
  | 6 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n112
  | 7 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n128
  | 8 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n144
  | 9 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n160
  | 10 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n176
  | 11 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n192
  | 12 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n208
  | 13 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n224
  | 14 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n240
  | 15 => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n256
  | _ => Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__n16
  end.
Lemma Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F1F2 : forall x : Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Type, (Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F1 x <= 15) /\ Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F2 (Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F2F1 : forall (y : nat) (H : y <= 15), Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F1 (Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFR1__ext0O__Type : Set :=
  make__Phy_ParametersFR1__ext0O__Type {
    Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot : option Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Type ;
}.
Definition Phy_ParametersFR1__ext0O__list := (
 Opt Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Type Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__cond ::
 nil).
Definition Phy_ParametersFR1__ext0O__cond z := 
  opt_cond Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__cond (Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot z) /\
  True.

Definition Phy_ParametersFR1__ext0__Type := Phy_ParametersFR1__ext0O__Type.
Definition Phy_ParametersFR1__ext0__cond := Phy_ParametersFR1__ext0O__cond.

Inductive Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Type : Set :=
 | Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__supported
.
Definition Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__cond := (fun (_ : Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Type) => True).
Lemma Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__nat__helper.

Definition Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F1 t :=
  match t with
  | Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__supported => 0
  end.
Definition Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F2 n :=
  match n with
  | 0 => Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__supported
  | _ => Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__supported
  end.
Lemma Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F1F2 : forall x : Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Type, (Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F1 x <= 0) /\ Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F2 (Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F1 x) = x. imp_solve. Qed.
Lemma Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F2F1 : forall (y : nat) (H : y <= 0), Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F1 (Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F2 y) = y. enum_solve H y. Qed.

Record Phy_ParametersFR1__ext1O__Type : Set :=
  make__Phy_ParametersFR1__ext1O__Type {
    Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16 : option Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Type ;
}.
Definition Phy_ParametersFR1__ext1O__list := (
 Opt Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Type Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__cond ::
 nil).
Definition Phy_ParametersFR1__ext1O__cond z := 
  opt_cond Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__cond (Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16 z) /\
  True.

Definition Phy_ParametersFR1__ext1__Type := Phy_ParametersFR1__ext1O__Type.
Definition Phy_ParametersFR1__ext1__cond := Phy_ParametersFR1__ext1O__cond.

Record Phy_ParametersFR1__Type : Set :=
  make__Phy_ParametersFR1__Type {
    Phy_ParametersFR1__pdcch_MonitoringSingleOccasion : option Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Type ;
    Phy_ParametersFR1__scs_60kHz : option Phy_ParametersFR1__scs_60kHz__Type ;
    Phy_ParametersFR1__pdsch_256QAM_FR1 : option Phy_ParametersFR1__pdsch_256QAM_FR1__Type ;
    Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol : option Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Type ;
    Phy_ParametersFR1__ext0 : option Phy_ParametersFR1__ext0__Type ;
    Phy_ParametersFR1__ext1 : option Phy_ParametersFR1__ext1__Type ;
}.
Definition Phy_ParametersFR1__root_list : list seq_elem := (
 Opt Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Type Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__cond ::
 Opt Phy_ParametersFR1__scs_60kHz__Type Phy_ParametersFR1__scs_60kHz__cond ::
 Opt Phy_ParametersFR1__pdsch_256QAM_FR1__Type Phy_ParametersFR1__pdsch_256QAM_FR1__cond ::
 Opt Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Type Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__cond ::
 nil).
Definition Phy_ParametersFR1__ext_list : list typ := (
  typ_cons Phy_ParametersFR1__ext0__Type Phy_ParametersFR1__ext0__cond ::
  typ_cons Phy_ParametersFR1__ext1__Type Phy_ParametersFR1__ext1__cond ::
  nil).
Definition Phy_ParametersFR1__cond (z : Phy_ParametersFR1__Type) := 
(  opt_cond Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__cond (Phy_ParametersFR1__pdcch_MonitoringSingleOccasion z) /\
  opt_cond Phy_ParametersFR1__scs_60kHz__cond (Phy_ParametersFR1__scs_60kHz z) /\
  opt_cond Phy_ParametersFR1__pdsch_256QAM_FR1__cond (Phy_ParametersFR1__pdsch_256QAM_FR1 z) /\
  opt_cond Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__cond (Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol z) /\
  True) /\ 
(  opt_cond Phy_ParametersFR1__ext0__cond (Phy_ParametersFR1__ext0 z) /\
  opt_cond Phy_ParametersFR1__ext1__cond (Phy_ParametersFR1__ext1 z) /\
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
Definition Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Format : T_Format Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__nat__Format Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F1 Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F2 Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F1F2 Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__F2F1.

Opaque Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__cond Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Format.

Definition Phy_ParametersFR1__scs_60kHz__Format : T_Format Phy_ParametersFR1__scs_60kHz__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFR1__scs_60kHz__nat__Format Phy_ParametersFR1__scs_60kHz__F1 Phy_ParametersFR1__scs_60kHz__F2 Phy_ParametersFR1__scs_60kHz__F1F2 Phy_ParametersFR1__scs_60kHz__F2F1.

Opaque Phy_ParametersFR1__scs_60kHz__cond Phy_ParametersFR1__scs_60kHz__Format.

Definition Phy_ParametersFR1__pdsch_256QAM_FR1__Format : T_Format Phy_ParametersFR1__pdsch_256QAM_FR1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFR1__pdsch_256QAM_FR1__nat__Format Phy_ParametersFR1__pdsch_256QAM_FR1__F1 Phy_ParametersFR1__pdsch_256QAM_FR1__F2 Phy_ParametersFR1__pdsch_256QAM_FR1__F1F2 Phy_ParametersFR1__pdsch_256QAM_FR1__F2F1.

Opaque Phy_ParametersFR1__pdsch_256QAM_FR1__cond Phy_ParametersFR1__pdsch_256QAM_FR1__Format.

Definition Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Format : T_Format Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__nat__Format Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F1 Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F2 Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F1F2 Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__F2F1.

Opaque Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__cond Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Format.

Definition Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Format : T_Format Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__nat__Format Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F1 Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F2 Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F1F2 Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__F2F1.

Opaque Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__cond Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Format.


Definition Phy_ParametersFR1__ext0O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFR1__ext0O__list.
Definition Phy_ParametersFR1__ext0O__Format_list : Phy_ParametersFR1__ext0O__Format_Type :=
  (Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot__Format, unit_format).
Definition Phy_ParametersFR1__ext0O__list__Format := (*Eval compute in *) seq_format Phy_ParametersFR1__ext0O__list Phy_ParametersFR1__ext0O__Format_list.
Definition Phy_ParametersFR1__ext0O__F1 z :=
  (Phy_ParametersFR1__ext0O__pdsch_RE_MappingFR1_PerSlot z, tt).
Definition Phy_ParametersFR1__ext0O__F2 (y : seq_type Phy_ParametersFR1__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersFR1__ext0O__Type i0
  end.
Lemma Phy_ParametersFR1__ext0O__F1F2_cond (z : Phy_ParametersFR1__ext0O__Type)
  : Phy_ParametersFR1__ext0O__cond z ->
  (seq_cond Phy_ParametersFR1__ext0O__list (Phy_ParametersFR1__ext0O__F1 z)).
intro H. unfold Phy_ParametersFR1__ext0O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFR1__ext0O__F1F2_cond2 (z : Phy_ParametersFR1__ext0O__Type)
 : Phy_ParametersFR1__ext0O__F2 (Phy_ParametersFR1__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFR1__ext0O__F2F1_cond (y : seq_type Phy_ParametersFR1__ext0O__list)
  : seq_cond Phy_ParametersFR1__ext0O__list y ->
 (Phy_ParametersFR1__ext0O__cond (Phy_ParametersFR1__ext0O__F2 y)) /\  Phy_ParametersFR1__ext0O__F1 (Phy_ParametersFR1__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFR1__ext0O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFR1__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFR1__ext0O__Format : T_Format Phy_ParametersFR1__ext0O__Type Phy_ParametersFR1__ext0O__cond :=
        proj2_format  Phy_ParametersFR1__ext0O__cond Phy_ParametersFR1__ext0O__list__Format
    Phy_ParametersFR1__ext0O__F1 Phy_ParametersFR1__ext0O__F2 Phy_ParametersFR1__ext0O__F1F2_cond  Phy_ParametersFR1__ext0O__F1F2_cond2 Phy_ParametersFR1__ext0O__F2F1_cond.
Opaque Phy_ParametersFR1__ext0O__cond Phy_ParametersFR1__ext0O__Format.

Definition Phy_ParametersFR1__ext0__check_all_none (b : Phy_ParametersFR1__ext0O__Type) : bool :=
match b with 
  | make__Phy_ParametersFR1__ext0O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersFR1__ext0__Format : T_Format Phy_ParametersFR1__ext0__Type Phy_ParametersFR1__ext0__cond :=
  restrict_add_format Phy_ParametersFR1__ext0__check_all_none Phy_ParametersFR1__ext0O__Format.

Opaque Phy_ParametersFR1__ext0__cond Phy_ParametersFR1__ext0__Format.

Definition Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Format : T_Format Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__nat__Format Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F1 Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F2 Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F1F2 Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__F2F1.

Opaque Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__cond Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Format.


Definition Phy_ParametersFR1__ext1O__Format_Type := Eval cbn in seq_format_prod Phy_ParametersFR1__ext1O__list.
Definition Phy_ParametersFR1__ext1O__Format_list : Phy_ParametersFR1__ext1O__Format_Type :=
  (Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16__Format, unit_format).
Definition Phy_ParametersFR1__ext1O__list__Format := (*Eval compute in *) seq_format Phy_ParametersFR1__ext1O__list Phy_ParametersFR1__ext1O__Format_list.
Definition Phy_ParametersFR1__ext1O__F1 z :=
  (Phy_ParametersFR1__ext1O__pdcch_MonitoringSingleSpanFirst4Sym_r16 z, tt).
Definition Phy_ParametersFR1__ext1O__F2 (y : seq_type Phy_ParametersFR1__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__Phy_ParametersFR1__ext1O__Type i0
  end.
Lemma Phy_ParametersFR1__ext1O__F1F2_cond (z : Phy_ParametersFR1__ext1O__Type)
  : Phy_ParametersFR1__ext1O__cond z ->
  (seq_cond Phy_ParametersFR1__ext1O__list (Phy_ParametersFR1__ext1O__F1 z)).
intro H. unfold Phy_ParametersFR1__ext1O__cond in H. simpl. auto. Qed.
Lemma Phy_ParametersFR1__ext1O__F1F2_cond2 (z : Phy_ParametersFR1__ext1O__Type)
 : Phy_ParametersFR1__ext1O__F2 (Phy_ParametersFR1__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma Phy_ParametersFR1__ext1O__F2F1_cond (y : seq_type Phy_ParametersFR1__ext1O__list)
  : seq_cond Phy_ParametersFR1__ext1O__list y ->
 (Phy_ParametersFR1__ext1O__cond (Phy_ParametersFR1__ext1O__F2 y)) /\  Phy_ParametersFR1__ext1O__F1 (Phy_ParametersFR1__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold Phy_ParametersFR1__ext1O__cond. simpl in *. auto.
 - simpl. unfold Phy_ParametersFR1__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition Phy_ParametersFR1__ext1O__Format : T_Format Phy_ParametersFR1__ext1O__Type Phy_ParametersFR1__ext1O__cond :=
        proj2_format  Phy_ParametersFR1__ext1O__cond Phy_ParametersFR1__ext1O__list__Format
    Phy_ParametersFR1__ext1O__F1 Phy_ParametersFR1__ext1O__F2 Phy_ParametersFR1__ext1O__F1F2_cond  Phy_ParametersFR1__ext1O__F1F2_cond2 Phy_ParametersFR1__ext1O__F2F1_cond.
Opaque Phy_ParametersFR1__ext1O__cond Phy_ParametersFR1__ext1O__Format.

Definition Phy_ParametersFR1__ext1__check_all_none (b : Phy_ParametersFR1__ext1O__Type) : bool :=
match b with 
  | make__Phy_ParametersFR1__ext1O__Type None  => false 
  | _ => true 
 end.
Definition Phy_ParametersFR1__ext1__Format : T_Format Phy_ParametersFR1__ext1__Type Phy_ParametersFR1__ext1__cond :=
  restrict_add_format Phy_ParametersFR1__ext1__check_all_none Phy_ParametersFR1__ext1O__Format.

Opaque Phy_ParametersFR1__ext1__cond Phy_ParametersFR1__ext1__Format.


Definition Phy_ParametersFR1__root_Format_Type := Eval cbn in seq_format_prod Phy_ParametersFR1__root_list.
Definition Phy_ParametersFR1__root_Format_list : Phy_ParametersFR1__root_Format_Type :=
  (Phy_ParametersFR1__pdcch_MonitoringSingleOccasion__Format, (Phy_ParametersFR1__scs_60kHz__Format, (Phy_ParametersFR1__pdsch_256QAM_FR1__Format, (Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol__Format, unit_format)))).

Definition Phy_ParametersFR1__ext_Format_Type := Eval cbn in get_formats Phy_ParametersFR1__ext_list.
Definition Phy_ParametersFR1__ext_Format_list : Phy_ParametersFR1__ext_Format_Type :=
  (Phy_ParametersFR1__ext0__Format, (Phy_ParametersFR1__ext1__Format, unit__Format)).

Definition Phy_ParametersFR1__list_type : Set := (seq_type Phy_ParametersFR1__root_list) * (seq_ext_type Phy_ParametersFR1__ext_list).
Definition Phy_ParametersFR1__list_cond (z : Phy_ParametersFR1__list_type) : Prop :=
        (seq_cond Phy_ParametersFR1__root_list (fst z)) /\ (seq_ext_cond Phy_ParametersFR1__ext_list (snd z)).
Definition Phy_ParametersFR1__list_format : T_Format Phy_ParametersFR1__list_type Phy_ParametersFR1__list_cond :=
 (* Eval compute in *) seq_ext_format Phy_ParametersFR1__root_list Phy_ParametersFR1__root_Format_list Phy_ParametersFR1__ext_list Phy_ParametersFR1__ext_Format_list.

Opaque Phy_ParametersFR1__list_format.
Definition Phy_ParametersFR1__F1 (z : Phy_ParametersFR1__Type) : Phy_ParametersFR1__list_type :=
  (((Phy_ParametersFR1__pdcch_MonitoringSingleOccasion z, (Phy_ParametersFR1__scs_60kHz z, (Phy_ParametersFR1__pdsch_256QAM_FR1 z, (Phy_ParametersFR1__pdsch_RE_MappingFR1_PerSymbol z, tt))))), (
(Phy_ParametersFR1__ext0 z, (Phy_ParametersFR1__ext1 z, tt)))).
Definition Phy_ParametersFR1__F2 (y : Phy_ParametersFR1__list_type) : Phy_ParametersFR1__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, (i1, _)))=>
    make__Phy_ParametersFR1__Type j0 j1 j2 j3 i0 i1
  end.
Definition Phy_ParametersFR1__helper1 : (forall a : Phy_ParametersFR1__Type, Phy_ParametersFR1__cond a -> Phy_ParametersFR1__list_cond (Phy_ParametersFR1__F1 a)).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersFR1__helper2 : (forall a : Phy_ParametersFR1__Type, Phy_ParametersFR1__F2 (Phy_ParametersFR1__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition Phy_ParametersFR1__helper3 : (forall b : Phy_ParametersFR1__list_type, Phy_ParametersFR1__list_cond b -> Phy_ParametersFR1__cond (Phy_ParametersFR1__F2 b) /\ Phy_ParametersFR1__F1 (Phy_ParametersFR1__F2 b) = b).
                     intros. destruct b as [y y1]. unfold Phy_ParametersFR1__cond, Phy_ParametersFR1__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition Phy_ParametersFR1__Format : T_Format Phy_ParametersFR1__Type Phy_ParametersFR1__cond :=
 proj2_format Phy_ParametersFR1__cond Phy_ParametersFR1__list_format  Phy_ParametersFR1__F1 Phy_ParametersFR1__F2 Phy_ParametersFR1__helper1 Phy_ParametersFR1__helper2 Phy_ParametersFR1__helper3.

Opaque Phy_ParametersFR1__cond Phy_ParametersFR1__Format.

