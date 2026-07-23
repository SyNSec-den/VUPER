Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RMTC_Config_r16__rmtc_Periodicity_r16__Type : Set :=
 | RMTC_Config_r16__rmtc_Periodicity_r16__ms40
 | RMTC_Config_r16__rmtc_Periodicity_r16__ms80
 | RMTC_Config_r16__rmtc_Periodicity_r16__ms160
 | RMTC_Config_r16__rmtc_Periodicity_r16__ms320
 | RMTC_Config_r16__rmtc_Periodicity_r16__ms640
.
Definition RMTC_Config_r16__rmtc_Periodicity_r16__cond := (fun (_ : RMTC_Config_r16__rmtc_Periodicity_r16__Type) => True).
Lemma RMTC_Config_r16__rmtc_Periodicity_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RMTC_Config_r16__rmtc_Periodicity_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 RMTC_Config_r16__rmtc_Periodicity_r16__nat__helper.

Definition RMTC_Config_r16__rmtc_Periodicity_r16__F1 t :=
  match t with
  | RMTC_Config_r16__rmtc_Periodicity_r16__ms40 => 0
  | RMTC_Config_r16__rmtc_Periodicity_r16__ms80 => 1
  | RMTC_Config_r16__rmtc_Periodicity_r16__ms160 => 2
  | RMTC_Config_r16__rmtc_Periodicity_r16__ms320 => 3
  | RMTC_Config_r16__rmtc_Periodicity_r16__ms640 => 4
  end.
Definition RMTC_Config_r16__rmtc_Periodicity_r16__F2 n :=
  match n with
  | 0 => RMTC_Config_r16__rmtc_Periodicity_r16__ms40
  | 1 => RMTC_Config_r16__rmtc_Periodicity_r16__ms80
  | 2 => RMTC_Config_r16__rmtc_Periodicity_r16__ms160
  | 3 => RMTC_Config_r16__rmtc_Periodicity_r16__ms320
  | 4 => RMTC_Config_r16__rmtc_Periodicity_r16__ms640
  | _ => RMTC_Config_r16__rmtc_Periodicity_r16__ms40
  end.
Lemma RMTC_Config_r16__rmtc_Periodicity_r16__F1F2 : forall x : RMTC_Config_r16__rmtc_Periodicity_r16__Type, (RMTC_Config_r16__rmtc_Periodicity_r16__F1 x <= 4) /\ RMTC_Config_r16__rmtc_Periodicity_r16__F2 (RMTC_Config_r16__rmtc_Periodicity_r16__F1 x) = x. imp_solve. Qed.
Lemma RMTC_Config_r16__rmtc_Periodicity_r16__F2F1 : forall (y : nat) (H : y <= 4), RMTC_Config_r16__rmtc_Periodicity_r16__F1 (RMTC_Config_r16__rmtc_Periodicity_r16__F2 y) = y. enum_solve H y. Qed.

Lemma RMTC_Config_r16__rmtc_SubframeOffset_r16__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma RMTC_Config_r16__rmtc_SubframeOffset_r16__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RMTC_Config_r16__rmtc_SubframeOffset_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RMTC_Config_r16__rmtc_SubframeOffset_r16__Type := Z.
Definition RMTC_Config_r16__rmtc_SubframeOffset_r16__cond := (fun z => (0 <= z <= 639)%Z).
Inductive RMTC_Config_r16__measDurationSymbols_r16__Type : Set :=
 | RMTC_Config_r16__measDurationSymbols_r16__sym1
 | RMTC_Config_r16__measDurationSymbols_r16__sym14or12
 | RMTC_Config_r16__measDurationSymbols_r16__sym28or24
 | RMTC_Config_r16__measDurationSymbols_r16__sym42or36
 | RMTC_Config_r16__measDurationSymbols_r16__sym70or60
.
Definition RMTC_Config_r16__measDurationSymbols_r16__cond := (fun (_ : RMTC_Config_r16__measDurationSymbols_r16__Type) => True).
Lemma RMTC_Config_r16__measDurationSymbols_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RMTC_Config_r16__measDurationSymbols_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 RMTC_Config_r16__measDurationSymbols_r16__nat__helper.

Definition RMTC_Config_r16__measDurationSymbols_r16__F1 t :=
  match t with
  | RMTC_Config_r16__measDurationSymbols_r16__sym1 => 0
  | RMTC_Config_r16__measDurationSymbols_r16__sym14or12 => 1
  | RMTC_Config_r16__measDurationSymbols_r16__sym28or24 => 2
  | RMTC_Config_r16__measDurationSymbols_r16__sym42or36 => 3
  | RMTC_Config_r16__measDurationSymbols_r16__sym70or60 => 4
  end.
Definition RMTC_Config_r16__measDurationSymbols_r16__F2 n :=
  match n with
  | 0 => RMTC_Config_r16__measDurationSymbols_r16__sym1
  | 1 => RMTC_Config_r16__measDurationSymbols_r16__sym14or12
  | 2 => RMTC_Config_r16__measDurationSymbols_r16__sym28or24
  | 3 => RMTC_Config_r16__measDurationSymbols_r16__sym42or36
  | 4 => RMTC_Config_r16__measDurationSymbols_r16__sym70or60
  | _ => RMTC_Config_r16__measDurationSymbols_r16__sym1
  end.
Lemma RMTC_Config_r16__measDurationSymbols_r16__F1F2 : forall x : RMTC_Config_r16__measDurationSymbols_r16__Type, (RMTC_Config_r16__measDurationSymbols_r16__F1 x <= 4) /\ RMTC_Config_r16__measDurationSymbols_r16__F2 (RMTC_Config_r16__measDurationSymbols_r16__F1 x) = x. imp_solve. Qed.
Lemma RMTC_Config_r16__measDurationSymbols_r16__F2F1 : forall (y : nat) (H : y <= 4), RMTC_Config_r16__measDurationSymbols_r16__F1 (RMTC_Config_r16__measDurationSymbols_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Inductive RMTC_Config_r16__ref_SCS_CP_r16__Type : Set :=
 | RMTC_Config_r16__ref_SCS_CP_r16__kHz15
 | RMTC_Config_r16__ref_SCS_CP_r16__kHz30
 | RMTC_Config_r16__ref_SCS_CP_r16__kHz60_NCP
 | RMTC_Config_r16__ref_SCS_CP_r16__kHz60_ECP
.
Definition RMTC_Config_r16__ref_SCS_CP_r16__cond := (fun (_ : RMTC_Config_r16__ref_SCS_CP_r16__Type) => True).
Lemma RMTC_Config_r16__ref_SCS_CP_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RMTC_Config_r16__ref_SCS_CP_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 RMTC_Config_r16__ref_SCS_CP_r16__nat__helper.

Definition RMTC_Config_r16__ref_SCS_CP_r16__F1 t :=
  match t with
  | RMTC_Config_r16__ref_SCS_CP_r16__kHz15 => 0
  | RMTC_Config_r16__ref_SCS_CP_r16__kHz30 => 1
  | RMTC_Config_r16__ref_SCS_CP_r16__kHz60_NCP => 2
  | RMTC_Config_r16__ref_SCS_CP_r16__kHz60_ECP => 3
  end.
Definition RMTC_Config_r16__ref_SCS_CP_r16__F2 n :=
  match n with
  | 0 => RMTC_Config_r16__ref_SCS_CP_r16__kHz15
  | 1 => RMTC_Config_r16__ref_SCS_CP_r16__kHz30
  | 2 => RMTC_Config_r16__ref_SCS_CP_r16__kHz60_NCP
  | 3 => RMTC_Config_r16__ref_SCS_CP_r16__kHz60_ECP
  | _ => RMTC_Config_r16__ref_SCS_CP_r16__kHz15
  end.
Lemma RMTC_Config_r16__ref_SCS_CP_r16__F1F2 : forall x : RMTC_Config_r16__ref_SCS_CP_r16__Type, (RMTC_Config_r16__ref_SCS_CP_r16__F1 x <= 3) /\ RMTC_Config_r16__ref_SCS_CP_r16__F2 (RMTC_Config_r16__ref_SCS_CP_r16__F1 x) = x. imp_solve. Qed.
Lemma RMTC_Config_r16__ref_SCS_CP_r16__F2F1 : forall (y : nat) (H : y <= 3), RMTC_Config_r16__ref_SCS_CP_r16__F1 (RMTC_Config_r16__ref_SCS_CP_r16__F2 y) = y. enum_solve H y. Qed.

Inductive RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Type : Set :=
 | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz100
 | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz400
 | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz800
 | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz1600
 | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz2000
.
Definition RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__cond := (fun (_ : RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Type) => True).
Lemma RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__nat__helper.

Definition RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F1 t :=
  match t with
  | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz100 => 0
  | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz400 => 1
  | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz800 => 2
  | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz1600 => 3
  | RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz2000 => 4
  end.
Definition RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F2 n :=
  match n with
  | 0 => RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz100
  | 1 => RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz400
  | 2 => RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz800
  | 3 => RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz1600
  | 4 => RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz2000
  | _ => RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__mhz100
  end.
Lemma RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F1F2 : forall x : RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Type, (RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F1 x <= 4) /\ RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F2 (RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F1 x) = x. imp_solve. Qed.
Lemma RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F2F1 : forall (y : nat) (H : y <= 4), RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F1 (RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F2 y) = y. enum_solve H y. Qed.

Inductive RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Type : Set :=
 | RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym140
 | RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym560
 | RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym1120
.
Definition RMTC_Config_r16__ext0O__measDurationSymbols_v1700__cond := (fun (_ : RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Type) => True).
Lemma RMTC_Config_r16__ext0O__measDurationSymbols_v1700__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RMTC_Config_r16__ext0O__measDurationSymbols_v1700__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 RMTC_Config_r16__ext0O__measDurationSymbols_v1700__nat__helper.

Definition RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F1 t :=
  match t with
  | RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym140 => 0
  | RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym560 => 1
  | RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym1120 => 2
  end.
Definition RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F2 n :=
  match n with
  | 0 => RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym140
  | 1 => RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym560
  | 2 => RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym1120
  | _ => RMTC_Config_r16__ext0O__measDurationSymbols_v1700__sym140
  end.
Lemma RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F1F2 : forall x : RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Type, (RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F1 x <= 2) /\ RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F2 (RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F1 x) = x. imp_solve. Qed.
Lemma RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F2F1 : forall (y : nat) (H : y <= 2), RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F1 (RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F2 y) = y. enum_solve H y. Qed.

Inductive RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Type : Set :=
 | RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz120
 | RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz480
 | RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz960
.
Definition RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__cond := (fun (_ : RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Type) => True).
Lemma RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__nat__helper.

Definition RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F1 t :=
  match t with
  | RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz120 => 0
  | RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz480 => 1
  | RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz960 => 2
  end.
Definition RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F2 n :=
  match n with
  | 0 => RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz120
  | 1 => RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz480
  | 2 => RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz960
  | _ => RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__kHz120
  end.
Lemma RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F1F2 : forall x : RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Type, (RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F1 x <= 2) /\ RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F2 (RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F1 x) = x. imp_solve. Qed.
Lemma RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F2F1 : forall (y : nat) (H : y <= 2), RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F1 (RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F2 y) = y. enum_solve H y. Qed.

Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Require Import NR.ServCellIndex.

Opaque ServCellIndex__cond ServCellIndex__Format.

Record RMTC_Config_r16__ext0O__tci_StateInfo_r17__Type : Set :=
  make__RMTC_Config_r16__ext0O__tci_StateInfo_r17__Type {
    RMTC_Config_r16__ext0O__tci_StateInfo_r17__tci_StateId_r17 : TCI_StateId__Type ;
    RMTC_Config_r16__ext0O__tci_StateInfo_r17__ref_ServCellId_r17 : option ServCellIndex__Type ;
}.
Definition RMTC_Config_r16__ext0O__tci_StateInfo_r17__list := (
 Nor TCI_StateId__Type TCI_StateId__cond ::
 Opt ServCellIndex__Type ServCellIndex__cond ::
 nil).
Definition RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond z := 
  TCI_StateId__cond (RMTC_Config_r16__ext0O__tci_StateInfo_r17__tci_StateId_r17 z) /\
  opt_cond ServCellIndex__cond (RMTC_Config_r16__ext0O__tci_StateInfo_r17__ref_ServCellId_r17 z) /\
  True.

Record RMTC_Config_r16__ext0O__Type : Set :=
  make__RMTC_Config_r16__ext0O__Type {
    RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17 : option RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Type ;
    RMTC_Config_r16__ext0O__measDurationSymbols_v1700 : option RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Type ;
    RMTC_Config_r16__ext0O__ref_SCS_CP_v1700 : option RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Type ;
    RMTC_Config_r16__ext0O__tci_StateInfo_r17 : option RMTC_Config_r16__ext0O__tci_StateInfo_r17__Type ;
}.
Definition RMTC_Config_r16__ext0O__list := (
 Opt RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Type RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__cond ::
 Opt RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Type RMTC_Config_r16__ext0O__measDurationSymbols_v1700__cond ::
 Opt RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Type RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__cond ::
 Opt RMTC_Config_r16__ext0O__tci_StateInfo_r17__Type RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond ::
 nil).
Definition RMTC_Config_r16__ext0O__cond z := 
  opt_cond RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__cond (RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17 z) /\
  opt_cond RMTC_Config_r16__ext0O__measDurationSymbols_v1700__cond (RMTC_Config_r16__ext0O__measDurationSymbols_v1700 z) /\
  opt_cond RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__cond (RMTC_Config_r16__ext0O__ref_SCS_CP_v1700 z) /\
  opt_cond RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond (RMTC_Config_r16__ext0O__tci_StateInfo_r17 z) /\
  True.

Definition RMTC_Config_r16__ext0__Type := RMTC_Config_r16__ext0O__Type.
Definition RMTC_Config_r16__ext0__cond := RMTC_Config_r16__ext0O__cond.

Require Import NR.BWP_Id.

Opaque BWP_Id__cond BWP_Id__Format.

Record RMTC_Config_r16__ext1O__Type : Set :=
  make__RMTC_Config_r16__ext1O__Type {
    RMTC_Config_r16__ext1O__ref_BWPId_r17 : option BWP_Id__Type ;
}.
Definition RMTC_Config_r16__ext1O__list := (
 Opt BWP_Id__Type BWP_Id__cond ::
 nil).
Definition RMTC_Config_r16__ext1O__cond z := 
  opt_cond BWP_Id__cond (RMTC_Config_r16__ext1O__ref_BWPId_r17 z) /\
  True.

Definition RMTC_Config_r16__ext1__Type := RMTC_Config_r16__ext1O__Type.
Definition RMTC_Config_r16__ext1__cond := RMTC_Config_r16__ext1O__cond.

Record RMTC_Config_r16__Type : Set :=
  make__RMTC_Config_r16__Type {
    RMTC_Config_r16__rmtc_Periodicity_r16 : RMTC_Config_r16__rmtc_Periodicity_r16__Type ;
    RMTC_Config_r16__rmtc_SubframeOffset_r16 : option Z ;
    RMTC_Config_r16__measDurationSymbols_r16 : RMTC_Config_r16__measDurationSymbols_r16__Type ;
    RMTC_Config_r16__rmtc_Frequency_r16 : ARFCN_ValueNR__Type ;
    RMTC_Config_r16__ref_SCS_CP_r16 : RMTC_Config_r16__ref_SCS_CP_r16__Type ;
    RMTC_Config_r16__ext0 : option RMTC_Config_r16__ext0__Type ;
    RMTC_Config_r16__ext1 : option RMTC_Config_r16__ext1__Type ;
}.
Definition RMTC_Config_r16__root_list : list seq_elem := (
 Nor RMTC_Config_r16__rmtc_Periodicity_r16__Type RMTC_Config_r16__rmtc_Periodicity_r16__cond ::
 Opt Z RMTC_Config_r16__rmtc_SubframeOffset_r16__cond ::
 Nor RMTC_Config_r16__measDurationSymbols_r16__Type RMTC_Config_r16__measDurationSymbols_r16__cond ::
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor RMTC_Config_r16__ref_SCS_CP_r16__Type RMTC_Config_r16__ref_SCS_CP_r16__cond ::
 nil).
Definition RMTC_Config_r16__ext_list : list typ := (
  typ_cons RMTC_Config_r16__ext0__Type RMTC_Config_r16__ext0__cond ::
  typ_cons RMTC_Config_r16__ext1__Type RMTC_Config_r16__ext1__cond ::
  nil).
Definition RMTC_Config_r16__cond (z : RMTC_Config_r16__Type) := 
(  RMTC_Config_r16__rmtc_Periodicity_r16__cond (RMTC_Config_r16__rmtc_Periodicity_r16 z) /\
  opt_cond RMTC_Config_r16__rmtc_SubframeOffset_r16__cond (RMTC_Config_r16__rmtc_SubframeOffset_r16 z) /\
  RMTC_Config_r16__measDurationSymbols_r16__cond (RMTC_Config_r16__measDurationSymbols_r16 z) /\
  ARFCN_ValueNR__cond (RMTC_Config_r16__rmtc_Frequency_r16 z) /\
  RMTC_Config_r16__ref_SCS_CP_r16__cond (RMTC_Config_r16__ref_SCS_CP_r16 z) /\
  True) /\ 
(  opt_cond RMTC_Config_r16__ext0__cond (RMTC_Config_r16__ext0 z) /\
  opt_cond RMTC_Config_r16__ext1__cond (RMTC_Config_r16__ext1 z) /\
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
Definition RMTC_Config_r16__rmtc_Periodicity_r16__Format : T_Format RMTC_Config_r16__rmtc_Periodicity_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RMTC_Config_r16__rmtc_Periodicity_r16__nat__Format RMTC_Config_r16__rmtc_Periodicity_r16__F1 RMTC_Config_r16__rmtc_Periodicity_r16__F2 RMTC_Config_r16__rmtc_Periodicity_r16__F1F2 RMTC_Config_r16__rmtc_Periodicity_r16__F2F1.

Opaque RMTC_Config_r16__rmtc_Periodicity_r16__cond RMTC_Config_r16__rmtc_Periodicity_r16__Format.

Definition RMTC_Config_r16__rmtc_SubframeOffset_r16__Format : T_Format Z RMTC_Config_r16__rmtc_SubframeOffset_r16__cond :=
 ranged_int_format (0) (639) RMTC_Config_r16__rmtc_SubframeOffset_r16__helper1 RMTC_Config_r16__rmtc_SubframeOffset_r16__helper2.

Opaque RMTC_Config_r16__rmtc_SubframeOffset_r16__cond RMTC_Config_r16__rmtc_SubframeOffset_r16__Format.

Definition RMTC_Config_r16__measDurationSymbols_r16__Format : T_Format RMTC_Config_r16__measDurationSymbols_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RMTC_Config_r16__measDurationSymbols_r16__nat__Format RMTC_Config_r16__measDurationSymbols_r16__F1 RMTC_Config_r16__measDurationSymbols_r16__F2 RMTC_Config_r16__measDurationSymbols_r16__F1F2 RMTC_Config_r16__measDurationSymbols_r16__F2F1.

Opaque RMTC_Config_r16__measDurationSymbols_r16__cond RMTC_Config_r16__measDurationSymbols_r16__Format.

Definition RMTC_Config_r16__ref_SCS_CP_r16__Format : T_Format RMTC_Config_r16__ref_SCS_CP_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RMTC_Config_r16__ref_SCS_CP_r16__nat__Format RMTC_Config_r16__ref_SCS_CP_r16__F1 RMTC_Config_r16__ref_SCS_CP_r16__F2 RMTC_Config_r16__ref_SCS_CP_r16__F1F2 RMTC_Config_r16__ref_SCS_CP_r16__F2F1.

Opaque RMTC_Config_r16__ref_SCS_CP_r16__cond RMTC_Config_r16__ref_SCS_CP_r16__Format.

Definition RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Format : T_Format RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__nat__Format RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F1 RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F2 RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F1F2 RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__F2F1.

Opaque RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__cond RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Format.

Definition RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Format : T_Format RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RMTC_Config_r16__ext0O__measDurationSymbols_v1700__nat__Format RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F1 RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F2 RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F1F2 RMTC_Config_r16__ext0O__measDurationSymbols_v1700__F2F1.

Opaque RMTC_Config_r16__ext0O__measDurationSymbols_v1700__cond RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Format.

Definition RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Format : T_Format RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__nat__Format RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F1 RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F2 RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F1F2 RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__F2F1.

Opaque RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__cond RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Format.


Definition RMTC_Config_r16__ext0O__tci_StateInfo_r17__Format_Type := Eval cbn in seq_format_prod RMTC_Config_r16__ext0O__tci_StateInfo_r17__list.
Definition RMTC_Config_r16__ext0O__tci_StateInfo_r17__Format_list : RMTC_Config_r16__ext0O__tci_StateInfo_r17__Format_Type :=
  (TCI_StateId__Format, (ServCellIndex__Format, unit_format)).
Definition RMTC_Config_r16__ext0O__tci_StateInfo_r17__list__Format := (*Eval compute in *) seq_format RMTC_Config_r16__ext0O__tci_StateInfo_r17__list RMTC_Config_r16__ext0O__tci_StateInfo_r17__Format_list.
Definition RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1 z :=
  (RMTC_Config_r16__ext0O__tci_StateInfo_r17__tci_StateId_r17 z, (RMTC_Config_r16__ext0O__tci_StateInfo_r17__ref_ServCellId_r17 z, tt)).
Definition RMTC_Config_r16__ext0O__tci_StateInfo_r17__F2 (y : seq_type RMTC_Config_r16__ext0O__tci_StateInfo_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__RMTC_Config_r16__ext0O__tci_StateInfo_r17__Type i0 i1
  end.
Lemma RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1F2_cond (z : RMTC_Config_r16__ext0O__tci_StateInfo_r17__Type)
  : RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond z ->
  (seq_cond RMTC_Config_r16__ext0O__tci_StateInfo_r17__list (RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1 z)).
intro H. unfold RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond in H. simpl. auto. Qed.
Lemma RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1F2_cond2 (z : RMTC_Config_r16__ext0O__tci_StateInfo_r17__Type)
 : RMTC_Config_r16__ext0O__tci_StateInfo_r17__F2 (RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RMTC_Config_r16__ext0O__tci_StateInfo_r17__F2F1_cond (y : seq_type RMTC_Config_r16__ext0O__tci_StateInfo_r17__list)
  : seq_cond RMTC_Config_r16__ext0O__tci_StateInfo_r17__list y ->
 (RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond (RMTC_Config_r16__ext0O__tci_StateInfo_r17__F2 y)) /\  RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1 (RMTC_Config_r16__ext0O__tci_StateInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond. simpl in *. auto.
 - simpl. unfold RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RMTC_Config_r16__ext0O__tci_StateInfo_r17__Format : T_Format RMTC_Config_r16__ext0O__tci_StateInfo_r17__Type RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond :=
        proj2_format  RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond RMTC_Config_r16__ext0O__tci_StateInfo_r17__list__Format
    RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1 RMTC_Config_r16__ext0O__tci_StateInfo_r17__F2 RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1F2_cond  RMTC_Config_r16__ext0O__tci_StateInfo_r17__F1F2_cond2 RMTC_Config_r16__ext0O__tci_StateInfo_r17__F2F1_cond.
Opaque RMTC_Config_r16__ext0O__tci_StateInfo_r17__cond RMTC_Config_r16__ext0O__tci_StateInfo_r17__Format.


Definition RMTC_Config_r16__ext0O__Format_Type := Eval cbn in seq_format_prod RMTC_Config_r16__ext0O__list.
Definition RMTC_Config_r16__ext0O__Format_list : RMTC_Config_r16__ext0O__Format_Type :=
  (RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17__Format, (RMTC_Config_r16__ext0O__measDurationSymbols_v1700__Format, (RMTC_Config_r16__ext0O__ref_SCS_CP_v1700__Format, (RMTC_Config_r16__ext0O__tci_StateInfo_r17__Format, unit_format)))).
Definition RMTC_Config_r16__ext0O__list__Format := (*Eval compute in *) seq_format RMTC_Config_r16__ext0O__list RMTC_Config_r16__ext0O__Format_list.
Definition RMTC_Config_r16__ext0O__F1 z :=
  (RMTC_Config_r16__ext0O__rmtc_Bandwidth_r17 z, (RMTC_Config_r16__ext0O__measDurationSymbols_v1700 z, (RMTC_Config_r16__ext0O__ref_SCS_CP_v1700 z, (RMTC_Config_r16__ext0O__tci_StateInfo_r17 z, tt)))).
Definition RMTC_Config_r16__ext0O__F2 (y : seq_type RMTC_Config_r16__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__RMTC_Config_r16__ext0O__Type i0 i1 i2 i3
  end.
Lemma RMTC_Config_r16__ext0O__F1F2_cond (z : RMTC_Config_r16__ext0O__Type)
  : RMTC_Config_r16__ext0O__cond z ->
  (seq_cond RMTC_Config_r16__ext0O__list (RMTC_Config_r16__ext0O__F1 z)).
intro H. unfold RMTC_Config_r16__ext0O__cond in H. simpl. auto. Qed.
Lemma RMTC_Config_r16__ext0O__F1F2_cond2 (z : RMTC_Config_r16__ext0O__Type)
 : RMTC_Config_r16__ext0O__F2 (RMTC_Config_r16__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RMTC_Config_r16__ext0O__F2F1_cond (y : seq_type RMTC_Config_r16__ext0O__list)
  : seq_cond RMTC_Config_r16__ext0O__list y ->
 (RMTC_Config_r16__ext0O__cond (RMTC_Config_r16__ext0O__F2 y)) /\  RMTC_Config_r16__ext0O__F1 (RMTC_Config_r16__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RMTC_Config_r16__ext0O__cond. simpl in *. auto.
 - simpl. unfold RMTC_Config_r16__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RMTC_Config_r16__ext0O__Format : T_Format RMTC_Config_r16__ext0O__Type RMTC_Config_r16__ext0O__cond :=
        proj2_format  RMTC_Config_r16__ext0O__cond RMTC_Config_r16__ext0O__list__Format
    RMTC_Config_r16__ext0O__F1 RMTC_Config_r16__ext0O__F2 RMTC_Config_r16__ext0O__F1F2_cond  RMTC_Config_r16__ext0O__F1F2_cond2 RMTC_Config_r16__ext0O__F2F1_cond.
Opaque RMTC_Config_r16__ext0O__cond RMTC_Config_r16__ext0O__Format.

Definition RMTC_Config_r16__ext0__check_all_none (b : RMTC_Config_r16__ext0O__Type) : bool :=
match b with 
  | make__RMTC_Config_r16__ext0O__Type None None None None  => false 
  | _ => true 
 end.
Definition RMTC_Config_r16__ext0__Format : T_Format RMTC_Config_r16__ext0__Type RMTC_Config_r16__ext0__cond :=
  restrict_add_format RMTC_Config_r16__ext0__check_all_none RMTC_Config_r16__ext0O__Format.

Opaque RMTC_Config_r16__ext0__cond RMTC_Config_r16__ext0__Format.


Definition RMTC_Config_r16__ext1O__Format_Type := Eval cbn in seq_format_prod RMTC_Config_r16__ext1O__list.
Definition RMTC_Config_r16__ext1O__Format_list : RMTC_Config_r16__ext1O__Format_Type :=
  (BWP_Id__Format, unit_format).
Definition RMTC_Config_r16__ext1O__list__Format := (*Eval compute in *) seq_format RMTC_Config_r16__ext1O__list RMTC_Config_r16__ext1O__Format_list.
Definition RMTC_Config_r16__ext1O__F1 z :=
  (RMTC_Config_r16__ext1O__ref_BWPId_r17 z, tt).
Definition RMTC_Config_r16__ext1O__F2 (y : seq_type RMTC_Config_r16__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__RMTC_Config_r16__ext1O__Type i0
  end.
Lemma RMTC_Config_r16__ext1O__F1F2_cond (z : RMTC_Config_r16__ext1O__Type)
  : RMTC_Config_r16__ext1O__cond z ->
  (seq_cond RMTC_Config_r16__ext1O__list (RMTC_Config_r16__ext1O__F1 z)).
intro H. unfold RMTC_Config_r16__ext1O__cond in H. simpl. auto. Qed.
Lemma RMTC_Config_r16__ext1O__F1F2_cond2 (z : RMTC_Config_r16__ext1O__Type)
 : RMTC_Config_r16__ext1O__F2 (RMTC_Config_r16__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RMTC_Config_r16__ext1O__F2F1_cond (y : seq_type RMTC_Config_r16__ext1O__list)
  : seq_cond RMTC_Config_r16__ext1O__list y ->
 (RMTC_Config_r16__ext1O__cond (RMTC_Config_r16__ext1O__F2 y)) /\  RMTC_Config_r16__ext1O__F1 (RMTC_Config_r16__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RMTC_Config_r16__ext1O__cond. simpl in *. auto.
 - simpl. unfold RMTC_Config_r16__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RMTC_Config_r16__ext1O__Format : T_Format RMTC_Config_r16__ext1O__Type RMTC_Config_r16__ext1O__cond :=
        proj2_format  RMTC_Config_r16__ext1O__cond RMTC_Config_r16__ext1O__list__Format
    RMTC_Config_r16__ext1O__F1 RMTC_Config_r16__ext1O__F2 RMTC_Config_r16__ext1O__F1F2_cond  RMTC_Config_r16__ext1O__F1F2_cond2 RMTC_Config_r16__ext1O__F2F1_cond.
Opaque RMTC_Config_r16__ext1O__cond RMTC_Config_r16__ext1O__Format.

Definition RMTC_Config_r16__ext1__check_all_none (b : RMTC_Config_r16__ext1O__Type) : bool :=
match b with 
  | make__RMTC_Config_r16__ext1O__Type None  => false 
  | _ => true 
 end.
Definition RMTC_Config_r16__ext1__Format : T_Format RMTC_Config_r16__ext1__Type RMTC_Config_r16__ext1__cond :=
  restrict_add_format RMTC_Config_r16__ext1__check_all_none RMTC_Config_r16__ext1O__Format.

Opaque RMTC_Config_r16__ext1__cond RMTC_Config_r16__ext1__Format.


Definition RMTC_Config_r16__root_Format_Type := Eval cbn in seq_format_prod RMTC_Config_r16__root_list.
Definition RMTC_Config_r16__root_Format_list : RMTC_Config_r16__root_Format_Type :=
  (RMTC_Config_r16__rmtc_Periodicity_r16__Format, (RMTC_Config_r16__rmtc_SubframeOffset_r16__Format, (RMTC_Config_r16__measDurationSymbols_r16__Format, (ARFCN_ValueNR__Format, (RMTC_Config_r16__ref_SCS_CP_r16__Format, unit_format))))).

Definition RMTC_Config_r16__ext_Format_Type := Eval cbn in get_formats RMTC_Config_r16__ext_list.
Definition RMTC_Config_r16__ext_Format_list : RMTC_Config_r16__ext_Format_Type :=
  (RMTC_Config_r16__ext0__Format, (RMTC_Config_r16__ext1__Format, unit__Format)).

Definition RMTC_Config_r16__list_type : Set := (seq_type RMTC_Config_r16__root_list) * (seq_ext_type RMTC_Config_r16__ext_list).
Definition RMTC_Config_r16__list_cond (z : RMTC_Config_r16__list_type) : Prop :=
        (seq_cond RMTC_Config_r16__root_list (fst z)) /\ (seq_ext_cond RMTC_Config_r16__ext_list (snd z)).
Definition RMTC_Config_r16__list_format : T_Format RMTC_Config_r16__list_type RMTC_Config_r16__list_cond :=
 (* Eval compute in *) seq_ext_format RMTC_Config_r16__root_list RMTC_Config_r16__root_Format_list RMTC_Config_r16__ext_list RMTC_Config_r16__ext_Format_list.

Opaque RMTC_Config_r16__list_format.
Definition RMTC_Config_r16__F1 (z : RMTC_Config_r16__Type) : RMTC_Config_r16__list_type :=
  (((RMTC_Config_r16__rmtc_Periodicity_r16 z, (RMTC_Config_r16__rmtc_SubframeOffset_r16 z, (RMTC_Config_r16__measDurationSymbols_r16 z, (RMTC_Config_r16__rmtc_Frequency_r16 z, (RMTC_Config_r16__ref_SCS_CP_r16 z, tt)))))), (
(RMTC_Config_r16__ext0 z, (RMTC_Config_r16__ext1 z, tt)))).
Definition RMTC_Config_r16__F2 (y : RMTC_Config_r16__list_type) : RMTC_Config_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), (i0, (i1, _)))=>
    make__RMTC_Config_r16__Type j0 j1 j2 j3 j4 i0 i1
  end.
Definition RMTC_Config_r16__helper1 : (forall a : RMTC_Config_r16__Type, RMTC_Config_r16__cond a -> RMTC_Config_r16__list_cond (RMTC_Config_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RMTC_Config_r16__helper2 : (forall a : RMTC_Config_r16__Type, RMTC_Config_r16__F2 (RMTC_Config_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RMTC_Config_r16__helper3 : (forall b : RMTC_Config_r16__list_type, RMTC_Config_r16__list_cond b -> RMTC_Config_r16__cond (RMTC_Config_r16__F2 b) /\ RMTC_Config_r16__F1 (RMTC_Config_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RMTC_Config_r16__cond, RMTC_Config_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RMTC_Config_r16__Format : T_Format RMTC_Config_r16__Type RMTC_Config_r16__cond :=
 proj2_format RMTC_Config_r16__cond RMTC_Config_r16__list_format  RMTC_Config_r16__F1 RMTC_Config_r16__F2 RMTC_Config_r16__helper1 RMTC_Config_r16__helper2 RMTC_Config_r16__helper3.

Opaque RMTC_Config_r16__cond RMTC_Config_r16__Format.

