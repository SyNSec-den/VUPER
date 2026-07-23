Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MRDC_Parameters__singleUL_Transmission__Type : Set :=
 | MRDC_Parameters__singleUL_Transmission__supported
.
Definition MRDC_Parameters__singleUL_Transmission__cond := (fun (_ : MRDC_Parameters__singleUL_Transmission__Type) => True).
Lemma MRDC_Parameters__singleUL_Transmission__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__singleUL_Transmission__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_Parameters__singleUL_Transmission__nat__helper.

Definition MRDC_Parameters__singleUL_Transmission__F1 t :=
  match t with
  | MRDC_Parameters__singleUL_Transmission__supported => 0
  end.
Definition MRDC_Parameters__singleUL_Transmission__F2 n :=
  match n with
  | 0 => MRDC_Parameters__singleUL_Transmission__supported
  | _ => MRDC_Parameters__singleUL_Transmission__supported
  end.
Lemma MRDC_Parameters__singleUL_Transmission__F1F2 : forall x : MRDC_Parameters__singleUL_Transmission__Type, (MRDC_Parameters__singleUL_Transmission__F1 x <= 0) /\ MRDC_Parameters__singleUL_Transmission__F2 (MRDC_Parameters__singleUL_Transmission__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__singleUL_Transmission__F2F1 : forall (y : nat) (H : y <= 0), MRDC_Parameters__singleUL_Transmission__F1 (MRDC_Parameters__singleUL_Transmission__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__dynamicPowerSharingENDC__Type : Set :=
 | MRDC_Parameters__dynamicPowerSharingENDC__supported
.
Definition MRDC_Parameters__dynamicPowerSharingENDC__cond := (fun (_ : MRDC_Parameters__dynamicPowerSharingENDC__Type) => True).
Lemma MRDC_Parameters__dynamicPowerSharingENDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__dynamicPowerSharingENDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_Parameters__dynamicPowerSharingENDC__nat__helper.

Definition MRDC_Parameters__dynamicPowerSharingENDC__F1 t :=
  match t with
  | MRDC_Parameters__dynamicPowerSharingENDC__supported => 0
  end.
Definition MRDC_Parameters__dynamicPowerSharingENDC__F2 n :=
  match n with
  | 0 => MRDC_Parameters__dynamicPowerSharingENDC__supported
  | _ => MRDC_Parameters__dynamicPowerSharingENDC__supported
  end.
Lemma MRDC_Parameters__dynamicPowerSharingENDC__F1F2 : forall x : MRDC_Parameters__dynamicPowerSharingENDC__Type, (MRDC_Parameters__dynamicPowerSharingENDC__F1 x <= 0) /\ MRDC_Parameters__dynamicPowerSharingENDC__F2 (MRDC_Parameters__dynamicPowerSharingENDC__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__dynamicPowerSharingENDC__F2F1 : forall (y : nat) (H : y <= 0), MRDC_Parameters__dynamicPowerSharingENDC__F1 (MRDC_Parameters__dynamicPowerSharingENDC__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__tdm_Pattern__Type : Set :=
 | MRDC_Parameters__tdm_Pattern__supported
.
Definition MRDC_Parameters__tdm_Pattern__cond := (fun (_ : MRDC_Parameters__tdm_Pattern__Type) => True).
Lemma MRDC_Parameters__tdm_Pattern__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__tdm_Pattern__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_Parameters__tdm_Pattern__nat__helper.

Definition MRDC_Parameters__tdm_Pattern__F1 t :=
  match t with
  | MRDC_Parameters__tdm_Pattern__supported => 0
  end.
Definition MRDC_Parameters__tdm_Pattern__F2 n :=
  match n with
  | 0 => MRDC_Parameters__tdm_Pattern__supported
  | _ => MRDC_Parameters__tdm_Pattern__supported
  end.
Lemma MRDC_Parameters__tdm_Pattern__F1F2 : forall x : MRDC_Parameters__tdm_Pattern__Type, (MRDC_Parameters__tdm_Pattern__F1 x <= 0) /\ MRDC_Parameters__tdm_Pattern__F2 (MRDC_Parameters__tdm_Pattern__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__tdm_Pattern__F2F1 : forall (y : nat) (H : y <= 0), MRDC_Parameters__tdm_Pattern__F1 (MRDC_Parameters__tdm_Pattern__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__ul_SharingEUTRA_NR__Type : Set :=
 | MRDC_Parameters__ul_SharingEUTRA_NR__tdm
 | MRDC_Parameters__ul_SharingEUTRA_NR__fdm
 | MRDC_Parameters__ul_SharingEUTRA_NR__both
.
Definition MRDC_Parameters__ul_SharingEUTRA_NR__cond := (fun (_ : MRDC_Parameters__ul_SharingEUTRA_NR__Type) => True).
Lemma MRDC_Parameters__ul_SharingEUTRA_NR__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__ul_SharingEUTRA_NR__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 MRDC_Parameters__ul_SharingEUTRA_NR__nat__helper.

Definition MRDC_Parameters__ul_SharingEUTRA_NR__F1 t :=
  match t with
  | MRDC_Parameters__ul_SharingEUTRA_NR__tdm => 0
  | MRDC_Parameters__ul_SharingEUTRA_NR__fdm => 1
  | MRDC_Parameters__ul_SharingEUTRA_NR__both => 2
  end.
Definition MRDC_Parameters__ul_SharingEUTRA_NR__F2 n :=
  match n with
  | 0 => MRDC_Parameters__ul_SharingEUTRA_NR__tdm
  | 1 => MRDC_Parameters__ul_SharingEUTRA_NR__fdm
  | 2 => MRDC_Parameters__ul_SharingEUTRA_NR__both
  | _ => MRDC_Parameters__ul_SharingEUTRA_NR__tdm
  end.
Lemma MRDC_Parameters__ul_SharingEUTRA_NR__F1F2 : forall x : MRDC_Parameters__ul_SharingEUTRA_NR__Type, (MRDC_Parameters__ul_SharingEUTRA_NR__F1 x <= 2) /\ MRDC_Parameters__ul_SharingEUTRA_NR__F2 (MRDC_Parameters__ul_SharingEUTRA_NR__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__ul_SharingEUTRA_NR__F2F1 : forall (y : nat) (H : y <= 2), MRDC_Parameters__ul_SharingEUTRA_NR__F1 (MRDC_Parameters__ul_SharingEUTRA_NR__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Type : Set :=
 | MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__type1
 | MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__type2
.
Definition MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__cond := (fun (_ : MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Type) => True).
Lemma MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__nat__helper.

Definition MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F1 t :=
  match t with
  | MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__type1 => 0
  | MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__type2 => 1
  end.
Definition MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F2 n :=
  match n with
  | 0 => MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__type1
  | 1 => MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__type2
  | _ => MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__type1
  end.
Lemma MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F1F2 : forall x : MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Type, (MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F1 x <= 1) /\ MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F2 (MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F2F1 : forall (y : nat) (H : y <= 1), MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F1 (MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__simultaneousRxTxInterBandENDC__Type : Set :=
 | MRDC_Parameters__simultaneousRxTxInterBandENDC__supported
.
Definition MRDC_Parameters__simultaneousRxTxInterBandENDC__cond := (fun (_ : MRDC_Parameters__simultaneousRxTxInterBandENDC__Type) => True).
Lemma MRDC_Parameters__simultaneousRxTxInterBandENDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__simultaneousRxTxInterBandENDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_Parameters__simultaneousRxTxInterBandENDC__nat__helper.

Definition MRDC_Parameters__simultaneousRxTxInterBandENDC__F1 t :=
  match t with
  | MRDC_Parameters__simultaneousRxTxInterBandENDC__supported => 0
  end.
Definition MRDC_Parameters__simultaneousRxTxInterBandENDC__F2 n :=
  match n with
  | 0 => MRDC_Parameters__simultaneousRxTxInterBandENDC__supported
  | _ => MRDC_Parameters__simultaneousRxTxInterBandENDC__supported
  end.
Lemma MRDC_Parameters__simultaneousRxTxInterBandENDC__F1F2 : forall x : MRDC_Parameters__simultaneousRxTxInterBandENDC__Type, (MRDC_Parameters__simultaneousRxTxInterBandENDC__F1 x <= 0) /\ MRDC_Parameters__simultaneousRxTxInterBandENDC__F2 (MRDC_Parameters__simultaneousRxTxInterBandENDC__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__simultaneousRxTxInterBandENDC__F2F1 : forall (y : nat) (H : y <= 0), MRDC_Parameters__simultaneousRxTxInterBandENDC__F1 (MRDC_Parameters__simultaneousRxTxInterBandENDC__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__asyncIntraBandENDC__Type : Set :=
 | MRDC_Parameters__asyncIntraBandENDC__supported
.
Definition MRDC_Parameters__asyncIntraBandENDC__cond := (fun (_ : MRDC_Parameters__asyncIntraBandENDC__Type) => True).
Lemma MRDC_Parameters__asyncIntraBandENDC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__asyncIntraBandENDC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_Parameters__asyncIntraBandENDC__nat__helper.

Definition MRDC_Parameters__asyncIntraBandENDC__F1 t :=
  match t with
  | MRDC_Parameters__asyncIntraBandENDC__supported => 0
  end.
Definition MRDC_Parameters__asyncIntraBandENDC__F2 n :=
  match n with
  | 0 => MRDC_Parameters__asyncIntraBandENDC__supported
  | _ => MRDC_Parameters__asyncIntraBandENDC__supported
  end.
Lemma MRDC_Parameters__asyncIntraBandENDC__F1F2 : forall x : MRDC_Parameters__asyncIntraBandENDC__Type, (MRDC_Parameters__asyncIntraBandENDC__F1 x <= 0) /\ MRDC_Parameters__asyncIntraBandENDC__F2 (MRDC_Parameters__asyncIntraBandENDC__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__asyncIntraBandENDC__F2F1 : forall (y : nat) (H : y <= 0), MRDC_Parameters__asyncIntraBandENDC__F1 (MRDC_Parameters__asyncIntraBandENDC__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__ext0O__dualPA_Architecture__Type : Set :=
 | MRDC_Parameters__ext0O__dualPA_Architecture__supported
.
Definition MRDC_Parameters__ext0O__dualPA_Architecture__cond := (fun (_ : MRDC_Parameters__ext0O__dualPA_Architecture__Type) => True).
Lemma MRDC_Parameters__ext0O__dualPA_Architecture__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__ext0O__dualPA_Architecture__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_Parameters__ext0O__dualPA_Architecture__nat__helper.

Definition MRDC_Parameters__ext0O__dualPA_Architecture__F1 t :=
  match t with
  | MRDC_Parameters__ext0O__dualPA_Architecture__supported => 0
  end.
Definition MRDC_Parameters__ext0O__dualPA_Architecture__F2 n :=
  match n with
  | 0 => MRDC_Parameters__ext0O__dualPA_Architecture__supported
  | _ => MRDC_Parameters__ext0O__dualPA_Architecture__supported
  end.
Lemma MRDC_Parameters__ext0O__dualPA_Architecture__F1F2 : forall x : MRDC_Parameters__ext0O__dualPA_Architecture__Type, (MRDC_Parameters__ext0O__dualPA_Architecture__F1 x <= 0) /\ MRDC_Parameters__ext0O__dualPA_Architecture__F2 (MRDC_Parameters__ext0O__dualPA_Architecture__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__ext0O__dualPA_Architecture__F2F1 : forall (y : nat) (H : y <= 0), MRDC_Parameters__ext0O__dualPA_Architecture__F1 (MRDC_Parameters__ext0O__dualPA_Architecture__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__ext0O__intraBandENDC_Support__Type : Set :=
 | MRDC_Parameters__ext0O__intraBandENDC_Support__non_contiguous
 | MRDC_Parameters__ext0O__intraBandENDC_Support__both
.
Definition MRDC_Parameters__ext0O__intraBandENDC_Support__cond := (fun (_ : MRDC_Parameters__ext0O__intraBandENDC_Support__Type) => True).
Lemma MRDC_Parameters__ext0O__intraBandENDC_Support__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__ext0O__intraBandENDC_Support__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 MRDC_Parameters__ext0O__intraBandENDC_Support__nat__helper.

Definition MRDC_Parameters__ext0O__intraBandENDC_Support__F1 t :=
  match t with
  | MRDC_Parameters__ext0O__intraBandENDC_Support__non_contiguous => 0
  | MRDC_Parameters__ext0O__intraBandENDC_Support__both => 1
  end.
Definition MRDC_Parameters__ext0O__intraBandENDC_Support__F2 n :=
  match n with
  | 0 => MRDC_Parameters__ext0O__intraBandENDC_Support__non_contiguous
  | 1 => MRDC_Parameters__ext0O__intraBandENDC_Support__both
  | _ => MRDC_Parameters__ext0O__intraBandENDC_Support__non_contiguous
  end.
Lemma MRDC_Parameters__ext0O__intraBandENDC_Support__F1F2 : forall x : MRDC_Parameters__ext0O__intraBandENDC_Support__Type, (MRDC_Parameters__ext0O__intraBandENDC_Support__F1 x <= 1) /\ MRDC_Parameters__ext0O__intraBandENDC_Support__F2 (MRDC_Parameters__ext0O__intraBandENDC_Support__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__ext0O__intraBandENDC_Support__F2F1 : forall (y : nat) (H : y <= 1), MRDC_Parameters__ext0O__intraBandENDC_Support__F1 (MRDC_Parameters__ext0O__intraBandENDC_Support__F2 y) = y. enum_solve H y. Qed.

Inductive MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Type : Set :=
 | MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__required
.
Definition MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__cond := (fun (_ : MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Type) => True).
Lemma MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__nat__helper.

Definition MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F1 t :=
  match t with
  | MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__required => 0
  end.
Definition MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F2 n :=
  match n with
  | 0 => MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__required
  | _ => MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__required
  end.
Lemma MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F1F2 : forall x : MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Type, (MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F1 x <= 0) /\ MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F2 (MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F1 x) = x. imp_solve. Qed.
Lemma MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F2F1 : forall (y : nat) (H : y <= 0), MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F1 (MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F2 y) = y. enum_solve H y. Qed.

Record MRDC_Parameters__ext0O__Type : Set :=
  make__MRDC_Parameters__ext0O__Type {
    MRDC_Parameters__ext0O__dualPA_Architecture : option MRDC_Parameters__ext0O__dualPA_Architecture__Type ;
    MRDC_Parameters__ext0O__intraBandENDC_Support : option MRDC_Parameters__ext0O__intraBandENDC_Support__Type ;
    MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR : option MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Type ;
}.
Definition MRDC_Parameters__ext0O__list := (
 Opt MRDC_Parameters__ext0O__dualPA_Architecture__Type MRDC_Parameters__ext0O__dualPA_Architecture__cond ::
 Opt MRDC_Parameters__ext0O__intraBandENDC_Support__Type MRDC_Parameters__ext0O__intraBandENDC_Support__cond ::
 Opt MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Type MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__cond ::
 nil).
Definition MRDC_Parameters__ext0O__cond z := 
  opt_cond MRDC_Parameters__ext0O__dualPA_Architecture__cond (MRDC_Parameters__ext0O__dualPA_Architecture z) /\
  opt_cond MRDC_Parameters__ext0O__intraBandENDC_Support__cond (MRDC_Parameters__ext0O__intraBandENDC_Support z) /\
  opt_cond MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__cond (MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR z) /\
  True.

Definition MRDC_Parameters__ext0__Type := MRDC_Parameters__ext0O__Type.
Definition MRDC_Parameters__ext0__cond := MRDC_Parameters__ext0O__cond.

Record MRDC_Parameters__Type : Set :=
  make__MRDC_Parameters__Type {
    MRDC_Parameters__singleUL_Transmission : option MRDC_Parameters__singleUL_Transmission__Type ;
    MRDC_Parameters__dynamicPowerSharingENDC : option MRDC_Parameters__dynamicPowerSharingENDC__Type ;
    MRDC_Parameters__tdm_Pattern : option MRDC_Parameters__tdm_Pattern__Type ;
    MRDC_Parameters__ul_SharingEUTRA_NR : option MRDC_Parameters__ul_SharingEUTRA_NR__Type ;
    MRDC_Parameters__ul_SwitchingTimeEUTRA_NR : option MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Type ;
    MRDC_Parameters__simultaneousRxTxInterBandENDC : option MRDC_Parameters__simultaneousRxTxInterBandENDC__Type ;
    MRDC_Parameters__asyncIntraBandENDC : option MRDC_Parameters__asyncIntraBandENDC__Type ;
    MRDC_Parameters__ext0 : option MRDC_Parameters__ext0__Type ;
}.
Definition MRDC_Parameters__root_list : list seq_elem := (
 Opt MRDC_Parameters__singleUL_Transmission__Type MRDC_Parameters__singleUL_Transmission__cond ::
 Opt MRDC_Parameters__dynamicPowerSharingENDC__Type MRDC_Parameters__dynamicPowerSharingENDC__cond ::
 Opt MRDC_Parameters__tdm_Pattern__Type MRDC_Parameters__tdm_Pattern__cond ::
 Opt MRDC_Parameters__ul_SharingEUTRA_NR__Type MRDC_Parameters__ul_SharingEUTRA_NR__cond ::
 Opt MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Type MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__cond ::
 Opt MRDC_Parameters__simultaneousRxTxInterBandENDC__Type MRDC_Parameters__simultaneousRxTxInterBandENDC__cond ::
 Opt MRDC_Parameters__asyncIntraBandENDC__Type MRDC_Parameters__asyncIntraBandENDC__cond ::
 nil).
Definition MRDC_Parameters__ext_list : list typ := (
  typ_cons MRDC_Parameters__ext0__Type MRDC_Parameters__ext0__cond ::
  nil).
Definition MRDC_Parameters__cond (z : MRDC_Parameters__Type) := 
(  opt_cond MRDC_Parameters__singleUL_Transmission__cond (MRDC_Parameters__singleUL_Transmission z) /\
  opt_cond MRDC_Parameters__dynamicPowerSharingENDC__cond (MRDC_Parameters__dynamicPowerSharingENDC z) /\
  opt_cond MRDC_Parameters__tdm_Pattern__cond (MRDC_Parameters__tdm_Pattern z) /\
  opt_cond MRDC_Parameters__ul_SharingEUTRA_NR__cond (MRDC_Parameters__ul_SharingEUTRA_NR z) /\
  opt_cond MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__cond (MRDC_Parameters__ul_SwitchingTimeEUTRA_NR z) /\
  opt_cond MRDC_Parameters__simultaneousRxTxInterBandENDC__cond (MRDC_Parameters__simultaneousRxTxInterBandENDC z) /\
  opt_cond MRDC_Parameters__asyncIntraBandENDC__cond (MRDC_Parameters__asyncIntraBandENDC z) /\
  True) /\ 
(  opt_cond MRDC_Parameters__ext0__cond (MRDC_Parameters__ext0 z) /\
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
Definition MRDC_Parameters__singleUL_Transmission__Format : T_Format MRDC_Parameters__singleUL_Transmission__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__singleUL_Transmission__nat__Format MRDC_Parameters__singleUL_Transmission__F1 MRDC_Parameters__singleUL_Transmission__F2 MRDC_Parameters__singleUL_Transmission__F1F2 MRDC_Parameters__singleUL_Transmission__F2F1.

Opaque MRDC_Parameters__singleUL_Transmission__cond MRDC_Parameters__singleUL_Transmission__Format.

Definition MRDC_Parameters__dynamicPowerSharingENDC__Format : T_Format MRDC_Parameters__dynamicPowerSharingENDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__dynamicPowerSharingENDC__nat__Format MRDC_Parameters__dynamicPowerSharingENDC__F1 MRDC_Parameters__dynamicPowerSharingENDC__F2 MRDC_Parameters__dynamicPowerSharingENDC__F1F2 MRDC_Parameters__dynamicPowerSharingENDC__F2F1.

Opaque MRDC_Parameters__dynamicPowerSharingENDC__cond MRDC_Parameters__dynamicPowerSharingENDC__Format.

Definition MRDC_Parameters__tdm_Pattern__Format : T_Format MRDC_Parameters__tdm_Pattern__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__tdm_Pattern__nat__Format MRDC_Parameters__tdm_Pattern__F1 MRDC_Parameters__tdm_Pattern__F2 MRDC_Parameters__tdm_Pattern__F1F2 MRDC_Parameters__tdm_Pattern__F2F1.

Opaque MRDC_Parameters__tdm_Pattern__cond MRDC_Parameters__tdm_Pattern__Format.

Definition MRDC_Parameters__ul_SharingEUTRA_NR__Format : T_Format MRDC_Parameters__ul_SharingEUTRA_NR__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__ul_SharingEUTRA_NR__nat__Format MRDC_Parameters__ul_SharingEUTRA_NR__F1 MRDC_Parameters__ul_SharingEUTRA_NR__F2 MRDC_Parameters__ul_SharingEUTRA_NR__F1F2 MRDC_Parameters__ul_SharingEUTRA_NR__F2F1.

Opaque MRDC_Parameters__ul_SharingEUTRA_NR__cond MRDC_Parameters__ul_SharingEUTRA_NR__Format.

Definition MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Format : T_Format MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__nat__Format MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F1 MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F2 MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F1F2 MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__F2F1.

Opaque MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__cond MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Format.

Definition MRDC_Parameters__simultaneousRxTxInterBandENDC__Format : T_Format MRDC_Parameters__simultaneousRxTxInterBandENDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__simultaneousRxTxInterBandENDC__nat__Format MRDC_Parameters__simultaneousRxTxInterBandENDC__F1 MRDC_Parameters__simultaneousRxTxInterBandENDC__F2 MRDC_Parameters__simultaneousRxTxInterBandENDC__F1F2 MRDC_Parameters__simultaneousRxTxInterBandENDC__F2F1.

Opaque MRDC_Parameters__simultaneousRxTxInterBandENDC__cond MRDC_Parameters__simultaneousRxTxInterBandENDC__Format.

Definition MRDC_Parameters__asyncIntraBandENDC__Format : T_Format MRDC_Parameters__asyncIntraBandENDC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__asyncIntraBandENDC__nat__Format MRDC_Parameters__asyncIntraBandENDC__F1 MRDC_Parameters__asyncIntraBandENDC__F2 MRDC_Parameters__asyncIntraBandENDC__F1F2 MRDC_Parameters__asyncIntraBandENDC__F2F1.

Opaque MRDC_Parameters__asyncIntraBandENDC__cond MRDC_Parameters__asyncIntraBandENDC__Format.

Definition MRDC_Parameters__ext0O__dualPA_Architecture__Format : T_Format MRDC_Parameters__ext0O__dualPA_Architecture__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__ext0O__dualPA_Architecture__nat__Format MRDC_Parameters__ext0O__dualPA_Architecture__F1 MRDC_Parameters__ext0O__dualPA_Architecture__F2 MRDC_Parameters__ext0O__dualPA_Architecture__F1F2 MRDC_Parameters__ext0O__dualPA_Architecture__F2F1.

Opaque MRDC_Parameters__ext0O__dualPA_Architecture__cond MRDC_Parameters__ext0O__dualPA_Architecture__Format.

Definition MRDC_Parameters__ext0O__intraBandENDC_Support__Format : T_Format MRDC_Parameters__ext0O__intraBandENDC_Support__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__ext0O__intraBandENDC_Support__nat__Format MRDC_Parameters__ext0O__intraBandENDC_Support__F1 MRDC_Parameters__ext0O__intraBandENDC_Support__F2 MRDC_Parameters__ext0O__intraBandENDC_Support__F1F2 MRDC_Parameters__ext0O__intraBandENDC_Support__F2F1.

Opaque MRDC_Parameters__ext0O__intraBandENDC_Support__cond MRDC_Parameters__ext0O__intraBandENDC_Support__Format.

Definition MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Format : T_Format MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__nat__Format MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F1 MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F2 MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F1F2 MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__F2F1.

Opaque MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__cond MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Format.


Definition MRDC_Parameters__ext0O__Format_Type := Eval cbn in seq_format_prod MRDC_Parameters__ext0O__list.
Definition MRDC_Parameters__ext0O__Format_list : MRDC_Parameters__ext0O__Format_Type :=
  (MRDC_Parameters__ext0O__dualPA_Architecture__Format, (MRDC_Parameters__ext0O__intraBandENDC_Support__Format, (MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR__Format, unit_format))).
Definition MRDC_Parameters__ext0O__list__Format := (*Eval compute in *) seq_format MRDC_Parameters__ext0O__list MRDC_Parameters__ext0O__Format_list.
Definition MRDC_Parameters__ext0O__F1 z :=
  (MRDC_Parameters__ext0O__dualPA_Architecture z, (MRDC_Parameters__ext0O__intraBandENDC_Support z, (MRDC_Parameters__ext0O__ul_TimingAlignmentEUTRA_NR z, tt))).
Definition MRDC_Parameters__ext0O__F2 (y : seq_type MRDC_Parameters__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MRDC_Parameters__ext0O__Type i0 i1 i2
  end.
Lemma MRDC_Parameters__ext0O__F1F2_cond (z : MRDC_Parameters__ext0O__Type)
  : MRDC_Parameters__ext0O__cond z ->
  (seq_cond MRDC_Parameters__ext0O__list (MRDC_Parameters__ext0O__F1 z)).
intro H. unfold MRDC_Parameters__ext0O__cond in H. simpl. auto. Qed.
Lemma MRDC_Parameters__ext0O__F1F2_cond2 (z : MRDC_Parameters__ext0O__Type)
 : MRDC_Parameters__ext0O__F2 (MRDC_Parameters__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRDC_Parameters__ext0O__F2F1_cond (y : seq_type MRDC_Parameters__ext0O__list)
  : seq_cond MRDC_Parameters__ext0O__list y ->
 (MRDC_Parameters__ext0O__cond (MRDC_Parameters__ext0O__F2 y)) /\  MRDC_Parameters__ext0O__F1 (MRDC_Parameters__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRDC_Parameters__ext0O__cond. simpl in *. auto.
 - simpl. unfold MRDC_Parameters__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRDC_Parameters__ext0O__Format : T_Format MRDC_Parameters__ext0O__Type MRDC_Parameters__ext0O__cond :=
        proj2_format  MRDC_Parameters__ext0O__cond MRDC_Parameters__ext0O__list__Format
    MRDC_Parameters__ext0O__F1 MRDC_Parameters__ext0O__F2 MRDC_Parameters__ext0O__F1F2_cond  MRDC_Parameters__ext0O__F1F2_cond2 MRDC_Parameters__ext0O__F2F1_cond.
Opaque MRDC_Parameters__ext0O__cond MRDC_Parameters__ext0O__Format.

Definition MRDC_Parameters__ext0__check_all_none (b : MRDC_Parameters__ext0O__Type) : bool :=
match b with 
  | make__MRDC_Parameters__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition MRDC_Parameters__ext0__Format : T_Format MRDC_Parameters__ext0__Type MRDC_Parameters__ext0__cond :=
  restrict_add_format MRDC_Parameters__ext0__check_all_none MRDC_Parameters__ext0O__Format.

Opaque MRDC_Parameters__ext0__cond MRDC_Parameters__ext0__Format.


Definition MRDC_Parameters__root_Format_Type := Eval cbn in seq_format_prod MRDC_Parameters__root_list.
Definition MRDC_Parameters__root_Format_list : MRDC_Parameters__root_Format_Type :=
  (MRDC_Parameters__singleUL_Transmission__Format, (MRDC_Parameters__dynamicPowerSharingENDC__Format, (MRDC_Parameters__tdm_Pattern__Format, (MRDC_Parameters__ul_SharingEUTRA_NR__Format, (MRDC_Parameters__ul_SwitchingTimeEUTRA_NR__Format, (MRDC_Parameters__simultaneousRxTxInterBandENDC__Format, (MRDC_Parameters__asyncIntraBandENDC__Format, unit_format))))))).

Definition MRDC_Parameters__ext_Format_Type := Eval cbn in get_formats MRDC_Parameters__ext_list.
Definition MRDC_Parameters__ext_Format_list : MRDC_Parameters__ext_Format_Type :=
  (MRDC_Parameters__ext0__Format, unit__Format).

Definition MRDC_Parameters__list_type : Set := (seq_type MRDC_Parameters__root_list) * (seq_ext_type MRDC_Parameters__ext_list).
Definition MRDC_Parameters__list_cond (z : MRDC_Parameters__list_type) : Prop :=
        (seq_cond MRDC_Parameters__root_list (fst z)) /\ (seq_ext_cond MRDC_Parameters__ext_list (snd z)).
Definition MRDC_Parameters__list_format : T_Format MRDC_Parameters__list_type MRDC_Parameters__list_cond :=
 (* Eval compute in *) seq_ext_format MRDC_Parameters__root_list MRDC_Parameters__root_Format_list MRDC_Parameters__ext_list MRDC_Parameters__ext_Format_list.

Opaque MRDC_Parameters__list_format.
Definition MRDC_Parameters__F1 (z : MRDC_Parameters__Type) : MRDC_Parameters__list_type :=
  (((MRDC_Parameters__singleUL_Transmission z, (MRDC_Parameters__dynamicPowerSharingENDC z, (MRDC_Parameters__tdm_Pattern z, (MRDC_Parameters__ul_SharingEUTRA_NR z, (MRDC_Parameters__ul_SwitchingTimeEUTRA_NR z, (MRDC_Parameters__simultaneousRxTxInterBandENDC z, (MRDC_Parameters__asyncIntraBandENDC z, tt)))))))), (
(MRDC_Parameters__ext0 z, tt))).
Definition MRDC_Parameters__F2 (y : MRDC_Parameters__list_type) : MRDC_Parameters__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, _))))))), (i0, _))=>
    make__MRDC_Parameters__Type j0 j1 j2 j3 j4 j5 j6 i0
  end.
Definition MRDC_Parameters__helper1 : (forall a : MRDC_Parameters__Type, MRDC_Parameters__cond a -> MRDC_Parameters__list_cond (MRDC_Parameters__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MRDC_Parameters__helper2 : (forall a : MRDC_Parameters__Type, MRDC_Parameters__F2 (MRDC_Parameters__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MRDC_Parameters__helper3 : (forall b : MRDC_Parameters__list_type, MRDC_Parameters__list_cond b -> MRDC_Parameters__cond (MRDC_Parameters__F2 b) /\ MRDC_Parameters__F1 (MRDC_Parameters__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MRDC_Parameters__cond, MRDC_Parameters__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MRDC_Parameters__Format : T_Format MRDC_Parameters__Type MRDC_Parameters__cond :=
 proj2_format MRDC_Parameters__cond MRDC_Parameters__list_format  MRDC_Parameters__F1 MRDC_Parameters__F2 MRDC_Parameters__helper1 MRDC_Parameters__helper2 MRDC_Parameters__helper3.

Opaque MRDC_Parameters__cond MRDC_Parameters__Format.

